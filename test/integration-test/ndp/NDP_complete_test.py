import socket
import time
from scapy.all import *
from scapy.layers.inet6 import IPv6, ICMPv6ND_NS, ICMPv6ND_NA, ICMPv6NDOptSrcLLAddr, ICMPv6NDOptDstLLAddr

# === CONFIGURATION ===
DUT_IP_V4 = "192.168.1.11"
DUT_CLI_PORT = 2402
DUT_LOG_PORT = 2403
IFACE_NAME = "Gigabit"
DUT_IPV6 = "fe80::7004"
LAPTOP_IPV6 = "fe80::45ca:55bb:17d4:3ca0"
LAPTOP_MAC = conf.ifaces.dev_from_name(IFACE_NAME).mac

def send_dut_cmd(cmd):
    """Sends a command to the DUT UDP CLI."""
    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
        s.sendto(f"{cmd}\n".encode(), (DUT_IP_V4, DUT_CLI_PORT))

def test_header(name):
    print(f"\n{'='*60}\nTEST: {name}\n{'='*60}")

def resolve_address(lladdr, target=LAPTOP_IPV6):
    """Get an address into the DUT's cache the only way the stack allows.

    The DUT never learns a neighbor from an advertisement it did not ask for, so
    a binding can only be established by provoking a Neighbor Solicitation and
    answering it. Returns True when the DUT solicited and was answered.
    """
    sniffer = AsyncSniffer(iface=IFACE_NAME,
                           filter=f"icmp6 and ip6 src {DUT_IPV6} and ip6[40] == 135")
    sniffer.start()

    send_dut_cmd(f"ping6 {target}")
    time.sleep(2)
    pkts = sniffer.stop()

    if not pkts:
        print("[FAIL] DUT did not send a Neighbor Solicitation.")
        return False

    na = (Ether(dst=pkts[0].src)/IPv6(src=target, dst=DUT_IPV6)/
          ICMPv6ND_NA(tgt=target, R=0, S=1, O=1)/
          ICMPv6NDOptDstLLAddr(lladdr=lladdr))
    sendp(na, iface=IFACE_NAME, verbose=False)
    time.sleep(0.5)
    return True

# === TEST 1: Standard Resolution (Incomplete -> Reachable) ===
def test_standard_resolution():
    test_header("Standard Resolution (Solicited)")
    send_dut_cmd("clearn")
    time.sleep(0.1)

    if resolve_address(LAPTOP_MAC):
        print("[PASS] DUT sent Neighbor Solicitation and was answered.")
        print("[RESULT] Cache should hold the real MAC as REACHABLE:")
        send_dut_cmd("cachen")

# === TEST 2: Security - Hop Limit Check (RFC 4861 Sec 6.1.1) ===
def test_hop_limit_security():
    test_header("Security: Hop Limit Check")
    # RFC 4861: Discard any NDP packet where Hop Limit != 255
    send_dut_cmd("clearn")
    time.sleep(0.1)

    print("[INFO] Sending NA with Hop Limit = 64 (Should be ignored)")
    bad_na = (Ether()/IPv6(src=LAPTOP_IPV6, dst=DUT_IPV6, hlim=64)/
              ICMPv6ND_NA(tgt=LAPTOP_IPV6, R=0, S=0, O=1)/
              ICMPv6NDOptDstLLAddr(lladdr=LAPTOP_MAC))
    sendp(bad_na, iface=IFACE_NAME, verbose=False)

    time.sleep(0.5)
    print("[INFO] Cache should be empty (check DUT logs):")
    send_dut_cmd("cachen")

# === TEST 3: Packet Queueing (RFC 4861 Sec 7.2.2) ===
def test_packet_queueing():
    test_header("Packet Queueing during Resolution")
    send_dut_cmd("clearn")
    time.sleep(0.1)

    # We sniff for the resulting Echo Request (ping) and for the solicitation.
    ping_sniffer = AsyncSniffer(iface=IFACE_NAME,
                               filter=f"icmp6 and ip6 src {DUT_IPV6} and ip6[40] == 128")
    ping_sniffer.start()
    ns_sniffer = AsyncSniffer(iface=IFACE_NAME,
                              filter=f"icmp6 and ip6 src {DUT_IPV6} and ip6[40] == 135")
    ns_sniffer.start()

    print("[INFO] Triggering 3 pings rapidly...")
    for _ in range(3):
        send_dut_cmd(f"ping6 {LAPTOP_IPV6}")

    time.sleep(1)
    ns_pkts = ns_sniffer.stop()

    if not ns_pkts:
        ping_sniffer.stop()
        print("[FAIL] DUT did not solicit the address.")
        return

    # Answer the DUT's own solicitation so the resolution completes.
    na = (Ether(dst=ns_pkts[0].src)/IPv6(src=LAPTOP_IPV6, dst=DUT_IPV6)/
          ICMPv6ND_NA(tgt=LAPTOP_IPV6, R=0, S=1, O=1)/
          ICMPv6NDOptDstLLAddr(lladdr=LAPTOP_MAC))
    sendp(na, iface=IFACE_NAME, verbose=False)

    time.sleep(1)
    pkts = ping_sniffer.stop()
    print(f"[RESULT] Captured {len(pkts)} queued pings released after NA.")
    if len(pkts) >= 1:
        print("[PASS] At least one packet was queued and released.")
    else:
        print("[FAIL] No packets released.")

# === TEST 4: Override Flag Logic (RFC 4861 Sec 7.2.5) ===
def test_override_flag():
    test_header("Override Flag Logic (O=0)")
    send_dut_cmd("clearn")
    time.sleep(0.1)

    # 1. Establish the real binding through a solicitation of the DUT's own.
    if not resolve_address(LAPTOP_MAC):
        return

    # 2. An attacker answers with a different MAC but Override=0.
    fake_mac = "00:de:ad:be:ef:00"
    print(f"[INFO] Sending attacker MAC {fake_mac} with Override=0")
    na = (Ether()/IPv6(src=LAPTOP_IPV6, dst=DUT_IPV6)/
          ICMPv6ND_NA(tgt=LAPTOP_IPV6, R=0, S=1, O=0)/
          ICMPv6NDOptDstLLAddr(lladdr=fake_mac))
    sendp(na, iface=IFACE_NAME, verbose=False)

    time.sleep(0.5)
    print(f"[RESULT] Cache MAC should still be the REAL one ({LAPTOP_MAC}), "
          "state demoted to STALE (check logs):")
    send_dut_cmd("cachen")

# === TEST 5: Unsolicited advertisement cannot seed the cache (RFC 4861 Sec 7.2.5) ===
def test_unsolicited_na_does_not_create_entry():
    test_header("Security: Unsolicited NA for an unknown target")
    send_dut_cmd("clearn")
    time.sleep(0.1)

    # An on-link attacker claims an address the DUT has not asked about. RFC 4861
    # says such an advertisement is silently discarded; accepting it would let the
    # attacker own e.g. the gateway binding before it is ever resolved.
    fake_mac = "00:de:ad:be:ef:00"
    print(f"[INFO] Injecting unsolicited NA for {LAPTOP_IPV6} with MAC {fake_mac}")
    for solicited, override in ((0, 1), (1, 1), (0, 0), (1, 0)):
        na = (Ether()/IPv6(src=LAPTOP_IPV6, dst=DUT_IPV6)/
              ICMPv6ND_NA(tgt=LAPTOP_IPV6, R=0, S=solicited, O=override)/
              ICMPv6NDOptDstLLAddr(lladdr=fake_mac))
        sendp(na, iface=IFACE_NAME, verbose=False)
        time.sleep(0.2)

    print("[RESULT] Cache must still be EMPTY (check DUT logs):")
    send_dut_cmd("cachen")

# === TEST 6: Unsolicited Override=1 must not replace a known MAC (RFC 3756 Sec 4.1.1) ===
def test_unsolicited_override_does_not_replace_mac():
    test_header("Security: Unsolicited NA with Override=1 on a known entry")
    send_dut_cmd("clearn")
    time.sleep(0.1)

    # 1. Establish the real binding through a solicitation of the DUT's own.
    if not resolve_address(LAPTOP_MAC):
        return

    # 2. The classic poisoning packet: unsolicited, Override set, different MAC.
    fake_mac = "00:de:ad:be:ef:00"
    print(f"[INFO] Sending unsolicited Override=1 NA with MAC {fake_mac}")
    na = (Ether()/IPv6(src=LAPTOP_IPV6, dst=DUT_IPV6)/
          ICMPv6ND_NA(tgt=LAPTOP_IPV6, R=0, S=0, O=1)/
          ICMPv6NDOptDstLLAddr(lladdr=fake_mac))
    sendp(na, iface=IFACE_NAME, verbose=False)

    # The DUT keeps the cached MAC and verifies it with a unicast NS instead.
    sniffer = AsyncSniffer(iface=IFACE_NAME,
                          filter=f"icmp6 and ip6 src {DUT_IPV6} and ip6[40] == 135")
    sniffer.start()
    time.sleep(12)
    probes = sniffer.stop()

    print(f"[RESULT] Cache MAC must still be the REAL one ({LAPTOP_MAC}).")
    print(f"[RESULT] Captured {len(probes)} NUD probe(s) verifying the binding.")
    send_dut_cmd("cachen")

# === EXECUTION ===
if __name__ == "__main__":
    # Ensure you run as Admin
    test_standard_resolution()
    test_hop_limit_security()
    test_packet_queueing()
    test_override_flag()
    test_unsolicited_na_does_not_create_entry()
    test_unsolicited_override_does_not_replace_mac()
