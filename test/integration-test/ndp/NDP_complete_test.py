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

# === TEST 1: Standard Resolution (Incomplete -> Reachable) ===
def test_standard_resolution():
    test_header("Standard Resolution (Solicited)")
    send_dut_cmd("clearn")
    time.sleep(0.1)

    # Start sniffer for the NS
    sniffer = AsyncSniffer(iface=IFACE_NAME, filter=f"icmp6 and ip6 src {DUT_IPV6} and ip6[40] == 135")
    sniffer.start()
    
    send_dut_cmd(f"ping6 {LAPTOP_IPV6}")
    time.sleep(2)
    pkts = sniffer.stop()

    if pkts:
        print("[PASS] DUT sent Neighbor Solicitation.")
        ns = pkts[0]
        # Send NA back
        na = (Ether(dst=ns.src)/IPv6(src=LAPTOP_IPV6, dst=DUT_IPV6)/
              ICMPv6ND_NA(tgt=LAPTOP_IPV6, R=0, S=1, O=1)/
              ICMPv6NDOptDstLLAddr(lladdr=LAPTOP_MAC))
        sendp(na, iface=IFACE_NAME, verbose=False)
        print("[INFO] Sent NA response. Checking cache...")
        time.sleep(0.5)
        send_dut_cmd("cachen") # Check logs for REACHABLE
    else:
        print("[FAIL] DUT did not send NS.")

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

    # We sniff for the resulting Echo Request (ping)
    sniffer = AsyncSniffer(iface=IFACE_NAME, filter=f"icmp6 and ip6 src {DUT_IPV6} and ip6[40] == 128")
    sniffer.start()

    print("[INFO] Triggering 3 pings rapidly...")
    for _ in range(3):
        send_dut_cmd(f"ping6 {LAPTOP_IPV6}")
    
    # Send NA to resolve the address
    time.sleep(0.5)
    na = (Ether()/IPv6(src=LAPTOP_IPV6, dst=DUT_IPV6)/
          ICMPv6ND_NA(tgt=LAPTOP_IPV6, R=0, S=0, O=1)/
          ICMPv6NDOptDstLLAddr(lladdr=LAPTOP_MAC))
    sendp(na, iface=IFACE_NAME, verbose=False)

    time.sleep(1)
    pkts = sniffer.stop()
    print(f"[RESULT] Captured {len(pkts)} queued pings released after NA.")
    if len(pkts) >= 1:
        print("[PASS] At least one packet was queued and released.")
    else:
        print("[FAIL] No packets released.")

# === TEST 4: Override Flag Logic (RFC 4861 Sec 7.2.5) ===
def test_override_flag():
    test_header("Override Flag Logic (O=0)")
    send_dut_cmd("clearn")
    
    # 1. Inject a fake MAC with O=1
    fake_mac = "00:de:ad:be:ef:00"
    print(f"[INFO] Injecting initial MAC: {fake_mac}")
    na1 = (Ether()/IPv6(src=LAPTOP_IPV6, dst=DUT_IPV6)/
           ICMPv6ND_NA(tgt=LAPTOP_IPV6, R=0, S=0, O=1)/
           ICMPv6NDOptDstLLAddr(lladdr=fake_mac))
    sendp(na1, iface=IFACE_NAME, verbose=False)
    time.sleep(0.2)

    # 2. Send NA with real MAC but O=0
    print(f"[INFO] Sending real MAC {LAPTOP_MAC} but with Override=0")
    na2 = (Ether()/IPv6(src=LAPTOP_IPV6, dst=DUT_IPV6)/
           ICMPv6ND_NA(tgt=LAPTOP_IPV6, R=0, S=1, O=0)/
           ICMPv6NDOptDstLLAddr(lladdr=LAPTOP_MAC))
    sendp(na2, iface=IFACE_NAME, verbose=False)
    
    time.sleep(0.5)
    print("[RESULT] Cache MAC should still be the FAKE one (check logs):")
    send_dut_cmd("cachen")

# === EXECUTION ===
if __name__ == "__main__":
    # Ensure you run as Admin
    test_standard_resolution()
    test_hop_limit_security()
    test_packet_queueing()
    test_override_flag()