The FreeRTOS+TCP IPv6/multiple-interface source code and example projects are
currently provided in the FreeRTOS+TCP repository's "feature/ipv6_multi_beta"
branch. These demos only require the FreeRTOS+TCP IPv6/multiple Interface
source code and the FreeRTOS-Kernel.

The FreeRTOS+TCP Multiple Interface Visual Studio project file is in the following
directory: demos\Multi_interface_demo

The Multiple Interface Visual studio demo showcases the Multiple Interfaces (or
rather the multiple endpoints) functionality of the FreeRTOS+TCP
IPv6/multi-interface library. The Windows Simulator environment doesn't actually
have multiple interfaces which can be used by FreeRTOS and thus, this demo shows
the use of different endpoints which will be resolved by the OS having multiple
interfaces. It shows that the library will use different endpoints (IP-addresses)
to connect to IP-addresses on different subnets (or using different netmasks).
The instructions for the full Windows demo are still relevant though as they
describe how to set up the WinPCap development environment, how to set the IP
address, and other such items. Note that, as delivered, configUSE_DHCP is set to 0,
so a static IP address is used. The instructions are provided on the following URL,
see the "Hardware Setup" section:
http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html

