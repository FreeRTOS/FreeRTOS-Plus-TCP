# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.

# TCP library source files.
set( TCP_SOURCES
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_ARP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_DNS.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../DNS/DNS_Cache.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../DNS/DNS_Parser.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../DNS/DNS_Networking.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../DNS/DNS_Callback.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_DHCP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_ICMP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_IP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_IP_Utils.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_IP_Timers.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_Sockets.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_Stream_Buffer.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_TCP_IP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_TCP_WIN.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_Tiny_TCP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_UDP_IP.c" )

# TCP library Include directories.
set( TCP_INCLUDE_DIRS
     ${CMAKE_CURRENT_LIST_DIR}/../../include
     ${CMAKE_CURRENT_LIST_DIR}/../../include/DNS
     ${CMAKE_CURRENT_LIST_DIR}/../../portable/Buffermanagement
     ${CMAKE_CURRENT_LIST_DIR}/../../portable/Compiler/MSVC
     ${CMAKE_CURRENT_LIST_DIR}/stubs )

set( KERNEL_SOURCES
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/croutine.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/event_groups.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/list.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/queue.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/stream_buffer.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/tasks.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/timers.c" )
