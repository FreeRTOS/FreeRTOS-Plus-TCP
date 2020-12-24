# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.

# Kernel source files.
set( KERNEL_SOURCES
      "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/list.c"
      "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/queue.c"
      "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/tasks.c"
      "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/portable/ThirdParty/GCC/Posix/port.c"
      "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/portable/ThirdParty/GCC/Posix/utils/wait_for_event.c" )

# TCP library source files.
set( TCP_SOURCES
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_ARP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_BitConfig.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_DNS.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_DHCP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_DHCPv6.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_IP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_ND.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_RA.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_Routing.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_Sockets.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_Stream_Buffer.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_TCP_IP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_TCP_WIN.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../FreeRTOS_UDP_IP.c" )

# TCP library Include directories.
set( TCP_INCLUDE_DIRS
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/include"
     "${CMAKE_CURRENT_LIST_DIR}/../../include"
     "${CMAKE_CURRENT_LIST_DIR}/../../portable/Buffermanagement"
     "${CMAKE_CURRENT_LIST_DIR}/../../portable/Compiler/GCC"
     "${CMAKE_CURRENT_LIST_DIR}/stubs" )

