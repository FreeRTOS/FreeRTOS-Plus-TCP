# Copyright 2024 Arm Limited and/or its affiliates
# <open-source-office@arm.com>
# SPDX-License-Identifier: MIT

if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "MPS4_CS315") )
    return()
endif()

add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    ${CMAKE_CURRENT_LIST_DIR}/../CMSIS/NetworkInterface.c
    CMSIS_Driver/ETH_LAN91C111.c
)

target_include_directories( freertos_plus_tcp_network_if
  PRIVATE
    ${CMAKE_CURRENT_LIST_DIR}/../CMSIS/Driver/Include
    CMSIS_Driver
    Device/Include
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
