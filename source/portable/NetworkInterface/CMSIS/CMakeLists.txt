# Copyright 2024 Arm Limited and/or its affiliates
# <open-source-office@arm.com>
# SPDX-License-Identifier: MIT

if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "CMSIS") )
    return()
endif()

# Optional:
#   - FREERTOS_PLUS_TCP_CMSIS_DRIVER_SOURCES:
#       Semicolon-separated list of board-specific CMSIS MAC/PHY driver sources
#       (example: EMAC_STM32F7xx.c;PHY_LAN8742A.c)
#   - FREERTOS_PLUS_TCP_CMSIS_DRIVER_INCLUDE_DIRS:
#       Semicolon-separated include directories required by those drivers
set(FREERTOS_PLUS_TCP_CMSIS_DRIVER_SOURCES "" CACHE STRING "Extra CMSIS MAC/PHY driver source files")
set(FREERTOS_PLUS_TCP_CMSIS_DRIVER_INCLUDE_DIRS "" CACHE STRING "Extra include directories for CMSIS MAC/PHY drivers")

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
)

target_include_directories( freertos_plus_tcp_network_if
  PRIVATE
    Driver/Include
)

if(FREERTOS_PLUS_TCP_CMSIS_DRIVER_SOURCES)
  target_sources( freertos_plus_tcp_network_if
    PRIVATE
      ${FREERTOS_PLUS_TCP_CMSIS_DRIVER_SOURCES}
  )
endif()

if(FREERTOS_PLUS_TCP_CMSIS_DRIVER_INCLUDE_DIRS)
  target_include_directories( freertos_plus_tcp_network_if
    PRIVATE
      ${FREERTOS_PLUS_TCP_CMSIS_DRIVER_INCLUDE_DIRS}
  )
endif()

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
