if (NOT ( (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "STM32") ) )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

set( FREERTOS_PLUS_TCP_STM32_IF_DRIVER "None" CACHE STRING "The driver sources to use with STM32 Network interface" )
set_property( CACHE FREERTOS_PLUS_TCP_STM32_IF_DRIVER PROPERTY STRINGS None F1 F2 F4 F7 H5 H7 H7RS N6 )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F1>:
      Drivers/F1/stm32f1xx_hal_eth.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F2>:
      Drivers/F2/stm32f2xx_hal_eth.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F4>:
      Drivers/F4/stm32f4xx_hal_eth.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F7>:
      Drivers/F7/stm32f7xx_hal_eth.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H5>:
      Drivers/H5/stm32h5xx_hal_eth_ex.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H5>:
      Drivers/H5/stm32h5xx_hal_eth.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H7>:
      Drivers/H7/stm32h7xx_hal_eth_ex.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H7>:
      Drivers/H7/stm32h7xx_hal_eth.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H7RS>:
      Drivers/H7RS/stm32h7rsxx_hal_eth_ex.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H7RS>:
      Drivers/H7RS/stm32h7rsxx_hal_eth.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},N6>:
      Drivers/N6/stm32n6xx_hal_eth_ex.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},N6>:
      Drivers/N6/stm32n6xx_hal_eth.c>
)

target_include_directories( freertos_plus_tcp_network_if
  PUBLIC
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F1>:
      Drivers/F1>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F2>:
      Drivers/F2>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F4>:
      Drivers/F4>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F7>:
      Drivers/F7>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H5>:
      Drivers/H5>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H7>:
      Drivers/H7>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H7RS>:
      Drivers/H7RS>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},N6>:
      Drivers/N6>
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
