if (NOT ( (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "STM32FXX") ) )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
    # stm32f2xx_hal_eth.h
    # stm32f4xx_hal_eth.h
    stm32f7xx_hal_eth.h  # Only one of these ?
    stm32fxx_hal_eth.c
    stm32fxx_hal_eth.h
)
