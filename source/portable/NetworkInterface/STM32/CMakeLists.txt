if (NOT ( (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "STM32") ) )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

set( FREERTOS_PLUS_TCP_STM32_IF_DRIVER "None" CACHE STRING "The driver sources to use with STM32 Network interface" )

if (FREERTOS_PLUS_TCP_STM32_IF_DRIVER STREQUAL "F4")
  FetchContent_Declare(stm32-eth-driver
      GIT_REPOSITORY https://github.com/STMicroelectronics/stm32f4xx-hal-driver.git
      GIT_TAG v1.8.4
      GIT_SHALLOW TRUE
  )
elseif (FREERTOS_PLUS_TCP_STM32_IF_DRIVER STREQUAL "F7")
  FetchContent_Declare(stm32-eth-driver
      GIT_REPOSITORY https://github.com/STMicroelectronics/stm32f7xx-hal-driver.git
      GIT_TAG v1.3.2
      GIT_SHALLOW TRUE
  )
elseif (FREERTOS_PLUS_TCP_STM32_IF_DRIVER STREQUAL "H5")
  FetchContent_Declare(stm32-eth-driver
      GIT_REPOSITORY https://github.com/STMicroelectronics/stm32h5xx-hal-driver.git
      GIT_TAG v1.5.0
      GIT_SHALLOW TRUE
  )
elseif (FREERTOS_PLUS_TCP_STM32_IF_DRIVER STREQUAL "H7")
  FetchContent_Declare(stm32-eth-driver
      GIT_REPOSITORY https://github.com/STMicroelectronics/stm32h7xx-hal-driver.git
      GIT_TAG v1.11.5
      GIT_SHALLOW TRUE
  )
endif ()
FetchContent_MakeAvailable(stm32-eth-driver)

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F4>:
      stm32-eth-driver_SOURCE_DIR/Src/stm32f4xx_hal_eth.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F7>:
      stm32-eth-driver_SOURCE_DIR/Src/stm32f7xx_hal_eth.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H5>:
      stm32-eth-driver_SOURCE_DIR/Src/stm32h5xx_hal_eth_ex.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H5>:
      stm32-eth-driver_SOURCE_DIR/Src/stm32h5xx_hal_eth.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H7>:
      stm32-eth-driver_SOURCE_DIR/Src/stm32h7xx_hal_eth_ex.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H7>:
      stm32-eth-driver_SOURCE_DIR/Src/stm32h7xx_hal_eth.c>
)

target_include_directories( freertos_plus_tcp_network_if
  PUBLIC
      stm32-eth-driver_SOURCE_DIR/Inc
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
