if (NOT ( (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "STM32") ) )
    return()
endif()

#------------------------------------------------------------------------------
add_library(freertos_plus_tcp_network_if STATIC)

set(FREERTOS_PLUS_TCP_STM32_IF_DRIVER "None" CACHE STRING "The driver sources to use with STM32 Network interface")
set_property(CACHE FREERTOS_PLUS_TCP_STM32_IF_DRIVER PROPERTY STRINGS F4 F7 H5 H7 None)

set(_repo "")
set(_tag "")
if(FREERTOS_PLUS_TCP_STM32_IF_DRIVER STREQUAL "F4")
    set(_repo https://github.com/STMicroelectronics/stm32f4xx-hal-driver.git)
    set(_tag v1.8.4)
elseif(FREERTOS_PLUS_TCP_STM32_IF_DRIVER STREQUAL "F7")
    set(_repo https://github.com/STMicroelectronics/stm32f7xx-hal-driver.git)
    set(_tag v1.3.2)
elseif(FREERTOS_PLUS_TCP_STM32_IF_DRIVER STREQUAL "H5")
    set(_repo https://github.com/STMicroelectronics/stm32h5xx-hal-driver.git)
    set(_tag v1.5.0)
elseif(FREERTOS_PLUS_TCP_STM32_IF_DRIVER STREQUAL "H7")
    set(_repo https://github.com/STMicroelectronics/stm32h7xx-hal-driver.git)
    set(_tag v1.11.5)
endif()

if(_repo STREQUAL "")
    message(FATAL_ERROR "Set FREERTOS_PLUS_TCP_STM32_IF_DRIVER to one of: F4, F7, H5, H7.")
endif()

include(FetchContent)
FetchContent_Declare(stm32_eth_driver
    GIT_REPOSITORY ${_repo}
    GIT_TAG ${_tag}
    GIT_SHALLOW TRUE
)
FetchContent_MakeAvailable(stm32_eth_driver)

target_sources(freertos_plus_tcp_network_if
    PRIVATE
        NetworkInterface.c
        $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F4>:${stm32_eth_driver_SOURCE_DIR}/Src/stm32f4xx_hal_eth.c>
        $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},F7>:${stm32_eth_driver_SOURCE_DIR}/Src/stm32f7xx_hal_eth.c>
        $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H5>:${stm32_eth_driver_SOURCE_DIR}/Src/stm32h5xx_hal_eth_ex.c>
        $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H5>:${stm32_eth_driver_SOURCE_DIR}/Src/stm32h5xx_hal_eth.c>
        $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H7>:${stm32_eth_driver_SOURCE_DIR}/Src/stm32h7xx_hal_eth_ex.c>
        $<$<STREQUAL:${FREERTOS_PLUS_TCP_STM32_IF_DRIVER},H7>:${stm32_eth_driver_SOURCE_DIR}/Src/stm32h7xx_hal_eth.c>
)

target_include_directories(freertos_plus_tcp_network_if
    PUBLIC
        ${stm32_eth_driver_SOURCE_DIR}/Inc
)

target_link_libraries( freertos_plus_tcp_network_if
    PUBLIC
        freertos_plus_tcp_port
        freertos_plus_tcp_network_if_common
    PRIVATE
        freertos_kernel
        freertos_plus_tcp
)
