
cmake_minimum_required(VERSION 3.15)
cmake_policy(SET CMP0048 NEW) # project version
cmake_policy(SET CMP0076 NEW) # full paths

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_LIST_DIR}/cmake_modules")

########################################################################
# Project Details
project(FreeRTOS-Plus-TCP
        VERSION 3.1.0
        DESCRIPTION "FreeRTOS TCP/UDP Network Layer"
        HOMEPAGE_URL https://freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/index.html
        LANGUAGES C)

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Options
option(FREERTOS_PLUS_TCP_BUILD_TEST "Build the test for FreeRTOS Plus TCP" OFF)

# Configuration
# Override these at project level with:
#   Optional: set(FREERTOS_PLUS_TCP_BUFFER_ALLOCATION "1" CACHE STRING "" FORCE)
#   Optional: set(FREERTOS_PLUS_TCP_COMPILER "" CACHE STRING "" FORCE)
#   Required: set(FREERTOS_PLUS_TCP_NETWORK_IF "POSIX" CACHE STRING "" FORCE)

# Select the appropriate buffer allocation method.
# See: https://freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/Embedded_Ethernet_Buffer_Management.html
if (NOT FREERTOS_PLUS_TCP_BUFFER_ALLOCATION)
    message(STATUS "Using default FREERTOS_PLUS_TCP_BUFFER_ALLOCATION = 2")
    set(FREERTOS_PLUS_TCP_BUFFER_ALLOCATION "2" CACHE STRING "FreeRTOS buffer allocation model number. 1 .. 2.")
endif()

# Select the Compiler - if left blank will detect using CMake
# Note relies on CMake to detect over any setting here.
# Valid options are:
#   FREERTOS_PLUS_TCP_COMPILER | Detected | CMake
#   -------------------------------------------------
#   CCS                        | No       | ?TBD?
#   GCC                        | Yes      | GNU
#   IAR                        | Yes      | IAR
#   Keil                       | Yes      | ARMCC
#   MSVC                       | Yes      | MSVC # Note only for MinGW
#   Renesas                    | No       | ?TBD?
# Will always a attempt to detect and if detectable double checks that the compiler is set correctly.
set(FREERTOS_PLUS_TCP_COMPILER "" CACHE STRING "FreeRTOS Plus TCP Compiler Selection")


# Select the appropriate network interface
# This will fail the CMake preparation step if not set to one of those values.
set(FREERTOS_PLUS_TCP_NETWORK_IF "" CACHE STRING "FreeRTOS Plus TCP Network Interface selection")
set(FREERTOS_PLUS_TCP_NETWORK_IF_LIST
    A_CUSTOM_NETWORK_IF
    ATSAM43 ATSAME5x # AT
    DRIVER_SAM
    ESP32
    KSZ8851SNL
    LIBSLIRP
    LPC17xx LPC18xx LPC54018
    M487
    MPS2_AN385
    MPS3_AN552
    MW300_RD
    PIC32MZEF_ETH PIC32MZEF_WIFI
    POSIX WIN_PCAP  # Native Linux & Windows respectively
    RX
    SH2A
    STM32FXX STM32HXX # ST Micro
    MSP432
    TM4C
    XILINX_ULTRASCALE ZYNQ # AMD/Xilinx
)
if(NOT FREERTOS_PLUS_TCP_NETWORK_IF)
    # Attempt to detect the system.
    if(UNIX)
        message(STATUS "Detected UNIX/Posix system setting FREERTOS_PLUS_TCP_NETWORK_IF = POSIX")
        set(FREERTOS_PLUS_TCP_NETWORK_IF POSIX)
    elseif(MINGW)
        message(STATUS "Detected Windows MinGW system setting FREERTOS_PLUS_TCP_NETWORK_IF = WIN_PCAP")
        set(FREERTOS_PLUS_TCP_NETWORK_IF WIN_PCAP)
    endif()
endif()

if(NOT FREERTOS_PLUS_TCP_NETWORK_IF IN_LIST FREERTOS_PLUS_TCP_NETWORK_IF_LIST )
    message(FATAL_ERROR " FREERTOS_PLUS_TCP_NETWORK_IF is '${FREERTOS_PLUS_TCP_NETWORK_IF}'.\n"
        " Please specify it from top-level CMake file (example):\n"
        "   set(FREERTOS_PLUS_TCP_NETWORK_IF POSIX CACHE STRING \"\")\n"
        " or from CMake command line option:\n"
        "   -DFREERTOS_PLUS_TCP_NETWORK_IF=POSIX\n"
        " \n"
        " Available port options: (Tested means compiled with that variant)\n"
        " A_CUSTOM_NETWORK_IF    Target: User Defined\n"
        " ATSAM4E                Target: ATSAM4E            Tested: TODO\n"
        " ATSAME5x               Target: ATSAME5x           Tested: TODO\n"
        " DRIVER_SAM             Target: Driver SAM         Tested: TODO\n"
        " ESP32                  Target: ESP-32             Tested: TODO\n"
        " KSZ8851SNL             Target: ksz8851snl         Tested: TODO\n"
        " LIBSLIRP               Target: libslirp           Tested: TODO\n"
        " POSIX                  Target: linux/Posix\n"
        " LPC17xx                Target: LPC17xx            Tested: TODO\n"
        " LPC18xx                Target: LPC18xx            Tested: TODO\n"
        " LPC54018               Target: LPC54018           Tested: TODO\n"
        " M487                   Target: M487               Tested: TODO\n"
        " MPS2_AN385             Target: MPS2_AN385         Tested: TODO\n"
        " MPS3_AN552             Target: MPS3_AN552"
        " MW300_RD               Target: mw300_rd           Tested: TODO\n"
        " PIC32MZEF_ETH          Target: pic32mzef ethernet Tested: TODO\n"
        " PIC32MZEF_WIFI         Target: pic32mzef Wifi     Tested: TODO\n"
        " RX                     Target: RX                 Tested: TODO\n"
        " SH2A                   Target: SH2A               Tested: TODO\n"
        " STM32FXX               Target: STM32Fxx           Tested: TODO\n"
        " STM32HXX               Target: STM32Hxx           Tested: TODO\n"
        " MSP432                 Target: MSP432             Tested: TODO\n"
        " TM4C                   Target: TM4C               Tested: TODO\n"
        " WIN_PCAP               Target: Windows            Tested: TODO\n"
        " XILINX_ULTRASCALE      Target: Xilinx Ultrascale  Tested: TODO\n"
        " ZYNQ                   Target: Xilinx Zynq")
elseif((FREERTOS_PORT STREQUAL "A_CUSTOM_PORT") AND (NOT TARGET freertos_kernel_port) )
    message(FATAL_ERROR " FREERTOS_PLUS_TCP_NETWORK_IF is set to A_CUSTOM_NETWORK_IF.\n"
    " Please specify the custom network interface target with all necessary files.\n"
    " For example, assuming a directory of:\n"
    "  FreeRTOSCustomNetworkInterface/\n"
    "    CMakeLists.txt\n"
    "    NetworkInterface.c\n\n"
    " Where FreeRTOSCustomNetworkInterface/CMakeLists.txt is a modified version of:\n"
    "   add_library(freertos_plus_tcp_network_if STATIC)\n\n"
    "   target_sources(freertos_plus_tcp_network_if\n"
    "     PRIVATE\n"
    "       NetworkInterface.c)\n\n"
    "   target_include_directories(freertos_plus_tcp_network_if\n"
    "     PUBLIC\n"
    "      .)\n\n"
    "   target_link_libraries(freertos_plus_tcp_network_if\n"
    "     PUBLIC\n"
    "       freertos_plus_tcp_port\n"
    "       freertos_plus_tcp_network_if_common\n"
    "     PRIVATE\n"
    "       freertos_kernel)")
endif()

# There is also the need to add a target - typically an interface library that describes the
# Configuration for FreeRTOS-Kernel and FreeRTOS-Plus-TCP.
# This is called freertos_config
# If not defined will be default compile with one of the test build combinations AllEnable.

# Select the appropriate Build Test configuration
# This is only used when freertos_config is not defined, otherwise the build test will be performed
# on the config defined in the freertos_config
set(FREERTOS_PLUS_TCP_TEST_CONFIGURATION "CUSTOM" CACHE STRING "FreeRTOS Plus TCP Build Test configuration")
set(FREERTOS_PLUS_TCP_TEST_CONFIGURATION_LIST
    CUSTOM                  # Custom (external) configuration -eg from a top-level project
    ENABLE_ALL              # Enable all configuration settings
    ENABLE_ALL_IPV4         # Enable all configuration settings IPv4 UDP
    ENABLE_ALL_IPV6         # Enable all configuration settings IPv6 UDP
    ENABLE_ALL_IPV4_TCP     # Enable all configuration settings IPv4 TCP
    ENABLE_ALL_IPV6_TCP     # Enable all configuration settings IPv6 TCP
    ENABLE_ALL_IPV4_IPV6    # Enable all configuration settings IPv4 IPv6 UDP
    DISABLE_ALL             # Disable all configuration settings
    HEADER_SELF_CONTAIN     # Enable header self contain test
    DEFAULT_CONF            # Default (typical) configuration
)
if(NOT FREERTOS_PLUS_TCP_TEST_CONFIGURATION IN_LIST FREERTOS_PLUS_TCP_TEST_CONFIGURATION_LIST)
    message(FATAL_ERROR "Invalid FREERTOS_PLUS_TCP_TEST_CONFIGURATION value '${FREERTOS_PLUS_TCP_TEST_CONFIGURATION}' should be one of: ${FREERTOS_PLUS_TCP_TEST_CONFIGURATION_LIST}")
else()
    message(STATUS "Using FreeRTOS-Plus-TCP Test Configuration : ${FREERTOS_PLUS_TCP_TEST_CONFIGURATION}")
    if (NOT FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "CUSTOM")
        message(WARNING "FreeRTOS-Kernel configuration settings are configured by FreeRTOS-Plus-TCP")
    endif()
endif()

########################################################################
# Overall Compile Options
# Note the compile option strategy is to error on everything and then
# Per library opt-out of things that are warnings/errors.
# This ensures that no matter what strategy for compilation you take, the
# builds will still occur.
#
# Only tested with GNU and Clang.
# Other options are https://cmake.org/cmake/help/latest/variable/CMAKE_LANG_COMPILER_ID.html#variable:CMAKE_%3CLANG%3E_COMPILER_ID
# Naming of compilers translation map:
# For the ?TBD? - Suggest trying GNU-based and adding the appropriate toolchain file.
#   For Toolchain examples see _deps/cmake-src/toolchain/arm-none-eabil-gcc.toolchain.cmake
#
#   FreeRTOS    | CMake
#   -------------------
#   CCS         | ?TBD?
#   GCC         | GNU, Clang, *Clang Others?
#   IAR         | IAR
#   Keil        | ARMCC
#   MSVC        | MSVC # Note only for MinGW?
#   Renesas     | ?TBD?

add_compile_options(
    ### Gnu/Clang C Options
    $<$<COMPILE_LANG_AND_ID:C,GNU>:-fdiagnostics-color=always>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-fcolor-diagnostics>

    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wall>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wextra>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Werror>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wpedantic>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wconversion>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wunused-variable>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Weverything>

    # Suppressions required to build clean with clang.
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-unused-macros>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-qual>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-switch-enum>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-declaration-after-statement>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-padded>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-variable-declarations>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-covered-switch-default>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-extra-semi-stmt>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-noreturn>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-align>
)

########################################################################
# External Dependencies
# Note: For backwards compatibility - still have .gitmodules defining submodules
# To support fetching content in a higher level project see
#   README.md `Consume with CMake`
# This will allow you to upgrade submodules and have one common submodule for
# all your builds despite multiple submodules having different versions.
include(FetchContent)

FetchContent_Declare( freertos_kernel
  GIT_REPOSITORY https://github.com/FreeRTOS/FreeRTOS-Kernel.git
  GIT_TAG        main
)

FetchContent_Declare( cmock
  GIT_REPOSITORY https://github.com/ThrowTheSwitch/CMock
  GIT_TAG        v2.5.3
)

add_subdirectory(source)
add_subdirectory(tools)
add_subdirectory(test)

FetchContent_MakeAvailable(freertos_kernel cmock)

# Note following are can be removed once FreeRTOS-Kernel v10.5.0 + fixes their issues.
# To ignore header specific issues - change all of the headers to SYSTEM
set(_freertos_kernel_targets freertos_kernel freertos_kernel_port)
# foreach (_target ${_freertos_kernel_targets} )
#   get_target_property( interface_directories ${_target} INTERFACE_INCLUDE_DIRECTORIES )
#   set_target_properties(${_target}  PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${interface_directories}" )
# endforeach()
