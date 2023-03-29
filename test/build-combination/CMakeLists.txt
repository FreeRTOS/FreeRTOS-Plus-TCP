add_library( freertos_plus_tcp_config_common INTERFACE )
target_include_directories(freertos_plus_tcp_config_common INTERFACE Common )

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_all_disable INTERFACE)
target_include_directories(freertos_plus_tcp_config_all_disable INTERFACE AllDisable)
target_link_libraries(freertos_plus_tcp_config_all_disable INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_all_enable INTERFACE)
target_include_directories(freertos_plus_tcp_config_all_enable INTERFACE AllEnable)
target_link_libraries(freertos_plus_tcp_config_all_enable INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
add_library( freertos_plus_tcp_config_default INTERFACE)
target_include_directories(freertos_plus_tcp_config_default INTERFACE DefaultConf)
target_link_libraries(freertos_plus_tcp_config_default INTERFACE freertos_plus_tcp_config_common)

# -------------------------------------------------------------------
# Configuration for FreeRTOS-Kernel
if(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "CUSTOM" )
    # Check Config target is available. And then do nothing.
    if(NOT TARGET freertos_config )
        message(FATAL_ERROR "FREERTOS_PLUS_TCP_TEST_CONFIGURATION = CUSTOM, but no freertos_config target defined.")
    endif()
elseif(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "DISABLE_ALL" )
    add_library( freertos_config ALIAS freertos_plus_tcp_config_all_disable)
elseif(FREERTOS_PLUS_TCP_TEST_CONFIGURATION STREQUAL "ENABLE_ALL" )
    add_library( freertos_config ALIAS freertos_plus_tcp_config_all_enable)
else()
    add_library( freertos_config ALIAS freertos_plus_tcp_config_default)
endif()

add_executable(freertos_plus_tcp_build_test EXCLUDE_FROM_ALL)

target_sources(freertos_plus_tcp_build_test
  PRIVATE
    Common/main.c
)

target_compile_options(freertos_plus_tcp_build_test
  PRIVATE
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-qual>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-format-nonliteral>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-implicit-function-declaration>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-noreturn>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-prototypes>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-variable-declarations>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-reserved-identifier>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-shorten-64-to-32>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-sign-conversion>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-unused-parameter>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-unused-macros>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-unused-variable>
)

target_link_libraries(freertos_plus_tcp_build_test
  PRIVATE
    freertos_plus_tcp
    freertos_kernel
)
