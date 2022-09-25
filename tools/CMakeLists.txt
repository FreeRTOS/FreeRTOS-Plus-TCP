add_library( freertos_plus_tcp_tools STATIC )
add_library( FreeRTOS::PlusTCP::Tools ALIAS freertos_plus_tcp_tools )

target_sources( freertos_plus_tcp_tools
  PRIVATE
    tcp_utilities/include/tcp_dump_packets.h
    tcp_utilities/include/tcp_mem_stats.h
    tcp_utilities/include/tcp_netstat.h

    tcp_utilities/tcp_dump_packets.c
    tcp_utilities/tcp_mem_stats.c
    tcp_utilities/tcp_netstat.c
)

# Note: Have to make system due to compiler warnings in header files.
target_include_directories( freertos_plus_tcp_tools SYSTEM
  PUBLIC
    tcp_utilities/include
)

#TODO(phelter): Investigate and fix in freertos_plus_tcp if not already fixed.
target_compile_options( freertos_plus_tcp_tools
  PRIVATE
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-format>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-variable-declarations>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-padded>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-unused-but-set-variable>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-unused-function>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-unused-macros>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-unused-variable>
)

target_link_libraries( freertos_plus_tcp_tools
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
