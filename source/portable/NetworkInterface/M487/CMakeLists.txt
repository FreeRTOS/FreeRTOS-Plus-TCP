if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "M487") )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    m480_eth.c
    m480_eth.h
    NetworkInterface.c
)
