if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "ATSAME5x") )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
)
