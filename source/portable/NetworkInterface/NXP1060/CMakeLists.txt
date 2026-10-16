if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "NXP1060") )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
)
