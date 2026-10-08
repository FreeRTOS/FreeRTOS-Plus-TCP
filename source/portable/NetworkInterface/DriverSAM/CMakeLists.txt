if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "DRIVER_SAM") )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    gmac_SAM.c
    gmac_SAM.h
    NetworkInterface.c
)
