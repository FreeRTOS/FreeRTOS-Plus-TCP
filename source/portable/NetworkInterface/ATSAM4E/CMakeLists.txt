if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "ATSAM4E") )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    component/gmac.h
    instance/gmac.h
    ethernet_phy.c
    ethernet_phy.h
    gmac.c
    gmac.h
    NetworkInterface.c
)
