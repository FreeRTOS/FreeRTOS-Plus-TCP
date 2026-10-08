if (NOT ( (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "WIN_PCAP") ) )
    return()
endif()

find_package(PCAP REQUIRED)

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    FaultInjection.c
    NetworkInterface.c
)

target_link_libraries( freertos_plus_tcp_network_if
  PRIVATE
    ${PCAP_LIBRARY}
)
