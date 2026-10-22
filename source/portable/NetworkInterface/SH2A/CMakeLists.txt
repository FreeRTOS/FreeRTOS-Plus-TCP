if (NOT ( (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "SH2A") ) )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
)

# target_link_libraries( freertos_plus_tcp_network_if
#   PRIVATE
#     hwEthernetLib # Where is hwEthernet.h?
# )
