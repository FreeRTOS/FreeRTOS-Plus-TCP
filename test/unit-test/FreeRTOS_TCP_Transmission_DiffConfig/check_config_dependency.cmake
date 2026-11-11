# Check the production configuration dependency without generated Annexed_TCP
# headers, which strip conditional definitions used by the mock generator.
set( includes
    -I${MODULE_ROOT_DIR}/source/include
    -I${MODULE_ROOT_DIR}/test/unit-test/FreeRTOS_TCP_Transmission_DiffConfig
    -I${MODULE_ROOT_DIR}/test/unit-test/ConfigFiles
    -I${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include
    -I${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/portable/ThirdParty/GCC/Posix )

foreach( psh 0 1 )
    foreach( arp defaults 0 1000 )
        set( definitions -DipconfigTCP_HANG_PROTECTION=0
                         -DipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY=${psh} )
        if( NOT arp STREQUAL "defaults" )
            list( APPEND definitions -DipconfigTCP_SKIP_ARP_LOOKUP_MS=${arp} )
        endif()
        execute_process(
            COMMAND ${C_COMPILER} -fsyntax-only ${includes} ${definitions}
                ${MODULE_ROOT_DIR}/source/FreeRTOS_TCP_Transmission_IPv4.c
            RESULT_VARIABLE result
            OUTPUT_VARIABLE output
            ERROR_VARIABLE error )
        if( arp STREQUAL "1000" )
            if( result STREQUAL "0" OR NOT error MATCHES
                "ipconfigTCP_SKIP_ARP_LOOKUP_MS needs ipconfigTCP_HANG_PROTECTION" )
                message( FATAL_ERROR "PSH=${psh}, ARP=${arp}: expected dependency diagnostic\n${output}${error}" )
            endif()
            message( STATUS "PSH=${psh}, ARP=${arp}, HANG=0: rejected with dependency diagnostic" )
        else()
            if( NOT result STREQUAL "0" )
                message( FATAL_ERROR "PSH=${psh}, ARP=${arp}: valid configuration failed\n${output}${error}" )
            endif()
            message( STATUS "PSH=${psh}, ARP=${arp}, HANG=0: compiled" )
        endif()
    endforeach()
endforeach()
