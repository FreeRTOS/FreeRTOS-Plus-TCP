set( COMPILE_OPTIONS 
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
     $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-unused-variable> )

set( binaryList
     TEST_HEADER_INC_ONLY_DHCP
     TEST_HEADER_INC_ONLY_DNS
     TEST_HEADER_INC_ONLY_IP
     TEST_HEADER_INC_ONLY_ND
     TEST_HEADER_INC_ONLY_ROUTING
     TEST_HEADER_INC_ONLY_SOCKETS
     TEST_HEADER_INC_ONLY_NETWORKBUFFERMANAGEMENT
     TEST_HEADER_INC_ONLY_NETWORKINTERFACE )

foreach( singleOpt IN LISTS binaryList )
    add_executable(freertos_plus_tcp_build_test_${singleOpt} EXCLUDE_FROM_ALL)
    target_compile_definitions(freertos_plus_tcp_build_test_${singleOpt} PRIVATE ${singleOpt})

    target_sources(freertos_plus_tcp_build_test_${singleOpt}
    PRIVATE
        HeaderSelfContain/main.c
        HeaderSelfContain/stubs.c
    )

    target_compile_options(freertos_plus_tcp_build_test_${singleOpt}
        PRIVATE
        ${COMPILE_OPTIONS}
    )

    target_link_libraries(freertos_plus_tcp_build_test_${singleOpt}
        PRIVATE
        freertos_plus_tcp
        freertos_kernel
    )
endforeach()
