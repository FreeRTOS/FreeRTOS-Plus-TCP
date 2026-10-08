# Include filepaths for source and include.
include( ${MODULE_ROOT_DIR}/test/unit-test/TCPFilePaths.cmake )

set( project_name "phyHandling" )
message( STATUS "${project_name}" )

set( phy_include_directories
     .
     ${TCP_INCLUDE_DIRS}
     ${MODULE_ROOT_DIR}/source/portable/NetworkInterface/include
     ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include
     ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/portable/ThirdParty/GCC/Posix
     ${MODULE_ROOT_DIR}/test/unit-test/ConfigFiles
     ${CMOCK_DIR}/vendor/unity/src )

set( real_name "${project_name}_real" )

create_real_library( ${real_name}
                     "${MODULE_ROOT_DIR}/source/portable/NetworkInterface/Common/phyHandling.c"
                     "${phy_include_directories}"
                     "" )

set( utest_link_list
     cmock
     lib${real_name}.a )
set( utest_dep_list ${real_name} )
set( utest_name "${project_name}_utest" )
set( utest_source "${project_name}/${project_name}_utest.c" )

create_test( ${utest_name}
             ${utest_source}
             "${utest_link_list}"
             "${utest_dep_list}"
             "${phy_include_directories}" )
