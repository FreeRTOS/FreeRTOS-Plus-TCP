set( phy_include_dirs
     ${TCP_INCLUDE_DIRS}
     ${KERNEL_DIRECTORY}/include
     ${UNIT_TEST_DIR}/ConfigFiles
     ${MODULE_ROOT_DIR}/source/portable/NetworkInterface/include )

create_mock_list( phyHandling_mock
                  "${KERNEL_DIRECTORY}/include/task.h"
                  "${UNIT_TEST_DIR}/cmock/project.yml"
                  "${phy_include_dirs}"
                  "" )

create_test( phyHandling_utest
             "phyHandling/phyHandling_utest.c"
             "phyHandling_mock"
             ""
             "${phy_include_dirs}" )

target_sources( phyHandling_utest PRIVATE
                ${MODULE_ROOT_DIR}/source/portable/NetworkInterface/Common/phyHandling.c )
