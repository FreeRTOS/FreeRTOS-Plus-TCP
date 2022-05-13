# Include filepaths for source and include.
include( ${MODULE_ROOT_DIR}/test/unit-test/TCPFilePaths.cmake )

# ====================  Define your project name (edit) ========================
set( project_name "FreeRTOS_DNS_Cache" )
message( STATUS "${project_name}" )
# =====================  Create your mock here  (edit)  ========================

# list the files to mock here
set (mock_list "")
list(APPEND mock_list
            "${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include/task.h"
            "${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include/list.h"
            "${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include/queue.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_IP.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_Sockets.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_IP_Private.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/NetworkBufferManagement.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_UDP_IP.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_DNS_Callback.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_DNS_Networking.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_DNS_Parser.h"
        )
# list the directories your mocks need
list(APPEND mock_include_list
            .
            ${TCP_INCLUDE_DIRS}
            ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include
            ${MODULE_ROOT_DIR}/test/unit-test/ConfigFiles
        )

#list the definitions of your mocks to control what to be included
list(APPEND mock_define_list
#-DportUSING_MPU_WRAPPERS=0
       )

# ================= Create the library under test here (edit) ==================

add_compile_options(-Wno-pedantic -Wno-div-by-zero -O0 -ggdb3)
# list the files you would like to test here
set(real_source_files ""
        )
list(APPEND real_source_files
            ${project_name}/FreeRTOS_UDP_IP_stubs.c
            ${MODULE_ROOT_DIR}/source/FreeRTOS_DNS_Cache.c
	)
# list the directories the module under test includes
list(APPEND real_include_directories
            .
            ${TCP_INCLUDE_DIRS}
            ${MODULE_ROOT_DIR}/test/unit-test/ConfigFiles
            ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include
            ${CMOCK_DIR}/vendor/unity/src
	)

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            .
            ${CMOCK_DIR}/vendor/unity/src
            ${TCP_INCLUDE_DIRS}
            ${MODULE_ROOT_DIR}/test/unit-test/${project_name}
            ${MODULE_ROOT_DIR}/source/include
        )

# =============================  (end edit)  ===================================

set(mock_name "${project_name}_mock")
set(real_name "${project_name}_real")

create_mock_list(${mock_name}
                "${mock_list}"
                "${MODULE_ROOT_DIR}/test/unit-test/cmock/project.yml"
                "${mock_include_list}"
                "${mock_define_list}"
        )

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
        )

set( utest_link_list "")
list(APPEND utest_link_list
            -l${mock_name}
            lib${real_name}.a
        )

set (utest_dep_list "")
list(APPEND utest_dep_list
            ${real_name}
        )

set(utest_name "${project_name}_utest")
set(utest_source "${project_name}/${project_name}_utest.c")

create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )
