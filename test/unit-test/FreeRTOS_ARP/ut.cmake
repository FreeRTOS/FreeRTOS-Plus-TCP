# FreeRTOS_ARP unit-test cmake
message( STATUS "Building FreeRTOS_ARP unit-tests...")

# Set TCP includes.
set( TCP_INCLUDES "${MODULE_ROOT_DIR}/include/FreeRTOS_IP.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_ARP.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_Sockets.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_IP_Private.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_UDP_IP.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_DHCP.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_DNS.h"
                  "${MODULE_ROOT_DIR}/include/NetworkBufferManagement.h"
                  "${MODULE_ROOT_DIR}/include/NetworkInterface.h" )

set( FREERTOS_INCLUDES "${UNIT_TEST_DIR}/../FreeRTOS-Kernel/include/list.h"
                       "${UNIT_TEST_DIR}/../FreeRTOS-Kernel/include/task.h"
                       "${UNIT_TEST_DIR}/../FreeRTOS-Kernel/include/queue.h"
                       "${UNIT_TEST_DIR}/../FreeRTOS-Kernel/include/timers.h"
                       "${UNIT_TEST_DIR}/../FreeRTOS-Kernel/include/event_groups.h"
                       "${UNIT_TEST_DIR}/../FreeRTOS-Kernel/include/semphr.h" )

file( MAKE_DIRECTORY ${CMAKE_BINARY_DIR}/Annexed_TCP )
#file( MAKE_DIRECTORY ${CMAKE_BINARY_DIR}/Annexed_Kernel )
# ===========================================================================

if( 0 )
# ===========================================================================
# Preprocess the Kernel files
#   Remove the #error which forces inclusion of FreeRTOS.h
foreach( file ${FREERTOS_INCLUDES} )
    get_filename_component( MODIFIED_FILE ${file} NAME_WLE )
    execute_process( COMMAND sed "s,#error,//#error," ${file}
                     OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_Kernel/${MODIFIED_FILE}_tmp.h )
endforeach()

#   Generate the final set of files and cleanup temporary files generate above.
foreach( file ${FREERTOS_INCLUDES} )
    get_filename_component( MODIFIED_FILE ${file} NAME_WLE )

    execute_process( COMMAND gcc -E -fpreprocessed -I ${UNIT_TEST_DIR}/ConfigFiles -I ${CMAKE_BINARY_DIR}/Annexed_Kernel -fdirectives-only ${CMAKE_BINARY_DIR}/Annexed_Kernel/${MODIFIED_FILE}_tmp.h
                     OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_Kernel/${MODIFIED_FILE}.h
                     WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                     OUTPUT_QUIET )

    # Remove the temporary files.
    execute_process( COMMAND rm ${CMAKE_BINARY_DIR}/Annexed_Kernel/${MODIFIED_FILE}_tmp.h )

    execute_process( COMMAND sed -i "s,PRIVILEGED_FUNCTION,,g" ${CMAKE_BINARY_DIR}/Annexed_Kernel/${MODIFIED_FILE}.h )

    string(TOUPPER ${MODIFIED_FILE} Guard)
    set( Guard ${Guard}_H )

    execute_process( COMMAND sed -i "1 i\#define ${Guard}" ${CMAKE_BINARY_DIR}/Annexed_Kernel/${MODIFIED_FILE}.h )
    execute_process( COMMAND sed -i "1 i\#ifndef ${Guard}" ${CMAKE_BINARY_DIR}/Annexed_Kernel/${MODIFIED_FILE}.h )
    execute_process( COMMAND sed -i -e "$ a\#endif" ${CMAKE_BINARY_DIR}/Annexed_Kernel/${MODIFIED_FILE}.h )
endforeach()

#   Generate a preprocessed FreeRTOS.h file
execute_process( COMMAND gcc -E -fpreprocessed -I ${UNIT_TEST_DIR}/ConfigFiles -fdirectives-only ${UNIT_TEST_DIR}/../FreeRTOS-Kernel/include/FreeRTOS.h
                 OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_Kernel/FreeRTOS.h
                 WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                 OUTPUT_QUIET )

set( Guard "INC_FREERTOS_H" )

execute_process( COMMAND sed -i "1 i\#define ${Guard}" ${CMAKE_BINARY_DIR}/Annexed_Kernel/FreeRTOS.h )
execute_process( COMMAND sed -i "1 i\#ifndef ${Guard}" ${CMAKE_BINARY_DIR}/Annexed_Kernel/FreeRTOS.h )
execute_process( COMMAND sed -i -e "$ a\#endif" ${CMAKE_BINARY_DIR}/Annexed_Kernel/FreeRTOS.h )
# ===========================================================================
endif()

# ===========================================================================
# Preprocess the TCP include files as they will be mocked later.
foreach( file ${TCP_INCLUDES} )
    get_filename_component( MODIFIED_FILE ${file} NAME_WLE )

    string(TOUPPER ${MODIFIED_FILE} Guard)
    set( Guard ${Guard}_H )

    execute_process( COMMAND sed "s,#include \"FreeRTOSIPConfigDefaults.h\",,g" ${file}
                     OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp1.h )

    execute_process( COMMAND sed "1 i\#include \"FreeRTOSIPConfig.h\"" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp1.h
                     OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp.h )

    execute_process( COMMAND unifdefall -U${Guard} -I ${MODULE_ROOT_DIR}/tools/CMock/vendor/unity/src -I ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include -I ${UNIT_TEST_DIR}/ConfigFiles -I ${MODULE_ROOT_DIR}/include ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp.h
                     #COMMAND gcc -E -fpreprocessed -fdirectives-only -MM -MG -I ${MODULE_ROOT_DIR}/include -I ${UNIT_TEST_DIR}/ConfigFiles -I ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include ${file} -MT ${file}.xx -MF ${file}.yy
                     WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                     OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h
                     OUTPUT_QUIET )

#    execute_process( COMMAND sed -i -E "s,#.*,,g" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h )

#    execute_process( COMMAND sed -i "1 i\#define ${Guard}" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h )
    execute_process( COMMAND sed -i "1 i\#ifndef ${Guard}" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h )
    execute_process( COMMAND sed -i -e "$ a\#endif" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h )

endforeach()

execute_process( COMMAND rm ${CMAKE_BINARY_DIR}/Annexed_TCP/*_tmp*.h )
# ===========================================================================
