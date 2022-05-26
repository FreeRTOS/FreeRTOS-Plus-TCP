# Set the required version.
cmake_minimum_required( VERSION 3.13.0 )

# Set the unit-test project.
project( "FreeRTOS-Plus-TCP test"
         VERSION 1.0.0
         LANGUAGES C )

# Allow the project to be organized into folders.
set_property( GLOBAL PROPERTY USE_FOLDERS ON )

# Use C90.
set( CMAKE_C_STANDARD 99 )
set( CMAKE_C_STANDARD_REQUIRED ON )

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Set global path variables.
get_filename_component( __MODULE_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}/../.." ABSOLUTE )
set( MODULE_ROOT_DIR ${__MODULE_ROOT_DIR} CACHE INTERNAL "FreeRTOS-Plus-TCP repository root." )

# Set the unit-test directory.
set( UNIT_TEST_DIR ${MODULE_ROOT_DIR}/test/unit-test CACHE INTERNAL "Unit-test directory." )

set( KERNEL_DIRECTORY ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel )

# See if FreRTOS-Kernel is submoduled
if( NOT EXISTS ${KERNEL_DIRECTORY}/include )
    # Inform the user of the actions
    message( STATUS "FreeRTOS-Kernel is required for this build. Submoduling it..." )
    execute_process( COMMAND git submodule update --init --checkout ${KERNEL_DIRECTORY}
                     WORKING_DIRECTORY ${MODULE_ROOT_DIR} )
endif()

# Set the include directories
string( APPEND GLOBAL_INCLUDES "-I ${MODULE_ROOT_DIR}/source/include ")
string( APPEND GLOBAL_INCLUDES "-I ${UNIT_TEST_DIR}/ConfigFiles " )
string( APPEND GLOBAL_INCLUDES "-I ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include " )

# Configure options to always show in CMake GUI.
option( BUILD_CLONE_SUBMODULES
        "Set this to ON to automatically clone any required Git submodules. When OFF, submodules must be manually cloned."
        ON )

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )


# Set TCP includes.
set( TCP_INCLUDES "${MODULE_ROOT_DIR}/source/include/FreeRTOS_IP.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_ARP.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_ICMP.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_IP_Timers.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_IP_Utils.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_Sockets.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_IP_Private.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_UDP_IP.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_DHCP.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_DNS.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_DNS_Cache.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_DNS_Globals.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_DNS_Callback.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_DNS_Networking.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_DNS_Parser.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_TCP_IP.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_TCP_Transmission.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_TCP_Reception.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_TCP_Utils.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_TCP_State_Handling.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_Stream_Buffer.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOS_TCP_WIN.h"
                  "${MODULE_ROOT_DIR}/source/include/FreeRTOSIPConfigDefaults.h"
                  "${MODULE_ROOT_DIR}/source/include/IPTraceMacroDefaults.h"
                  "${MODULE_ROOT_DIR}/source/include/NetworkBufferManagement.h"
                  "${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include/portable.h"
                  "${MODULE_ROOT_DIR}/source/include/NetworkInterface.h" )

# Create a directory for the modified files
file( MAKE_DIRECTORY ${CMAKE_BINARY_DIR}/Annexed_TCP )
# ===========================================================================

# ===========================================================================
# Preprocess the TCP include files as they will be mocked later.
foreach( file ${TCP_INCLUDES} )
    get_filename_component( MODIFIED_FILE ${file} NAME_WLE )

    string(TOUPPER ${MODIFIED_FILE} Guard)

    if(${MODIFIED_FILE} STREQUAL "NetworkBufferManagement" )
        set( Guard "NETWORK_BUFFER_MANAGEMENT_H" )
    elseif(  ${MODIFIED_FILE} STREQUAL "NetworkInterface" )
        set( Guard "NETWORK_INTERFACE_H" )
    else()
        set( Guard ${Guard}_H )
    endif()

    # Remove IPConfigDefaults from the file
    execute_process( COMMAND sed "s,#include \"FreeRTOSIPConfigDefaults.h\",,g" ${file}
                     OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp1.h )

    # Add the FreeRTOSIPConfig file to each directory
    execute_process( COMMAND sed "1 i\#include \"FreeRTOSIPConfig.h\"" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp1.h
                     OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp.h )

    if(${MODIFIED_FILE} STREQUAL "FreeRTOS_IP_Private" )
        execute_process( COMMAND sed "s/extern const BaseType_t xBufferAllocFixedSize/extern BaseType_t xBufferAllocFixedSize/g" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp.h
                         OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp2.h )
        execute_process( COMMAND mv ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp2.h ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp.h )
    endif()

    # Use this tool to process all conditional declarations.
    execute_process( COMMAND unifdefall -U${Guard} -USEND_REPEATED_COUNT -UpdTRUE_SIGNED -UFreeRTOS_htonl -D__COVERITY__ -DTEST -I ${MODULE_ROOT_DIR}/tools/CMock/vendor/unity/src
                                                   -I ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include
                                                   -I ${UNIT_TEST_DIR}/ConfigFiles
                                                   -I ${MODULE_ROOT_DIR}/source/include
                                                   -I ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/portable/ThirdParty/GCC/Posix
                                                   ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp.h
                     WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                     OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h
                     OUTPUT_QUIET )

    # Remove the temporary files
    file( REMOVE ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp.h )
    file( REMOVE ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp1.h )

    # Add the guards back to the files
    execute_process( COMMAND sed -i "1 i\#ifndef ${Guard}" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h )
    execute_process( COMMAND sed -i -e "$ a\#endif" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h )

    execute_process( COMMAND sed -i -E "s,[ ]*extern ipDECL_CAST_.*,,g" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h )

endforeach()
# ===========================================================================

# ===================================== Include the cmake configurations =================================================
message( STATUS ${CMAKE_BINARY_DIR} )
# Include filepaths for source and include.
include( ${UNIT_TEST_DIR}/TCPFilePaths.cmake )
# ===========================================================================


# ===========================================================================
# Remove static qualifier from the souce files so that internal functions
# can be called directly.
file( MAKE_DIRECTORY ${CMAKE_BINARY_DIR}/Annexed_TCP_Sources )

foreach( file ${TCP_SOURCES} )

    get_filename_component( MODIFIED_FILE ${file} NAME_WLE )

    if(${MODIFIED_FILE} STREQUAL "FreeRTOS_Sockets" )
        execute_process( COMMAND sed "/#include \"task.h\"/ a \#include \"Sockets_list_macros.h\" " ${file}
                         OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp2.c  )
        set( file ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp2.c )
    endif()

    # Strip static constraints so unit tests may call internal functions
    execute_process( COMMAND sed "s/^[ ]*static //"
                     WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                     INPUT_FILE ${file}
                     OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_TCP_Sources/${MODIFIED_FILE}.c )

    # Generate a header file for internal functions
    execute_process( COMMAND sed -n "/^[ ]*static.*(/,/^{\$/{s/^static //; s/)\$/&;/; /{/d; p;}"
                     WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                     INPUT_FILE ${file}
                     OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_TCP_Sources/${MODIFIED_FILE}_internal.h )
endforeach()
# ===========================================================================


# ========================= Test Configuration ==============================
# Define a CMock resource path.
set( CMOCK_DIR ${MODULE_ROOT_DIR}/tools/CMock CACHE INTERNAL "CMock library source directory." )

# Include CMock build configuration.
include( cmock_build.cmake )

# Check if the CMock source directory exists, and if not present, clone the submodule
# if BUILD_CLONE_SUBMODULES configuration is enabled.
if( NOT EXISTS ${CMOCK_DIR}/src )
    # Attempt to clone CMock.
    if( ${BUILD_CLONE_SUBMODULES} )
        clone_cmock()
    else()
        message( FATAL_ERROR "The required submodule CMock does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 'ON' to automatically clone it during build." )
    endif()
endif()

# Use CTest utility for managing test runs. This has to be added BEFORE
# defining test targets with add_test()
enable_testing()

# Add build targets for CMock and Unit, required for unit testing.
add_cmock_targets()

# Add function to enable CMock based tests and coverage.
include( ${MODULE_ROOT_DIR}/test/unit-test/cmock/create_test.cmake )

# Include unit-test build configuration

include( ${UNIT_TEST_DIR}/FreeRTOS_ARP/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_ARP_DataLenLessThanMinPacket/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_DHCP/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_TCP_WIN/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_Tiny_TCP/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_DNS/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_DNS_Cache/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_DNS_Networking/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_DNS_Callback/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_DNS_Parser/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_IP/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_IP_DiffConfig/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_ICMP/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_ICMP_wo_assert/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_IP_Utils/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_IP_Utils_DiffConfig/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_IP_Timers/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_Sockets/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_Sockets_DiffConfig/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_Sockets_DiffConfig1/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_Stream_Buffer/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_UDP_IP/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_TCP_Reception/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_TCP_IP/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_TCP_IP_DiffConfig/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_TCP_State_Handling/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_TCP_Transmission/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_TCP_Utils/ut.cmake )

#  ==================================== Coverage Analysis configuration ========================================
# Add a target for running coverage on tests.
add_custom_target( coverage
    COMMAND ${CMAKE_COMMAND} -P ${MODULE_ROOT_DIR}/test/unit-test/cmock/coverage.cmake
    DEPENDS cmock unity FreeRTOS_ARP_utest FreeRTOS_DHCP_utest FreeRTOS_UDP_IP_utest FreeRTOS_IP_utest FreeRTOS_ICMP_utest FreeRTOS_IP_Utils_utest FreeRTOS_IP_Timers_utest FreeRTOS_Stream_Buffer_utest FreeRTOS_DNS_utest FreeRTOS_TCP_WIN_utest FreeRTOS_Tiny_TCP_utest FreeRTOS_TCP_Reception_utest FreeRTOS_TCP_State_Handling FreeRTOS_TCP_Transmission FreeRTOS_TCP_IP FreeRTOS_TCP_Utils
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
)

