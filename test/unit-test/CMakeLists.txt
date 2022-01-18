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

# Set the platform specific variables to default value.
set( UT_PLATFORM "Ubuntu" CACHE STRING "The platform on which the unit tests are compiled and executed." )
set( SYSTEM_PKG_MNGR "" CACHE STRING "The package manager on the underlying OS." )
set( SYSTEM_INSTALL_CMD "" CACHE STRING "The command to install a package." )

# Flag to allow cmake to install tools required for running unit-tests.
set( ALLOW_CMAKE_TO_INSTALL_TOOLS "0" CACHE STRING "Option which user can set to enable installation of certain tools required for running the unit-tests." )

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
    message( WARNING "FreeRTOS-Kernel is required for this build. Submoduling it..." )
    execute_process( COMMAND git submodule update --init --checkout ${KERNEL_DIRECTORY}
                     WORKING_DIRECTORY ${MODULE_ROOT_DIR} )
endif()

# Define a CMock resource path.
set( CMOCK_DIR ${MODULE_ROOT_DIR}/tools/CMock CACHE INTERNAL "CMock library source directory." )

# Check if the CMock source directory exists, and if not present, clone the submodule
# if BUILD_CLONE_SUBMODULES configuration is enabled.
if( NOT EXISTS ${CMOCK_DIR}/src )
    # Attempt to clone CMock and inform the user of the actions.
    message( WARNING "CMock is required for this build. Submoduling it..." )
    execute_process( COMMAND git submodule update --init --checkout --recursive ${CMOCK_DIR}
                     WORKING_DIRECTORY ${MODULE_ROOT_DIR} )
endif()


if( NOT EXISTS ${CMOCK_DIR}/vendor/unity/docs )
    # Attempt to clone Unity and inform the user of the actions.
    message( WARNING "Unity is required for this build. Submoduling it..." )
    execute_process( COMMAND git submodule update --init --checkout --recursive ${CMOCK_DIR}
                     WORKING_DIRECTORY ${MODULE_ROOT_DIR} )
endif()

# Check for the platform/OS specific details only if user has allowed the Cmake to
# install tools.
if( ${ALLOW_CMAKE_TO_INSTALL_TOOLS} )
    # If the platform is Ubuntu.
    if( ${UT_PLATFORM} STREQUAL "Ubuntu" )
        set( SYSTEM_PKG_MNGR "apt-get" )
        set( SYSTEM_INSTALL_CMD "install" )
    # Or the platform is MacOS.
    elseif( ${UT_PLATFORM} STREQUAL "MacOS" )
        set( SYSTEM_PKG_MNGR "brew" )
        set( SYSTEM_INSTALL_CMD "install" )
    # Or the platform is rpm based system.
    elseif( ${UT_PLATFORM} STREQUAL "RPMSystem" )
        set( SYSTEM_PKG_MNGR "yum" )
        set( SYSTEM_INSTALL_CMD "install" )
    else()
        # Otherwise, check whether user has given any system package manager and
        # corresponding command.
        if( ( "${SYSTEM_PKG_MNGR}" STREQUAL "" ) OR ( "${SYSTEM_INSTALL_CMD}" STREQUAL "" ) )
            message( FATAL_ERROR "Wrong platform specified. While invoking the cmake command, you can choose the platform as shown below\n"
                                 "Only 'Ubuntu', 'RPMSystem' and 'MacOS' are valid options.\n"
                                 "    cmake -S. -B build <Additional commands/options> -DUT_PLATFORM=Ubuntu\n"
                                 "Otherwise, you can set the package manager and the install command. Example for Red Hat Enterprise Linux:\n"
                                 "    cmake -S. -B build <Additional commands/options> -DSYSTEM_PKG_MNGR=yum -DSYSTEM_INSTALL_CMD=install" )
        endif()
    endif()
endif()

# Find 'unifdef' utility.
find_program( UNIFDEF_found unifdef )

if( NOT UNIFDEF_found )
    if( ${ALLOW_CMAKE_TO_INSTALL_TOOLS} )
        # unifdef was not found, install it and inform the user of the location of installation.
        message( WARNING "unifdef utility not found. Installing it." )
        execute_process( COMMAND ${SYSTEM_PKG_MNGR} ${SYSTEM_INSTALL_CMD} unifdef )

        find_program( UNIFDEF_found unifdef )
        if( NOT UNIFDEF_found )
            message( FATAL_ERROR "Could not install unifdef. Stopping. Please install the tool manually." )
        endif()
        message( STATUS "unifdef installed at location ${UNIFDEF_found}" )
    else()
        message( FATAL_ERROR "unifdef utility was not found in the system path.\n"
                             "You may choose to install it yourself, or set ALLOW_CMAKE_TO_INSTALL_TOOLS to 1 while\n"
                             "invoking CMake to let the script install unifdef, lcov and ruby. You can set the macro as shown below\n"
                             "    cmake <all your options go here> -DALLOW_CMAKE_TO_INSTALL_TOOLS=1" )
    endif()
endif()

# Find 'lcov' utility.
find_program( LCOV_found lcov )

if( NOT LCOV_found )
    if( ${ALLOW_CMAKE_TO_INSTALL_TOOLS} )
        # lcov was not found, install it and inform the user of the location of installation.
        message( WARNING "lcov utility not found. Installing it." )
        execute_process( COMMAND ${SYSTEM_PKG_MNGR} ${SYSTEM_INSTALL_CMD} lcov )

        find_program( LCOV_found lcov )
        if( NOT LCOV_found )
            message( FATAL_ERROR "Could not install lcov. Stopping. Please install the tool manually." )
        endif()
        message( STATUS "lcov installed at location ${LCOV_found}" )
    else()
        message( FATAL_ERROR "lcov utility was not found in the system path.\n"
                             "You may choose to install it yourself, or set ALLOW_CMAKE_TO_INSTALL_TOOLS to 1 while\n"
                             "invoking CMake to let the script install unifdef, lcov and ruby. You can set the macro as shown below\n"
                             "    cmake <all your options go here> -DALLOW_CMAKE_TO_INSTALL_TOOLS=1" )
    endif()
endif()

# Find whether ruby is installed.
find_program( RUBY_found ruby )

if( NOT RUBY_found )
    if( ${ALLOW_CMAKE_TO_INSTALL_TOOLS} )
        # Ruby was not found, install it and inform the user of the location of installation.
        message( WARNING "Ruby (required by CMock) not found. Installing it." )
        execute_process( COMMAND ${SYSTEM_PKG_MNGR} ${SYSTEM_INSTALL_CMD} ruby )

        find_program( RUBY_found ruby )
        if( NOT RUBY_found )
            message( FATAL_ERROR "Could not install Ruby. Stopping. Please install Ruby manually." )
        endif()
        message( STATUS "ruby installed at location ${RUBY_found}" )
    else()
        message( FATAL_ERROR "Ruby was not found in the system path.\n"
                             "You may choose to install it yourself, or set ALLOW_CMAKE_TO_INSTALL_TOOLS to 1 while\n"
                             "invoking CMake to let the script install unifdef, lcov and ruby. You can set the macro as shown below\n"
                             "    cmake <all your options go here> -DALLOW_CMAKE_TO_INSTALL_TOOLS=1" )
    endif()

endif()

# Set the include directories
string( APPEND GLOBAL_INCLUDES "-I ${MODULE_ROOT_DIR}/include ")
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
set( TCP_INCLUDES "${MODULE_ROOT_DIR}/include/FreeRTOS_IP.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_ARP.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_Sockets.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_IP_Private.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_UDP_IP.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_DHCP.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_DNS.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_TCP_IP.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_Stream_Buffer.h"
                  "${MODULE_ROOT_DIR}/include/FreeRTOS_TCP_WIN.h"
                  "${MODULE_ROOT_DIR}/include/NetworkBufferManagement.h"
                  "${MODULE_ROOT_DIR}/include/NetworkInterface.h" )

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

    # Use this tool to process all conditional declarations.
    execute_process( COMMAND unifdefall -U${Guard} -D__COVERITY__ -I ${MODULE_ROOT_DIR}/tools/CMock/vendor/unity/src
                                                   -I ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include
                                                   -I ${UNIT_TEST_DIR}/ConfigFiles
                                                   -I ${MODULE_ROOT_DIR}/include
                                                   -I ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/portable/ThirdParty/GCC/Posix
                                                   ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}_tmp.h
                     WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                     OUTPUT_FILE ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h
                     OUTPUT_QUIET )

    # Add the guards back to the files
    execute_process( COMMAND sed -i "1 i\#ifndef ${Guard}" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h )
    execute_process( COMMAND sed -i -e "$ a\#endif" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h )

    execute_process( COMMAND sed -i -E "s,[ ]*extern ipDECL_CAST_.*,,g" ${CMAKE_BINARY_DIR}/Annexed_TCP/${MODIFIED_FILE}.h )

endforeach()
# ===========================================================================



# ===================================== Include the cmake configurations =================================================

# Include filepaths for source and include.
include( ${UNIT_TEST_DIR}/TCPFilePaths.cmake )

#  ==================================== Test Configuration ========================================

# Include CMock build configuration.
include( cmock_build.cmake )

# Add unit test and coverage configuration.

# Use CTest utility for managing test runs. This has to be added BEFORE
# defining test targets with add_test()
enable_testing()

# Add build targets for CMock and Unit, required for unit testing.
add_cmock_targets()

# Add function to enable CMock based tests and coverage.
include( ${MODULE_ROOT_DIR}/test/unit-test/cmock/create_test.cmake )

# Include unit-test build configuration

include( ${UNIT_TEST_DIR}/FreeRTOS_ARP/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_DHCP/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_Sockets/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_Stream_Buffer/ut.cmake )
include( ${UNIT_TEST_DIR}/FreeRTOS_UDP_IP/ut.cmake )

#  ==================================== Coverage Analysis configuration ========================================

# Add a target for running coverage on tests.
add_custom_target( coverage
    COMMAND ${CMAKE_COMMAND} -P ${MODULE_ROOT_DIR}/test/unit-test/cmock/coverage.cmake
    DEPENDS cmock unity FreeRTOS_ARP_utest FreeRTOS_DHCP_utest FreeRTOS_UDP_IP_utest FreeRTOS_Stream_Buffer_utest FreeRTOS_Sockets_utest
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
)
