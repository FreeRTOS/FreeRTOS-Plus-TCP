cmake_minimum_required ( VERSION 3.13.0 )
project ( "FreeRTOS-Plus-TCP Build Combination"
          VERSION 1.0.0
          LANGUAGES C )

# Allow the project to be organized into folders.
set_property( GLOBAL PROPERTY USE_FOLDERS ON )

# Use C90.
set( CMAKE_C_STANDARD 90 )
set( CMAKE_C_STANDARD_REQUIRED ON )

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Set global path variables.
get_filename_component(__MODULE_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}/../.." ABSOLUTE)
set(MODULE_ROOT_DIR ${__MODULE_ROOT_DIR} CACHE INTERNAL "FreeRTOS-Plus-TCP repository root.")

# Configure options to always show in CMake GUI.
option( BUILD_CLONE_SUBMODULES
        "Set this to ON to automatically clone any required Git submodules. When OFF, submodules must be manually cloned."
        ON )


option(TEST_CONFIGURATION "Configuration All Enable/Disable" ENABLE_ALL)

message( STATUS "Argument: ${TEST_CONFIGURATION}")

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )


set( FREERTOS_KERNEL_DIR ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel )
set( TEST_DIR ${MODULE_ROOT_DIR}/test/build-combination )

include_directories( ${MODULE_ROOT_DIR}/include )
include_directories( ${MODULE_ROOT_DIR}/portable/Compiler/MSVC )
include_directories( ${FREERTOS_KERNEL_DIR}/include )
include_directories( ${FREERTOS_KERNEL_DIR}/portable/MSVC-MingW )
include_directories( ${FREERTOS_KERNEL_DIR}/portable/MemMang )
include_directories( ${TEST_DIR}/Common )

if( ${TEST_CONFIGURATION} STREQUAL "ENABLE_ALL" )
	include_directories( ${TEST_DIR}/AllEnable )
else()
	include_directories( ${TEST_DIR}/AllDisable )
endif()



file(GLOB KERNEL_SOURCES "${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/*.c")
file(GLOB TCP_SOURCES "${MODULE_ROOT_DIR}/*.c")

message(STATUS "${KERNEL_SOURCES}")
message(STATUS "${TCP_SOURCES}")


add_executable(project ${KERNEL_SOURCES}
		       ${TCP_SOURCES}
		       ${FREERTOS_KERNEL_DIR}/portable/MemMang/heap_4.c
		       ${MODULE_ROOT_DIR}/portable/BufferManagement/BufferAllocation_2.c
		       ${TEST_DIR}/Common/main.c )
