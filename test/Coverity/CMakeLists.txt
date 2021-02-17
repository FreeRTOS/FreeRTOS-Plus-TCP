cmake_minimum_required ( VERSION 3.13.0 )
project ( "FreeRTOS-Plus-TCP Coverity"
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

# =============  Define source path and related variables (edit)  ==============
# Set global path variables.
get_filename_component(__MODULE_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}/../.." ABSOLUTE)
set( MODULE_ROOT_DIR ${__MODULE_ROOT_DIR} CACHE INTERNAL "FreeRTOS-Plus-TCP repository root." )

# Add kernel sources to a list
file( GLOB KERNEL_SOURCES
           ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/*.c )

# Add TCP sources to a list
file( GLOB TCP_SOURCES
           ${MODULE_ROOT_DIR}/*.c )

add_executable( Coverity ${TCP_SOURCES}
                         ${KERNEL_SOURCES}
                         ${CMAKE_CURRENT_LIST_DIR}/Portable.c
                         ${MODULE_ROOT_DIR}/portable/BufferManagement/BufferAllocation_2.c )

message( STATUS "Including ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include  ${CMAKE_CURRENT_LIST_DIR}/Portable.c  " )

target_include_directories( Coverity
                            PUBLIC "${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include"
                            PUBLIC "${MODULE_ROOT_DIR}/test/Coverity/ConfigFiles"
                            PUBLIC "${MODULE_ROOT_DIR}/include" )
