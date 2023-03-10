add_subdirectory(build-combination)

if(FREERTOS_PLUS_TCP_BUILD_TEST)
  add_subdirectory(Coverity)
  add_subdirectory(unit-test)
endif()

