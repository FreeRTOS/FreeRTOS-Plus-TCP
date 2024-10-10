#!/bin/bash
# This script should be run from the root directory of the FreeRTOS+TCP repo.

if [[ ! -d source ]]; then
    echo "Please run this script from the root directory of the FreeRTOS+TCP repo."
    exit 1
fi

clear

UNIT_TEST_DIR="test/unit-test"
BUILD_DIR="${UNIT_TEST_DIR}/build/"

# Create the build directory using CMake:
rm -rf ${BUILD_DIR}
cmake -S ${UNIT_TEST_DIR} -B ${BUILD_DIR} -G Ninja

# Create the executables:
ninja -C ${BUILD_DIR} all

pushd ${BUILD_DIR}
# Run the tests for all units
ctest -E system --output-on-failure
popd

# Calculate the coverage
# ninja -C ${BUILD_DIR} coverage
# lcov --list --rc lcov_branch_coverage=1 ${BUILD_DIR}coverage.info
