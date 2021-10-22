# !/bin/bash

if [[ ! -f run_test.sh ]]; then
    echo "Please run this script from the test/unit-test directory of the FreeRTOS+TCP repo."
    exit 1
fi

echo "Starting submodule checks"
cd ../..

git submodule update --init

# Check whether FreeRTOS-Kernel is already present. If not, try to checkout
# the submodule.
if [ -f test/FreeRTOS-Kernel/tasks.c ]; then
    echo "FreeRTOS Kernel is already submoduled. Skipping..."
else
    echo "Checking out FreeRTOS-Kernel..."
    git submodule update --init --checkout test/FreeRTOS-Kernel
fi


# Check whether CMock and unity are already present. If not, try to checkout
# the submodules.
if [ -d tools/CMock/vendor ]; then
    if [ -d tools/CMock/vendor/unity/docs ]; then
        echo "CMock and Unity already checked out. Skipping..."
    else
        echo "CMock already present, checking out Unity..."
        git submodule update --init --checkout tools/CMock/vendor/unity
    fi
else
    echo "Checking out CMock and Unity..."
    git submodule update --init --checkout tools/CMock
    cd tools/CMock
    git submodule update --init --checkout vendor/unity
    cd ../..
fi

# Install the required tools
echo ""
echo ""
echo "Installing make..."
apt-get install make > /dev/null

echo ""
echo ""
echo "Installing Ruby (required by CMock)..."
apt-get install ruby > /dev/null


echo ""
echo ""
echo "Installing CMake (Used to generate the build system)..."
apt-get install cmake > /dev/null

echo ""
echo ""
echo "Installing lcov..."
apt-get install -y lcov > /dev/null
lcov --version

echo ""
echo ""
echo "Installing unifdef..."
apt-get install -y unifdef > /dev/null
unifdef -V

# Build the build system
cmake -S test/unit-test -B test/unit-test/build/

# Compile the tests
make -C test/unit-test/build/ all

# Run the tests
cd test/unit-test/build/
ctest -E system --output-on-failure
cd ..

# Build the coverage info
make -C build/ coverage

# Display the coverage
lcov --list --rc lcov_branch_coverage=1 build/coverage.info
