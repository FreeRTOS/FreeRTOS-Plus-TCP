# !/bin/bash

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
echo "Installing lcov..."
sudo apt-get install -y lcov > /dev/null
lcov --version

echo ""
echo ""
echo "Installing unifdef..."
sudo apt-get install -y unifdef > /dev/null
unifdef -V

# Build the build system
cmake -S test/unit-test -B test/unit-test/build/

# Compile the tests
make -C test/unit-test/build/ all

# Run the tests
cd test/unit-test/build/
ctest -E system --output-on-failure
cd ..
