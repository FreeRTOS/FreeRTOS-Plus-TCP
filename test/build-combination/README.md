# Build Instructions

This test aims at finding only compilation issues and as a result, the
generated binary is not runnable.

## UNIX (Linux and Mac)

All the CMake commands are to be run from the root of the repository.

* Build checks (Enable all functionalities)
```
cmake -S test/build-combination -B test/build-combination/build/ -DTEST_CONFIGURATION=ENABLE_ALL
make -C test/build-combination/build/
```

* Build checks (Disable all functionalities)
```
cmake -S test/build-combination -B test/build-combination/build/ -DTEST_CONFIGURATION=DISABLE_ALL
make -C test/build-combination/build/
```

* Build checks (Default configuration)
```
cmake -S test/build-combination -B test/build-combination/build/ -DTEST_CONFIGURATION=DEFAULT_CONF
make -C test/build-combination/build/
```

## Windows

All the CMake commands are to be run from the root of the repository.

* Build checks (Enable all functionalities)
```
cmake -S test/build-combination -B test/build-combination/build/ -DTEST_CONFIGURATION=ENABLE_ALL -DCMAKE_GENERATOR_PLATFORM=Win32
```
Open the generated Visual Studio Solution file `test\build-combination\build\FreeRTOS-Plus-TCP Build Combination.sln`
in Visual Studio and click `Build --> Build Solution`.

* Build checks (Disable all functionalities)
```
cmake -S test/build-combination -B test/build-combination/build/ -DTEST_CONFIGURATION=ENABLE_ALL -DCMAKE_GENERATOR_PLATFORM=Win32
```
Open the generated Visual Studio Solution file `test\build-combination\build\FreeRTOS-Plus-TCP Build Combination.sln`
in Visual Studio and click `Build --> Build Solution`.

* Build checks (Default configuration)
```
cmake -S test/build-combination -B test/build-combination/build/ -DTEST_CONFIGURATION=ENABLE_ALL -DCMAKE_GENERATOR_PLATFORM=Win32
```
Open the generated Visual Studio Solution file `test\build-combination\build\FreeRTOS-Plus-TCP Build Combination.sln`
in Visual Studio and click `Build --> Build Solution`.
