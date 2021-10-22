# Unit Tests for FreeRTOS-Plus-TCP library
This directory is made for the purpose of Unit testing and provides tools to create and run unit-tests. To that end, this directory submodules the [CMock](https://github.com/ThrowTheSwitch/CMock) framework (which submodules [Unity](https://github.com/throwtheswitch/unity/tree/cf949f45ca6d172a177b00da2.3.1607b97bc7a7)) and the [FreeRTOS-Kernel](https://github.com/FreeRTOS/FreeRTOS-Kernel/).

## Getting Started
### To run the Unit tests:
You can run this on any Linux based system.
Once you have cloned the FreeRTOS-Plus-TCP repository (using `git clone https://github.com/FreeRTOS/FreeRTOS-Plus-TCP.git ./FreeRTOS_Plus_TCP` command), go to the `test/unit-test` directory of the FreeRTOS+TCP repo and run the `run_test.sh` script (by typing "./run_test.sh").

You should see tools being installed, CMake generating the build system, the tests being compiled. Also, the script will run the tests whereafter you should see an output similar to the one below.
-------------------------------------
```
=================== SUMMARY =====================

Tests Passed  : 186
Tests Failed  : 0
Tests Ignored : 0
OK
Capturing coverage data from .
... <Skipped some lines here for the sake of brevity>
Overall coverage rate:
  lines......: 42.1% (853 of 2024 lines)
  functions..: 41.3% (45 of 109 functions)
  branches...: 39.4% (474 of 1203 branches)
```

And also:

```
Reading tracefile test/unit-test/build/coverage.info
                                |Lines       |Functions  |Branches    
Filename                        |Rate     Num|Rate    Num|Rate     Num
======================================================================
[<Directory of FreeRTOS+TCP>]
FreeRTOS_ARP.c                  | 100%    238| 100%    14|99.3%    137
FreeRTOS_DHCP.c                 |98.7%    314|92.9%    14| 100%    150
FreeRTOS_Sockets.c              | 3.5%   1150| 1.6%    61| 4.2%    722
FreeRTOS_Stream_Buffer.c        | 100%    107| 100%    12| 100%     54
FreeRTOS_UDP_IP.c               | 100%     97| 100%     2| 100%     58
======================================================================
                          Total:|41.6%   1906|40.8%   103|38.2%   1121
```

NOTE: If this does not work or you run into issue with any of the tools, then please refer to the section below to install correct versions of tools for the tests.

### Installing tools manually/downloading the repository.
To compile and run this project successfully, you must have the following:
1. Make (You can check whether you have this by typing `make --version`)
    - Not found? Try `apt-get install make`.
2. Ruby (You can check whether you have this by typing `ruby --version`)
    - Not found? Try `apt-get install ruby`.
3. CMake version > 3.13.0 (You can check whether you have this by typing `cmake --version`)
    - Not found? Try `apt-get install cmake`
    - Try the `cmake --version` command. If still the version number is >= 3.13.0, skip to (4.) or else, continue.
    - You will need to get the latest CMake version using curl or wget (or similar command).
        - Uninstall the current version of CMake using `sudo apt remove --purge --auto-remove cmake`.
        - Download the 3.13.0 version using `wget https://cmake.org/files/v3.13/cmake-3.13.0.tar.gz`.
        - Extract the cmake download using `tar -xzvf cmake-3.13.0.tar.gz`.
        - Go to the extracted folder (`cd cmake-3.13.0`) and run `./bootstrap`.
        - Run `make -j$(nproc)' and then run `sudo make install`.
        - Check the version using `cmake --version` command.
4. lcov version 1.14 ( check with --version option )
    - 'sudo apt-get install lcov'
5. unifdef version 2.10 ( check with -V option )
    - 'sudo apt-get install unifdef'
6. Download the repo and include the submodules using the following commands.
    - `git clone https://github.com/FreeRTOS/FreeRTOS-Plus-TCP.git ./FreeRTOS_Plus_TCP`
    - `cd FreeRTOS_Plus_TCP`
    - `git submodule update --checkout --init --recursive tools/CMock test/FreeRTOS-Kernel`
