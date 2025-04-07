# Unit Tests for FreeRTOS-Plus-TCP library

This directory is made for the purpose of Unit testing and tries to provide the
tools for developing unit tests. To that end, this directory submodules the
[CMock](https://github.com/ThrowTheSwitch/CMock) framework (which submodules
[Unity](https://github.com/throwtheswitch/unity/))
and the [FreeRTOS-Kernel](https://github.com/FreeRTOS/FreeRTOS-Kernel/).

Note: The following steps are tested on Ubuntu 24.04

## Getting Started

### Prerequisites

You can run this on any GNU Make compatible systems. But in case of DOS based
systems some tweaking is required with the makefile. To compile and run this
project successfully, you must have the following:

1. Make (You can check whether you have this by typing `make --version`)
   - Not found? Try `sudo apt-get install make`.
2. Ruby (You can check whether you have this by typing `ruby --version`)
   - Not found? Try `sudo apt-get install ruby`.
3. Ninja (You can check whether you have this by typing `ninja --version`)
   - Not found? Try `sudo apt install ninja-build`.
3. CMake version > 3.15.0 (You can check whether you have this by typing
   `cmake --version`)
   - Not found? Try `sudo apt-get install cmake`
   - Try the `cmake --version` command. If still the version number is >=
     3.15.0, skip to (4.) or else, continue.
   - You will need to get the latest CMake version using curl or wget (or
     similar command).
     - Uninstall the current version of CMake using
       `sudo apt remove --purge --auto-remove cmake`.
     - Download the [CMAKE version 3.15.0](https://cmake.org/files/v3.15/).
     - Extract the cmake download using `tar -xzvf cmake-3.15.0.tar.gz`.
     - Go to the extracted folder (`cd cmake-3.15.0`) and run `./bootstrap`.
     - Run `make -j$(nproc)' and then run `sudo make install`.
     - Check the version using `cmake --version` command.
4. lcov ( check with `lcov --version` option )
   - `sudo apt-get install lcov`
   - If file specific coverage list is required check the note in the below section
     for the required version.
5. unifdef version 2.10 ( check with -V option )
   - `sudo apt-get install unifdef`

### To run the Unit tests:

Go to the root directory of the FreeRTOS+TCP repo and run the following script:

``` sh
#!/bin/bash
# This script should be run from the root directory of the FreeRTOS+TCP repo.

if [[ ! -d source ]]; then
    echo "Please run this script from the root directory of the FreeRTOS+TCP repo."
    exit 1
fi

UNIT_TEST_DIR="test/unit-test"
BUILD_DIR="${UNIT_TEST_DIR}/build/"

# Create the build directory using CMake:
rm -rf ${BUILD_DIR}
cmake --fresh -G Ninja -S ${UNIT_TEST_DIR} -B ${UNIT_TEST_DIR}/build/ -DSANITIZE=

# Create the executables:
ninja -C ${UNIT_TEST_DIR}/build/

# Run tests
ctest --test-dir ${BUILD_DIR} -E system --output-on-failure

# Make and calculate the coverage
cmake --build ${BUILD_DIR} --target coverage
lcov --summary --rc branch_coverage=1 ${BUILD_DIR}/coverage.info

# For file specific coverage list uncomment the following lines

# wget https://github.com/linux-test-project/lcov/releases/download/v2.3.1/lcov-2.3.1.tar.gz
# tar -xvzf lcov-2.3.1.tar.gz
# ./lcov-2.3.1/bin/lcov --list --rc branch_coverage=1  ${BUILD_DIR}/coverage.info

```

You should see an output similar to this:

```
... <Skipped some lines here for the sake of brevity>
Overall coverage rate:
  lines......: 100.0% (9388 of 9388 lines)
  functions......: 100.0% (525 of 525 functions)
  branches......: 100.0% (4920 of 4920 branches)
```

Note: If file specific coverage list is required the lcov version should be updated to
the newer version (for example, [v2.3.1](https://github.com/linux-test-project/lcov/releases/tag/v2.3.1))
as the default version of `lcov` in Ubuntu 24.04 results in incorrect parsing of
`coverage.info`.

Sample file specific coverage data:


```
                                    |Lines      |Functions |Branches
Filename                            |Rate    Num|Rate  Num|Rate   Num
=====================================================================
[/home/ubuntu/FreeRTOS-Plus-TCP/source/]
FreeRTOS_ARP.c                      | 100%   358| 100%  21| 100%  241
FreeRTOS_DNS.c                      | 100%   361| 100%  23| 100%  184
FreeRTOS_DNS_Cache.c                | 100%   126| 100%  11| 100%   54
FreeRTOS_DNS_Callback.c             | 100%    80| 100%   4| 100%   34
FreeRTOS_DNS_Networking.c           | 100%    31| 100%   5| 100%    4
FreeRTOS_DNS_Parser.c               | 100%   366| 100%   6| 100%  192
FreeRTOS_Stream_Buffer.c            | 100%   101| 100%  12| 100%   46
FreeRTOS_Tiny_TCP.c                 | 100%    92| 100%  12| 100%   40

[/home/ubuntu/FreeRTOS-Plus-TCP/test/unit-test/build/Annexed_TCP_Sources/]
FreeRTOS_BitConfig.c                | 100%    87| 100%  11| 100%   30
FreeRTOS_DHCP.c                     | 100%   444| 100%  19| 100%  256
FreeRTOS_DHCPv6.c                   | 100%   576| 100%  18| 100%  252
FreeRTOS_ICMP.c                     | 100%    44| 100%   3| 100%   11
FreeRTOS_IP.c                       | 100%   642| 100%  46| 100%  331
FreeRTOS_IP_Timers.c                | 100%   152| 100%  21| 100%   84
FreeRTOS_IP_Utils.c                 | 100%   472| 100%  33| 100%  256
FreeRTOS_IPv4.c                     | 100%   148| 100%   7| 100%  110
FreeRTOS_IPv4_Sockets.c             | 100%    62| 100%   4| 100%   40
FreeRTOS_IPv4_Utils.c               | 100%    40| 100%   2| 100%   16
FreeRTOS_IPv6.c                     | 100%   201| 100%  10| 100%  126
FreeRTOS_IPv6_Sockets.c             | 100%   189| 100%  12| 100%  106
FreeRTOS_IPv6_Utils.c               | 100%    99| 100%   5| 100%   49
FreeRTOS_ND.c                       | 100%   431| 100%  18| 100%  187
FreeRTOS_RA.c                       | 100%   198| 100%   9| 100%   80
FreeRTOS_Routing.c                  | 100%   360| 100%  24| 100%  213
FreeRTOS_Sockets.c                  | 100%  1542| 100%  89| 100%  841
FreeRTOS_TCP_IP.c                   | 100%   243| 100%  10| 100%  196
FreeRTOS_TCP_Reception.c            | 100%   157| 100%   5| 100%   87
FreeRTOS_TCP_State_Handling.c       | 100%   277| 100%   9| 100%  124
FreeRTOS_TCP_State_Handling_IPv4.c  | 100%    52| 100%   1| 100%   30
FreeRTOS_TCP_State_Handling_IPv6.c  | 100%    50| 100%   1| 100%   32
FreeRTOS_TCP_Transmission.c         | 100%   331| 100%  19| 100%  154
FreeRTOS_TCP_Transmission_IPv4.c    | 100%   131| 100%   3| 100%   36
FreeRTOS_TCP_Transmission_IPv6.c    | 100%   145| 100%   3| 100%   50
FreeRTOS_TCP_Utils.c                | 100%    21| 100%   2| 100%   16
FreeRTOS_TCP_Utils_IPv4.c           | 100%     9| 100%   1| 100%    4
FreeRTOS_TCP_Utils_IPv6.c           | 100%    15| 100%   1| 100%    6
FreeRTOS_TCP_WIN.c                  | 100%   456| 100%  37| 100%  222
FreeRTOS_UDP_IP.c                   | 100%    28| 100%   2| 100%   12
FreeRTOS_UDP_IPv4.c                 | 100%   128| 100%   2| 100%   84
FreeRTOS_UDP_IPv6.c                 | 100%   143| 100%   4| 100%   84
=====================================================================
                              Total:| 100%  9388| 100% 525| 100% 4920
Message summary:
  no messages were reported
```
