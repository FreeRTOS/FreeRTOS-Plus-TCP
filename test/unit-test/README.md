# Unit Tests for FreeRTOS-Plus-TCP library
This directory is made for the purpose of Unit testing and tries to provide the tools for developing unit tests. To that end, this directory submodules the [CMock](https://github.com/ThrowTheSwitch/CMock) framework (which submodules [Unity](https://github.com/throwtheswitch/unity/tree/cf949f45ca6d172a177b00da2.3.1607b97bc7a7)) and the [FreeRTOS-Kernel](https://github.com/FreeRTOS/FreeRTOS-Kernel/).

## Getting Started
### Prerequisites
You can run this on any GNU Make compatible systems. But in case of DOS based systems some tweaking is required with the makefile.
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
4. Download the repo and include the submodules using the following commands.
    - `git clone https://github.com/FreeRTOS/FreeRTOS.git ./FreeRTOS_Dir`
    - `git submodule update --checkout --init --recursive tools/CMock test/FreeRTOS-Kernel`

### To run the Unit tests:
Go to `test/unit-test`.
CMake: (do replace the `<your-build-directory>` with directory of your choice)
- `cmake -B<your-build-directory> .`
Make and coverage:
- `cd <your-build-directory>`
- `make all`
- `make coverage`

You should see an output similar to this:
```
-----------------------
6 Tests 0 Failures 0 Ignored 
OK
Capturing coverage data from .
... <Skipped some lines here for the sake of brevity>
Overall coverage rate:
  lines......: 84.8% (56 of 66 lines)
  functions..: 85.7% (12 of 14 functions)
  branches...: 50.0% (2 of 4 branches)

```
