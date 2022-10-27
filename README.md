## FreeRTOS-Plus-TCP Library
FreeRTOS-Plus-TCP is a lightweight TCP/IP stack for FreeRTOS. It provides a familiar Berkeley sockets interface, making it as simple to use and learn as possible. FreeRTOS-Plus-TCP's features and RAM footprint are fully scalable, making FreeRTOS-Plus-TCP equally applicable to smaller lower throughput microcontrollers as well as larger higher throughput microprocessors.

This library has undergone static code analysis and checks for compliance with the [MISRA coding standard](https://www.misra.org.uk/). Any deviations from the MISRA C:2012 guidelines are documented under [MISRA Deviations](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md). The library is validated for memory safety and data structure invariance through the [CBMC automated reasoning tool](https://www.cprover.org/cbmc/) for the functions that parse data originating from the network.

## Getting started
The easiest way to use FreeRTOS-Plus-TCP is to start with the pre-configured demo application project (found in [this directory](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS-Plus/Demo/FreeRTOS_Plus_TCP_Minimal_Windows_Simulator)).  That way you will have the correct FreeRTOS source files included, and the correct include paths configured.  Once a demo application is building and executing you can remove the demo application files, and start to add in your own application source files.  See the [FreeRTOS Kernel Quick Start Guide](https://www.freertos.org/FreeRTOS-quick-start-guide.html) for detailed instructions and other useful links.

Additionally, for FreeRTOS-Plus-TCP source code organization refer to the [Documentation](http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_Networking_Tutorial.html), and [API Reference](https://freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/FreeRTOS_TCP_API_Functions.html).

**FreeRTOS-Plus-TCP V3.1.0 [source code](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/tree/V3.1.0)(.c .h) is part of the [FreeRTOS 202210.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202210.00-LTS) release.**

### Getting help
If you have any questions or need assistance troubleshooting your FreeRTOS project, we have an active community that can help on the [FreeRTOS Community Support Forum](https://forums.freertos.org). Please also refer to [FAQ](http://www.freertos.org/FAQHelp.html) for frequently asked questions.

Also see the [Submitting a bugs/feature request](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/.github/CONTRIBUTING.md#submitting-a-bugsfeature-request) section of CONTRIBUTING.md for more details.

## Upgrading to V3.0.0 and above
In version 3.0.0 or higher, the folder structure of FreeRTOS-Plus-TCP has changed and the files have been broken down into smaller logically separated modules. This change makes the code more modular and conducive to unit-tests. FreeRTOS-Plus-TCP V3.0.0 improves the robustness, security, and modularity of the library. Version 3.0.0 adds comprehensive unit test coverage for all lines and branches of code and has undergone protocol testing, and penetration testing by AWS Security to reduce the exposure to security vulnerabilities. Additionally, the source files have been moved to a `source` directory. This change requires modification of any existing project(s) to include the modified source files and directories. There are examples on how to use the new files and directory structure. For a windows simulator based example, refer to this [demo](https://github.com/FreeRTOS/FreeRTOS/tree/TCPRefactorDemo/FreeRTOS-Plus/Demo/FreeRTOS_Plus_TCP_Minimal_Windows_Simulator). For an example based on the Xilinx Zynq-7000, use the code in this [branch](https://github.com/aws/amazon-freertos/tree/TCPRefactorDemo) and follow these [instructions](https://docs.aws.amazon.com/freertos/latest/userguide/getting_started_xilinx.html) to build and run the demo.

### Generating pre V3.0.0 folder structure for backward compatibility:
If you wish to continue using a version earlier than V3.0.0 i.e. continue to use your existing source code organization, a script is provided to generate the folder structure similar to [this](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/tree/f118c8415b4373e3d6e6dbd2d5a116f7eaf27b63).

**Note:** After running the script, while the .c files will have same names as the pre V3.0.0 source, the files in the `include` directory will have different names and the number of files will differ as well. This should, however, not pose any problems to most projects as projects generally include all files in a given directory.

Running the script to generate pre V3.0.0 folder structure:
For running the script, you will need Python version > 3.7. You can download/install it from [here](https://www.python.org/downloads/).

Once python is downloaded and installed, you can verify the version from your terminal/command window by typing `python --version`.

To run the script, you should switch to the FreeRTOS-Plus-TCP directory that was created using the [Cloning this repository](#cloning-this-repository) step above.
And then run  `python <Path/to/the/script>/GenerateOriginalFiles.py`.

## Cloning this repository
This repository uses [Git Submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) to bring in dependent components.

Note: If you download the ZIP file provided by GitHub UI, you will not get the contents of the submodules. (The ZIP file is also not a valid Git repository)

To clone using HTTPS:
```
git clone https://github.com/FreeRTOS/FreeRTOS-Plus-TCP.git ./FreeRTOS-Plus-TCP
cd ./FreeRTOS-Plus-TCP
git submodule update --checkout --init --recursive tools/CMock test/FreeRTOS-Kernel
```
Using SSH:
```
git clone git@github.com:FreeRTOS/FreeRTOS-Plus-TCP.git ./FreeRTOS-Plus-TCP
cd ./FreeRTOS-Plus-TCP
git submodule update --checkout --init --recursive tools/CMock test/FreeRTOS-Kernel
```

## Porting
The porting guide is available on [this page](http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/FreeRTOS_TCP_Porting.html).

## Repository structure
This repository contains the FreeRTOS-Plus-TCP repository and a number of supplementary libraries for testing/PR Checks.
Below is the breakdown of what each directory contains:
- tools
    - This directory contains the tools and related files (CMock/uncrustify) required to run tests/checks on the TCP source code.
- tests
    - This directory contains all the tests (unit tests and CBMC) and the dependencies ([FreeRTOS-Kernel](https://github.com/FreeRTOS/FreeRTOS-Kernel)/[Litani-port](https://github.com/awslabs/aws-build-accumulator)) the tests require.
- source/portable
    - This directory contains the portable files required to compile the FreeRTOS-Plus-TCP source code for different hardware/compilers.
- source/include
    - The include directory has all the 'core' header files of FreeRTOS-Plus-TCP source.
- source
    - This directory contains all the [.c] source files.

## Note
At this time it is recommended to use BufferAllocation_2.c in which case it is essential to use the heap_4.c memory allocation scheme. See [memory management](http://www.FreeRTOS.org/a00111.html).

### Kernel sources
The FreeRTOS Kernel Source is in [FreeRTOS/FreeRTOS-Kernel repository](https://github.com/FreeRTOS/FreeRTOS-Kernel), and it is consumed by testing/PR checks as a submodule in this repository.

The version of the FreeRTOS Kernel Source in use could be accessed at ```./test/FreeRTOS-Kernel``` directory.

## CBMC

The `test/cbmc/proofs` directory contains CBMC proofs.

To learn more about CBMC and proofs specifically, review the training material [here](https://model-checking.github.io/cbmc-training).

In order to run these proofs you will need to install CBMC and other tools by following the instructions [here](https://model-checking.github.io/cbmc-training/installation.html).
