## Getting started
The easiest way to use FreeRTOS-Plus-TCP is to start with the pre-configured demo application project (found in [this directory](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS-Plus/Demo/FreeRTOS_Plus_TCP_Minimal_Windows_Simulator)).  That way you will have the correct FreeRTOS source files included, and the correct include paths configured.  Once a demo application is building and executing you can remove the demo application files, and start to add in your own application source files.  See the [FreeRTOS Kernel Quick Start Guide](https://www.freertos.org/FreeRTOS-quick-start-guide.html) for detailed instructions and other useful links.

Additionally, for FreeRTOS-Plus-TCP source code organization refer to the [Documentation](http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_Networking_Tutorial.html), and [API Reference](https://freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/FreeRTOS_TCP_API_Functions.html).

FreeRTOS+TCP V2.3.2 [source code](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/tree/V2.3.2)(.c .h) is part of the [FreeRTOS 202012.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202012.00-LTS) release.

### Getting help
If you have any questions or need assistance troubleshooting your FreeRTOS project, we have an active community that can help on the [FreeRTOS Community Support Forum](https://forums.freertos.org). Please also refer to [FAQ](http://www.freertos.org/FAQHelp.html) for frequently asked questions.

Also see the [Submitting a bugs/feature request](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/master/CONTRIBUTING.md#submitting-a-bugsfeature-request) section of CONTRIBUTING.md for more details.

## Cloning this repository
This repository uses [Git Submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) to bring in dependent components.

Note: If you download the ZIP file provided by GitHub UI, you will not get the contents of the submodules. (The ZIP file is also not a valid Git repository)

To clone using HTTPS:
```
git clone https://github.com/FreeRTOS/FreeRTOS-Plus-TCP.git
git submodule update --checkout --init --recursive tools/CMock test/FreeRTOS-Kernel
```
Using SSH:
```
git clone git@github.com:FreeRTOS/FreeRTOS-Plus-TCP.git
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
- portable
    - This directory contains the portable files required to compile the FreeRTOS-Plus-TCP source code for different hardware/compilers.
- include
    - The include directory has all the 'core' header files of FreeRTOS-Plus-TCP source.

## Note
At this time it is recommended to use BufferAllocation_2.c in which case it is essential to use the heap_4.c memory allocation scheme. See [memory management](http://www.FreeRTOS.org/a00111.html).

### Kernel sources
The FreeRTOS Kernel Source is in [FreeRTOS/FreeRTOS-Kernel repository](https://github.com/FreeRTOS/FreeRTOS-Kernel), and it is consumed by testing/PR checks as a submodule in this repository.

The version of the FreeRTOS Kernel Source in use could be accessed at ```./test/FreeRTOS-Kernel``` directory.
