## Getting started
The easiest way to use FreeRTOS-Plus-TCP is to start with the pre-configured demo application project (found in the [this directory](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS-Plus/Demo/FreeRTOS_Plus_TCP_Minimal_Windows_Simulator)).  That way you will have the correct FreeRTOS source files included, and the correct include paths configured.  Once a demo application is building and executing you can remove the demo application files, and start to add in your own application source files.  See the [FreeRTOS Kernel Quick Start Guide](https://www.freertos.org/FreeRTOS-quick-start-guide.html) for detailed instructions and other useful links.

Additionally, for FreeRTOS-Plus-TCP information refer to the [Documentation](https://freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/index.html), and [API Reference](https://freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/FreeRTOS_TCP_API_Functions.html).

### Getting help
If you have any questions or need assistance troubleshooting your FreeRTOS project, we have an active community that can help on the [FreeRTOS Community Support Forum](https://forums.freertos.org). Please also refer to [FAQ](http://www.freertos.org/FAQHelp.html) for frequently asked questions.

## Cloning this repository
This repo uses [Git Submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) to bring in dependent components.

Note: If you download the ZIP file provided by GitHub UI, you will not get the contents of the submodules. (The ZIP file is also not a valid git repository)

To clone using HTTPS:
```
git clone https://github.com/FreeRTOS/FreeRTOS-Plus-TCP.git --recurse-submodules
```
Using SSH:
```
git clone git@github.com:FreeRTOS/FreeRTOS-Plus-TCP.git --recurse-submodules
```

If you have downloaded the repo without using the `--recurse-submodules` argument, you need to run:
```
git submodule update --init --recursive
```

## Repository structure
This repository contains the FreeRTOS-Plus-TCP repository and a number of supplementary libraries for testing/PR Checks.

### Kernel sources
The FreeRTOS Kernel Source is in [FreeRTOS/FreeRTOS-Kernel repository](https://github.com/FreeRTOS/FreeRTOS-Kernel), and it is consumed by testing/PR checks as a submodule in this repository.

The version of the FreeRTOS Kernel Source in use could be accessed at ```./FreeRTOS/Source``` directory.
