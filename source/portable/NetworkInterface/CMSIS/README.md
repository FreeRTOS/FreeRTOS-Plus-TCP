# CMSIS NetworkInterface Template

This directory provides a generic FreeRTOS+TCP `NetworkInterface.c` for boards using CMSIS Ethernet drivers (`Driver_ETH_MACx` + `Driver_ETH_PHYx`).

## Included In This Folder

- `NetworkInterface.c`: CMSIS-based FreeRTOS+TCP network interface template.
- `Driver/Include`: CMSIS driver API headers (`Driver_ETH_MAC.h`, `Driver_ETH_PHY.h`, etc.).
- `Driver/DriverTemplates`: upstream CMSIS driver template sources.
- `Driver/Examples`: reference MAC/PHY implementations.
- `Core/Include`: CMSIS-Core headers used by many example drivers (for example `cmsis_compiler.h`).

Bundled driver examples:

- Combined MAC+PHY examples (single source provides both driver types):
  - `Driver/Examples/Ethernet/KSZ8851SNL/ETH_KSZ8851SNL.c`
  - `Driver/Examples/Ethernet/LAN91C111/ETH_LAN91C111.c`
  - `Driver/Examples/Ethernet/LAN9220/ETH_LAN9220.c`
- MAC-only example:
  - `Driver/Examples/Ethernet_MAC/ETH_MAC_STM32.c`
- PHY-only examples:
  - `Driver/Examples/Ethernet_PHY/DP83848C/PHY_DP83848C.c`
  - `Driver/Examples/Ethernet_PHY/KSZ8061RNB/PHY_KSZ8061RNB.c`
  - `Driver/Examples/Ethernet_PHY/KSZ8081RNA/PHY_KSZ8081RNA.c`
  - `Driver/Examples/Ethernet_PHY/LAN8710A/PHY_LAN8710A.c`
  - `Driver/Examples/Ethernet_PHY/LAN8720/PHY_LAN8720.c`
  - `Driver/Examples/Ethernet_PHY/LAN8740A/PHY_LAN8740A.c`
  - `Driver/Examples/Ethernet_PHY/LAN8741A/PHY_LAN8741A.c`
  - `Driver/Examples/Ethernet_PHY/LAN8742A/PHY_LAN8742A.c`
  - `Driver/Examples/Ethernet_PHY/ST802RT1/PHY_ST802RT1.c`

## CMake Selection

Select this interface:

```cmake
set(FREERTOS_PLUS_TCP_NETWORK_IF "CMSIS" CACHE STRING "" FORCE)
```

The CMSIS CMake port accepts:

- `FREERTOS_PLUS_TCP_CMSIS_DRIVER_SOURCES`
- `FREERTOS_PLUS_TCP_CMSIS_DRIVER_INCLUDE_DIRS`

## Example: In-Repo STM32 Driver

```cmake
set(FREERTOS_PLUS_TCP_CMSIS_DRIVER_SOURCES
    "source/portable/NetworkInterface/CMSIS/Driver/Examples/Ethernet_MAC/ETH_MAC_STM32.c"
    "source/portable/NetworkInterface/CMSIS/Driver/Examples/Ethernet_PHY/LAN8742A/PHY_LAN8742A.c"
    CACHE STRING "" FORCE)

set(FREERTOS_PLUS_TCP_CMSIS_DRIVER_INCLUDE_DIRS
    "source/portable/NetworkInterface/CMSIS/Core/Include"
    "source/portable/NetworkInterface/CMSIS/Driver/Examples/Ethernet_MAC"
    "source/portable/NetworkInterface/CMSIS/Driver/Examples/Ethernet_PHY/LAN8742A"
    CACHE STRING "" FORCE)
```

Note: `ETH_MAC_STM32.c` requires STM32 HAL/CMSIS device and CubeMX/RTE configuration headers (`RTE_Components.h`, `CMSIS_device_header`, `MX_Device.h`, and related STM32 HAL headers). Add those include paths from your board SDK/project.

## Integration Notes

- The template defaults to `Driver_ETH_MAC0` and `Driver_ETH_PHY0`.
- Override driver instances with:
  - `cmsisETH_MAC_DRIVER_INSTANCE`
  - `cmsisETH_PHY_DRIVER_INSTANCE`
- This template is copy-based and expects:
  - `ipconfigZERO_COPY_TX_DRIVER == 0`
  - `ipconfigZERO_COPY_RX_DRIVER == 0`
- If using `BufferAllocation_1.c`, implement `vNetworkInterfaceAllocateRAMToBuffers()`.
