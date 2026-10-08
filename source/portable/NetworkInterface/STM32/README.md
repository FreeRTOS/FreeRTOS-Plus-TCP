# STM32 network interface

This directory contains the unified FreeRTOS+TCP Ethernet network interface
for STM32F1, STM32F2, STM32F4, STM32F7, STM32H5, STM32H7, STM32H7RS, and
STM32N6 devices.

The network interface contains the portable Ethernet logic. The application
must still provide board-specific clock, GPIO, interrupt, linker, and memory
configuration.

## Configuration

Enable the Ethernet HAL module. The network interface also requires zero-copy
receive and transmit buffers:

```c
#define HAL_ETH_MODULE_ENABLED

#define ipconfigZERO_COPY_RX_DRIVER  1
#define ipconfigZERO_COPY_TX_DRIVER  1
```

The following options are recommended so the hardware can perform filtering,
checksum offload, and batched receive-event delivery:

```c
#define ipconfigUSE_LINKED_RX_MESSAGES              1
#define ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES  1
#define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM       1
#define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM       1
```

The driver uses file-static HAL, PHY, task, semaphore, and address-filter
state. Consequently, one Ethernet peripheral instance is supported.

On STM32N6, initialization checks the configured DMA channel and MTL queue
counts against the hardware capabilities reported by the HAL. Initialization
fails before starting DMA if a configured count exceeds the available
capacity. Descriptor arrays retain their compile-time sizes.

### Media and PHY

The unified driver keeps the legacy STM32 network-interface configuration
names. All options accept `ipconfigENABLE` or `ipconfigDISABLE`.

| Option | Default | Purpose |
| --- | --- | --- |
| `ipconfigUSE_RMII` | Enabled unless RGMII is selected | Select RMII instead of MII. |
| `ipconfigUSE_RGMII` | Disabled | Select the STM32N6 RGMII interface and permit 1000BASE-T negotiation. |
| `ipconfigETHERNET_AN_ENABLE` | Enabled | Enable PHY auto-negotiation. |
| `ipconfigETHERNET_AUTO_CROSS_ENABLE` | Enabled with auto-negotiation | Enable automatic MDI/MDI-X selection. |
| `ipconfigETHERNET_CROSSED_LINK` | Enabled when automatic MDI/MDI-X is disabled | Select a crossed connection when automatic MDI/MDI-X is disabled. |
| `ipconfigETHERNET_USE_100MB` | Enabled in fixed mode | Select 100 Mbit/s instead of 10 Mbit/s when auto-negotiation is disabled. |
| `ipconfigETHERNET_USE_FULL_DUPLEX` | Enabled in fixed mode | Select full duplex instead of half duplex when auto-negotiation is disabled. |

When both media options are disabled, the driver selects MII. RGMII is
available only with the STM32N6 HAL and currently supports the RTL8211 PHY.
The generic PHY layer continues to limit all other configurations to 100
Mbit/s, including STM32N6 RMII configurations.

The RTL8211 advertises 1000BASE-T full duplex as well as 10/100 Mbit/s
fallback modes when RGMII and auto-negotiation are enabled. Fixed 1000BASE-T
operation is intentionally unsupported because copper gigabit Ethernet uses
auto-negotiation for master/slave resolution. If auto-negotiation is disabled,
the existing 10/100 Mbit/s fixed-speed options continue to apply.

The selected media mode must match the clocks and GPIOs configured by
`HAL_ETH_MspInit()`. An RGMII board must also provide the PHY reset and strap
configuration, 125 MHz clocking, and the required transmit/receive clock
delays. Configure RTL8211 internal delays or Energy-Efficient Ethernet policy
in board code when they are not established by hardware straps.

### Task and timeouts

The following values may be defined before this source file is compiled:

| Option | Default |
| --- | --- |
| `niEMAC_HANDLER_TASK_NAME` | `"EMAC_STM32"` |
| `niEMAC_HANDLER_TASK_PRIORITY` | `configMAX_PRIORITIES - 1` |
| `niEMAC_HANDLER_TASK_STACK_SIZE` | `4 * configMINIMAL_STACK_SIZE` |
| `niEMAC_TASK_MAX_BLOCK_TIME_MS` | 100 ms |
| `niEMAC_TX_MAX_BLOCK_TIME_MS` | 20 ms |
| `niEMAC_RX_MAX_BLOCK_TIME_MS` | 20 ms |
| `niDESCRIPTOR_WAIT_TIME_MS` | 20 ms |

For compatibility with the legacy F-series driver,
`configEMAC_TASK_STACK_SIZE` is used when
`niEMAC_HANDLER_TASK_STACK_SIZE` is not defined. For compatibility with the
legacy H-series driver, `ipconfigEMAC_TASK_HOOK()` is called at task startup
when `iptraceEMAC_TASK_STARTING()` is not defined.

### Trace hooks

The optional hooks below default to no-ops:

```c
#define iptraceSTM32_ETH_RX_DESC_USAGE( ulChannel, uxDescriptorsUsed )
#define iptraceSTM32_ETH_TX_DESC_USAGE( ulChannel, uxDescriptorsUsed )
#define iptraceSTM32_ETH_FATAL_ERROR( ulHalErrorCode, ulDmaErrorCode, ulMacErrorCode )
```

The descriptor-usage hooks run from the Ethernet completion callbacks and
must be interrupt-safe and non-blocking. They can be used to maintain
application-visible descriptor high-water marks. The fatal-error hook runs
once in the EMAC task before each recovery episode, so production firmware can
persist the HAL, DMA, and MAC error codes without depending on debug printing.

## HAL Ethernet initialization

Provide `HAL_ETH_MspInit()` and, when deinitialization is required,
`HAL_ETH_MspDeInit()` in the application. A CubeMX-generated implementation is
the best starting point because the exact clocks, alternate functions, pinout,
and interrupt name depend on the STM32 family, part, package, and board.

The initialization must:

1. Enable all Ethernet MAC, transmit, receive, and peripheral clocks required
   by the selected family.
2. Enable the GPIO port clocks and configure every MII or RMII signal used by
   the board.
3. Configure and enable the Ethernet interrupt at a priority from which
   FreeRTOS APIs may be called. Use the priority-number representation expected
   by the STM32 HAL/CMSIS call rather than a pre-shifted register value.

The deinitialization should disable the interrupt, release the GPIOs, and
disable the clocks enabled during initialization.

The generic structure is:

```c
void HAL_ETH_MspInit( ETH_HandleTypeDef * pxEthHandle )
{
    if( pxEthHandle->Instance == ETH_INSTANCE_FOR_THIS_DEVICE )
    {
        /* Enable the family-specific Ethernet and GPIO clocks. */
        /* Configure the board-specific MII or RMII pins. */
        /* Configure and enable the Ethernet interrupt. */
    }
}

void HAL_ETH_MspDeInit( ETH_HandleTypeDef * pxEthHandle )
{
    if( pxEthHandle->Instance == ETH_INSTANCE_FOR_THIS_DEVICE )
    {
        /* Disable the Ethernet interrupt. */
        /* Deinitialize the board-specific Ethernet pins. */
        /* Disable the clocks enabled by HAL_ETH_MspInit(). */
    }
}
```

Replace `ETH_INSTANCE_FOR_THIS_DEVICE` with the instance exposed by the device
HAL, such as `ETH` or `ETH1`.

## DMA memory and cache coherency

Place the following sections in DMA-accessible memory:

- `.TxDescripSection`
- `.RxDescripSection`
- `.EthBuffersSection`

The names may be overridden with `niEMAC_TX_DESC_SECTION`,
`niEMAC_RX_DESC_SECTION`, and `niEMAC_BUFFERS_SECTION`, respectively. The
linker script must use the same names.

The descriptor sections must be non-cacheable. Packet buffers may also be
non-cacheable, or the application may define `niEMAC_USE_MPU` as
`ipconfigDISABLE` so that the network interface performs explicit data-cache
maintenance.

If an MPU is used, configure its regions in application startup code using the
actual linker-provided section boundaries and sizes. Do not copy fixed region
sizes from another STM32 part or linker layout.

## Compile coverage

CI cross-compiles this network interface and every bundled Ethernet HAL source
for all eight supported families with warnings treated as errors. The pinned
CMSIS Core, CMSIS Device, and supporting HAL revisions are recorded in
`.github/workflows/ci.yml`; the reusable compile command is
`test/network-interface/stm32/compile.sh`.
