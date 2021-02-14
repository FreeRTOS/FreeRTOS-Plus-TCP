# Scope
This is a driver and network middleware for the MSP432E401Y microcontroller
with built-in Ethernet MAC.

# Prerequisites

Ensure that driverlib for the MSP432E4 is installed and added to the include
path for the project.

# Recommendation
When a MAC address changes or when there is a change in the network setup,
it is recommended to perform a hard reset of the microcontroller in lieu
of resetting only the MAC hardware.

# Example Code

```
#include "NetworkInterface.h"
#include "NetworkMiddleware.h"

void setup_wired_ethernet()
{
    struct InternalNetworkInterfaceMSP432EConfig config;
    vGetInternalNetworkInterfaceMSP432EConfigDefaults(&config);
    config.setMACAddrInternal = false;  /* true if the MAC address is to be read from microcontroller flash */
    config.MACAddr[0] = 0x70;           /* replace with a custom MAC address */
    config.MACAddr[1] = 0xFF;
    config.MACAddr[2] = 0x76;
    config.MACAddr[3] = 0x1C;
    config.MACAddr[4] = 0xC1;
    config.MACAddr[5] = 0xD0;
    vPublicSetupEMACNetwork(config);

    // setup the network stack middleware
    const char *devname = "device";
    struct InternalNetworkMiddlewareData setupData;
    strncpy(setupData.deviceName, devname, strlen(devname));
    setupData.resetNetworkTaskEveryXSeconds = 86400;           /* Restart the network every 24 hours (86400 seconds) only when  setupData.resetNetworkTaskRunning == true */
    setupData.resetNetworkTaskRunning = false;                /* Run the network task to reset the network every so often (i.e. to periodically obtain a new IP address) */

    // set the static IP address
    convertOctetsToAddr(setupData.ucIPAddress, 192, 168, 1, 9);
    convertOctetsToAddr(setupData.ucNetMask, 255, 255, 255, 0);
    convertOctetsToAddr(setupData.ucGatewayAddress, 192, 168, 1, 1);
    convertOctetsToAddr(setupData.ucDNSServerAddress, 192, 168, 1, 1);

    vPublicSetupFreeRTOSTasks(setupData);
    /*
       Start the RTOS scheduler by calling vTaskStartScheduler()
       Use publicPreventNetworkReset() to block the network reset during a critical section of the code
       Set the device name using vPublicSetupDeviceName() */
}

```
# Contact
Nicholas J. Kinar (n.kinar@usask.ca) or FreeRTOS Forums
