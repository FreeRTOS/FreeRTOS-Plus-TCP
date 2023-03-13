What’s New:
----------

   1. Unified code for IPv4 and IPv6
   2. Multiple Interface/Endpoint support
      (Reference: https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/freertostcp-multiple-interfaces.html)
   3. Neighbor Discovery & Router Advertisement
   4. New WinSim demo to support both IPv4 and IPv6

FreeRTOS-Plus-TCP 4.0.0-rc1 complies with the following code quality criteria:

   1. 100% Unit test cases Passed for IPv4
   2. IPv4 Protocol Testing with Maxwell Pro
   3. All functions comply with the MISRA 2012 coding standard.
   4. All functions passing Coverity static checking.
   5. CBMC IPv4 memory safety proofs
   6. GNU Complexity score same as of main branch ( less than 8 *with exceptions)

Moving to 4.0.0-rc1 from 3.0.0:
-----------------------------
In version 4.0.0-rc1, new files have been added to support IPv6 functionality and each file has been broken down into logically seperated IPv4 and IPv6 files. The folder structure of FreeRTOS-Plus-TCP has not changed.

Some of the APIs have changed which is illustrated in the section below. However, there is a backward compatibility mode provided as well.

Running Demos:
-------------

The demo branch compatible with this branch:
https://github.com/FreeRTOS/FreeRTOS/tree/devIPv6

In all the demos, there is a backward compatibility mode which can be enabled by setting the flag “ipconfigIPv4_BACKWARD_COMPATIBLE” to 1 in the header file “FreeRTOSIPConfigDefaults.h”.


This flag is by default set to zero.

New API's in 4.0.0-rc1:
----------------------
Change 1:

   1. Old API: FreeRTOS_IPInit
   2. New API: FreeRTOS_IPInit_Multi
   3. Backward Compatibility - Yes
   4. Change:
      1. FreeRTOS_IPInit - Backward compatibility with the IPv4 FreeRTOS+TCP main branch which only supports single network interface. This can be used for single  interface IPv4 systems.
      2. FreeRTOS_IPInit_Multi - It supports multiple interfaces. Before calling this function, at least 1 interface and 1 end-point must have been set-up. FreeRTOS_IPInit_Multi() replaces the earlier FreeRTOS_IPInit().

Change 2:

   1. Old API: FreeRTOS_GetAddressConfiguration/FreeRTOS_SetAddressConfiguration
   2. New API: FreeRTOS_GetEndPointConfiguration/FreeRTOS_SetEndPointConfiguration
   3. Backward Compatibility - Yes
   4. Change:
      1. FreeRTOS_GetAddressConfiguration/FreeRTOS_SetAddressConfiguration - used to get/set the address configuration from the global variables initialised during FreeRTOS_IPInit
      2. FreeRTOS_GetEndPointConfiguration/FreeRTOS_SetEndPointConfiguration will get/set the same address configuration from/to the end point.

Change 3:

   1. Old API:  void * FreeRTOS_GetUDPPayloadBuffer( size_t uxRequestedSizeBytes,
                                                TickType_t uxBlockTimeTicks)
   2. New API: void * FreeRTOS_GetUDPPayloadBuffer_Multi( size_t uxRequestedSizeBytes,
                                                     TickType_t uxBlockTimeTicks, uint8_t ucIPType )
   3. Backward Compatibility - Yes
   4. Change:
    1. FreeRTOS_GetUDPPayloadBuffer - Backward compatibility with the IPv4 FreeRTOS+TCP main branch. Can still be used for IPv4 use cases.
    2. FreeRTOS_GetUDPPayloadBuffer_Multi-  A new argument (uint8_t ucIPType) to specify IP type to support both IPv4 and IPv6

Change 4:

   1. Old API: pxFillInterfaceDescriptor
   2. New API: prefix_pxFillInterfaceDescriptor
    1. where prefix = Network Interface Name
    2. E.g pxWinPcap_FillInterfaceDescriptor
   3. Backward Compatibility - Yes
   4. Change:
    1. pxFillInterfaceDescriptor - It is there for downward compatibility. The function FreeRTOS_IPInit() will call it to initialise the interface and end-point objects
    2. pxWinPcap_FillInterfaceDescriptor - New function with the same functionality.

Change 5:

   1. Old API: void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
   2. New API: New argument “NetworkEndPoint_t * pxEndPoint” added
     1. void vApplicationIPNetworkEventHook_Multi( eIPCallbackEvent_t eNetworkEvent, struct xNetworkEndPoint * pxEndPoint )
   3. Backward Compatibility - Yes
   4. Change:
     1. New argument “struct xNetworkInterface * pxNetworkInterface” added.
     2. We are adding ipconfigIPv4_BACKWARD_COMPATIBLE flag to differentiate between old API and new API.

NOTE : We are NOT considering the APIs changes in FreeRTOS_IP_Private.h for backward compatibility as those are not part of published interface.

Change 6:

   New Flag for backward compatibility - ipconfigIPv4_BACKWARD_COMPATIBLE defined in  the header file “FreeRTOSIPConfigDefaults.h”
   1. ipconfigIPv4_BACKWARD_COMPATIBLE = 0
    This flag is by default set to zero, which means it supports multiple end point implementation of both IPv4 and IPv6.
   2. ipconfigIPv4_BACKWARD_COMPATIBLE = 1
    End users can move to the older single interface and endpoint model by setting this flag to 1

Code Snippet:
------------
    #if ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
    {
       vApplicationIPNetworkEventHook_Multi( eNetworkUp, pxEndPoint );
    }
    #else
    {
       vApplicationIPNetworkEventHook( eNetworkUp );
    }
    #endif
