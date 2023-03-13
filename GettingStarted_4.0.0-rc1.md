Moving to 4.0.0-rc1 from 3.x.x:
-----------------------------
In version 4.0.0-rc1, new files have been added to support IPv6 functionality and each file has been broken down into logically seperated IPv4 and IPv6 files. The folder structure of FreeRTOS-Plus-TCP has not changed.

Some of the APIs have changed which is illustrated in the section below. However, there is a backward compatibility mode provided as well.

Backward Compatibility Mode:
---------------------------
   Set "ipconfigIPv4_BACKWARD_COMPATIBLE" value to 1 in “FreeRTOSIPConfigDefaults.h” to run the code in backward compatible mode.
   The "Existing API"s defined in all the API changes below work only when the backward compatibility mode is enabled.
  

API changes in 4.0.0-rc1:
----------------------
Change 1:

   - Existing API: FreeRTOS_IPInit
   - New API: FreeRTOS_IPInit_Multi
   - Change:
      - FreeRTOS_IPInit - Backward compatibility with the IPv4 FreeRTOS+TCP main branch which only supports single network interface. This can be used for single  interface IPv4 systems.
      - FreeRTOS_IPInit_Multi - It supports multiple interfaces. Before calling this function, at least 1 interface and 1 end-point must have been set-up. FreeRTOS_IPInit_Multi() replaces the earlier FreeRTOS_IPInit().

Change 2:

   - Existing API: FreeRTOS_GetAddressConfiguration/FreeRTOS_SetAddressConfiguration
   - New API: FreeRTOS_GetEndPointConfiguration/FreeRTOS_SetEndPointConfiguration
   - Change:
      - FreeRTOS_GetAddressConfiguration/FreeRTOS_SetAddressConfiguration - used to get/set the address configuration from the global variables initialised during FreeRTOS_IPInit
      - FreeRTOS_GetEndPointConfiguration/FreeRTOS_SetEndPointConfiguration will get/set the same address configuration from/to the end point.

Change 3:

   - Existing API:  void * FreeRTOS_GetUDPPayloadBuffer( size_t uxRequestedSizeBytes,
                                                TickType_t uxBlockTimeTicks)
   - New API: void * FreeRTOS_GetUDPPayloadBuffer_Multi( size_t uxRequestedSizeBytes,
                                                     TickType_t uxBlockTimeTicks, uint8_t ucIPType )
   - Change:
      - FreeRTOS_GetUDPPayloadBuffer - Backward compatibility with the IPv4 FreeRTOS+TCP V3.x.x. This can still be used for IPv4 use cases.
      - FreeRTOS_GetUDPPayloadBuffer_Multi-  A new argument (uint8_t ucIPType) to specify IP type to support both IPv4 and IPv6

Change 4:

   - Existing API: pxFillInterfaceDescriptor
   - New API: prefix_pxFillInterfaceDescriptor
      - where prefix = Network Interface Name
      - E.g pxWinPcap_FillInterfaceDescriptor
   - Change:
      - pxFillInterfaceDescriptor - It is there for downward compatibility. The function FreeRTOS_IPInit() will call it to initialise the interface and end-point objects
      - pxWinPcap_FillInterfaceDescriptor - New function with the same functionality.

Change 5:

   - Existing API: void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
   - New API: New argument “NetworkEndPoint_t * pxEndPoint” added
      - void vApplicationIPNetworkEventHook_Multi( eIPCallbackEvent_t eNetworkEvent, struct xNetworkEndPoint * pxEndPoint )
   - Change:
      - New argument “struct xNetworkInterface * pxNetworkInterface” added.
      - We are adding ipconfigIPv4_BACKWARD_COMPATIBLE flag to differentiate between old API and new API.
  
  **NOTE** : We are NOT considering the APIs changes in FreeRTOS_IP_Private.h for backward compatibility as those are not part of published interface.
  
Running Demos:
-------------
The demos can be found at: https://github.com/FreeRTOS/FreeRTOS/tree/devIPv6/FreeRTOS-Plus/Demo

In all the demos, there is a backward compatibility mode which can be enabled by setting the flag “ipconfigIPv4_BACKWARD_COMPATIBLE” to 1 in the header file “FreeRTOSIPConfigDefaults.h”.
This flag is by default set to zero.

New IPv6 WinSim Demo: https://github.com/FreeRTOS/FreeRTOS/tree/devIPv6/FreeRTOS-Plus/Demo/FreeRTOS_Plus_TCP_IPv6_Demo
