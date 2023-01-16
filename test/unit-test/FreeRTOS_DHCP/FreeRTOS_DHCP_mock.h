#include "FreeRTOS_DHCP.h"

eDHCPCallbackAnswer_t xApplicationDHCPHook( eDHCPCallbackPhase_t eDHCPPhase,
                                            uint32_t ulIPAddress );

/* Return true if a given end-point is up and running.
* When FreeRTOS_IsNetworkUp() is called with NULL as a parameter,
* it will return pdTRUE when all end-points are up. */
BaseType_t FreeRTOS_IsEndPointUp( const struct xNetworkEndPoint * pxEndPoint );
