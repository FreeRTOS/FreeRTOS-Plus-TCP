#include "FreeRTOS_DHCP.h"

eDHCPCallbackAnswer_t xApplicationDHCPHook_Multi( eIPCallbackEvent_t eNetworkEvent,
                                                  struct xNetworkEndPoint * pxEndPoint,
                                                  IP_Address_t * pxIPAddress );
