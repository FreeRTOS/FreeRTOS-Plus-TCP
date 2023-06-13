/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"

/* CBMC includes. */
#include "cbmc.h"



/* Static members defined in FreeRTOS_DHCP.c */
extern Socket_t xDHCPv6Socket;
void prvCreateDHCPv6Socket( NetworkEndPoint_t * pxEndPoint );
void prvSendDHCPMessage( NetworkEndPoint_t * pxEndPoint );

BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPv6ProcessEndPoint_HandleState( NetworkEndPoint_t * pxEndPoint,
                                                                                      DHCPMessage_IPv6_t * pxDHCPMessage )
{
    __CPROVER_assume( pxEndPoint != NULL );
    __CPROVER_assume( pxDHCPMessage != NULL );

    if( pxEndPoint->xDHCPData.eDHCPState == eLeasedAddress || pxEndPoint->xDHCPData.eDHCPState == eInitialWait )
    {
        prvCreateDHCPv6Socket( pxEndPoint );
    }
    return nondet_BaseType();
}

BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPv6ProcessEndPoint_HandleAdvertise( NetworkEndPoint_t * pxEndPoint,
                                                                                      DHCPMessage_IPv6_t * pxDHCPMessage )
{
    __CPROVER_assume( pxEndPoint != NULL );
    __CPROVER_assume( pxDHCPMessage != NULL );

    return nondet_BaseType();
}

void __CPROVER_file_local_FreeRTOS_DHCPv6_c_vDHCPv6ProcessEndPoint_HandleReply( NetworkEndPoint_t * pxEndPoint,
                                                                                      DHCPMessage_IPv6_t * pxDHCPMessage )
{
    __CPROVER_assume( pxEndPoint != NULL );
    __CPROVER_assume( pxDHCPMessage != NULL );
}

void __CPROVER_file_local_FreeRTOS_DHCPv6_c_vDHCPv6ProcessEndPoint( BaseType_t xReset,
                                                                    NetworkEndPoint_t * pxEndPoint,
                                                                    DHCPMessage_IPv6_t * pxDHCPMessage );

void harness()
{
    BaseType_t xReset, xGivingUp;

    NetworkEndPoint_t * pxNetworkEndPoint_Temp = safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoint_Temp != NULL );

    DHCPMessage_IPv6_t * pxDHCPMessage = safeMalloc( sizeof( DHCPMessage_IPv6_t ) );
    __CPROVER_assume( pxDHCPMessage != NULL );

    xDHCPv6Socket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

    __CPROVER_file_local_FreeRTOS_DHCPv6_c_vDHCPv6ProcessEndPoint( xReset, pxNetworkEndPoint_Temp, pxDHCPMessage );
}
