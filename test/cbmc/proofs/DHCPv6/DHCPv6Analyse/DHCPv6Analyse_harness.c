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


BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvDHCPv6Analyse( struct xNetworkEndPoint * pxEndPoint,
                                                                    const uint8_t * pucAnswer,
                                                                    size_t uxTotalLength,
                                                                    DHCPMessage_IPv6_t * pxDHCPMessage )
{
    return nondet_BaseType();
}



void harness()
{
    size_t uxTotalLength;
    BaseType_t xResult;

    NetworkEndPoint_t * pxNetworkEndPoint_Temp = safeMalloc( sizeof( NetworkEndPoint_t ) );

    __CPROVER_assume( pxNetworkEndPoint_Temp != NULL );

    DHCPMessage_IPv6_t * pxDHCPMessage = safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxDHCPMessage != NULL );

    uint8_t * pucAnswer = safeMalloc( sizeof( uint8_t ) );

    __CPROVER_assume( uxTotalLength > 0 );

    uint8_t * pucAnswer = safeMalloc( sizeof( uint8_t ) );

    xResult = __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvDHCPv6Analyse( pxNetworkEndPoint_Temp, pucAnswer, uxTotalLength, pxDHCPMessage );
}
