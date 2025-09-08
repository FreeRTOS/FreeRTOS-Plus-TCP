/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_IPv6_Utils.h"

/* CBMC includes. */
#include "cbmc.h"

void harness()
{
    size_t uxBufferSize;
    uint8_t * pucEthernetBuffer;
    struct xPacketSummary xSet;
    BaseType_t xReturn;

    /* We must have ethernet header to get frame type. */
    __CPROVER_assume( uxBufferSize >= sizeof( IPPacket_IPv6_t ) && uxBufferSize <= ipconfigNETWORK_MTU );

    /* Ethernet buffer is not possible to be NULL. */
    pucEthernetBuffer = ( uint8_t * ) safeMalloc( uxBufferSize );
    __CPROVER_assume( pucEthernetBuffer != NULL );
    __CPROVER_havoc_object( pucEthernetBuffer );

    /* This is set before calling prvChecksumIPv6Checks. */
    xSet.pxIPPacket = ( const IPPacket_t * ) pucEthernetBuffer;
    xSet.pxIPPacket_IPv6 = ( const IPHeader_IPv6_t * ) ( pucEthernetBuffer + ipSIZE_OF_ETH_HEADER );

    xReturn = prvChecksumIPv6Checks( pucEthernetBuffer,
                                     uxBufferSize,
                                     &xSet );

    if( xReturn == 0 )
    {
        __CPROVER_assert( ( xSet.usProtocolBytes <= FreeRTOS_ntohs( xSet.pxIPPacket_IPv6->usPayloadLength ) ), "xSet.usProtocolBytes shouldn't be greater than IPv6 usPayloadLength" );
    }
}
