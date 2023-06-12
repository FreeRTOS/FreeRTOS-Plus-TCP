/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* CBMC includes. */
#include "cbmc.h"

/* Function usGenerateChecksum is proven to be correct separately.
 * Check if input buffer is readable. */
uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
    __CPROVER_assert( __CPROVER_r_ok( pucNextData, uxByteCount ), "pucNextData should be readable." );
}

void harness()
{
    size_t uxBufferLength;
    uint8_t * pucEthernetBuffer;
    BaseType_t xOutgoingPacket;
    EthernetHeader_t * pxEthernetHeader;
    IPPacket_IPv6_t * pxIPPacket;
    uint16_t usHeaderLength;

    /* The buffer must contain enough buffer size for ethernet header + IPv6 header and less than MTU size. */
    __CPROVER_assume( uxBufferLength >= ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ProtocolHeaders_t ) && uxBufferLength < ipconfigNETWORK_MTU );
    pucEthernetBuffer = safeMalloc( uxBufferLength );
    __CPROVER_assume( pucEthernetBuffer != NULL );

    /* This test case verifies IPv6 only. */
    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;
    __CPROVER_assume( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE );
    
    /* Set to valid input. */
    __CPROVER_assume( ( xOutgoingPacket == pdTRUE ) || ( xOutgoingPacket == pdFALSE ) );

    ( void ) usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );
}
