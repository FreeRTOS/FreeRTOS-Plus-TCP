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
    IPPacket_t * pxIPPacket;
    uint16_t usHeaderLength;

    /* The buffer must contain enough buffer size for ethernet header + IPv4 header and less than MTU size. */
    __CPROVER_assume( uxBufferLength >= ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + sizeof( ProtocolHeaders_t ) && uxBufferLength < ipconfigNETWORK_MTU );
    pucEthernetBuffer = safeMalloc( uxBufferLength );
    __CPROVER_assume( pucEthernetBuffer != NULL );

    /* This test case verifies IPv4 only. */
    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    __CPROVER_assume( pxIPPacket->xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE );

    /* Make sure the length of buffer is enough for protocol header.
     * CBMC checks union structure before accessing it, so we need to make sure the buffer size is enough for whole union structure. */
    usHeaderLength = pxIPPacket->xIPHeader.ucVersionHeaderLength & ( uint8_t ) 0x0FU;
    usHeaderLength = usHeaderLength << 2;
    __CPROVER_assume( uxBufferLength >= ipSIZE_OF_ETH_HEADER + usHeaderLength + sizeof( ProtocolHeaders_t ) );
    /* IPv4 header length is checked in prvProcessIPPacket. */
    __CPROVER_assume( ( usHeaderLength <= ( uxBufferLength - ipSIZE_OF_ETH_HEADER ) ) && ( usHeaderLength >= ipSIZE_OF_IPv4_HEADER ) );
    
    /* Set to valid input. */
    __CPROVER_assume( ( xOutgoingPacket == pdTRUE ) || ( xOutgoingPacket == pdFALSE ) );

    ( void ) usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );
}
