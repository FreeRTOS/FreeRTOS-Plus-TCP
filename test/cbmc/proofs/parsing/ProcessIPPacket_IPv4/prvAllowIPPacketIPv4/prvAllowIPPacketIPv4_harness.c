/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IPv4.h"
#include "FreeRTOS_IP_Private.h"

/* CBMC includes. */
#include "cbmc.h"

/* prvAllowIPPacketIPv4() is a file-local (static) function, exported for
 * verification via --export-file-local-symbols. */
eFrameProcessingResult_t prvAllowIPPacketIPv4( const IPPacket_t * const pxIPPacket,
                                               const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                               UBaseType_t uxHeaderLength );

/* Return either pdTRUE or pdFALSE (nondeterministic) for endpoint state. */
BaseType_t FreeRTOS_IsEndPointUp( const struct xNetworkEndPoint * pxEndPoint )
{
    BaseType_t xReturn;

    return xReturn;
}

/* The IP-header checksum generation is stubbed out; the actual checksum
 * value does not matter. Returns an indeterminate value each time. */
uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
    uint16_t usReturn;

    __CPROVER_assert( pucNextData != NULL, "Checksum input buffer cannot be NULL" );

    return usReturn;
}

/* The protocol checksum generation is stubbed out. Returns an indeterminate
 * value each time. */
uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    uint16_t usReturn;

    __CPROVER_assert( pucEthernetBuffer != NULL, "Ethernet buffer cannot be NULL" );

    return usReturn;
}

void harness()
{
    NetworkBufferDescriptor_t * const pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
    uint8_t * pucEthernetBuffer = ( uint8_t * ) safeMalloc( ipTOTAL_ETHERNET_FRAME_SIZE + ipIP_TYPE_OFFSET );

    /* Network buffer must be valid, it's checked in prvProcessEthernetPacket. */
    __CPROVER_assume( pxNetworkBuffer != NULL );

    /* Ethernet buffer in network buffer must be valid, the data length is
     * checked in prvProcessEthernetPacket. */
    __CPROVER_assume( pucEthernetBuffer != NULL );

    /* Points to ethernet buffer offset by ipIP_TYPE_OFFSET, so the buffer
     * allocation matches pxGetNetworkBufferWithDescriptor. */
    pxNetworkBuffer->pucEthernetBuffer = &( pucEthernetBuffer[ ipIP_TYPE_OFFSET ] );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Minimum length of pxNetworkBuffer->xDataLength is at least the size of
     * an IPPacket_t. Contents are left fully nondeterministic. */
    __CPROVER_assume( ( pxNetworkBuffer->xDataLength >= sizeof( IPPacket_t ) ) &&
                      ( pxNetworkBuffer->xDataLength <= ipTOTAL_ETHERNET_FRAME_SIZE ) );

    pxNetworkEndPoints = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );
    pxNetworkEndPoints->pxNext = NULL;

    /* The packet is assigned to an endpoint during pxEasyFit(); model that. */
    pxNetworkBuffer->pxEndPoint = pxNetworkEndPoints;

    IPPacket_t * const pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
}
