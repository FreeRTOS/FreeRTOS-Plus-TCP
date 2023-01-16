/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* proof is done separately */
BaseType_t xProcessReceivedTCPPacket( NetworkBufferDescriptor_t * pxNetworkBuffer )
{
}

/* proof is done separately */
BaseType_t xProcessReceivedUDPPacket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                      uint16_t usPort )
{
}

/* This proof was done before. Hence we assume it to be correct here. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                            const uint32_t ulIPAddress )
{
}

eFrameProcessingResult_t publicProcessIPPacket( IPPacket_t * const pxIPPacket,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer );

#if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )

/* The checksum generation is stubbed out since the actual checksum
 * does not matter. The stub will return an indeterminate value each time. */
    uint16_t usGenerateChecksum( uint16_t usSum,
                                 const uint8_t * pucNextData,
                                 size_t uxByteCount )
    {
        uint16_t usReturn;

        __CPROVER_assert( pucNextData != NULL, "Next data cannot be NULL" );

        /* Return an indeterminate value. */
        return usReturn;
    }

/* The checksum generation is stubbed out since the actual checksum
 * does not matter. The stub will return an indeterminate value each time. */
    uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                         size_t uxBufferLength,
                                         BaseType_t xOutgoingPacket )
    {
        uint16_t usReturn;

        __CPROVER_assert( pucEthernetBuffer != NULL, "Ethernet buffer cannot be NULL" );

        /* Return an indeterminate value. */
        return usReturn;
    }
#endif /* if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 ) */

void harness()
{
    NetworkBufferDescriptor_t * const pxNetworkBuffer = malloc( sizeof( NetworkBufferDescriptor_t ) );

    __CPROVER_assume( pxNetworkBuffer != NULL );

    /* Pointer to the start of the Ethernet frame. It should be able to access the whole Ethernet frame.*/
    pxNetworkBuffer->pucEthernetBuffer = malloc( ipTOTAL_ETHERNET_FRAME_SIZE );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Minimum length of the pxNetworkBuffer->xDataLength is at least the size of the IPPacket_t. */
    __CPROVER_assume( pxNetworkBuffer->xDataLength >= sizeof( IPPacket_t ) && pxNetworkBuffer->xDataLength <= ipTOTAL_ETHERNET_FRAME_SIZE );

    IPPacket_t * const pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    publicProcessIPPacket( pxIPPacket, pxNetworkBuffer );
}
