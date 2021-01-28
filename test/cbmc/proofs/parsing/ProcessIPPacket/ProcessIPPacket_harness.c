/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Routing.h"

/* Function Abstraction:
 * Function xProcessReceivedTCPPacket is proven to be memory safe separately. */
BaseType_t xProcessReceivedTCPPacket( NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    BaseType_t xReturn;

    __CPROVER_assert( pxNetworkBuffer != NULL, "The network Buffer cannot be NULL" );

    return xReturn;
}

/* Function Abstraction:
 * Function xProcessReceivedUDPPacket is proven to be memory safe separately. */
BaseType_t xProcessReceivedUDPPacket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                      uint16_t usPort )
{
    BaseType_t xReturn;

    __CPROVER_assert( pxNetworkBuffer != NULL, "The network Buffer cannot be NULL" );

    return xReturn;
}

/* Function Abstraction:
 * Function vARPRefreshCacheEntry is proven to be memory safe separately. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                            const uint32_t ulIPAddress )
{
}

/* Signature of function under test (prvProcessIPPacket). The function name is
 * mangled since we are using a CBMC flag (--export-file-local-symbols) to make
 * static functions available outside the file in which they are declared. This
 * process mangles the name. */
eFrameProcessingResult_t __CPROVER_file_local_FreeRTOS_IP_c_prvProcessIPPacket( IPPacket_t * const pxIPPacket,
                                                                                NetworkBufferDescriptor_t * const pxNetworkBuffer );


uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
    uint16_t usReturn;

    __CPROVER_assert( pucNextData != NULL, "pucNext data cannot be NULL" );

    /* Return an arbitrary value. */
    return usReturn;
}

void harness()
{
    NetworkBufferDescriptor_t * const pxNetworkBuffer = nondet_bool() ? NULL : malloc( sizeof( NetworkBufferDescriptor_t ) );

    __CPROVER_assume( pxNetworkBuffer != NULL );

    size_t xLocalDatalength;

    /* Minimum length of the pxNetworkBuffer->xDataLength is at least the size of the IPPacket_t. */
    __CPROVER_assume( ( xLocalDatalength >= sizeof( IPPacket_t ) ) &&
                      ( xLocalDatalength <= ipTOTAL_ETHERNET_FRAME_SIZE ) );

    pxNetworkBuffer->xDataLength = xLocalDatalength;

    /* Pointer to the start of the Ethernet frame. It should be able to access the whole Ethernet frame.*/
    pxNetworkBuffer->pucEthernetBuffer = nondet_bool() ? NULL : malloc( ipTOTAL_ETHERNET_FRAME_SIZE );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    IPPacket_t * const pxIPPacket = nondet_bool() ? NULL : malloc( xLocalDatalength ); /*sizeof( IPPacket_t ) ); */
    __CPROVER_assume( pxIPPacket != NULL );

    /* IP packet length is the length field * 4 */
    size_t ActualHeaderLength = ( pxIPPacket->xIPHeader.ucVersionHeaderLength & 0x0F ) << 2;

/*    pxNetworkBuffer->pucEthernetBuffer = pxIPPacket; */
    /* The total length must be at least equal to the sum of IP-header length and the enternet header.  */
    __CPROVER_assume( ActualHeaderLength + ipSIZE_OF_ETH_HEADER <= xLocalDatalength );

    /* Assume that the list of interfaces/endpoints is not initialized.
     * These are defined in the FreeRTOS_Routing.c file and used as a
     * list by the TCP stack. */
    __CPROVER_assume( pxNetworkInterfaces == NULL );
    __CPROVER_assume( pxNetworkEndPoints == NULL );

    __CPROVER_file_local_FreeRTOS_IP_c_prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );
}
