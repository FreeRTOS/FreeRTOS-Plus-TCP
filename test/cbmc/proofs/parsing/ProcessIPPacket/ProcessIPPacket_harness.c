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

//    __CPROVER_assert( pxNetworkBuffer != NULL, "The network Buffer cannot be NULL" );

    return xReturn;
}

/* Function Abstraction:
 * Function xProcessReceivedUDPPacket is proven to be memory safe separately. */
BaseType_t xProcessReceivedUDPPacket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                      uint16_t usPort )
{
    BaseType_t xReturn;

  //  __CPROVER_assert( pxNetworkBuffer != NULL, "The network Buffer cannot be NULL" );

    return xReturn;
}

/* Function Abstraction:
 * Function vARPRefreshCacheEntry is proven to be memory safe separately. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                            const uint32_t ulIPAddress )
{
    /* The MAC address can be NULL or non-NULL. */
}

/* Function Abstraction:
 * Function vARPRefreshCacheEntry is proven to be memory safe separately. */
eFrameProcessingResult_t __CPROVER_file_local_FreeRTOS_IP_c_prvProcessICMPPacket( ICMPPacket_t * const pxICMPPacket )
{
    eFrameProcessingResult_t eReturn;
//    __CPROVER_assert( pxICMPPacket != NULL, "ICMP packet sent cannot be NULL" );

    return eReturn;
}


uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    uint16_t usReturn;
    return usReturn;
}

eFrameProcessingResult_t __CPROVER_file_local_FreeRTOS_IP_c_prvAllowIPPacketIPv4( const IPPacket_t * const pxIPPacket,
                                                      const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                      UBaseType_t uxHeaderLength )
{
    eFrameProcessingResult_t eReturn;
    //__CPROVER_assert( pxIPPacket != NULL, "IP packet sent cannot be NULL" );

    return eReturn;
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

    //__CPROVER_assert( pucNextData != NULL, "pucNext data cannot be NULL" );

    /* Return an arbitrary value. */
    return usReturn;
}

void harness()
{
    NetworkBufferDescriptor_t * const pxNetworkBuffer = nondet_bool() ? NULL : malloc( sizeof( NetworkBufferDescriptor_t ) );
    __CPROVER_assume( pxNetworkBuffer != NULL );

    size_t xLocalDatalength;

    /* Minimum length of the pxNetworkBuffer->xDataLength is at least the size of the IPPacket_t. */
    __CPROVER_assume( ( xLocalDatalength >= sizeof( IPPacket_t ) + sizeof(ProtocolHeaders_t) ) &&
                      ( xLocalDatalength <= ipTOTAL_ETHERNET_FRAME_SIZE ) );

    pxNetworkBuffer->xDataLength = xLocalDatalength;

    /* Pointer to the start of the Ethernet frame. It should be able to access the whole Ethernet frame.*/
    //pxNetworkBuffer->pucEthernetBuffer = nondet_bool() ? NULL : malloc( xLocalDatalength );
    pxNetworkBuffer->pucEthernetBuffer = malloc( xLocalDatalength );

    //malloc( sizeof( IPPacket_t ) );//malloc(xLocalDatalength);//malloc( ipTOTAL_ETHERNET_FRAME_SIZE );
    //__CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Only IPv4 frames are supported. */
    __CPROVER_assume( ( ( EthernetHeader_t *) ( pxNetworkBuffer->pucEthernetBuffer ) )->usFrameType == ipIPv4_FRAME_TYPE );

    /* Assume that the list of interfaces/endpoints is not initialized.
     * These are defined in the FreeRTOS_Routing.c file and used as a
     * list by the TCP stack. */
    __CPROVER_assume( pxNetworkInterfaces == NULL );
    __CPROVER_assume( pxNetworkEndPoints == NULL );

    __CPROVER_file_local_FreeRTOS_IP_c_prvProcessIPPacket( ( ( IPPacket_t *) ( pxNetworkBuffer->pucEthernetBuffer ) ), pxNetworkBuffer );
}
