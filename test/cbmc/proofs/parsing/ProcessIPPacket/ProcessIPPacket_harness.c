/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Routing.h"

/* Function Abstraction:
 * memmove standard library function is abstracted away to speed up proof
 * execution. */
void * memmove( void * str1,
                const void * str2,
                size_t len )
{
    __CPROVER_assert( str1 != NULL, "First string cannot be NULL" );
    __CPROVER_assert( str2 != NULL, "Second string cannot be NULL" );

    __CPROVER_w_ok( str1, len );
    __CPROVER_r_ok( str2, len );

    __CPROVER_havoc_object( str1 );
    return str1;
}

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
    /* The MAC address can be NULL or non-NULL. */
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
    uint8_t ucVersionHeaderLength;

    /* Minimum length of the pxNetworkBuffer->xDataLength is at least the size of the IPPacket_t.
     * But since we are casting the headers to ProtocolHeaders_t, we need to add the size of that
     * data structure as well which is a union. Additionally, there will be space required for the
     * IP header options. */
    __CPROVER_assume( ( xLocalDatalength > sizeof( IPPacket_t ) + sizeof( ProtocolHeaders_t ) + ( ( ucVersionHeaderLength & 0x0F ) << 2 ) ) &&
                      ( xLocalDatalength <= ipTOTAL_ETHERNET_FRAME_SIZE ) );


    pxNetworkBuffer->xDataLength = xLocalDatalength;

    /* We need to allocate endpoint since the local netmask will be used. */
    pxNetworkBuffer->pxEndPoint = malloc( sizeof( struct xNetworkEndPoint ) );

    /* Pointer to the start of the Ethernet frame. It should be able to access the whole Ethernet frame.*/
    pxNetworkBuffer->pucEthernetBuffer = nondet_bool() ? NULL : malloc( xLocalDatalength );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Only IPv4 frames are supported. */
    __CPROVER_assume( ( ( EthernetHeader_t * ) ( pxNetworkBuffer->pucEthernetBuffer ) )->usFrameType == ipIPv4_FRAME_TYPE );

    /* Put the header length used to malloc the ethernet buffer. */
    ( ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer ) )->xIPHeader.ucVersionHeaderLength = ucVersionHeaderLength;

    /* Assume that the list of interfaces/endpoints is not initialized.
     * These are defined in the FreeRTOS_Routing.c file and used as a
     * list by the TCP stack. */
    __CPROVER_assume( pxNetworkInterfaces == NULL );
    __CPROVER_assume( pxNetworkEndPoints == NULL );

    __CPROVER_file_local_FreeRTOS_IP_c_prvProcessIPPacket( ( ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer ) ), pxNetworkBuffer );
}
