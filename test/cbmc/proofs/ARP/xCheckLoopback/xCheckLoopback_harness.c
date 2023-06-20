/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ARP.h"

/* CBMC includes. */
#include "cbmc.h"

/* Abstraction of FreeRTOS_FindEndPointOnMAC. */
NetworkEndPoint_t * FreeRTOS_FindEndPointOnMAC( const MACAddress_t * pxMACAddress,
                                                const NetworkInterface_t * pxInterface )
{
    NetworkEndPoint_t * pxReturnEndPoint = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

    return pxReturnEndPoint;
}

/* Abstraction of pxDuplicateNetworkBufferWithDescriptor. */
NetworkBufferDescriptor_t * pxDuplicateNetworkBufferWithDescriptor( const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                    size_t uxNewLength )
{
    /* In this function, we can either return NULL or valid pointer as return value. */
    NetworkBufferDescriptor_t * pxReturnNetworkBuffer = ( NetworkBufferDescriptor_t * ) safeMalloc( sizeof( NetworkBufferDescriptor_t ) );

    if( pxReturnNetworkBuffer )
    {
        /* If the pointer is valid, we must have enough ethernet buffer for it with correct data length. */
        pxReturnNetworkBuffer->pucEthernetBuffer = safeMalloc( uxNewLength );
        __CPROVER_assume( pxReturnNetworkBuffer->pucEthernetBuffer != NULL );

        pxReturnNetworkBuffer->xDataLength = uxNewLength;
    }

    return pxReturnNetworkBuffer;
}

void harness()
{
    size_t xBufferLength;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    BaseType_t bReleaseAfterSend;

    __CPROVER_assume( ( xBufferLength >= 0 ) &&
                      ( xBufferLength < ipconfigNETWORK_MTU ) );

    pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) safeMalloc( sizeof( NetworkBufferDescriptor_t ) );

    if( pxNetworkBuffer )
    {
        /* If buffer pointer is valid, allocate ethernet buffer and set data length for it. */
        pxNetworkBuffer->xDataLength = xBufferLength;

        pxNetworkBuffer->pucEthernetBuffer = safeMalloc( xBufferLength );
        __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );
    }

    ( void ) xCheckLoopback( pxNetworkBuffer, bReleaseAfterSend );
}
