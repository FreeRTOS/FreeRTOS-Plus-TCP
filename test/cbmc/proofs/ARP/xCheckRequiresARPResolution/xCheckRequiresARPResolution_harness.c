/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_Routing.h"
/* CBMC includes. */
#include "cbmc.h"

/* Global variables. */
BaseType_t xIsIPv6;

/* Abstraction of xIsIPInARPCache. */
BaseType_t xIsIPInARPCache( uint32_t ulAddressToLookup )
{
    BaseType_t xReturn;

    __CPROVER_assume( ( xReturn == pdTRUE ) || ( xReturn == pdFALSE ) );

    return xReturn;
}

/* Function uxIPHeaderSizePacket is proven to be correct separately.*/
size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    size_t xReturn = ipSIZE_OF_IPv4_HEADER;

    __CPROVER_assert( __CPROVER_r_ok( pxNetworkBuffer, sizeof( NetworkBufferDescriptor_t ) ), "pxNetworkBuffer must be readable" );
    __CPROVER_assert( __CPROVER_r_ok( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength ), "pxNetworkBuffer;s buffer must be readable" );

    if( xIsIPv6 )
    {
        xReturn = ipSIZE_OF_IPv6_HEADER;
    }

    return xReturn;
}

/* Abstraction of FreeRTOS_OutputARPRequest_Multi. */
void FreeRTOS_OutputARPRequest_Multi( NetworkEndPoint_t * pxEndPoint,
                                      uint32_t ulIPAddress )
{
}

/* Abstraction of xIPv6_GetIPType. */
IPv6_Type_t xIPv6_GetIPType( const IPv6_Address_t * pxAddress )
{
    IPv6_Type_t eType;

    __CPROVER_assert( __CPROVER_r_ok( pxAddress, sizeof( IPv6_Address_t ) ), "pxAddress must be readable" );

    return eType;
}

/* Abstraction of eNDGetCacheEntry. */
eResolutionLookupResult_t eNDGetCacheEntry( IPv6_Address_t * pxIPAddress,
                                            MACAddress_t * const pxMACAddress,
                                            struct xNetworkEndPoint ** ppxEndPoint )
{
    eResolutionLookupResult_t xReturn;

    __CPROVER_assert( __CPROVER_r_ok( pxIPAddress, sizeof( IPv6_Address_t ) ), "pxIPAddress must be readable" );
    __CPROVER_assert( __CPROVER_w_ok( pxMACAddress, sizeof( MACAddress_t ) ), "pxMACAddress must be writeable" );

    return xReturn;
}

/* Abstraction of pxGetNetworkBufferWithDescriptor. */
NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) safeMalloc( sizeof( NetworkBufferDescriptor_t ) );

    return pxNetworkBuffer;
}

/* Abstraction of vNDSendNeighbourSolicitation. */
void vNDSendNeighbourSolicitation( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                   const IPv6_Address_t * pxIPAddress )
{
    __CPROVER_assert( __CPROVER_r_ok( pxNetworkBuffer, sizeof( NetworkBufferDescriptor_t ) ), "pxNetworkBuffer must be readable" );
    __CPROVER_assert( __CPROVER_r_ok( pxIPAddress, sizeof( IPv6_Address_t ) ), "pxIPAddress must be readable" );
}

void harness()
{
    size_t xBufferLength;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    IPPacket_t * pxIPPacket;
    IPHeader_t * pxIPHeader;

    /* Make sure buffer size is enough, xCheckRequiresARPResolution is only called for
     * IPv4 packets hence the minimum size should be  sizeof( IPPacket_t ) */
    __CPROVER_assume( ( xBufferLength >= sizeof( IPPacket_t ) ) && ( xBufferLength < ipconfigNETWORK_MTU ) );

    pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
    __CPROVER_assume( pxNetworkBuffer != NULL );

    pxNetworkBuffer->xDataLength = xBufferLength;

    pxNetworkBuffer->pucEthernetBuffer = safeMalloc( xBufferLength );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Its asserted in the code that xCheckRequiresARPResolution is only called on IPv4 frame types */

    /* See assertion: configASSERT( ( pxIPPacket->xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE ) || ( pxIPPacket->xEthernetHeader.usFrameType == ipARP_FRAME_TYPE ) );
     * in xCheckRequiresARPResolution() */
    pxIPPacket = ( ( const IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxIPHeader = &( pxIPPacket->xIPHeader );
    __CPROVER_assume( pxIPPacket->xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE );

    pxNetworkBuffer->pxEndPoint = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkBuffer->pxEndPoint != NULL );

    ( void ) xCheckRequiresARPResolution( pxNetworkBuffer );
}
