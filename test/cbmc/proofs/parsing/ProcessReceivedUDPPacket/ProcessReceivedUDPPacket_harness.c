/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_TCP_IP.h"

/* CBMC includes. */
#include "cbmc.h"

/*This proof assumes that pxUDPSocketLookup is implemented correctly. */

/* This proof was done before. Hence we assume it to be correct here. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                            const uint32_t ulIPAddress )
{
}

void vARPRefreshCacheEntryAge( const MACAddress_t * pxMACAddress,
                               const uint32_t ulIPAddress )
{
    __CPROVER_assert( pxMACAddress != NULL, "pxMACAddress cannot be NULL" );
}

/* This proof was done before. Hence we assume it to be correct here. */
BaseType_t xIsDHCPSocket( Socket_t xSocket )
{
}

/* This proof was done before. Hence we assume it to be correct here. */
uint32_t ulDNSHandlePacket( NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    /* ulDNSHandlePacket always returns pdFAIL. */
    return pdFAIL;
}

/* This proof was done before. Hence we assume it to be correct here. */
uint32_t ulNBNSHandlePacket( NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    /* ulNBNSHandlePacket always returns pdFAIL. */
    return pdFAIL;
}

/* This proof was done before. Hence we assume it to be correct here. */
BaseType_t xCheckRequiresARPResolution( NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    BaseType_t xReturn;

    __CPROVER_assume( ( xReturn == pdTRUE ) || ( xReturn == pdFALSE ) );

    return xReturn;
}

/* Abstraction of xSendDHCPEvent */
BaseType_t xSendDHCPEvent( struct xNetworkEndPoint * pxEndPoint )
{
    BaseType_t xReturn;

    __CPROVER_assume( ( xReturn == pdTRUE ) || ( xReturn == pdFALSE ) );

    return xReturn;
}

/* This proof was done before. Hence we assume it to be correct here. */
BaseType_t xProcessReceivedUDPPacket_IPv6( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                           uint16_t usPort,
                                           BaseType_t * pxIsWaitingForARPResolution )
{
    BaseType_t xReturn;

    __CPROVER_assume( ( xReturn == pdTRUE ) || ( xReturn == pdFALSE ) );

    return xReturn;
}

/* Abstraction of pxUDPSocketLookup */
FreeRTOS_Socket_t * pxUDPSocketLookup( UBaseType_t uxLocalPort )
{
    return safeMalloc( sizeof( FreeRTOS_Socket_t ) );
}

void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    BaseType_t xIsWaitingForARPResolution;
    NetworkEndPoint_t xEndpoint;
    uint16_t usPort;
    EthernetHeader_t * pxHeader;

    pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( sizeof( UDPPacket_t ), 0 );
    /* The network buffer must not be NULL, checked in prvProcessEthernetPacket. */
    __CPROVER_assume( pxNetworkBuffer != NULL );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    pxNetworkBuffer->pxEndPoint = &xEndpoint;

    /* In this test case, we only focus on IPv4. */
    pxHeader = ( ( const EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );
    __CPROVER_assume( pxHeader->usFrameType != ipIPv6_FRAME_TYPE );

    xIsWaitingForARPResolution = nondet_BaseType();
    xProcessReceivedUDPPacket( pxNetworkBuffer, usPort, &xIsWaitingForARPResolution );
}
