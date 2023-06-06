/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_TCP_IP.h"

/*This proof assumes that pxUDPSocketLookup is implemented correctly. */

/* This proof was done before. Hence we assume it to be correct here. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                            const uint32_t ulIPAddress )
{
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

/* Implementation of safe malloc */
void * safeMalloc( size_t xWantedSize )
{
    if( xWantedSize == 0 )
    {
        return NULL;
    }

    uint8_t byte;

    return byte ? malloc( xWantedSize ) : NULL;
}

/* Abstraction of pxUDPSocketLookup */
FreeRTOS_Socket_t * pxUDPSocketLookup( UBaseType_t uxLocalPort )
{
    return safeMalloc( sizeof( FreeRTOS_Socket_t ) );
}

void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
    BaseType_t * pxIsWaitingForARPResolution;
    NetworkEndPoint_t xEndpoint;

    pxIsWaitingForARPResolution = safeMalloc( sizeof( BaseType_t ) );

    /* The function under test is only called by the IP-task. The below pointer is an
     * address of a local variable which is being passed to the function under test.
     * Thus, it cannot ever be NULL. */
    __CPROVER_assume( pxIsWaitingForARPResolution != NULL );

    if( pxNetworkBuffer )
    {
        pxNetworkBuffer->pucEthernetBuffer = safeMalloc( sizeof( UDPPacket_IPv6_t ) );
        pxNetworkBuffer->pxEndPoint = &xEndpoint;
    }

    uint16_t usPort;

    if( pxNetworkBuffer && pxNetworkBuffer->pucEthernetBuffer )
    {
        xProcessReceivedUDPPacket( pxNetworkBuffer, usPort, pxIsWaitingForARPResolution );
    }
}
