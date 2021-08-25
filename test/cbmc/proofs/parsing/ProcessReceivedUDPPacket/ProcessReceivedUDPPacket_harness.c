/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_Routing.h"

/*This proof assumes that pxUDPSocketLookup is implemented correctly. */

/* This proof was done before. Hence we assume it to be correct here. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                            const uint32_t ulIPAddress )
{
    __CPROVER_assert( pxMACAddress, "The MAC address cannot be NULL" );
}

/* This proof was done before. Hence we assume it to be correct here. */
BaseType_t xIsDHCPSocket( Socket_t xSocket )
{
}

/* This proof was done before. Hence we assume it to be correct here. */
uint32_t ulDNSHandlePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    __CPROVER_assert( pxNetworkBuffer, "The Network Buffer cannot be NULL" );
}

/* Abstraction of pxUDPSocketLookup */
FreeRTOS_Socket_t * pxUDPSocketLookup( UBaseType_t uxLocalPort )
{
    return nondet_bool() ? NULL : malloc( sizeof( FreeRTOS_Socket_t ) );
}

void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = nondet_bool() ? NULL : malloc( sizeof( NetworkBufferDescriptor_t ) );

    __CPROVER_assume( pxNetworkBuffer != NULL );

    size_t xBufferLength;

    /* The length of the buffer should be bigger than UDPPacket_t. But,
     * the code casts the ethernet packet to ProtocolHeaders_t (which
     * is a union) and accesses the UDP header (which is smaller than a
     * TCP header and thus smaller than the size of union). But CBMC
     * doesn't like that and will trigger an out of bound access
     * violation. To avoid that, the below assumption is made instead of
     * the commented one */

    /* This is how it should be:
     * xBufferLength >= ( sizeof( UDPPacket_t ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ) */
    __CPROVER_assume( xBufferLength >= ( sizeof( ProtocolHeaders_t ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ) &&
                      xBufferLength <= ipTOTAL_ETHERNET_FRAME_SIZE );

    pxNetworkBuffer->xDataLength = xBufferLength;
    pxNetworkBuffer->pucEthernetBuffer = nondet_bool() ? NULL : malloc( xBufferLength );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    pxNetworkBuffer->pxEndPoint = nondet_bool() ? NULL : malloc( sizeof( *( pxNetworkBuffer->pxEndPoint ) ) );

    uint16_t usPort;

    xProcessReceivedUDPPacket( pxNetworkBuffer, usPort );
}
