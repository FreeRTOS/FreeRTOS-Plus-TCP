/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_Routing.h"

/* Global variables accessible throughout the program. Used in adding
 * Network interface/endpoint. */
NetworkInterface_t xNetworkInterface1;
NetworkEndPoint_t xEndPoint1;

const uint8_t ucIPAddress2[ 4 ];
const uint8_t ucNetMask2[ 4 ];
const uint8_t ucGatewayAddress2[ 4 ];
const uint8_t ucDNSServerAddress2[ 4 ];
const uint8_t ucMACAddress[ 6 ];

void harness()
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    struct xNetworkEndPoint xLocalEndPoint;
    struct xNetworkEndPoint * pxLocalEndPointPointer = &xLocalEndPoint;

    /* Assume that the list of interfaces/endpoints is not initialized. */
    __CPROVER_assume( pxNetworkInterfaces == NULL );
    __CPROVER_assume( pxNetworkEndPoints == NULL );

    /* Non-deterministically add a network-interface and its endpoint. */
    if( nondet_bool() )
    {
        /* Add the network interfaces to the list. */
        FreeRTOS_AddNetworkInterface( &xNetworkInterface1 );

        /* Fill the endpoints and put them in the network interface. */
        FreeRTOS_FillEndPoint( &xNetworkInterface1,
                               &xEndPoint1,
                               ucIPAddress2,
                               ucNetMask2,
                               ucGatewayAddress2,
                               ucDNSServerAddress2,
                               ucMACAddress );
    }

    /* The pointers to the MAC-Address, IP-Address and the End point cannot be NULL.
     * Therefore, addresses to actual local variables are passed to the function. */
    eARPGetCacheEntryByMac( &xMACAddress, &ulIPAddress, &pxLocalEndPointPointer );
}
