/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
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

/** A list of all network end-points.  Each element has a next pointer. */
extern struct xNetworkEndPoint * pxNetworkEndPoints;

/** A list of all network interfaces: */
extern struct xNetworkInterface * pxNetworkInterfaces;

void harness()
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    struct xNetworkEndPoint xLocalEndPoint;
    struct xNetworkEndPoint * pxLocalEndPointPointer;
    MACAddress_t * pxLocalMACPointer;

    /* Assume that the list of interfaces/endpoints is not initialized.
     * Note: These variables are defined in FreeRTOS_Routing.c in global scope.
     *       They serve as a list to the network interfaces and the corresponding
     *       endpoints respectively. And are defined as NULL initially. */
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

    /* Arbitrarily assign a NULL/non-NULL value to the pointer. */
    pxLocalEndPointPointer = nondet_bool() ? NULL : &xLocalEndPoint;

    /* Arbitrarily assign a NULL/non-NULL value to the pointer. */
    pxLocalMACPointer = nondet_bool() ? NULL : &xMACAddress;

    /* Call the function under test. */
    vARPRefreshCacheEntry( pxLocalMACPointer, ulIPAddress, pxLocalEndPointPointer );
}
