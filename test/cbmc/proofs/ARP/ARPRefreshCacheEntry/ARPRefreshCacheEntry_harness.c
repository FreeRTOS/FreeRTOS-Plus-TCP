/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ARP.h"

void harness()
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;

    /*
    For this proof, its assumed that the endpoints and interfaces are correctly
    initialised and the pointers are set correctly.
    Assumes one endpoints and interface is present.
    */

    pxNetworkEndPoints = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );
    __CPROVER_assume( pxNetworkEndPoints->pxNext == NULL );

    NetworkEndPoint_t * pxEndPoint = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxEndPoint != NULL );

    vARPRefreshCacheEntry( &xMACAddress, ulIPAddress, pxEndPoint );
    vARPRefreshCacheEntry( NULL, ulIPAddress, pxEndPoint );
}
