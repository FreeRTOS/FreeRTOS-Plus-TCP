/* CBMC includes */
#include "cbmc.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_Routing.h"

void harness()
{
    /* Randomly assign a pointer to be sent to the function. */
    struct xNetworkEndPoint *pxEndPoint = safeMalloc( sizeof( struct xNetworkEndPoint ) );

    FreeRTOS_ClearARP( pxEndPoint );
}
