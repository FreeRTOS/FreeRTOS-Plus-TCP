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
    /* Use safeMalloc to indeterminately return a valid pointer or a NULL. */
    struct xNetworkEndPoint * pxEndPoint = safeMalloc( sizeof( *pxEndPoint ) );

    FreeRTOS_ClearARP( pxEndPoint );
}
