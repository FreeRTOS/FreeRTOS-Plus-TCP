/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "semphr.h"
#include "event_groups.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"

#include "memory_assignments.c"

/* The memory safety of xQueueGenericSend has been proved before.
 * See github.com/FreeRTOS/FreeRTOS/FreeRTOS/Test/CBMC/proofs/Queue/QueueGenericSend.
 */
BaseType_t xQueueGenericSend( QueueHandle_t xQueue,
                              const void * const pvItemToQueue,
                              TickType_t xTicksToWait,
                              const BaseType_t xCopyPosition )
{
    BaseType_t xResult;

    /* Return any random value. */
    return xResult;
}

void harness()
{
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();

    __CPROVER_assume( pxSocket != NULL );
    __CPROVER_assume( pxSocket != FREERTOS_INVALID_SOCKET );

    pxSocket->pxUserWakeCallback = safeMalloc( sizeof( SocketWakeupCallback_t ) );
    pxSocket->pxSocketSet = safeMalloc( sizeof( struct xSOCKET_SET ) );

    if( pxSocket->pxSocketSet != NULL )
    {
        pxSocket->pxSocketSet->xSelectGroup = safeMalloc( sizeof( EventGroupHandle_t ) );
    }

    /* Call to init the socket list. */
    vNetworkSocketsInit();

    vSocketWakeUpUser( pxSocket );
}
