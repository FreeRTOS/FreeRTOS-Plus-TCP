/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "event_groups.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"

#include "memory_assignments.c"

uint16_t prvGetPrivatePortNumber( BaseType_t xProtocol );


uint16_t prvGetPrivatePortNumber( BaseType_t xProtocol )
{
    uint16_t usResult;

    return usResult;
}

BaseType_t xIPIsNetworkTaskReady( void )
{
    /* Return true saying that the task is ready. */
    return pdTRUE;
}


/* Random number generator provided by the application. In our case, CBMC provides
 * an indeterministic value. */
BaseType_t xApplicationGetRandomNumber( uint32_t * pulNumber )
{
    __CPROVER_assert( pulNumber != NULL, "Argument to xApplicationGetRandomNumber cannot be NULL" );

    if( nondet_bool() )
    {
        *pulNumber = nondet_uint32_t();
        return 1;
    }
    else
    {
        *pulNumber = NULL;
        return 0;
    }
}

void harness()
{
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();

    __CPROVER_assume( pxSocket != NULL );
    __CPROVER_assume( pxSocket != FREERTOS_INVALID_SOCKET );

    /* Call to init the socket list. */
    vNetworkSocketsInit();

    vSocketWakeUpUser( pxSocket );
}
