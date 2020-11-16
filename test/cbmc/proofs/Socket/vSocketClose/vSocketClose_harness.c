/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"
#include "event_groups.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"

#include "freertos_api.c"
#include "memory_assignments.c"

void vEventGroupDelete( EventGroupHandle_t xEventGroup )
{
    __CPROVER_assert( xEventGroup, "Event group cannot be NULL" );
}

/* The memory safety of vTCPWindowDestroy has already been proved in
 * proofs/TCPWin/vTCPWindowDestroy. */
void vTCPWindowDestroy( TCPWindow_t const * xWindow )
{
    __CPROVER_assert( xWindow != NULL, "xWindow cannot be NULL" );

    /* Do nothing. */
}

void harness()
{
    size_t xRequestedSizeBytes;
    TickType_t xBlockTimeTicks;

    /* Request a random number of bytes keeping in mind the maximum bound of CBMC. */
    __CPROVER_assume( ( xRequestedSizeBytes >= 0 ) && ( xRequestedSizeBytes < ( CBMC_MAX_OBJECT_SIZE - ipBUFFER_PADDING ) ) );

    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
    /* Assume socket to not be NULL or invalid. */
    __CPROVER_assume( pxSocket != NULL );
    __CPROVER_assume( pxSocket != FREERTOS_INVALID_SOCKET );

    pxSocket->pxUserWakeCallback = safeMalloc( sizeof( SocketWakeupCallback_t ) );

    /* Get a network buffer descriptor with requested bytes. See the constraints
     * on the number of requested bytes above. And block for random timer ticks. */
    pxSocket->u.xTCP.pxAckMessage = pxGetNetworkBufferWithDescriptor( xRequestedSizeBytes, xBlockTimeTicks );


    /* Create and fill the socket in the bound socket list. Which will be removed
     * by a call to the vSocketClose. */
    List_t BoundSocketList;
    vListInitialise( &BoundSocketList );

    if( nondet_bool() )
    {
        vListInitialiseItem( &( pxSocket->xBoundSocketListItem ) );
        pxSocket->xBoundSocketListItem.pxContainer = &( BoundSocketList );

        vListInsertEnd( &BoundSocketList, &( pxSocket->xBoundSocketListItem ) );
    }
    else
    {
        pxSocket->xBoundSocketListItem.pxContainer = NULL;
    }

    /* Initialise and place some random packets in the waiting packet list. */
    ListItem_t xWaitingPacketListItem;
    NetworkBufferDescriptor_t NetworkBuffer;

    if( pxSocket->ucProtocol == FREERTOS_IPPROTO_UDP )
    {
        vListInitialise( &( pxSocket->u.xUDP.xWaitingPacketsList ) );

        if( nondet_bool() )
        {
            vListInitialiseItem( &xWaitingPacketListItem );
            listSET_LIST_ITEM_OWNER( &xWaitingPacketListItem, ( void * ) &NetworkBuffer );
            vListInsertEnd( &( pxSocket->u.xUDP.xWaitingPacketsList ), &xWaitingPacketListItem );

            vListInitialiseItem( &( NetworkBuffer.xBufferListItem ) );

            /* Below 2 statements to be checked. */
            NetworkBuffer.xBufferListItem.pxContainer = &( pxSocket->u.xUDP.xWaitingPacketsList );
            vListInsertEnd( &( pxSocket->u.xUDP.xWaitingPacketsList ), &( NetworkBuffer.xBufferListItem ) );
        }
        else
        {
            pxSocket->u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0;
        }
    }

    /* Call to init the socket list. */
    vNetworkSocketsInit();

    vSocketClose( pxSocket );
}
