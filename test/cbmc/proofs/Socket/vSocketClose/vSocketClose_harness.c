/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"
/*#include "event_groups.h" */
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"

#include "freertos_api.c"
#include "memory_assignments.c"

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
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();

    /* Request a random number of bytes keeping in mind the maximum bound of CBMC. */
    __CPROVER_assume( xRequestedSizeBytes < ( CBMC_MAX_OBJECT_SIZE - ipBUFFER_PADDING ) );

    /* Assume socket to not be NULL or invalid. */
    __CPROVER_assume( pxSocket != NULL );
    __CPROVER_assume( pxSocket != FREERTOS_INVALID_SOCKET );

    pxSocket->pxUserWakeCallback = safeMalloc( sizeof( SocketWakeupCallback_t ) );

    /* Get a network buffer descriptor with requested bytes. See the constraints
     * on the number of requested bytes above. And block for random timer ticks. */
    if( pxSocket->ucProtocol == FREERTOS_IPPROTO_TCP )
    {
        if( nondet_bool() )
        {
            pxSocket->u.xTCP.pxAckMessage = pxGetNetworkBufferWithDescriptor( xRequestedSizeBytes, xBlockTimeTicks );
        }
        else
        {
            pxSocket->u.xTCP.pxAckMessage = NULL;
        }
    }

    /* Non deterministically add an event group. */
    if( nondet_bool() )
    {
        pxSocket->xEventGroup = xEventGroupCreate();
        __CPROVER_assume( pxSocket->xEventGroup != NULL );
    }
    else
    {
        pxSocket->xEventGroup = NULL;
    }

    /* Create and fill the socket in the bound socket list. This socket will then be
     * removed by a call to the vSocketClose. */
    List_t BoundSocketList;
    vListInitialise( &BoundSocketList );

    /* Non-deterministically add the socket to bound socket list. */
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
    ListItem_t xWaitingPacketListItem, BufferList;
    NetworkBufferDescriptor_t Buffer;
    NetworkBufferDescriptor_t * NetworkBuffer = pxGetNetworkBufferWithDescriptor( 100, xBlockTimeTicks );

/*    NetworkBuffer->pucEthernetBuffer = malloc( 100 ); */
/*    NetworkBuffer->xDataLength = 100; */

    __CPROVER_assume( NetworkBuffer != NULL );

    if( pxSocket->ucProtocol == FREERTOS_IPPROTO_UDP )
    {
        /*************************************************************************
         ********************* THIS SECTION NEEDS ATTENTION ***********************
         **************************************************************************/

        /* THE PROOF gets stuck if I uncomment the below line
         * Initialise the waiting packet list. */
        vListInitialise( &( pxSocket->u.xUDP.xWaitingPacketsList ) );
        vListInitialise( &( BufferList ) );

        /* This section can be looked at later. */
        if( nondet_bool() )
        {
            /* Initialise an item to be placed in the list and set its owner. */
            /*           vListInitialiseItem( &xWaitingPacketListItem ); */
/*            listSET_LIST_ITEM_OWNER( &xWaitingPacketListItem, ( void * ) NetworkBuffer ); */

            /* Insert the waiting packet into the list at the end. */
/*            vListInsertEnd( &( pxSocket->u.xUDP.xWaitingPacketsList ), &xWaitingPacketListItem ); */

            /* Initialise the buffer list item. */
            vListInitialiseItem( &( NetworkBuffer->xBufferListItem ) );
            listSET_LIST_ITEM_OWNER( &( NetworkBuffer->xBufferListItem ), ( void * ) NetworkBuffer );
            /* Set the container of the buffer list item as the waiting packet list. */
            NetworkBuffer->xBufferListItem.pxContainer = &( pxSocket->u.xUDP.xWaitingPacketsList );
            vListInsertEnd( &( pxSocket->u.xUDP.xWaitingPacketsList ), &( NetworkBuffer->xBufferListItem ) );
        }
        else
        {
            /* Do nothing. */
        }
    }

    /* Call to init the socket list. */
    vNetworkSocketsInit();

    vSocketClose( pxSocket );
}
