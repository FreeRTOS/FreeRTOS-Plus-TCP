/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"
#include "event_groups.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"

#include "freertos_api.c"
#include "memory_assignments.c"

void vEventGroupDelete( EventGroupHandle_t xEventGroup )
{
    __CPROVER_assert( xEventGroup );

    /**/
}

/* The memory safety of vTCPWindowDestroy has already been proved in
 * proofs/TCPWin/vTCPWindowDestroy. */
void vTCPWindowDestroy( TCPWindow_t const * xWindow )
{
    /* Do nothing. */
}

void harness()
{
    size_t xRequestedSizeBytes;
    /* Request a random number of bytes keeping in mind the maximum bound of CBMC. */
    __CPROVER_assume( ( xRequestedSizeBytes >=0 ) && ( xRequestedSizeBytes < ( CBMC_MAX_OBJECT_SIZE - ipBUFFER_PADDING ) ) );

    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
    /* Assume socket to not be NULL or invalid. */
    __CPROVER_assume( pxSocket != NULL );
    __CPROVER_assume( pxSocket != FREERTOS_INVALID_SOCKET );

    pxSocket->pxUserWakeCallback = safeMalloc( sizeof( SocketWakeupCallback_t ) );

    /* Get a network buffer descriptor with requested bytes. See the constraints
     * on the number of requested bytes above. */
    pxSocket->u.xTCP.pxAckMessage = pxGetNetworkBufferWithDescriptor( xRequestedSizeBytes, 0 );

    pxSocket->u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0;
/*    NetworkBufferDescriptor_t *temp = pxGetNetworkBufferWithDescriptor( 200, 0 );

    struct xLIST_ITEM temp1;

    List_t temp2;
    vListInitialise( &temp2 );

    pxSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &temp1;
    pxSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext->pvOwner = temp;
    ( ( NetworkBufferDescriptor_t * ) ( pxSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext->pvOwner ) )->xBufferListItem.pvContainer = NULL;
*/

    /* Initialise the item to be used later on in the proof.  */
    vListInitialiseItem( &( pxSocket->xBoundSocketListItem ) );

    /* Call to init the socket list. */
    vNetworkSocketsInit();

    vSocketClose( pxSocket );
}
