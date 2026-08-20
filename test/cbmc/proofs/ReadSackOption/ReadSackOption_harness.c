/*
 * Minimal-assumptions memory-safety proof for prvReadSackOption() in
 * FreeRTOS_TCP_Reception.c.
 *
 * prvReadSackOption unconditionally reads eight option bytes:
 *   ulChar2u32( &pucPtr[ uxIndex ] )      -> pucPtr[uxIndex   .. uxIndex+3]
 *   ulChar2u32( &pucPtr[ uxIndex + 4U ] ) -> pucPtr[uxIndex+4 .. uxIndex+7]
 * so the sole memory-safety precondition is uxIndex + 8 <= buffer_size
 * (this is exactly the invariant the caller prvSingleStepTCPHeaderOptions
 * maintains via its `while( ucLen >= 8 )` loop).
 *
 * The buffer is allocated to EXACTLY buffer_size with nondeterministic
 * contents, and uxIndex is left nondeterministic within the modeled bound,
 * so the eight-byte read window is checked against the true buffer end.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"

#include "cbmc.h"

/****************************************************************
* Signature of the function under test.
****************************************************************/

void __CPROVER_file_local_FreeRTOS_TCP_Reception_c_prvReadSackOption( const uint8_t * const pucPtr,
                                                                      size_t uxIndex,
                                                                      FreeRTOS_Socket_t * const pxSocket );

/****************************************************************
* Proof harness.
****************************************************************/

void harness()
{
    /* Buffer of nondeterministic size, allocated to exactly that size. */
    size_t buffer_size;

    __CPROVER_assume( buffer_size < ipconfigNETWORK_MTU );

    uint8_t * pucPtr = malloc( buffer_size );

    __CPROVER_assume( pucPtr != NULL );

    /* uxIndex is nondeterministic within the caller-maintained invariant.
     * uxIndex + 8 <= buffer_size is the minimal precondition for the eight
     * option bytes to be in bounds; it also prevents pointer-offset
     * overflow in &pucPtr[ uxIndex + 4U ]. */
    size_t uxIndex;

    /* Both bounds are required: `uxIndex <= buffer_size` prevents a huge
     * uxIndex from making `uxIndex + 8U` wrap (unsigned overflow) and
     * spuriously satisfy the second bound. This matches the caller, where
     * uxIndex is a small positive int32 stepped in units of 8. */
    __CPROVER_assume( uxIndex <= buffer_size );
    __CPROVER_assume( uxIndex + 8U <= buffer_size );

    /* A socket, initialized enough for the ulTCPWindowTxSack call graph. */
    FreeRTOS_Socket_t * pxSocket = malloc( sizeof( FreeRTOS_Socket_t ) );

    __CPROVER_assume( pxSocket != NULL );

    pxSocket->u.xTCP.txStream = malloc( sizeof( StreamBuffer_t ) );
    __CPROVER_assume( pxSocket->u.xTCP.txStream != NULL );

    vListInitialise( &pxSocket->u.xTCP.xTCPWindow.xWaitQueue );

    if( nondet_bool() )
    {
        TCPSegment_t * segment = malloc( sizeof( TCPSegment_t ) );
        __CPROVER_assume( segment != NULL );
        listSET_LIST_ITEM_OWNER( &segment->xQueueItem, ( void * ) segment );
        vListInsertEnd( &pxSocket->u.xTCP.xTCPWindow.xWaitQueue, &segment->xQueueItem );
    }

    vListInitialise( &pxSocket->u.xTCP.xTCPWindow.xTxSegments );

    if( nondet_bool() )
    {
        TCPSegment_t * segment = malloc( sizeof( TCPSegment_t ) );
        __CPROVER_assume( segment != NULL );
        vListInitialiseItem( &segment->xSegmentItem );
        listSET_LIST_ITEM_OWNER( &segment->xQueueItem, ( void * ) segment );
        vListInsertEnd( &pxSocket->u.xTCP.xTCPWindow.xTxSegments, &segment->xQueueItem );
    }

    vListInitialise( &pxSocket->u.xTCP.xTCPWindow.xPriorityQueue );

    extern List_t xSegmentList;
    vListInitialise( &xSegmentList );

    /* lSRTT is guaranteed to be always greater than or equal to minimum value. */
    __CPROVER_assume( pxSocket->u.xTCP.xTCPWindow.lSRTT >= ipconfigTCP_SRTT_MINIMUM_VALUE_MS );

    __CPROVER_file_local_FreeRTOS_TCP_Reception_c_prvReadSackOption( pucPtr, uxIndex, pxSocket );
}
