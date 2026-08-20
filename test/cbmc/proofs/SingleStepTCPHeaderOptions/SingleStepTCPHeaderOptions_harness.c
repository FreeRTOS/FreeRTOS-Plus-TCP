/*
 * Minimal-assumptions memory-safety proof for
 * prvSingleStepTCPHeaderOptions() in FreeRTOS_TCP_Reception.c.
 *
 * Unlike the CheckOptionsOuter proof (which STUBS prvReadSackOption and
 * permits buffer_size > uxTotalLength), this harness:
 *   - links the REAL prvReadSackOption via the .goto objects, so the
 *     SACK-option index arithmetic is fully exercised, and
 *   - allocates the option buffer to EXACTLY uxTotalLength bytes, so any
 *     read past the modeled option length is a genuine out-of-bounds bug.
 *
 * Buffer contents are fully nondeterministic and uxTotalLength is left
 * nondeterministic within the modeled bound (the real caller,
 * prvCheckOptions, derives it from the TCP data-offset field, whose max
 * option area is 40 bytes; it also guarantees uxTotalLength >= 1 because
 * the calling loop breaks when the remaining length reaches 0).
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

int32_t __CPROVER_file_local_FreeRTOS_TCP_Reception_c_prvSingleStepTCPHeaderOptions( const uint8_t * const pucPtr,
                                                                                     size_t uxTotalLength,
                                                                                     FreeRTOS_Socket_t * const pxSocket,
                                                                                     BaseType_t xHasSYNFlag );

/****************************************************************
* Proof harness.
****************************************************************/

void harness()
{
    /* Modeled length of the TCP options area.  Left nondeterministic; the
     * real caller bounds it to at most 40 bytes (10 * 4-byte option words)
     * and never calls with 0. */
    size_t uxTotalLength;

    __CPROVER_assume( uxTotalLength >= 1 );
    __CPROVER_assume( uxTotalLength <= OPTION_BUFFER_BOUND );

    /* Allocate the option buffer to EXACTLY its modeled length so that any
     * over-read is a real out-of-bounds access rather than a read into
     * over-provisioned slack. Contents are fully nondeterministic. */
    uint8_t * pucPtr = malloc( uxTotalLength );

    __CPROVER_assume( pucPtr != NULL );

    /* A socket, initialized enough for the real prvReadSackOption /
     * ulTCPWindowTxSack call graph reached through the SACK option. */
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

    BaseType_t xHasSYNFlag;

    int32_t index = __CPROVER_file_local_FreeRTOS_TCP_Reception_c_prvSingleStepTCPHeaderOptions( pucPtr,
                                                                                                 uxTotalLength,
                                                                                                 pxSocket,
                                                                                                 xHasSYNFlag );

    /* Postcondition relied upon by the calling loop in prvCheckOptions:
     * the returned advance is either an error (-1), a stop (0/1), or a
     * positive step no larger than the remaining option length. */
    __CPROVER_assert( ( index == -1 ) || ( index == 0 ) || ( index == 1 ) || ( ( size_t ) index <= uxTotalLength ),
                      "prvSingleStepTCPHeaderOptions: index <= uxTotalLength" );
}
