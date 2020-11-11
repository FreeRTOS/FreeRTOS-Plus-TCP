/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_TCP_WIN.h"

/* Randomly chosen Number of segments */
#define NUM_OF_SEGMENTS    3

/* Rx/Tx list items to be used in the proof. */
TCPSegment_t xRxSegmentListItem[ NUM_OF_SEGMENTS ];
TCPSegment_t xTxSegmentListItem[ NUM_OF_SEGMENTS ];

/* Definition of this function in FreeRTOS_TCP_WIN.c. */
extern void vListInsertGeneric( List_t * const pxList,
                                ListItem_t * const pxNewListItem,
                                MiniListItem_t * const pxWhere );

/* Segment List is defined in FreeRTOS_TCP_WIN.c */
extern List_t xSegmentList;

void harness()
{
    uint32_t temp;

    /* Choose any value between 0 and NUM_OF_SEGMENTS. */
    __CPROVER_assume( temp <= NUM_OF_SEGMENTS );

    /* Create a TCP Window to be destroyed and fill it with random data. */
    TCPWindow_t xWindow;

    /* Initialise the segment list. */
    vListInitialise( &xSegmentList );

    /* Initialise the Rx and Tx lists of the window. */
    vListInitialise( &xWindow.xRxSegments );
    vListInitialise( &xWindow.xTxSegments );

    /* Below loop fills in various segments in the Rx/Tx list of the window. */
    for( int i = 0; i < temp; i++ )
    {
        /********************** Fill in Rx segments ********************/
        xRxSegmentListItem[ i ].xSegmentItem.pvOwner = &( xRxSegmentListItem[ i ] );

        /* Make the container of the queue item is NULL. */
        xRxSegmentListItem[ i ].xQueueItem.pxContainer = NULL;

        vListInsertGeneric( &xWindow.xRxSegments, &( xRxSegmentListItem[ i ].xSegmentItem ), &xWindow.xRxSegments.xListEnd );


        /********************** Fill in Tx segments ********************/
        xTxSegmentListItem[ i ].xSegmentItem.pvOwner = &( xTxSegmentListItem[ i ] );

        /* Make the container of the queue item is NULL. */
        xTxSegmentListItem[ i ].xQueueItem.pxContainer = NULL;

        vListInsertGeneric( &xWindow.xTxSegments, &( xTxSegmentListItem[ i ].xSegmentItem ), &xWindow.xTxSegments.xListEnd );
    }

    /* Call the function. */
    vTCPWindowDestroy( &xWindow );
}
