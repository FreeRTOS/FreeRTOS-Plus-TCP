/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_TCP_WIN.h"

#define NUM_OF_SEGMENTS 3

TCPSegment_t xRxSegmentListItem[ NUM_OF_SEGMENTS ];
TCPSegment_t xTxSegmentListItem[ NUM_OF_SEGMENTS ];

static void vListInsertGeneric( List_t * const pxList,
                                    ListItem_t * const pxNewListItem,
                                    MiniListItem_t * const pxWhere )
    {
        /* Insert a new list item into pxList, it does not sort the list,
         * but it puts the item just before xListEnd, so it will be the last item
         * returned by listGET_HEAD_ENTRY() */
        pxNewListItem->pxNext = ( struct xLIST_ITEM * configLIST_VOLATILE ) pxWhere;
        pxNewListItem->pxPrevious = pxWhere->pxPrevious;
        pxWhere->pxPrevious->pxNext = pxNewListItem;
        pxWhere->pxPrevious = pxNewListItem;

        /* Remember which list the item is in. */
        listLIST_ITEM_CONTAINER( pxNewListItem ) = ( struct xLIST * configLIST_VOLATILE ) pxList;

        ( pxList->uxNumberOfItems )++;
    }

extern List_t xSegmentList;

void harness()
{
    /* Create a TCP Window to be destroyed and fill it with random data. */
    TCPWindow_t xWindow;
    uint32_t ulSequenceNumber;
    int32_t lCount;
    BaseType_t xIsForRx = nondet_bool();

    vListInitialise( &xSegmentList );

    /* Initialise the Rx and Tx lists of the window. */
    vListInitialise( &xWindow.xRxSegments );
    vListInitialise( &xWindow.xTxSegments );

    for( int i=0; i < NUM_OF_SEGMENTS; i++ )
    {
        xRxSegmentListItem[ i ].xSegmentItem.pvOwner = &( xRxSegmentListItem[ i ] );

        __CPROVER_assume( xRxSegmentListItem[ i ].xQueueItem.pxContainer == NULL );

        vListInsertGeneric( &xWindow.xRxSegments, &( xRxSegmentListItem[ i ].xSegmentItem ), &xWindow.xRxSegments.xListEnd );



        xTxSegmentListItem[ i ].xSegmentItem.pvOwner = &( xTxSegmentListItem[ i ] );

        __CPROVER_assume( xTxSegmentListItem[ i ].xQueueItem.pxContainer == NULL );

        vListInsertGeneric( &xWindow.xTxSegments, &( xTxSegmentListItem[ i ].xSegmentItem ), &xWindow.xTxSegments.xListEnd );
    }

    vTCPWindowDestroy( &xWindow );
}
