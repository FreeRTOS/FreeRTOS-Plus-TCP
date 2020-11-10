/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_TCP_WIN.h"

#define NUM_OF_SEGMENTS 1

const TCPSegment_t xRxSegmentListItem[ NUM_OF_SEGMENTS ];
const TCPSegment_t xTxSegmentListItem[ NUM_OF_SEGMENTS ];

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


void harness()
{
    /* Create a TCP Window to be destroyed and fill it with random data. */
    TCPWindow_t xWindow;

    /* Initialise the Rx and Tx lists of the window. */
    vListInitialise( &xWindow.xRxSegments );
    vListInitialise( &xWindow.xTxSegments );

    for( int i=0; i < NUM_OF_SEGMENTS; i++ )
    {
        vListInsertGeneric( &xWindow.xRxSegments, &( xRxSegmentListItem[ i ].xSegmentItem ), &xWindow.xRxSegments.xListEnd );
        //vListInsertFifo( &xWindow.xTxSegments, &( xTxSegmentListItem[ i ].xSegmentItem ) );
    }

    vTCPWindowDestroy( &xWindow );
}
