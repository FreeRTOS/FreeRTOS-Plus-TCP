/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"

/* CBMC includes. */
#include "cbmc.h"

/* This proof assumes the length of pcHostName is bounded by MAX_HOSTNAME_LEN. This also abstracts the concurrency. */

void vDNSInitialise( void );

BaseType_t xDNSSetCallBack( const char * pcHostName,
                            void * pvSearchID,
                            FOnDNSEvent pCallbackFunction,
                            TickType_t xTimeout,
                            TickType_t xIdentifier,
                            BaseType_t xIsIPv6 );

/* Abstraction of uxListRemove from list. This also abstracts the concurrency. */
void vListInitialise( List_t * const pxList )
{
    __CPROVER_assert( pxList != NULL, "pxList cannot be NULL" );

    pxList->pxIndex = ( ListItem_t * ) &( pxList->xListEnd );
    pxList->xListEnd.xItemValue = portMAX_DELAY;

    /* The list end next and previous pointers point to itself so we know
     * when the list is empty. */
    pxList->xListEnd.pxNext = ( ListItem_t * ) &( pxList->xListEnd );
    pxList->xListEnd.pxPrevious = ( ListItem_t * ) &( pxList->xListEnd );
    pxList->uxNumberOfItems = ( UBaseType_t ) 0U;
}

/* Abstraction of uxListRemove from list. This also abstracts the concurrency. */
UBaseType_t uxListRemove( ListItem_t * const pxItemToRemove )
{
    List_t * const pxList = pxItemToRemove->pxContainer;

    pxItemToRemove->pxNext->pxPrevious = pxItemToRemove->pxPrevious;
    pxItemToRemove->pxPrevious->pxNext = pxItemToRemove->pxNext;

    if( pxList->pxIndex == pxItemToRemove )
    {
        pxList->pxIndex = pxItemToRemove->pxPrevious;
    }

    pxItemToRemove->pxContainer = NULL;
    ( pxList->uxNumberOfItems )--;

    return pxList->uxNumberOfItems;
}

/* The function func mimics the callback function.*/
void func( const char * pcHostName,
           void * pvSearchID,
           uint32_t ulIPAddress )
{
}

void harness()
{
    vDNSInitialise(); /* We initialize the callbacklist in order to be able to check for functions that timed out. */
    size_t pvSearchID;
    FOnDNSEvent pCallback = func;
    TickType_t xTimeout;
    TickType_t xIdentifier;
    BaseType_t xIsIPv6;
    size_t len;
    BaseType_t xReturn;

    __CPROVER_assume( len > 0 && len <= MAX_HOSTNAME_LEN );
    char * pcHostName = safeMalloc( len );
    __CPROVER_assume( pcHostName != NULL );
    __CPROVER_havoc_slice( pcHostName, len - 1 );
    pcHostName[ len - 1 ] = NULL;

    xReturn = xDNSSetCallBack( pcHostName, &pvSearchID, pCallback, xTimeout, xIdentifier, xIsIPv6 ); /* Add an item to be able to check the cancel function if the list is non-empty. */
    FreeRTOS_gethostbyname_cancel( &pvSearchID );
}
