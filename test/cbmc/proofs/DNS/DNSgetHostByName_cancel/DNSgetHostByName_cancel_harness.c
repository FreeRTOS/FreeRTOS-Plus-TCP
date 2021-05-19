#include "cbmc.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"


/* This proof assumes the length of pcHostName is bounded by MAX_HOSTNAME_LEN. This also abstracts the concurrency. */
void vDNSInitialise( void );

/* Signature of function under test. */
void __CPROVER_file_local_FreeRTOS_DNS_c_vDNSSetCallBack( const char * pcHostName,
                                                          void * pvSearchID,
                                                          FOnDNSEvent pCallbackFunction,
                                                          TickType_t xTimeout,
                                                          TickType_t xIdentifier );


/* Abstraction of xTaskCheckForTimeOut from task pool. This also abstracts the concurrency. */
BaseType_t xTaskCheckForTimeOut( TimeOut_t * const pxTimeOut,
                                 TickType_t * const pxTicksToWait )
{
    BaseType_t xReturn;

    /* This API asserts below conditions. */
    __CPROVER_assert( pxTimeOut != NULL, "Timeout cannot be NULL" );
    __CPROVER_assert( pxTicksToWait != NULL, "Ticks to wait cannot be NULL" );

    /* Return an arbitrary value. */
    return xReturn;
}

/* Abstraction of xTaskResumeAll from task pool. This also abstracts the concurrency. */
BaseType_t xTaskResumeAll( void )
{
    BaseType_t xReturn;

    /* Return an arbitrary value. */
    return xReturn;
}

/* Abstraction of vTaskSuspendAll from task pool. This also abstracts the concurrency. */
void vTaskSuspendAll( void )
{
}


/***************************************************************************
 ***************************************************************************
 *****  THIS PROOF ASSUMES THAT THE KERNEL LIST APIS HAVE BEEN PROVED  *****
 *****       MEMORY SAFE AND HENCE WE ARE ABSTRACTING THEM.            *****
 ***************************************************************************
 ***************************************************************************/

/* Abstraction of vListInitialise. Initialise the list in the simplest possible way. */
void vListInitialise( List_t * pxList )
{
    __CPROVER_assert( pxList != NULL, "NULL list cannot be initialised." );

    /* Fill the list data structure with unconstrained data. */
    __CPROVER_havoc_object( pxList );

    /* The list end next and previous pointers point to itself so we know
     * when the list is empty. */
    pxList->xListEnd.pxNext = ( ListItem_t * ) &( pxList->xListEnd );

    pxList->uxNumberOfItems = ( UBaseType_t ) 0U;
}

/* Abstraction of vListInsertEnd. Fill in the item in the list considering
 * the list as a singly linked list. */
void vListInsertEnd( List_t * const pxList,
                     ListItem_t * const pxNewListItem )
{
    __CPROVER_assert( pxList != NULL, "NULL list cannot be inserted into." );
    __CPROVER_assert( pxNewListItem != NULL, "NULL value cannot be inserted into a list." );

    ListItem_t * const pxIndex = &(pxList->xListEnd);
    ListItem_t * temp = &( pxList->xListEnd );

    /* Fill in unconstrained data in these fields. */
    pxNewListItem->pxPrevious = nondet_uint32_t();
    pxIndex->pxPrevious = nondet_uint32_t();

    /* This is a crude implementation. We do not care about the
     * previous and other values. */
    temp->pxNext = pxNewListItem;
    pxNewListItem->pxNext = temp;

    /* Remember the list in which this is stored. */
    pxNewListItem->pxContainer = pxList;

    /* Increment the item count. We will use only this to remove
     * something from the list. */
    ( pxList->uxNumberOfItems )++;
}

/* Abstraction of uxListRemove. Here, we will only decrement the count
 * to indicate the number of remaining elements.
 * NOTE: this would work as long as loop is using listLIST_IS_EMPTY as
 *       a check. */
UBaseType_t uxListRemove( ListItem_t * const pxItemToRemove )
{
    __CPROVER_assert( pxItemToRemove != NULL, "NULL value cannot be passed to list remove function." );

    List_t * const pxList = pxItemToRemove->pxContainer;

    /* This should suffice for the stub. */
    ( pxList->uxNumberOfItems )--;
}

/* The function func mimics the callback function.*/
void func( const char * pcHostName,
           void * pvSearchID,
           uint32_t ulIPAddress )
{
    __CPROVER_assert( pcHostName != NULL, "Host name cannot be NULL." );

    /* pvSearchID can be NULL/non-NULL and ulIPAddress can be any value.
     * Therefore, these values are not checked. */
}

void harness()
{
    size_t vSearchID, LocalSearchID;

    /* Arbitrarily assign a NULL or a non-NULL value to the pointer. */
    size_t * pvLocalPointerSearchID = nondet_bool() ? NULL : &vSearchID;

    FOnDNSEvent pCallback = func;
    TickType_t xTimeout;
    TickType_t xIdentifier;
    size_t len;

    /* len is a size_t variable and hence always positive. */
    __CPROVER_assume( ( len > 0 ) && ( len <= MAX_HOSTNAME_LEN ) );

    char * pcHostName = nondet_bool() ? malloc( len ) : NULL;
    __CPROVER_assume( pcHostName != NULL );

    /* NULL terminate the string. */
    pcHostName[ len - 1 ] = NULL;

    /* We initialize the callbacklist in order to be able to check for functions that timed out. */
    vDNSInitialise();

    if( nondet_bool() )
    {
        /* Add an item to be able to check the cancel function if the list is non-empty. */
        __CPROVER_file_local_FreeRTOS_DNS_c_vDNSSetCallBack( pcHostName, pvLocalPointerSearchID, pCallback, xTimeout, xIdentifier );
    }

    FreeRTOS_gethostbyname_cancel( nondet_bool() ? &LocalSearchID : NULL );
}
