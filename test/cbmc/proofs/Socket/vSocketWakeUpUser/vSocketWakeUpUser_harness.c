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

#include "memory_assignments.c"

/* Define the bits used by Kernel. */
#define eventEVENT_BITS_CONTROL_BYTES    0xff000000UL

typedef struct EventGroupDef_t
{
    EventBits_t uxEventBits;
    List_t xTasksWaitingForBits; /*< List of tasks waiting for a bit to be set. */

    #if ( configUSE_TRACE_FACILITY == 1 )
        UBaseType_t uxEventGroupNumber;
    #endif

    #if ( ( configSUPPORT_STATIC_ALLOCATION == 1 ) && ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) )
        uint8_t ucStaticallyAllocated; /*< Set to pdTRUE if the event group is statically allocated to ensure no attempt is made to free the memory. */
    #endif
} EventGroup_t;

/* Definition of QueuePointers as required for the proof. */
typedef struct QueuePointers
{
    int8_t * pcTail;     /*< Points to the byte at the end of the queue storage area.  Once more byte is allocated than necessary to store the queue items, this is used as a marker. */
    int8_t * pcReadFrom; /*< Points to the last place that a queued item was read from when the structure is used as a queue. */
} QueuePointers_t;

/* Definition of SemaphoreData as required for the proof. */
typedef struct SemaphoreData
{
    TaskHandle_t xMutexHolder;        /*< The handle of the task that holds the mutex. */
    UBaseType_t uxRecursiveCallCount; /*< Maintains a count of the number of times a recursive mutex has been recursively 'taken' when the structure is used as a mutex. */
} SemaphoreData_t;

/* Definition of QueueDefinition as required for the proof. */
typedef struct QueueDefinition /* The old naming convention is used to prevent breaking kernel aware debuggers. */
{
    int8_t * pcHead;           /*< Points to the beginning of the queue storage area. */
    int8_t * pcWriteTo;        /*< Points to the free next place in the storage area. */

    union
    {
        QueuePointers_t xQueue;     /*< Data required exclusively when this structure is used as a queue. */
        SemaphoreData_t xSemaphore; /*< Data required exclusively when this structure is used as a semaphore. */
    } u;

    List_t xTasksWaitingToSend;             /*< List of tasks that are blocked waiting to post onto this queue.  Stored in priority order. */
    List_t xTasksWaitingToReceive;          /*< List of tasks that are blocked waiting to read from this queue.  Stored in priority order. */

    volatile UBaseType_t uxMessagesWaiting; /*< The number of items currently in the queue. */
    UBaseType_t uxLength;                   /*< The length of the queue defined as the number of items it will hold, not the number of bytes. */
    UBaseType_t uxItemSize;                 /*< The size of each items that the queue will hold. */

    volatile int8_t cRxLock;                /*< Stores the number of items received from the queue (removed from the queue) while the queue was locked.  Set to queueUNLOCKED when the queue is not locked. */
    volatile int8_t cTxLock;                /*< Stores the number of items transmitted to the queue (added to the queue) while the queue was locked.  Set to queueUNLOCKED when the queue is not locked. */

    #if ( ( configSUPPORT_STATIC_ALLOCATION == 1 ) && ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) )
        uint8_t ucStaticallyAllocated; /*< Set to pdTRUE if the memory used by the queue was statically allocated to ensure no attempt is made to free the memory. */
    #endif

    #if ( configUSE_QUEUE_SETS == 1 )
        struct QueueDefinition * pxQueueSetContainer;
    #endif

    #if ( configUSE_TRACE_FACILITY == 1 )
        UBaseType_t uxQueueNumber;
        uint8_t ucQueueType;
    #endif
} xQUEUE;


/* The memory safety of xQueueGenericSend has been proved before.
 * See github.com/FreeRTOS/FreeRTOS/FreeRTOS/Test/CBMC/proofs/Queue/QueueGenericSend.
 */
BaseType_t xQueueGenericSend( QueueHandle_t xQueue,
                              const void * const pvItemToQueue,
                              TickType_t xTicksToWait,
                              const BaseType_t xCopyPosition )
{
    BaseType_t xResult;

    __CPROVER_assert( xQueue != NULL, "xQueue cannot be NULL" );
    __CPROVER_assert( !( ( pvItemToQueue == NULL ) && ( xQueue->uxItemSize != ( UBaseType_t ) 0U ) ), "If itemsize is non-zero, then pvItemToQueue cannot be NULL." );
    __CPROVER_assert( !( ( xCopyPosition == queueOVERWRITE ) && ( xQueue->uxLength != 1 ) ), "If length is one, then check the copy position" );

    /* Return any random value. */
    return xResult;
}


EventBits_t xEventGroupSetBits( EventGroupHandle_t xEventGroup,
                                const EventBits_t uxBitsToSet )
{
    EventGroup_t * TempEventGroup = xEventGroup;

    /* Check the user is not attempting to set the bits used by the kernel
     * itself. */
    __CPROVER_assert( xEventGroup != NULL, "The event group cannot be NULL" );
    __CPROVER_assert( ( uxBitsToSet & eventEVENT_BITS_CONTROL_BYTES ) == 0, "Cannot set Kernel bits" );

    return TempEventGroup->uxEventBits;
}


void harness()
{
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();

    __CPROVER_assume( pxSocket != NULL );
    __CPROVER_assume( pxSocket != FREERTOS_INVALID_SOCKET );

    pxSocket->pxUserWakeCallback = safeMalloc( sizeof( SocketWakeupCallback_t ) );

    pxSocket->pxSocketSet = safeMalloc( sizeof( struct xSOCKET_SET ) );

    if( pxSocket->pxSocketSet != NULL )
    {
        pxSocket->pxSocketSet->xSelectGroup = safeMalloc( sizeof( struct EventGroupDef_t ) );

        /* The event group cannot be NULL. */
        __CPROVER_assume( pxSocket->pxSocketSet->xSelectGroup != NULL );
    }

    pxSocket->pxUserSemaphore = safeMalloc( sizeof( xQUEUE ) );

    if( pxSocket->pxUserSemaphore != NULL )
    {
        /* The itemsize must be zero since this queue will act as a semaphore.  */
        __CPROVER_assume(pxSocket->pxUserSemaphore->uxItemSize == 0);
    }

    pxSocket->xEventGroup = safeMalloc( sizeof( struct EventGroupDef_t ) );

    /* Call to init the socket list. */
    vNetworkSocketsInit();

    vSocketWakeUpUser( pxSocket );
}
