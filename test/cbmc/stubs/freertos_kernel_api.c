/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

#include "cbmc.h"

/****************************************************************
* This is a collection of abstractions of methods in the FreeRTOS Kernel
* API.  The abstractions simply perform minimal validation of
* function arguments, and return unconstrained values of the
* appropriate type.
****************************************************************/

/****************************************************************
* Abstract vTaskSuspendAll
****************************************************************/
void vTaskSuspendAll( void )
{
}

/****************************************************************/

/****************************************************************
* Abstract vPortEnterCritical
****************************************************************/
void vPortEnterCritical( void )
{
}

/****************************************************************/

/****************************************************************
* Abstract vListInsertEnd
****************************************************************/
void vListInsertEnd( List_t * const pxList,
                     ListItem_t * const pxNewListItem )
{
}

/****************************************************************/

/****************************************************************
* Abstract vPortExitCritical
****************************************************************/
void vPortExitCritical( void )
{
}

/****************************************************************/

/****************************************************************
* Abstract xTaskResumeAll
****************************************************************/
BaseType_t xTaskResumeAll( void )
{
    BaseType_t xReturn;

    __CPROVER_assume( ( xReturn == pdTRUE ) || ( xReturn == pdFALSE ) );

    return xReturn;
}

/****************************************************************/

/****************************************************************
* Abstract xEventGroupSetBits
****************************************************************/
EventBits_t xEventGroupSetBits( EventGroupHandle_t xEventGroup,
                                const EventBits_t uxBitsToSet )
{
    EventBits_t xReturn;

    return xReturn;
}

/****************************************************************/

/****************************************************************
* Abstract xEventGroupSetBits
****************************************************************/
void vEventGroupDelete( EventGroupHandle_t xEventGroup )
{
}

/****************************************************************/

/****************************************************************
* Abstract xEventGroupSetBits
****************************************************************/
EventGroupHandle_t xEventGroupCreate( void )
{
    EventGroupHandle_t xReturn;

    return xReturn;
}

/****************************************************************/

/****************************************************************
* Abstract xQueueGenericSend
****************************************************************/
BaseType_t xQueueGenericSend( QueueHandle_t xQueue,
                              const void * const pvItemToQueue,
                              TickType_t xTicksToWait,
                              const BaseType_t xCopyPosition )
{
    BaseType_t xReturn;

    __CPROVER_assume( ( xReturn == pdTRUE ) || ( xReturn == pdFALSE ) );

    return xReturn;
}

/****************************************************************/

/****************************************************************
* Abstract uxQueueMessagesWaiting
****************************************************************/
UBaseType_t uxQueueMessagesWaiting( const QueueHandle_t xQueue )
{
    UBaseType_t uxReturn;

    __CPROVER_assume( uxReturn <= 2 );

    return uxReturn;
}

/****************************************************************/

/****************************************************************
* Abstract vTaskSetTimeOutState
****************************************************************/
void vTaskSetTimeOutState( TimeOut_t * const pxTimeOut )
{
}

/****************************************************************/

/****************************************************************
* Abstract xTaskCheckForTimeOut
****************************************************************/
BaseType_t xTaskCheckForTimeOut( TimeOut_t * const pxTimeOut,
                                 TickType_t * const pxTicksToWait )
{
    BaseType_t xReturn;

    __CPROVER_assume( ( xReturn == pdTRUE ) || ( xReturn == pdFALSE ) );

    return xReturn;
}

/****************************************************************/

/****************************************************************
* Abstract xTaskGetTickCount
****************************************************************/
TickType_t xTaskGetTickCount( void )
{
    TickType_t xReturn;

    return xReturn;
}

/****************************************************************/
