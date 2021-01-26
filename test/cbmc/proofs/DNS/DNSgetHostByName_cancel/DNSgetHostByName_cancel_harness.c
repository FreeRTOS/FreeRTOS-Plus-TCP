#include "cbmc.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"


/* This proof assumes the length of pcHostName is bounded by MAX_HOSTNAME_LEN. This also abstracts the concurrency. */
void vDNSInitialise( void );

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
    return;
}

/* The function func mimics the callback function.*/
void func( const char * pcHostName,
           void * pvSearchID,
           uint32_t ulIPAddress )
{
    return;
}

void harness()
{
    size_t pvSearchID;
    FOnDNSEvent pCallback = func;
    TickType_t xTimeout;
    TickType_t xIdentifier;
    size_t len;

    /* len is a size_t variable and hence always positive. */
    __CPROVER_assume( ( len > 0 ) && ( len <= MAX_HOSTNAME_LEN ) );

    char * pcHostName = nondet_bool ? malloc( len ) : NULL;
    __CPROVER_assume( pcHostName != NULL );

    if( pcHostName != NULL )
    {
        pcHostName[ len - 1 ] = NULL;
    }

    /* We initialize the callbacklist in order to be able to check for functions that timed out. */
    vDNSInitialise();

    if( nondet_bool() )
    {
        /* Add an item to be able to check the cancel function if the list is non-empty. */
        __CPROVER_file_local_FreeRTOS_DNS_c_vDNSSetCallBack( pcHostName, &pvSearchID, pCallback, xTimeout, xIdentifier );
    }

    FreeRTOS_gethostbyname_cancel( nondet_bool() ? &pvSearchID : NULL );
}
