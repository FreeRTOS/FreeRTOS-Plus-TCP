/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file FreeRTOS_DNS_Callback.c
 * @brief File that handles the DNS Callback option
 */

#include "FreeRTOS_DNS_Callback.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_DNS_Globals.h"
#include "FreeRTOS_IP_Timers.h"

#if ( ( ipconfigDNS_USE_CALLBACKS == 1 ) && ( ipconfigUSE_DNS != 0 ) )

/**
 * @brief list of callbacks to send
 */
    static List_t xCallbackList;

/**
 * @brief A DNS reply was received, see if there is any matching entry and
 *        call the handler.
 *
 * @param[in] uxIdentifier: Identifier associated with the callback function.
 * @param[in] pcName: The name associated with the callback function.
 * @param[in] ulIPAddress: IP-address obtained from the DNS server.
 *
 * @return Returns pdTRUE if uxIdentifier was recognized.
 */
    BaseType_t xDNSDoCallback( TickType_t uxIdentifier,
                               const char * pcName,
                               uint32_t ulIPAddress )
    {
        BaseType_t xResult = pdFALSE;
        const ListItem_t * pxIterator;
        const ListItem_t * xEnd = listGET_END_MARKER( &xCallbackList );
        DNSCallback_t * pxKeepCallback = NULL;

        /* Find the right entry in the list without getting disturbed by
         * another task. */
        vTaskSuspendAll();
        {
            for( pxIterator = ( const ListItem_t * ) listGET_NEXT( xEnd );
                 pxIterator != ( const ListItem_t * ) xEnd;
                 pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator ) )
            {
                if( listGET_LIST_ITEM_VALUE( pxIterator ) == uxIdentifier )
                {
                    DNSCallback_t * pxCallback = ( ( DNSCallback_t * )
                                                   listGET_LIST_ITEM_OWNER( pxIterator ) );

                    /* Remember the callback instance that must be called.  Call it outside
                     * the critical section, so that FreeRTOS API's can be called. */
                    pxKeepCallback = pxCallback;
                    break;
                }
            }
        }
        ( void ) xTaskResumeAll();

        if( pxKeepCallback )
        {
            pxKeepCallback->pCallbackFunction( pcName, pxKeepCallback->pvSearchID,
                                               ulIPAddress );
            vTaskSuspendAll();
            {
                /* uxListRemove() needs the protection of some critical section. */
                ( void ) uxListRemove( &pxKeepCallback->xListItem );
            }
            ( void ) xTaskResumeAll();

            vPortFree( pxKeepCallback );

            if( listLIST_IS_EMPTY( &xCallbackList ) != pdFALSE )
            {
                /* The list of outstanding requests is empty. No need for periodic polling. */
                vIPSetDNSTimerEnableState( pdFALSE );
            }

            xResult = pdTRUE;
        }

        return xResult;
    }

/**
 * @brief FreeRTOS_gethostbyname_a() was called along with callback parameters.
 *        Store them in a list for later reference.
 *
 * @param[in] pcHostName: The hostname whose IP address is being searched for.
 * @param[in] pvSearchID: The search ID of the DNS callback function to set.
 * @param[in] pCallbackFunction: The callback function pointer.
 * @param[in] uxTimeout: Timeout of the callback function.
 * @param[in] uxIdentifier: Random number used as ID in the DNS message.
 */
    void vDNSSetCallBack( const char * pcHostName,
                          void * pvSearchID,
                          FOnDNSEvent pCallbackFunction,
                          TickType_t uxTimeout,
                          TickType_t uxIdentifier )
    {
        size_t lLength = strlen( pcHostName );
        DNSCallback_t * pxCallback = ( ( DNSCallback_t * ) pvPortMalloc( sizeof( *pxCallback ) + lLength ) );

        /* Translate from ms to number of clock ticks. */
        uxTimeout /= portTICK_PERIOD_MS;

        if( pxCallback != NULL )
        {
            if( listLIST_IS_EMPTY( &xCallbackList ) != pdFALSE )
            {
                /* This is the first one, start the DNS timer to check for timeouts */
                vDNSTimerReload( FreeRTOS_min_uint32( 1000U, uxTimeout ) );
            }

            ( void ) strcpy( pxCallback->pcName, pcHostName );
            pxCallback->pCallbackFunction = pCallbackFunction;
            pxCallback->pvSearchID = pvSearchID;
            pxCallback->uxRemainingTime = uxTimeout;
            vTaskSetTimeOutState( &pxCallback->uxTimeoutState );
            listSET_LIST_ITEM_OWNER( &( pxCallback->xListItem ), ( void * ) pxCallback );
            listSET_LIST_ITEM_VALUE( &( pxCallback->xListItem ), uxIdentifier );
            vTaskSuspendAll();
            {
                vListInsertEnd( &xCallbackList, &pxCallback->xListItem );
            }
            ( void ) xTaskResumeAll();
        }
        else
        {
            FreeRTOS_debug_printf( ( " vDNSSetCallBack : Could not allocate memory: %u bytes",
                                     ( unsigned ) ( sizeof( *pxCallback ) + lLength ) ) );
        }
    }

/**
 * @brief Iterate through the list of call-back structures and remove
 *        old entries which have reached a timeout.
 *        As soon as the list has become empty, the DNS timer will be stopped.
 *        In case pvSearchID is supplied, the user wants to cancel a DNS request.
 *
 * @param[in] pvSearchID: The search ID of callback function whose associated
 *                 DNS request is being cancelled. If non-ID specific checking of
 *                 all requests is required, then this field should be kept as NULL.
 */
    void vDNSCheckCallBack( void * pvSearchID )
    {
        const ListItem_t * pxIterator;
        const ListItem_t * xEnd = listGET_END_MARKER( &xCallbackList );
        DNSCallback_t * pxKeepCallback;

        do
        {
            vTaskSuspendAll();
            {
                pxKeepCallback = NULL;

                for( pxIterator = ( const ListItem_t * ) listGET_NEXT( xEnd );
                     pxIterator != xEnd; )
                {
                    DNSCallback_t * pxCallback = ( ( DNSCallback_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );
                    /* Move to the next item because we might remove this item */
                    pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator );

                    if( ( pvSearchID != NULL ) && ( pvSearchID == pxCallback->pvSearchID ) )
                    {
                        ( void ) uxListRemove( &( pxCallback->xListItem ) );
                        vPortFree( pxCallback );
                    }
                    else if( xTaskCheckForTimeOut( &pxCallback->uxTimeoutState, &pxCallback->uxRemainingTime ) != pdFALSE )
                    {
                        /* Remember the entry that has expired. Call the user function from
                         * outside the critical section, so that FreeRTOS API's may be called. */
                        pxKeepCallback = pxCallback;
                        break;
                    }
                    else
                    {
                        /* This call-back is still waiting for a reply or a time-out. */
                    }
                }
            }
            ( void ) xTaskResumeAll();

            if( pxKeepCallback != NULL )
            {
                pxKeepCallback->pCallbackFunction( pxKeepCallback->pcName, pxKeepCallback->pvSearchID, 0 );
                vTaskSuspendAll();
                {
                    ( void ) uxListRemove( &( pxKeepCallback->xListItem ) );
                }
                ( void ) xTaskResumeAll();

                vPortFree( pxKeepCallback );

                /* The do-while-loop will make a new iteration to see if
                 * there is another entry that has expired. */
            }
        } while( pxKeepCallback != NULL );

        if( listLIST_IS_EMPTY( &xCallbackList ) != pdFALSE )
        {
            vIPSetDNSTimerEnableState( pdFALSE );
        }
    }

/**
 * @brief initialize the cache
 * @post will modify global list xCallbackList
 */
    void vDNSCallbackInitialise()
    {
        vListInitialise( &xCallbackList );
    }
#endif /* if ( ipconfigDNS_USE_CALLBACKS == 1 ) */
