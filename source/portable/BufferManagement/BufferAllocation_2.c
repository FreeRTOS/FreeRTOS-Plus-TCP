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

/******************************************************************************
*
* See the following web page for essential buffer allocation scheme usage and
* configuration details:
* http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/Embedded_Ethernet_Buffer_Management.html
*
******************************************************************************/

/* THIS FILE SHOULD NOT BE USED IF THE PROJECT INCLUDES A MEMORY ALLOCATOR
 * THAT WILL FRAGMENT THE HEAP MEMORY.  For example, heap_2 must not be used,
 * heap_4 can be used. */

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"

/* The obtained network buffer must be large enough to hold a packet that might
 * replace the packet that was requested to be sent. */
#if (ipconfigUSE_TCP == 1)
    #define baMINIMAL_BUFFER_SIZE    sizeof( TCPPacket_t )
#else
    #define baMINIMAL_BUFFER_SIZE    sizeof( ARPPacket_t )
#endif /* ipconfigUSE_TCP == 1 */

/* Compile time assertion with zero runtime effects
 * it will assert on 'e' not being zero, as it tries to divide by it,
 * will also print the line where the error occured in case of failure */
/* MISRA Ref 20.10.1 [Lack of sizeof operator and compile time error checking] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-2010 */
/* coverity[misra_c_2012_rule_20_10_violation] */
#if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES )
    #define ASSERT_CONCAT_( a, b )    a ## b
    #define ASSERT_CONCAT( a, b )     ASSERT_CONCAT_( a, b )
    #define STATIC_ASSERT( e ) \
    ; enum { ASSERT_CONCAT( assert_line_, __LINE__ ) = 1 / ( !!( e ) ) }

    STATIC_ASSERT( ipconfigETHERNET_MINIMUM_PACKET_BYTES <= baMINIMAL_BUFFER_SIZE );
#endif

/* A list of free (available) NetworkBufferDescriptor_t structures. */
static List_t xFreeBuffersList;

/* Some statistics about the use of buffers. */
static UBaseType_t uxMinimumFreeNetworkBuffers = 0U;

/* This constant is defined as false to let FreeRTOS_TCP_IP.c know that the
 * network buffers have a variable size: resizing may be necessary */
const BaseType_t xBufferAllocFixedSize = pdFALSE;

/* The semaphore used to obtain network buffers. */
static SemaphoreHandle_t xNetworkBufferSemaphore = NULL;

#if ( ipconfigTCP_IP_SANITY != 0 )
    static char cIsLow = pdFALSE;
    UBaseType_t bIsValidNetworkDescriptor( const NetworkBufferDescriptor_t * pxDesc );
#else
    static UBaseType_t bIsValidNetworkDescriptor( const NetworkBufferDescriptor_t * pxDesc );
#endif /* ipconfigTCP_IP_SANITY */

static void prvShowWarnings( void );

/* The user can define their own ipconfigBUFFER_ALLOC_LOCK() and
 * ipconfigBUFFER_ALLOC_UNLOCK() macros, especially for use from an ISR.  If these
 * are not defined then default them to call the normal enter/exit critical
 * section macros. */
#if !defined( ipconfigBUFFER_ALLOC_LOCK )

    #define ipconfigBUFFER_ALLOC_INIT()    do {} while( ipFALSE_BOOL )
    #define ipconfigBUFFER_ALLOC_LOCK_FROM_ISR()                                            \
    UBaseType_t uxSavedInterruptStatus = ( UBaseType_t ) portSET_INTERRUPT_MASK_FROM_ISR(); \
    {
    #define ipconfigBUFFER_ALLOC_UNLOCK_FROM_ISR()               \
    portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus ); \
    }

    #define ipconfigBUFFER_ALLOC_LOCK()      taskENTER_CRITICAL()
    #define ipconfigBUFFER_ALLOC_UNLOCK()    taskEXIT_CRITICAL()

#endif /* ipconfigBUFFER_ALLOC_LOCK */

/*-----------------------------------------------------------*/

#if ( ipconfigTCP_IP_SANITY != 0 )

/* HT: SANITY code will be removed as soon as the library is stable
 * and and ready to become public
 * Function below gives information about the use of buffers */
    #define WARN_LOW     ( 2 )
    #define WARN_HIGH    ( ( 5 * ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ) / 10 )

#endif /* ipconfigTCP_IP_SANITY != 0 */

/*-----------------------------------------------------------*/

#if ( ipconfigTCP_IP_SANITY != 0 )

    BaseType_t prvIsFreeBuffer( const NetworkBufferDescriptor_t * pxDescr )
    {
        return ( bIsValidNetworkDescriptor( pxDescr ) != 0 ) &&
               ( listIS_CONTAINED_WITHIN( &xFreeBuffersList, &( pxDescr->xBufferListItem ) ) != 0 );
    }
    /*-----------------------------------------------------------*/

    static void prvShowWarnings( void )
    {
        UBaseType_t uxCount = uxGetNumberOfFreeNetworkBuffers();

        if( ( ( cIsLow == 0 ) && ( uxCount <= WARN_LOW ) ) || ( ( cIsLow != 0 ) && ( uxCount >= WARN_HIGH ) ) )
        {
            cIsLow = !cIsLow;
            FreeRTOS_debug_printf( ( "*** Warning *** %s %lu buffers left\n", cIsLow ? "only" : "now", uxCount ) );
        }
    }
    /*-----------------------------------------------------------*/

    UBaseType_t bIsValidNetworkDescriptor( const NetworkBufferDescriptor_t * pxDesc )
    {
        uint32_t offset = ( uint32_t ) ( ( ( const char * ) pxDesc ) - ( ( const char * ) xNetworkBuffers ) );

        if( ( offset >= sizeof( xNetworkBuffers ) ) ||
            ( ( offset % sizeof( xNetworkBuffers[ 0 ] ) ) != 0 ) )
        {
            return pdFALSE;
        }

        return ( UBaseType_t ) ( pxDesc - xNetworkBuffers ) + 1;
    }
    /*-----------------------------------------------------------*/

#else /* ipconfigTCP_IP_SANITY != 0 */
    static UBaseType_t bIsValidNetworkDescriptor( const NetworkBufferDescriptor_t * pxDesc )
    {
        ( void ) pxDesc;
        return ( UBaseType_t ) pdTRUE;
    }
    /*-----------------------------------------------------------*/

    static void prvShowWarnings( void )
    {
    }
    /*-----------------------------------------------------------*/

#endif /* ipconfigTCP_IP_SANITY != 0 */

/*-----------------------------------------------------------*/

BaseType_t xNetworkBuffersInitialise( void )
{
    /* Declares the pool of NetworkBufferDescriptor_t structures that are available
     * to the system.  All the network buffers referenced from xFreeBuffersList exist
     * in this array.  The array is not accessed directly except during initialisation,
     * when the xFreeBuffersList is filled (as all the buffers are free when the system
     * is booted). */
    static NetworkBufferDescriptor_t xNetworkBufferDescriptors[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ];
    BaseType_t xReturn;

    /* Only initialise the buffers and their associated kernel objects if they
     * have not been initialised before. */
    if( xNetworkBufferSemaphore == NULL )
    {
        /* In case alternative locking is used, the mutexes can be initialised
         * here */
        ipconfigBUFFER_ALLOC_INIT();

        #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
            {
                static StaticSemaphore_t xNetworkBufferSemaphoreBuffer;
                xNetworkBufferSemaphore = xSemaphoreCreateCountingStatic(
                    ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS,
                    ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS,
                    &xNetworkBufferSemaphoreBuffer );
            }
        #else
            {
                xNetworkBufferSemaphore = xSemaphoreCreateCounting( ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS, ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS );
            }
        #endif /* configSUPPORT_STATIC_ALLOCATION == 1 */

        configASSERT( xNetworkBufferSemaphore != NULL );

        if( xNetworkBufferSemaphore != NULL )
        {
            #if ( configQUEUE_REGISTRY_SIZE > 0 )
                {
                    vQueueAddToRegistry( xNetworkBufferSemaphore, "NetBufSem" );
                }
            #endif /* configQUEUE_REGISTRY_SIZE > 0 */

            /* If the trace recorder code is included name the semaphore for viewing
             * in FreeRTOS+Trace.  */
            #if ( ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS == 1 )
                {
                    extern QueueHandle_t xNetworkEventQueue;
                    vTraceSetQueueName( xNetworkEventQueue, "IPStackEvent" );
                    vTraceSetQueueName( xNetworkBufferSemaphore, "NetworkBufferCount" );
                }
            #endif /*  ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS == 1 */

            vListInitialise( &xFreeBuffersList );

            /* Initialise all the network buffers.  No storage is allocated to
             * the buffers yet. */
            for( uint32_t x = 0U; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++ )
            {
                /* Initialise and set the owner of the buffer list items. */
                xNetworkBufferDescriptors[ x ].pucEthernetBuffer = NULL;
                vListInitialiseItem( &( xNetworkBufferDescriptors[ x ].xBufferListItem ) );
                listSET_LIST_ITEM_OWNER( &( xNetworkBufferDescriptors[ x ].xBufferListItem ), &xNetworkBufferDescriptors[ x ] );

                /* Currently, all buffers are available for use. */
                vListInsert( &xFreeBuffersList, &( xNetworkBufferDescriptors[ x ].xBufferListItem ) );
            }

            uxMinimumFreeNetworkBuffers = ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
        }
    }

    if( xNetworkBufferSemaphore == NULL )
    {
        xReturn = pdFAIL;
    }
    else
    {
        xReturn = pdPASS;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    NetworkBufferDescriptor_t * pxReturn = NULL;
    UBaseType_t uxCount;
    BaseType_t xInvalid = pdFALSE;

    if( ( xNetworkBufferSemaphore != NULL ) && ( xRequestedSizeBytes <= ( SIZE_MAX >> 1 ) ) )
    {
        /* If there is a semaphore available, there is a network buffer available. */
        if( xSemaphoreTake( xNetworkBufferSemaphore, xBlockTimeTicks ) == pdPASS )
        {
            /* Protect the structure as it is accessed from tasks and interrupts. */
            ipconfigBUFFER_ALLOC_LOCK();
            {
                pxReturn = ( NetworkBufferDescriptor_t * ) listGET_OWNER_OF_HEAD_ENTRY( &xFreeBuffersList );

                if( ( bIsValidNetworkDescriptor( pxReturn ) != pdFALSE_UNSIGNED ) &&
                    listIS_CONTAINED_WITHIN( &xFreeBuffersList, &( pxReturn->xBufferListItem ) ) )
                {
                    ( void ) uxListRemove( &( pxReturn->xBufferListItem ) );
                }
                else
                {
                    xInvalid = pdTRUE;
                }
            }
            ipconfigBUFFER_ALLOC_UNLOCK();

            if( xInvalid == pdTRUE )
            {
                FreeRTOS_debug_printf( ( "pxGetNetworkBufferWithDescriptor: INVALID BUFFER: %p (valid %lu)\n",
                                         pxReturn, bIsValidNetworkDescriptor( pxReturn ) ) );
                pxReturn = NULL;
            }
            else
            {
                /* Reading UBaseType_t, no critical section needed. */
                uxCount = listCURRENT_LIST_LENGTH( &xFreeBuffersList );

                /* For stats, latch the lowest number of network buffers since booting. */
                if( uxMinimumFreeNetworkBuffers > uxCount )
                {
                    uxMinimumFreeNetworkBuffers = uxCount;
                }

                /* Allocate storage of exactly the requested size to the buffer. */
                configASSERT( pxReturn->pucEthernetBuffer == NULL );

                if( xRequestedSizeBytes > 0U )
                {
                    if( ( xRequestedSizeBytes < ( size_t ) baMINIMAL_BUFFER_SIZE ) )
                    {
                        /* ARP packets can replace application packets, so the storage must be
                         * at least large enough to hold an ARP. */
                        xRequestedSizeBytes = baMINIMAL_BUFFER_SIZE;
                    }

                    /* Add 2 bytes to xRequestedSizeBytes and round up xRequestedSizeBytes
                     * to the nearest multiple of N bytes, where N equals 'sizeof( size_t )'. */
                    xRequestedSizeBytes += 2U;

                    if( ( xRequestedSizeBytes & ( sizeof( size_t ) - 1U ) ) != 0U )
                    {
                        xRequestedSizeBytes = ( xRequestedSizeBytes | ( sizeof( size_t ) - 1U ) ) + 1U;
                    }

                    /* Extra space is obtained so a pointer to the network buffer can
                     * be stored at the beginning of the buffer. */
                    pxReturn->pucEthernetBuffer = ( uint8_t * ) pvPortMalloc( xRequestedSizeBytes + ipBUFFER_PADDING );

                    if( pxReturn->pucEthernetBuffer == NULL )
                    {
                        /* The attempt to allocate storage for the buffer payload failed,
                         * so the network buffer structure cannot be used and must be
                         * released. */
                        vReleaseNetworkBufferAndDescriptor( pxReturn );
                        pxReturn = NULL;
                    }
                    else
                    {
                        /* Store a pointer to the network buffer structure in the
                         * buffer storage area, then move the buffer pointer on past the
                         * stored pointer so the pointer value is not overwritten by the
                         * application when the buffer is used. */
                        /* MISRA Ref 11.3.1 [Misaligned access] */
                        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                        /* coverity[misra_c_2012_rule_11_3_violation] */
                        *( ( NetworkBufferDescriptor_t ** ) ( pxReturn->pucEthernetBuffer ) ) = pxReturn;
                        pxReturn->pucEthernetBuffer += ipBUFFER_PADDING;

                        /* Store the actual size of the allocated buffer, which may be
                         * greater than the original requested size. */
                        pxReturn->xDataLength = xRequestedSizeBytes;

                        #if ( ipconfigTCP_IP_SANITY != 0 )
                            {
                                prvShowWarnings();
                            }
                        #endif /* ipconfigTCP_IP_SANITY != 0 */

                        #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
                            {
                                /* make sure the buffer is not linked */
                                pxReturn->pxNextBuffer = NULL;
                            }
                        #endif /* ipconfigUSE_LINKED_RX_MESSAGES != 0 */
                    }
                }
                else
                {
                    /* A descriptor is being returned without an associated buffer being
                     * allocated. */
                }
            }
        }
    }

    if( pxReturn == NULL )
    {
        iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER();
    }
    else
    {
        /* No action. */
        iptraceNETWORK_BUFFER_OBTAINED( pxReturn );
    }

    return pxReturn;
}
/*-----------------------------------------------------------*/

void vReleaseNetworkBufferAndDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    BaseType_t xListItemAlreadyInFreeList;

    if( bIsValidNetworkDescriptor( pxNetworkBuffer ) == pdFALSE_UNSIGNED )
    {
        FreeRTOS_debug_printf( ( "vReleaseNetworkBufferAndDescriptor: Invalid buffer %p\n", pxNetworkBuffer ) );
    }
    else
    {
        /* Ensure the buffer is returned to the list of free buffers before the
         * counting semaphore is 'given' to say a buffer is available.  Release the
         * storage allocated to the buffer payload. */
        vReleaseNetworkBuffer( pxNetworkBuffer->pucEthernetBuffer );
        pxNetworkBuffer->pucEthernetBuffer = NULL;
        pxNetworkBuffer->xDataLength = 0U;

        ipconfigBUFFER_ALLOC_LOCK();
        {
            xListItemAlreadyInFreeList = listIS_CONTAINED_WITHIN( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );

            if( xListItemAlreadyInFreeList == pdFALSE )
            {
                vListInsertEnd( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );
            }
        }
        ipconfigBUFFER_ALLOC_UNLOCK();

        /* Update the network state machine, unless the program fails to release its 'xNetworkBufferSemaphore'.
         * The program should only try to release its semaphore if 'xListItemAlreadyInFreeList' is false. */
        if( xListItemAlreadyInFreeList == pdFALSE )
        {
            if( xSemaphoreGive( xNetworkBufferSemaphore ) == pdTRUE )
            {
                iptraceNETWORK_BUFFER_RELEASED( pxNetworkBuffer );
            }
            prvShowWarnings();
        }
        else
        {
            FreeRTOS_debug_printf( ( "vReleaseNetworkBufferAndDescriptor: %p ALREADY RELEASED (now %lu)\n",
                                     pxNetworkBuffer, uxGetNumberOfFreeNetworkBuffers() ) );
            iptraceNETWORK_BUFFER_RELEASED( pxNetworkBuffer );
            prvShowWarnings();
        }
    }
}
/*-----------------------------------------------------------*/

UBaseType_t uxGetMinimumFreeNetworkBuffers( void )
{
    return uxMinimumFreeNetworkBuffers;
}
/*-----------------------------------------------------------*/

/* Returns the number of free network buffers */
UBaseType_t uxGetNumberOfFreeNetworkBuffers( void )
{
    return listCURRENT_LIST_LENGTH( &xFreeBuffersList );
}
/*-----------------------------------------------------------*/

NetworkBufferDescriptor_t * pxResizeNetworkBufferWithDescriptor( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                                 size_t xNewSizeBytes )
{
    size_t xOriginalLength;
    uint8_t * pucBuffer;
    size_t uxSizeBytes = xNewSizeBytes;
    NetworkBufferDescriptor_t * pxNetworkBufferCopy = pxNetworkBuffer;

    xOriginalLength = pxNetworkBufferCopy->xDataLength + ipBUFFER_PADDING;
    uxSizeBytes = uxSizeBytes + ipBUFFER_PADDING;

    pucBuffer = pucGetNetworkBuffer( &( uxSizeBytes ) );

    if( pucBuffer == NULL )
    {
        /* In case the allocation fails, return NULL. */
        pxNetworkBufferCopy = NULL;
    }
    else
    {
        pxNetworkBufferCopy->xDataLength = uxSizeBytes;

        if( uxSizeBytes > xOriginalLength )
        {
            uxSizeBytes = xOriginalLength;
        }

        ( void ) memcpy( pucBuffer - ipBUFFER_PADDING,
                         pxNetworkBufferCopy->pucEthernetBuffer - ipBUFFER_PADDING,
                         uxSizeBytes );
        vReleaseNetworkBuffer( pxNetworkBufferCopy->pucEthernetBuffer );
        pxNetworkBufferCopy->pucEthernetBuffer = pucBuffer;
    }

    return pxNetworkBufferCopy;
}
/*-----------------------------------------------------------*/

uint8_t * pucGetNetworkBuffer( size_t * pxRequestedSizeBytes )
{
    uint8_t * pucEthernetBuffer;
    size_t xSize = *pxRequestedSizeBytes;

    if( xSize < baMINIMAL_BUFFER_SIZE )
    {
        /* Buffers must be at least large enough to hold a TCP-packet with
         * headers, or an ARP packet, in case TCP is not included. */
        xSize = baMINIMAL_BUFFER_SIZE;
    }

    /* Round up xSize to the nearest multiple of N bytes,
     * where N equals 'sizeof( size_t )'. */
    if( ( xSize & ( sizeof( size_t ) - 1U ) ) != 0U )
    {
        xSize = ( xSize | ( sizeof( size_t ) - 1U ) ) + 1U;
    }

    *pxRequestedSizeBytes = xSize;

    /* Allocate a buffer large enough to store the requested Ethernet frame size
     * and a pointer to a network buffer structure (hence the addition of
     * ipBUFFER_PADDING bytes). */
    pucEthernetBuffer = ( uint8_t * ) pvPortMalloc( xSize + ipBUFFER_PADDING );
    configASSERT( pucEthernetBuffer != NULL );

    if( pucEthernetBuffer != NULL )
    {
        /* Enough space is left at the start of the buffer to place a pointer to
         * the network buffer structure that references this Ethernet buffer.
         * Return a pointer to the start of the Ethernet buffer itself. */
        pucEthernetBuffer += ipBUFFER_PADDING;
    }

    return pucEthernetBuffer;
}
/*-----------------------------------------------------------*/

void vReleaseNetworkBuffer( uint8_t * pucEthernetBuffer )
{
    uint8_t * pucEthernetBufferCopy = pucEthernetBuffer;

    /* There is space before the Ethernet buffer in which a pointer to the
     * network buffer that references this Ethernet buffer is stored.  Remove the
     * space before freeing the buffer. */
    if( pucEthernetBufferCopy != NULL )
    {
        pucEthernetBufferCopy -= ipBUFFER_PADDING;
        vPortFree( ( void * ) pucEthernetBufferCopy );
    }
}
