/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Copyright 2023-2024 Arm Limited and/or its affiliates
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
 * https://github.com/FreeRTOS
 * https://www.FreeRTOS.org
 */

/* Standard library includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

#if ( cmsisETH_USE_TX_COMPLETE_EVENT != 0 )
    #include "semphr.h"
#endif

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

/* CMSIS Ethernet driver includes. */
#include "Driver_ETH_MAC.h"
#include "Driver_ETH_PHY.h"

/*
 * This is a generic template for CMSIS Ethernet MAC/PHY drivers.
 *
 * CMSIS Ethernet APIs pass frames via copy semantics (ReadFrame/SendFrame),
 * therefore this template is intended for non-zero-copy operation.
 */
#if ( ipconfigZERO_COPY_TX_DRIVER != 0 ) || ( ipconfigZERO_COPY_RX_DRIVER != 0 )
    #error "The CMSIS template expects copy-based MAC drivers. Set zero-copy to 0."
#endif

/*-----------------------------------------------------------*/
/* Configuration macros with defaults.                       */
/*-----------------------------------------------------------*/

#ifndef cmsisETH_MAX_INSTANCES
    #define cmsisETH_MAX_INSTANCES    1
#endif

#ifndef cmsisETH_USE_TX_COMPLETE_EVENT
    #define cmsisETH_USE_TX_COMPLETE_EVENT    0
#endif

#ifndef cmsisETH_PHY_LINK_CHANGE_NOTIFICATION
    #define cmsisETH_PHY_LINK_CHANGE_NOTIFICATION    0
#endif

#ifndef cmsisETH_MAX_MAC_FILTER_ENTRIES
    #define cmsisETH_MAX_MAC_FILTER_ENTRIES    0
#endif

/* Allow selection of CMSIS driver instances (single-instance mode only). */
#if ( cmsisETH_MAX_INSTANCES == 1 )
    #ifndef cmsisETH_MAC_DRIVER_INSTANCE
        #define cmsisETH_MAC_DRIVER_INSTANCE    0
    #endif

    #ifndef cmsisETH_PHY_DRIVER_INSTANCE
        #define cmsisETH_PHY_DRIVER_INSTANCE    0
    #endif
#endif /* cmsisETH_MAX_INSTANCES == 1 */

/* Optional template tuning macros. */
#ifndef cmsisETH_RX_TASK_STACK_SIZE
    #define cmsisETH_RX_TASK_STACK_SIZE    ( configMINIMAL_STACK_SIZE * 2 )
#endif

#ifndef cmsisETH_RX_TASK_PRIORITY
    #define cmsisETH_RX_TASK_PRIORITY      ( tskIDLE_PRIORITY + 4 )
#endif

#ifndef cmsisETH_RX_TASK_BLOCK_TIME_MS
    #define cmsisETH_RX_TASK_BLOCK_TIME_MS    100U
#endif

#ifndef cmsisETH_LINK_CHECK_INTERVAL_MS
    #define cmsisETH_LINK_CHECK_INTERVAL_MS    1000U
#endif

#ifndef cmsisETH_MAX_FRAME_SIZE
    #define cmsisETH_MAX_FRAME_SIZE    1536U
#endif

#ifndef cmsisETH_PHY_MODE
    #define cmsisETH_PHY_MODE    ARM_ETH_PHY_AUTO_NEGOTIATE
#endif

#ifndef cmsisETH_MAC_CONTROL_FLAGS
    #define cmsisETH_MAC_CONTROL_FLAGS    ARM_ETH_MAC_ADDRESS_BROADCAST
#endif

#ifndef cmsisETH_TX_RETRY_COUNT
    #define cmsisETH_TX_RETRY_COUNT    2U
#endif

#ifndef cmsisETH_TX_RETRY_DELAY_MS
    #define cmsisETH_TX_RETRY_DELAY_MS    1U
#endif

#ifndef cmsisETH_TX_COMPLETE_TIMEOUT_MS
    #define cmsisETH_TX_COMPLETE_TIMEOUT_MS    50U
#endif

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
 * driver will filter incoming packets and only pass the stack those packets it
 * considers need processing. */
#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
    #define cmsisCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
    #define cmsisCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/*-----------------------------------------------------------*/
/* PHY link-change notification bits.                        */
/*-----------------------------------------------------------*/

#if ( cmsisETH_PHY_LINK_CHANGE_NOTIFICATION != 0 )
    #define cmsisETH_NOTIFY_RX_FRAME      ( 1UL << 0 )
    #define cmsisETH_NOTIFY_LINK_CHANGE   ( 1UL << 1 )
#endif

/*-----------------------------------------------------------*/
/* Instance limit guard.                                     */
/*-----------------------------------------------------------*/

#if ( cmsisETH_MAX_INSTANCES > 4 )
    #error "cmsisETH_MAX_INSTANCES must be <= 4 (ISR trampoline limit)."
#endif

/*-----------------------------------------------------------*/
/* Types.                                                    */
/*-----------------------------------------------------------*/

typedef enum xEMAC_STATE
{
    xEMAC_Init = 0,
    xEMAC_WaitPHY,
    xEMAC_Ready,
    xEMAC_Fatal
} EMACState_t;

typedef struct xCMSISEthernetInterface
{
    ARM_DRIVER_ETH_MAC * pxEthernetMACDriver;
    ARM_DRIVER_ETH_PHY * pxEthernetPHYDriver;
    ARM_ETH_MAC_CAPABILITIES xMACCapabilities;
    ARM_ETH_LINK_STATE eEthernetLinkState;
    EMACState_t eEMACState;
    TaskHandle_t xRxTaskHandle;
    NetworkInterface_t * pxMyInterface;
    BaseType_t xIndex;
    char pcName[ 8 ];

    #if ( cmsisETH_USE_TX_COMPLETE_EVENT != 0 )
        SemaphoreHandle_t xTxCompleteSemaphore;
    #endif

    #if ( cmsisETH_MAX_MAC_FILTER_ENTRIES > 0 )
        ARM_ETH_MAC_ADDR xMACFilterTable[ cmsisETH_MAX_MAC_FILTER_ENTRIES ];
        uint8_t ucMACFilterRefCount[ cmsisETH_MAX_MAC_FILTER_ENTRIES ];
        uint32_t ulMACFilterCount;
    #endif
} CMSISEthernetInterface_t;

/*-----------------------------------------------------------*/
/* External driver references.                               */
/*-----------------------------------------------------------*/

#if ( cmsisETH_MAX_INSTANCES == 1 )
    extern ARM_DRIVER_ETH_MAC ARM_Driver_ETH_MAC_( cmsisETH_MAC_DRIVER_INSTANCE );
    extern ARM_DRIVER_ETH_PHY ARM_Driver_ETH_PHY_( cmsisETH_PHY_DRIVER_INSTANCE );
#else
    extern ARM_DRIVER_ETH_MAC * const pxCMSIS_MACDrivers[ cmsisETH_MAX_INSTANCES ];
    extern ARM_DRIVER_ETH_PHY * const pxCMSIS_PHYDrivers[ cmsisETH_MAX_INSTANCES ];
#endif

/*-----------------------------------------------------------*/
/* Forward declarations.                                     */
/*-----------------------------------------------------------*/

static void prvRxTask( void * pvParameters );
static void prvProcessReceivedPackets( CMSISEthernetInterface_t * pxCtx );
static void prvCheckEthernetLinkStatus( CMSISEthernetInterface_t * pxCtx );
static void prvUninitialiseDrivers( CMSISEthernetInterface_t * pxCtx,
                                    BaseType_t xPHYInitialised,
                                    BaseType_t xMACPowered );
static void prvEthernetDriverNotificationsCommon( CMSISEthernetInterface_t * pxCtx,
                                                  uint32_t ulEvent );

static BaseType_t xCMSIS_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface );
static BaseType_t xCMSIS_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                 NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                 BaseType_t bReleaseAfterSend );
static BaseType_t xCMSIS_GetPhyLinkStatus( NetworkInterface_t * pxInterface );

NetworkInterface_t * pxCMSIS_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                      NetworkInterface_t * pxInterface );

#if ( cmsisETH_MAX_MAC_FILTER_ENTRIES > 0 )
    static void prvAddAllowedMACAddress( struct xNetworkInterface * pxInterface,
                                         const uint8_t * pucMacAddress );
    static void prvRemoveAllowedMACAddress( struct xNetworkInterface * pxInterface,
                                            const uint8_t * pucMacAddress );
#endif

/*-----------------------------------------------------------*/
/* Instance array.                                           */
/*-----------------------------------------------------------*/

static CMSISEthernetInterface_t xInstances[ cmsisETH_MAX_INSTANCES ];

/*-----------------------------------------------------------*/
/* Context retrieval helper.                                 */
/*-----------------------------------------------------------*/

static inline CMSISEthernetInterface_t * prvGetContext( const NetworkInterface_t * pxInterface )
{
    return ( CMSISEthernetInterface_t * ) pxInterface->pvArgument;
}

/*-----------------------------------------------------------*/
/* ISR callback trampolines.                                 */
/* CMSIS MAC callback has no user-data parameter, so we need */
/* per-instance trampolines that forward to a common handler.*/
/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
#define DEFINE_ETH_CALLBACK( n )                                            \
    static void prvEthernetCallback_ ## n( uint32_t ulEvent )               \
    {                                                                       \
        prvEthernetDriverNotificationsCommon( &xInstances[ n ], ulEvent );  \
    }
/* *INDENT-ON* */

DEFINE_ETH_CALLBACK( 0 )

#if ( cmsisETH_MAX_INSTANCES > 1 )
    DEFINE_ETH_CALLBACK( 1 )
#endif

#if ( cmsisETH_MAX_INSTANCES > 2 )
    DEFINE_ETH_CALLBACK( 2 )
#endif

#if ( cmsisETH_MAX_INSTANCES > 3 )
    DEFINE_ETH_CALLBACK( 3 )
#endif

static ARM_ETH_MAC_SignalEvent_t prvCallbackTable[ cmsisETH_MAX_INSTANCES ] =
{
    prvEthernetCallback_0
    #if ( cmsisETH_MAX_INSTANCES > 1 )
        , prvEthernetCallback_1
    #endif
    #if ( cmsisETH_MAX_INSTANCES > 2 )
        , prvEthernetCallback_2
    #endif
    #if ( cmsisETH_MAX_INSTANCES > 3 )
        , prvEthernetCallback_3
    #endif
};

/*-----------------------------------------------------------*/

static void prvEthernetDriverNotificationsCommon( CMSISEthernetInterface_t * pxCtx,
                                                  uint32_t ulEvent )
{
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    if( ( ulEvent & ARM_ETH_MAC_EVENT_RX_FRAME ) != 0U )
    {
        if( pxCtx->xRxTaskHandle != NULL )
        {
            #if ( cmsisETH_PHY_LINK_CHANGE_NOTIFICATION != 0 )
                ( void ) xTaskNotifyFromISR( pxCtx->xRxTaskHandle,
                                             cmsisETH_NOTIFY_RX_FRAME,
                                             eSetBits,
                                             &xHigherPriorityTaskWoken );
            #else
                vTaskNotifyGiveFromISR( pxCtx->xRxTaskHandle, &xHigherPriorityTaskWoken );
            #endif
        }
    }

    #if ( cmsisETH_USE_TX_COMPLETE_EVENT != 0 )
        if( ( ulEvent & ARM_ETH_MAC_EVENT_TX_FRAME ) != 0U )
        {
            if( pxCtx->xTxCompleteSemaphore != NULL )
            {
                ( void ) xSemaphoreGiveFromISR( pxCtx->xTxCompleteSemaphore,
                                                &xHigherPriorityTaskWoken );
            }
        }
    #endif

    #if defined( portYIELD_FROM_ISR )
        portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
    #elif defined( portEND_SWITCHING_ISR )
        portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
    #else
        ( void ) xHigherPriorityTaskWoken;
    #endif
}

/*-----------------------------------------------------------*/

#if ( cmsisETH_PHY_LINK_CHANGE_NOTIFICATION != 0 )
    void vCMSIS_PHYLinkChangeNotify( BaseType_t xInterfaceIndex )
    {
        BaseType_t xHigherPriorityTaskWoken = pdFALSE;

        configASSERT( ( xInterfaceIndex >= 0 ) && ( xInterfaceIndex < ( BaseType_t ) cmsisETH_MAX_INSTANCES ) );

        if( xInstances[ xInterfaceIndex ].xRxTaskHandle != NULL )
        {
            ( void ) xTaskNotifyFromISR( xInstances[ xInterfaceIndex ].xRxTaskHandle,
                                         cmsisETH_NOTIFY_LINK_CHANGE,
                                         eSetBits,
                                         &xHigherPriorityTaskWoken );

            #if defined( portYIELD_FROM_ISR )
                portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
            #elif defined( portEND_SWITCHING_ISR )
                portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
            #else
                ( void ) xHigherPriorityTaskWoken;
            #endif
        }
    }
#endif /* cmsisETH_PHY_LINK_CHANGE_NOTIFICATION */

/*-----------------------------------------------------------*/

static void prvCheckEthernetLinkStatus( CMSISEthernetInterface_t * pxCtx )
{
    const ARM_ETH_LINK_STATE eCurrentLinkState = pxCtx->pxEthernetPHYDriver->GetLinkState();
    IPStackEvent_t xRxEvent;

    if( eCurrentLinkState == pxCtx->eEthernetLinkState )
    {
        return;
    }

    pxCtx->eEthernetLinkState = eCurrentLinkState;

    if( eCurrentLinkState == ARM_ETH_LINK_DOWN )
    {
        FreeRTOS_printf( ( "NetworkInterface: Ethernet link is down\n" ) );

        if( pxCtx->eEMACState == xEMAC_Ready )
        {
            ( void ) pxCtx->pxEthernetMACDriver->Control( ARM_ETH_MAC_CONTROL_TX, 0U );
            ( void ) pxCtx->pxEthernetMACDriver->Control( ARM_ETH_MAC_CONTROL_RX, 0U );
            ( void ) pxCtx->pxEthernetPHYDriver->Uninitialize();
            ( void ) pxCtx->pxEthernetMACDriver->Uninitialize();
        }

        pxCtx->eEMACState = xEMAC_Init;

        if( pxCtx->pxMyInterface != NULL )
        {
            xRxEvent.eEventType = eNetworkDownEvent;
            xRxEvent.pvData = ( void * ) pxCtx->pxMyInterface;
            ( void ) xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0 );
        }
    }
    else
    {
        FreeRTOS_printf( ( "NetworkInterface: Ethernet link is up\n" ) );
    }
}

/*-----------------------------------------------------------*/

static void prvRxTask( void * pvParameters )
{
    CMSISEthernetInterface_t * pxCtx = ( CMSISEthernetInterface_t * ) pvParameters;

    for( ; ; )
    {
        #if ( cmsisETH_PHY_LINK_CHANGE_NOTIFICATION != 0 )
        {
            uint32_t ulNotificationValue = 0U;
            ( void ) xTaskNotifyWait( 0U,
                                      UINT32_MAX,
                                      &ulNotificationValue,
                                      pdMS_TO_TICKS( cmsisETH_RX_TASK_BLOCK_TIME_MS ) );

            if( ( ulNotificationValue & cmsisETH_NOTIFY_RX_FRAME ) != 0U )
            {
                prvProcessReceivedPackets( pxCtx );
            }

            if( ( ( ulNotificationValue & cmsisETH_NOTIFY_LINK_CHANGE ) != 0U ) ||
                ( ulNotificationValue == 0U ) )
            {
                prvCheckEthernetLinkStatus( pxCtx );
            }
        }
        #else
        {
            ( void ) ulTaskNotifyTake( pdTRUE, pdMS_TO_TICKS( cmsisETH_RX_TASK_BLOCK_TIME_MS ) );
            prvProcessReceivedPackets( pxCtx );
            prvCheckEthernetLinkStatus( pxCtx );
        }
        #endif
    }
}

/*-----------------------------------------------------------*/

static void prvProcessReceivedPackets( CMSISEthernetInterface_t * pxCtx )
{
    const TickType_t xDescriptorWaitTime = 0U;
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };

    for( ; ; )
    {
        const uint32_t ulMessageLength = pxCtx->pxEthernetMACDriver->GetRxFrameSize();
        NetworkBufferDescriptor_t * pxNetworkBuffer = NULL;
        int32_t lReceivedBytes;

        if( ulMessageLength == 0U )
        {
            break;
        }

        if( ulMessageLength == 0xFFFFFFFFU )
        {
            FreeRTOS_debug_printf( ( "NetworkInterface: GetRxFrameSize driver error, flushing\n" ) );
            ( void ) pxCtx->pxEthernetMACDriver->ReadFrame( NULL, 0U );
            continue;
        }

        if( ( ulMessageLength < ipSIZE_OF_ETH_HEADER ) || ( ulMessageLength > cmsisETH_MAX_FRAME_SIZE ) )
        {
            FreeRTOS_debug_printf( ( "NetworkInterface: drop invalid frame length %lu\n", ( unsigned long ) ulMessageLength ) );
            ( void ) pxCtx->pxEthernetMACDriver->ReadFrame( NULL, 0U );
            continue;
        }

        pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( ulMessageLength, xDescriptorWaitTime );

        if( pxNetworkBuffer == NULL )
        {
            FreeRTOS_debug_printf( ( "NetworkInterface: drop frame, no network buffer\n" ) );
            ( void ) pxCtx->pxEthernetMACDriver->ReadFrame( NULL, 0U );
            continue;
        }

        lReceivedBytes = pxCtx->pxEthernetMACDriver->ReadFrame( pxNetworkBuffer->pucEthernetBuffer, ulMessageLength );

        if( lReceivedBytes <= 0 )
        {
            FreeRTOS_debug_printf( ( "NetworkInterface: ReadFrame returned %ld\n", ( long ) lReceivedBytes ) );
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
            continue;
        }

        pxNetworkBuffer->xDataLength = ( size_t ) lReceivedBytes;

        if( cmsisCONSIDER_FRAME_FOR_PROCESSING( pxNetworkBuffer->pucEthernetBuffer ) != eProcessBuffer )
        {
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
            continue;
        }

        pxNetworkBuffer->pxInterface = pxCtx->pxMyInterface;
        pxNetworkBuffer->pxEndPoint = FreeRTOS_MatchingEndpoint( pxCtx->pxMyInterface, pxNetworkBuffer->pucEthernetBuffer );

        if( pxNetworkBuffer->pxEndPoint == NULL )
        {
            FreeRTOS_debug_printf( ( "NetworkInterface: no matching endpoint for received frame\n" ) );
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
            continue;
        }

        xRxEvent.pvData = ( void * ) pxNetworkBuffer;

        if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0 ) == pdFAIL )
        {
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
        }
    }
}

/*-----------------------------------------------------------*/

static void prvUninitialiseDrivers( CMSISEthernetInterface_t * pxCtx,
                                    BaseType_t xPHYInitialised,
                                    BaseType_t xMACPowered )
{
    if( xPHYInitialised == pdTRUE )
    {
        ( void ) pxCtx->pxEthernetPHYDriver->Uninitialize();
    }

    if( xMACPowered == pdTRUE )
    {
        ( void ) pxCtx->pxEthernetMACDriver->PowerControl( ARM_POWER_OFF );
    }

    ( void ) pxCtx->pxEthernetMACDriver->Uninitialize();
}

/*-----------------------------------------------------------*/

static BaseType_t xCMSIS_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    CMSISEthernetInterface_t * pxCtx = prvGetContext( pxInterface );
    BaseType_t xReturn = pdFAIL;
    BaseType_t xTaskReturn;
    int32_t lDriverReturn = ARM_DRIVER_ERROR;
    uint32_t ulMACControlArg = 0U;
    ARM_ETH_LINK_INFO xEthernetLinkInfo;

    BaseType_t xContinue = pdTRUE;

    while( xContinue == pdTRUE )
    {
        xContinue = pdFALSE;

        switch( pxCtx->eEMACState )
        {
            case xEMAC_Init:
                lDriverReturn = pxCtx->pxEthernetMACDriver->Initialize( prvCallbackTable[ pxCtx->xIndex ] );

                if( lDriverReturn != ARM_DRIVER_OK )
                {
                    pxCtx->eEMACState = xEMAC_Fatal;
                    FreeRTOS_printf( ( "NetworkInterface: failed to initialize MAC driver: %ld\n", ( long ) lDriverReturn ) );
                    break;
                }

                lDriverReturn = pxCtx->pxEthernetMACDriver->PowerControl( ARM_POWER_FULL );

                if( lDriverReturn != ARM_DRIVER_OK )
                {
                    pxCtx->eEMACState = xEMAC_Fatal;
                    ( void ) pxCtx->pxEthernetMACDriver->Uninitialize();
                    FreeRTOS_printf( ( "NetworkInterface: failed to set MAC power: %ld\n", ( long ) lDriverReturn ) );
                    break;
                }

                pxCtx->xMACCapabilities = pxCtx->pxEthernetMACDriver->GetCapabilities();

                configASSERT( pxInterface->pxEndPoint != NULL );
                lDriverReturn = pxCtx->pxEthernetMACDriver->SetMacAddress( ( ARM_ETH_MAC_ADDR * ) &pxInterface->pxEndPoint->xMACAddress );

                if( lDriverReturn != ARM_DRIVER_OK )
                {
                    pxCtx->eEMACState = xEMAC_Fatal;
                    prvUninitialiseDrivers( pxCtx, pdFALSE, pdTRUE );
                    FreeRTOS_printf( ( "NetworkInterface: failed to set MAC address: %ld\n", ( long ) lDriverReturn ) );
                    break;
                }

                lDriverReturn = pxCtx->pxEthernetPHYDriver->Initialize(
                    pxCtx->pxEthernetMACDriver->PHY_Read,
                    pxCtx->pxEthernetMACDriver->PHY_Write );

                if( lDriverReturn != ARM_DRIVER_OK )
                {
                    pxCtx->eEMACState = xEMAC_Fatal;
                    prvUninitialiseDrivers( pxCtx, pdFALSE, pdTRUE );
                    FreeRTOS_printf( ( "NetworkInterface: failed to initialize PHY driver: %ld\n", ( long ) lDriverReturn ) );
                    break;
                }

                lDriverReturn = pxCtx->pxEthernetPHYDriver->PowerControl( ARM_POWER_FULL );

                if( lDriverReturn != ARM_DRIVER_OK )
                {
                    pxCtx->eEMACState = xEMAC_Fatal;
                    prvUninitialiseDrivers( pxCtx, pdTRUE, pdTRUE );
                    FreeRTOS_printf( ( "NetworkInterface: failed to set PHY power: %ld\n", ( long ) lDriverReturn ) );
                    break;
                }

                lDriverReturn = pxCtx->pxEthernetPHYDriver->SetInterface( pxCtx->xMACCapabilities.media_interface );

                if( lDriverReturn != ARM_DRIVER_OK )
                {
                    pxCtx->eEMACState = xEMAC_Fatal;
                    prvUninitialiseDrivers( pxCtx, pdTRUE, pdTRUE );
                    FreeRTOS_printf( ( "NetworkInterface: failed to set PHY interface: %ld\n", ( long ) lDriverReturn ) );
                    break;
                }

                lDriverReturn = pxCtx->pxEthernetPHYDriver->SetMode( cmsisETH_PHY_MODE );

                if( lDriverReturn != ARM_DRIVER_OK )
                {
                    pxCtx->eEMACState = xEMAC_Fatal;
                    prvUninitialiseDrivers( pxCtx, pdTRUE, pdTRUE );
                    FreeRTOS_printf( ( "NetworkInterface: failed to set PHY mode: %ld\n", ( long ) lDriverReturn ) );
                    break;
                }

                pxCtx->eEMACState = xEMAC_WaitPHY;
                xContinue = pdTRUE;
                break;

            case xEMAC_WaitPHY:
                vTaskDelay( pdMS_TO_TICKS( cmsisETH_LINK_CHECK_INTERVAL_MS ) );

                pxCtx->eEthernetLinkState = pxCtx->pxEthernetPHYDriver->GetLinkState();

                if( pxCtx->eEthernetLinkState == ARM_ETH_LINK_DOWN )
                {
                    break;
                }

                xEthernetLinkInfo = pxCtx->pxEthernetPHYDriver->GetLinkInfo();
                ulMACControlArg = ( ( uint32_t ) xEthernetLinkInfo.speed << ARM_ETH_MAC_SPEED_Pos ) |
                                  ( ( uint32_t ) xEthernetLinkInfo.duplex << ARM_ETH_MAC_DUPLEX_Pos ) |
                                  ( uint32_t ) cmsisETH_MAC_CONTROL_FLAGS;

                lDriverReturn = pxCtx->pxEthernetMACDriver->Control( ARM_ETH_MAC_CONFIGURE, ulMACControlArg );

                if( lDriverReturn != ARM_DRIVER_OK )
                {
                    pxCtx->eEMACState = xEMAC_Fatal;
                    FreeRTOS_printf( ( "NetworkInterface: failed to configure MAC: %ld\n", ( long ) lDriverReturn ) );
                    break;
                }

                #if ( cmsisETH_USE_TX_COMPLETE_EVENT != 0 )
                    if( pxCtx->xTxCompleteSemaphore == NULL )
                    {
                        pxCtx->xTxCompleteSemaphore = xSemaphoreCreateBinary();
                        configASSERT( pxCtx->xTxCompleteSemaphore != NULL );

                        /* Start signaled so the first SendFrame does not block. */
                        ( void ) xSemaphoreGive( pxCtx->xTxCompleteSemaphore );

                        if( pxCtx->xMACCapabilities.event_tx_frame == 0U )
                        {
                            FreeRTOS_printf( ( "NetworkInterface: WARNING - TX complete event enabled but MAC does not report event_tx_frame capability\n" ) );
                        }
                    }
                #endif /* cmsisETH_USE_TX_COMPLETE_EVENT */

                if( pxCtx->xRxTaskHandle == NULL )
                {
                    xTaskReturn = xTaskCreate( prvRxTask,
                                               pxCtx->pcName,
                                               cmsisETH_RX_TASK_STACK_SIZE,
                                               ( void * ) pxCtx,
                                               cmsisETH_RX_TASK_PRIORITY,
                                               &pxCtx->xRxTaskHandle );

                    if( xTaskReturn != pdPASS )
                    {
                        pxCtx->eEMACState = xEMAC_Fatal;
                        FreeRTOS_printf( ( "NetworkInterface: failed to create RX task: %ld\n", ( long ) xTaskReturn ) );
                        break;
                    }
                }

                lDriverReturn = pxCtx->pxEthernetMACDriver->Control( ARM_ETH_MAC_CONTROL_RX, 1U );

                if( lDriverReturn != ARM_DRIVER_OK )
                {
                    pxCtx->eEMACState = xEMAC_Fatal;
                    FreeRTOS_printf( ( "NetworkInterface: failed to enable MAC RX: %ld\n", ( long ) lDriverReturn ) );
                    break;
                }

                lDriverReturn = pxCtx->pxEthernetMACDriver->Control( ARM_ETH_MAC_CONTROL_TX, 1U );

                if( lDriverReturn != ARM_DRIVER_OK )
                {
                    pxCtx->eEMACState = xEMAC_Fatal;
                    FreeRTOS_printf( ( "NetworkInterface: failed to enable MAC TX: %ld\n", ( long ) lDriverReturn ) );
                    break;
                }

                pxCtx->eEMACState = xEMAC_Ready;
                xContinue = pdTRUE;
                break;

            case xEMAC_Ready:
                xReturn = pdPASS;
                break;

            case xEMAC_Fatal:
            default:
                /* A fatal error has occurred and this interface can not start. */
                break;
        }
    } /* end while( xContinue ) */

    return xReturn;
}

/*-----------------------------------------------------------*/

static BaseType_t xCMSIS_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                 NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                 BaseType_t xReleaseAfterSend )
{
    CMSISEthernetInterface_t * pxCtx = prvGetContext( pxInterface );
    BaseType_t xReturn = pdFAIL;

    if( ( pxNetworkBuffer != NULL ) && ( pxCtx->eEthernetLinkState == ARM_ETH_LINK_UP ) )
    {
        if( pxNetworkBuffer->xDataLength > cmsisETH_MAX_FRAME_SIZE )
        {
            FreeRTOS_debug_printf( ( "NetworkInterface: frame too large for SendFrame: %lu\n", ( unsigned long ) pxNetworkBuffer->xDataLength ) );
        }
        else
        {
            #if ( cmsisETH_USE_TX_COMPLETE_EVENT != 0 )
            {
                int32_t lDriverStatus;

                if( xSemaphoreTake( pxCtx->xTxCompleteSemaphore,
                                    pdMS_TO_TICKS( cmsisETH_TX_COMPLETE_TIMEOUT_MS ) ) == pdTRUE )
                {
                    lDriverStatus = pxCtx->pxEthernetMACDriver->SendFrame(
                        pxNetworkBuffer->pucEthernetBuffer,
                        ( uint32_t ) pxNetworkBuffer->xDataLength,
                        ARM_ETH_MAC_TX_FRAME_EVENT );

                    if( lDriverStatus == ARM_DRIVER_OK )
                    {
                        xReturn = pdPASS;
                    }
                    else
                    {
                        /* TX was not accepted; give semaphore back so it is not lost. */
                        ( void ) xSemaphoreGive( pxCtx->xTxCompleteSemaphore );
                        FreeRTOS_debug_printf( ( "NetworkInterface: SendFrame failed: %ld\n", ( long ) lDriverStatus ) );
                    }
                }
                else
                {
                    FreeRTOS_debug_printf( ( "NetworkInterface: TX complete semaphore timeout\n" ) );
                }
            }
            #else /* cmsisETH_USE_TX_COMPLETE_EVENT == 0 */
            {
                uint32_t ulAttempt;
                int32_t lDriverStatus = ARM_DRIVER_ERROR;

                for( ulAttempt = 0U; ulAttempt <= cmsisETH_TX_RETRY_COUNT; ulAttempt++ )
                {
                    lDriverStatus = pxCtx->pxEthernetMACDriver->SendFrame(
                        pxNetworkBuffer->pucEthernetBuffer,
                        ( uint32_t ) pxNetworkBuffer->xDataLength,
                        0U );

                    if( lDriverStatus == ARM_DRIVER_OK )
                    {
                        xReturn = pdPASS;
                        break;
                    }

                    if( lDriverStatus != ARM_DRIVER_ERROR_BUSY )
                    {
                        break;
                    }

                    if( ulAttempt < cmsisETH_TX_RETRY_COUNT )
                    {
                        vTaskDelay( pdMS_TO_TICKS( cmsisETH_TX_RETRY_DELAY_MS ) );
                    }
                }

                if( xReturn != pdPASS )
                {
                    FreeRTOS_debug_printf( ( "NetworkInterface: SendFrame failed: %ld\n", ( long ) lDriverStatus ) );
                }
            }
            #endif /* cmsisETH_USE_TX_COMPLETE_EVENT */
        }
    }

    if( ( xReleaseAfterSend == pdTRUE ) && ( pxNetworkBuffer != NULL ) )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

    return xReturn;
}

/*-----------------------------------------------------------*/

size_t uxNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    /* BufferAllocation_1.c users must provide a static buffer mapping here. */
    ( void ) pxNetworkBuffers;
    configASSERT( 0 );
    return 0U;
}

/*-----------------------------------------------------------*/

static BaseType_t xCMSIS_GetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    CMSISEthernetInterface_t * pxCtx = prvGetContext( pxInterface );

    return ( pxCtx->pxEthernetPHYDriver->GetLinkState() == ARM_ETH_LINK_UP ) ? pdTRUE : pdFALSE;
}

/*-----------------------------------------------------------*/

#if ( cmsisETH_MAX_MAC_FILTER_ENTRIES > 0 )

    static BaseType_t prvFindMACInFilter( const CMSISEthernetInterface_t * pxCtx,
                                          const uint8_t * pucMac )
    {
        uint32_t ulIdx;

        for( ulIdx = 0U; ulIdx < pxCtx->ulMACFilterCount; ulIdx++ )
        {
            if( memcmp( pxCtx->xMACFilterTable[ ulIdx ].b, pucMac, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
            {
                return ( BaseType_t ) ulIdx;
            }
        }

        return ( BaseType_t ) -1;
    }

/*-----------------------------------------------------------*/

    static void prvCommitAddressFilter( CMSISEthernetInterface_t * pxCtx )
    {
        ( void ) pxCtx->pxEthernetMACDriver->SetAddressFilter(
            pxCtx->xMACFilterTable,
            pxCtx->ulMACFilterCount );
    }

/*-----------------------------------------------------------*/

    static void prvAddAllowedMACAddress( struct xNetworkInterface * pxInterface,
                                         const uint8_t * pucMacAddress )
    {
        CMSISEthernetInterface_t * pxCtx = prvGetContext( pxInterface );
        BaseType_t xIdx = prvFindMACInFilter( pxCtx, pucMacAddress );

        if( xIdx >= 0 )
        {
            if( pxCtx->ucMACFilterRefCount[ xIdx ] < UINT8_MAX )
            {
                pxCtx->ucMACFilterRefCount[ xIdx ]++;
            }

            return;
        }

        if( pxCtx->ulMACFilterCount >= ( uint32_t ) cmsisETH_MAX_MAC_FILTER_ENTRIES )
        {
            FreeRTOS_debug_printf( ( "NetworkInterface: MAC filter table full, cannot add address\n" ) );
            return;
        }

        ( void ) memcpy( pxCtx->xMACFilterTable[ pxCtx->ulMACFilterCount ].b,
                          pucMacAddress, ipMAC_ADDRESS_LENGTH_BYTES );
        pxCtx->ucMACFilterRefCount[ pxCtx->ulMACFilterCount ] = 1U;
        pxCtx->ulMACFilterCount++;

        prvCommitAddressFilter( pxCtx );
    }

/*-----------------------------------------------------------*/

    static void prvRemoveAllowedMACAddress( struct xNetworkInterface * pxInterface,
                                            const uint8_t * pucMacAddress )
    {
        CMSISEthernetInterface_t * pxCtx = prvGetContext( pxInterface );
        BaseType_t xIdx = prvFindMACInFilter( pxCtx, pucMacAddress );

        if( xIdx < 0 )
        {
            return;
        }

        pxCtx->ucMACFilterRefCount[ xIdx ]--;

        if( pxCtx->ucMACFilterRefCount[ xIdx ] == 0U )
        {
            /* Compact: swap last entry into this slot. */
            pxCtx->ulMACFilterCount--;

            if( ( uint32_t ) xIdx < pxCtx->ulMACFilterCount )
            {
                ( void ) memcpy( &pxCtx->xMACFilterTable[ xIdx ],
                                 &pxCtx->xMACFilterTable[ pxCtx->ulMACFilterCount ],
                                 sizeof( ARM_ETH_MAC_ADDR ) );
                pxCtx->ucMACFilterRefCount[ xIdx ] =
                    pxCtx->ucMACFilterRefCount[ pxCtx->ulMACFilterCount ];
            }

            prvCommitAddressFilter( pxCtx );
        }
    }

#endif /* cmsisETH_MAX_MAC_FILTER_ENTRIES > 0 */

/*-----------------------------------------------------------*/

#if ( ipconfigIPv4_BACKWARD_COMPATIBLE != 0 )

    /* Do not call this function directly. It is there for backward compatibility.
     * FreeRTOS_IPInit() will call it to initialize the interface and endpoint objects. */
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface )
    {
        return pxCMSIS_FillInterfaceDescriptor( xEMACIndex, pxInterface );
    }

#endif /* if ( ipconfigIPv4_BACKWARD_COMPATIBLE != 0 ) */

/*-----------------------------------------------------------*/

NetworkInterface_t * pxCMSIS_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                      NetworkInterface_t * pxInterface )
{
    CMSISEthernetInterface_t * pxCtx;

    configASSERT( ( xEMACIndex >= 0 ) && ( xEMACIndex < ( BaseType_t ) cmsisETH_MAX_INSTANCES ) );

    pxCtx = &xInstances[ xEMACIndex ];

    ( void ) memset( pxCtx, 0, sizeof( *pxCtx ) );

    pxCtx->xIndex = xEMACIndex;
    pxCtx->eEthernetLinkState = ARM_ETH_LINK_DOWN;
    pxCtx->eEMACState = xEMAC_Init;

    #if ( cmsisETH_MAX_INSTANCES == 1 )
        pxCtx->pxEthernetMACDriver = &ARM_Driver_ETH_MAC_( cmsisETH_MAC_DRIVER_INSTANCE );
        pxCtx->pxEthernetPHYDriver = &ARM_Driver_ETH_PHY_( cmsisETH_PHY_DRIVER_INSTANCE );
    #else
        pxCtx->pxEthernetMACDriver = pxCMSIS_MACDrivers[ xEMACIndex ];
        pxCtx->pxEthernetPHYDriver = pxCMSIS_PHYDrivers[ xEMACIndex ];
    #endif

    ( void ) snprintf( pxCtx->pcName, sizeof( pxCtx->pcName ), "eth%ld", ( long ) xEMACIndex );

    ( void ) memset( pxInterface, 0, sizeof( *pxInterface ) );

    pxCtx->pxMyInterface = pxInterface;
    pxInterface->pcName = pxCtx->pcName;
    pxInterface->pvArgument = ( void * ) pxCtx;
    pxInterface->pfInitialise = xCMSIS_NetworkInterfaceInitialise;
    pxInterface->pfOutput = xCMSIS_NetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = xCMSIS_GetPhyLinkStatus;

    #if ( cmsisETH_MAX_MAC_FILTER_ENTRIES > 0 )
        pxInterface->pfAddAllowedMAC = prvAddAllowedMACAddress;
        pxInterface->pfRemoveAllowedMAC = prvRemoveAllowedMACAddress;
    #endif

    FreeRTOS_AddNetworkInterface( pxInterface );

    return pxInterface;
}

/*-----------------------------------------------------------*/
