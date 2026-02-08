/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Copyright 2023 Arm Limited and/or its affiliates
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

/* Allow selection of CMSIS driver instances. */
#ifndef cmsisETH_MAC_DRIVER_INSTANCE
    #define cmsisETH_MAC_DRIVER_INSTANCE    0
#endif

#ifndef cmsisETH_PHY_DRIVER_INSTANCE
    #define cmsisETH_PHY_DRIVER_INSTANCE    0
#endif

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

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
 * driver will filter incoming packets and only pass the stack those packets it
 * considers need processing. */
#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
    #define cmsisCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
    #define cmsisCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/* Ethernet MAC & PHY drivers selected by instance. */
extern ARM_DRIVER_ETH_MAC ARM_Driver_ETH_MAC_( cmsisETH_MAC_DRIVER_INSTANCE );
extern ARM_DRIVER_ETH_PHY ARM_Driver_ETH_PHY_( cmsisETH_PHY_DRIVER_INSTANCE );

typedef struct xCMSISEthernetInterface
{
    ARM_DRIVER_ETH_MAC * pxEthernetMACDriver;
    ARM_DRIVER_ETH_PHY * pxEthernetPHYDriver;
    ARM_ETH_MAC_CAPABILITIES xMACCapabilities;
    ARM_ETH_LINK_STATE eEthernetLinkState;
} CMSISEthernetInterface_t;

typedef enum xEMAC_STATE
{
    xEMAC_Init = 0,
    xEMAC_WaitPHY,
    xEMAC_Ready,
    xEMAC_Fatal
} EMACState_t;

/*-----------------------------------------------------------*/

/*
 * The task that processes incoming Ethernet packets.
 * It is unblocked by the Ethernet Rx interrupt callback.
 */
static void prvRxTask( void * pvParameters );

/* Read all pending frames from the MAC and send them to the IP-task. */
static void prvProcessReceivedPackets( void );

/* Poll PHY status and notify the IP-task if link goes down. */
static void prvCheckEthernetLinkStatus( void );

/* CMSIS MAC callback. */
static void prvEthernetDriverNotifications( uint32_t ulEvent );

/* NetworkInterface functions. */
static BaseType_t xCMSIS_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface );
static BaseType_t xCMSIS_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                 NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                 BaseType_t bReleaseAfterSend );
static BaseType_t xCMSIS_GetPhyLinkStatus( NetworkInterface_t * pxInterface );

NetworkInterface_t * pxCMSIS_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                      NetworkInterface_t * pxInterface );

/* Legacy alias retained for backward compatibility with older CMSIS example ports. */
NetworkInterface_t * pxLAN91C111_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                          NetworkInterface_t * pxInterface );

/*-----------------------------------------------------------*/

static CMSISEthernetInterface_t xEthernetInterface0 =
{
    .pxEthernetMACDriver = &ARM_Driver_ETH_MAC_( cmsisETH_MAC_DRIVER_INSTANCE ),
    .pxEthernetPHYDriver = &ARM_Driver_ETH_PHY_( cmsisETH_PHY_DRIVER_INSTANCE ),
    .eEthernetLinkState = ARM_ETH_LINK_DOWN
};

static EMACState_t eEMACState = xEMAC_Init;
static TaskHandle_t xRxTaskHandle = NULL;
static NetworkInterface_t * pxMyInterface = NULL;

/*-----------------------------------------------------------*/

static void prvCheckEthernetLinkStatus( void )
{
    const ARM_ETH_LINK_STATE eCurrentLinkState = xEthernetInterface0.pxEthernetPHYDriver->GetLinkState();
    IPStackEvent_t xRxEvent;

    if( eCurrentLinkState == xEthernetInterface0.eEthernetLinkState )
    {
        return;
    }

    xEthernetInterface0.eEthernetLinkState = eCurrentLinkState;

    if( eCurrentLinkState == ARM_ETH_LINK_DOWN )
    {
        FreeRTOS_printf( ( "NetworkInterface: Ethernet link is down\n" ) );
        eEMACState = xEMAC_Init;

        if( pxMyInterface != NULL )
        {
            xRxEvent.eEventType = eNetworkDownEvent;
            xRxEvent.pvData = ( void * ) pxMyInterface;
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
    ( void ) pvParameters;

    for( ; ; )
    {
        ( void ) ulTaskNotifyTake( pdFALSE, pdMS_TO_TICKS( cmsisETH_RX_TASK_BLOCK_TIME_MS ) );
        prvProcessReceivedPackets();
        prvCheckEthernetLinkStatus();
    }
}

/*-----------------------------------------------------------*/

static void prvProcessReceivedPackets( void )
{
    const TickType_t xDescriptorWaitTime = 0U;
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };

    for( ; ; )
    {
        const uint32_t ulMessageLength = xEthernetInterface0.pxEthernetMACDriver->GetRxFrameSize();
        NetworkBufferDescriptor_t * pxNetworkBuffer = NULL;
        int32_t lReceivedBytes;

        if( ulMessageLength == 0U )
        {
            break;
        }

        if( ( ulMessageLength < ipSIZE_OF_ETH_HEADER ) || ( ulMessageLength > cmsisETH_MAX_FRAME_SIZE ) )
        {
            FreeRTOS_debug_printf( ( "NetworkInterface: drop invalid frame length %lu\n", ( unsigned long ) ulMessageLength ) );
            ( void ) xEthernetInterface0.pxEthernetMACDriver->ReadFrame( NULL, 0U );
            continue;
        }

        pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( ulMessageLength, xDescriptorWaitTime );

        if( pxNetworkBuffer == NULL )
        {
            FreeRTOS_debug_printf( ( "NetworkInterface: drop frame, no network buffer\n" ) );
            ( void ) xEthernetInterface0.pxEthernetMACDriver->ReadFrame( NULL, 0U );
            continue;
        }

        lReceivedBytes = xEthernetInterface0.pxEthernetMACDriver->ReadFrame( pxNetworkBuffer->pucEthernetBuffer, ulMessageLength );

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

        pxNetworkBuffer->pxInterface = pxMyInterface;
        pxNetworkBuffer->pxEndPoint = FreeRTOS_MatchingEndpoint( pxMyInterface, pxNetworkBuffer->pucEthernetBuffer );

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

static BaseType_t xCMSIS_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    BaseType_t xReturn = pdFAIL;
    BaseType_t xTaskReturn;
    int32_t lDriverReturn = ARM_DRIVER_ERROR;
    uint32_t ulMACControlArg = 0U;
    ARM_ETH_LINK_INFO xEthernetLinkInfo;

    switch( eEMACState )
    {
        case xEMAC_Init:
            lDriverReturn = xEthernetInterface0.pxEthernetMACDriver->Initialize( prvEthernetDriverNotifications );

            if( lDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: failed to initialize MAC driver: %ld\n", ( long ) lDriverReturn ) );
                break;
            }

            lDriverReturn = xEthernetInterface0.pxEthernetMACDriver->PowerControl( ARM_POWER_FULL );

            if( lDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: failed to set MAC power: %ld\n", ( long ) lDriverReturn ) );
                break;
            }

            xEthernetInterface0.xMACCapabilities = xEthernetInterface0.pxEthernetMACDriver->GetCapabilities();

            lDriverReturn = xEthernetInterface0.pxEthernetMACDriver->SetMacAddress( ( ARM_ETH_MAC_ADDR * ) &pxInterface->pxEndPoint->xMACAddress );

            if( lDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: failed to set MAC address: %ld\n", ( long ) lDriverReturn ) );
                break;
            }

            lDriverReturn = xEthernetInterface0.pxEthernetPHYDriver->Initialize(
                xEthernetInterface0.pxEthernetMACDriver->PHY_Read,
                xEthernetInterface0.pxEthernetMACDriver->PHY_Write );

            if( lDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: failed to initialize PHY driver: %ld\n", ( long ) lDriverReturn ) );
                break;
            }

            lDriverReturn = xEthernetInterface0.pxEthernetPHYDriver->PowerControl( ARM_POWER_FULL );

            if( lDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: failed to set PHY power: %ld\n", ( long ) lDriverReturn ) );
                break;
            }

            lDriverReturn = xEthernetInterface0.pxEthernetPHYDriver->SetInterface( xEthernetInterface0.xMACCapabilities.media_interface );

            if( lDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: failed to set PHY interface: %ld\n", ( long ) lDriverReturn ) );
                break;
            }

            lDriverReturn = xEthernetInterface0.pxEthernetPHYDriver->SetMode( cmsisETH_PHY_MODE );

            if( lDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: failed to set PHY mode: %ld\n", ( long ) lDriverReturn ) );
                break;
            }

            eEMACState = xEMAC_WaitPHY;

        /* Fall through: continue with link bring-up. */
        case xEMAC_WaitPHY:
            vTaskDelay( pdMS_TO_TICKS( cmsisETH_LINK_CHECK_INTERVAL_MS ) );

            xEthernetInterface0.eEthernetLinkState = xEthernetInterface0.pxEthernetPHYDriver->GetLinkState();

            if( xEthernetInterface0.eEthernetLinkState == ARM_ETH_LINK_DOWN )
            {
                break;
            }

            xEthernetLinkInfo = xEthernetInterface0.pxEthernetPHYDriver->GetLinkInfo();
            ulMACControlArg = ( ( uint32_t ) xEthernetLinkInfo.speed << ARM_ETH_MAC_SPEED_Pos ) |
                              ( ( uint32_t ) xEthernetLinkInfo.duplex << ARM_ETH_MAC_DUPLEX_Pos ) |
                              ( uint32_t ) cmsisETH_MAC_CONTROL_FLAGS;

            lDriverReturn = xEthernetInterface0.pxEthernetMACDriver->Control( ARM_ETH_MAC_CONFIGURE, ulMACControlArg );

            if( lDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: failed to configure MAC: %ld\n", ( long ) lDriverReturn ) );
                break;
            }

            if( xRxTaskHandle == NULL )
            {
                xTaskReturn = xTaskCreate( prvRxTask,
                                           "CMSIS_EMAC",
                                           cmsisETH_RX_TASK_STACK_SIZE,
                                           NULL,
                                           cmsisETH_RX_TASK_PRIORITY,
                                           &xRxTaskHandle );

                if( xTaskReturn != pdPASS )
                {
                    eEMACState = xEMAC_Fatal;
                    FreeRTOS_printf( ( "NetworkInterface: failed to create RX task: %ld\n", ( long ) xTaskReturn ) );
                    break;
                }
            }

            lDriverReturn = xEthernetInterface0.pxEthernetMACDriver->Control( ARM_ETH_MAC_CONTROL_RX, 1U );

            if( lDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: failed to enable MAC RX: %ld\n", ( long ) lDriverReturn ) );
                break;
            }

            lDriverReturn = xEthernetInterface0.pxEthernetMACDriver->Control( ARM_ETH_MAC_CONTROL_TX, 1U );

            if( lDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: failed to enable MAC TX: %ld\n", ( long ) lDriverReturn ) );
                break;
            }

            eEMACState = xEMAC_Ready;

        /* Fall through. */
        case xEMAC_Ready:
            xReturn = pdPASS;
            break;

        case xEMAC_Fatal:
        default:
            /* A fatal error has occurred and this interface can not start. */
            break;
    }

    return xReturn;
}

/*-----------------------------------------------------------*/

static void prvEthernetDriverNotifications( uint32_t ulEvent )
{
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    if( ( ulEvent & ARM_ETH_MAC_EVENT_RX_FRAME ) != 0U )
    {
        if( xRxTaskHandle != NULL )
        {
            vTaskNotifyGiveFromISR( xRxTaskHandle, &xHigherPriorityTaskWoken );
        }
    }

#if defined( portYIELD_FROM_ISR )
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
#elif defined( portEND_SWITCHING_ISR )
    portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
#else
    ( void ) xHigherPriorityTaskWoken;
#endif
}

/*-----------------------------------------------------------*/

static BaseType_t xCMSIS_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                 NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                 BaseType_t xReleaseAfterSend )
{
    BaseType_t xReturn = pdFAIL;
    uint32_t ulAttempt;
    int32_t lDriverStatus = ARM_DRIVER_ERROR;

    ( void ) pxInterface;

    if( ( pxNetworkBuffer != NULL ) && ( xEthernetInterface0.eEthernetLinkState == ARM_ETH_LINK_UP ) )
    {
        if( pxNetworkBuffer->xDataLength > cmsisETH_MAX_FRAME_SIZE )
        {
            FreeRTOS_debug_printf( ( "NetworkInterface: frame too large for SendFrame: %lu\n", ( unsigned long ) pxNetworkBuffer->xDataLength ) );
        }
        else
        {
            for( ulAttempt = 0U; ulAttempt <= cmsisETH_TX_RETRY_COUNT; ulAttempt++ )
            {
                lDriverStatus = xEthernetInterface0.pxEthernetMACDriver->SendFrame(
                    pxNetworkBuffer->pucEthernetBuffer,
                    pxNetworkBuffer->xDataLength,
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
    }

    if( xReleaseAfterSend == pdTRUE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

    return xReturn;
}

/*-----------------------------------------------------------*/

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    /* BufferAllocation_1.c users must provide a static buffer mapping here. */
    configASSERT( 0 );
    ( void ) pxNetworkBuffers;
}

/*-----------------------------------------------------------*/

static BaseType_t xCMSIS_GetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    ( void ) pxInterface;

    return ( xEthernetInterface0.pxEthernetPHYDriver->GetLinkState() == ARM_ETH_LINK_UP ) ? pdTRUE : pdFALSE;
}

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
    static char pcName[ 17 ];

    pxMyInterface = pxInterface;

    ( void ) snprintf( pcName, sizeof( pcName ), "eth%ld", ( long ) xEMACIndex );

    memset( pxInterface, 0, sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;
    pxInterface->pvArgument = ( void * ) ( uintptr_t ) xEMACIndex;
    pxInterface->pfInitialise = xCMSIS_NetworkInterfaceInitialise;
    pxInterface->pfOutput = xCMSIS_NetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = xCMSIS_GetPhyLinkStatus;

    FreeRTOS_AddNetworkInterface( pxInterface );

    return pxInterface;
}

/*-----------------------------------------------------------*/

NetworkInterface_t * pxLAN91C111_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                          NetworkInterface_t * pxInterface )
{
    return pxCMSIS_FillInterfaceDescriptor( xEMACIndex, pxInterface );
}

/*-----------------------------------------------------------*/
