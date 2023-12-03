/*
 * Some constants, hardware definitions and comments taken from ST's HAL driver
 * library, COPYRIGHT(c) 2015 STMicroelectronics.
 */

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

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"
#include "phyHandling.h"

/* ST includes. */
#if defined( STM32F4 )
    #include "stm32f4xx_hal.h"
#elif defined( STM32F7 )
    #include "stm32f7xx_hal.h"
#elif defined( STM32H7 )
    #include "stm32h7xx_hal.h"
#elif defined( STM32H5 )
    #include "stm32h5xx_hal.h"
#else
    #error Unknown STM32 Family for NetworkInterface
#endif

/*-----------------------------------------------------------*/

/* TODO: This should be moved from FreeRTOS_IP.c to FreeRTOS_IP_Private.h
 * so that all the network interfaces don't have to keep defining it. */
#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/*-----------------------------------------------------------*/

#define EMAC_TX_DESCRIPTORS_SECTION ".TxDescripSection"
#define EMAC_RX_DESCRIPTORS_SECTION ".RxDescripSection"
#define EMAC_BUFFERS_SECTION    ".EthBuffersSection"

#define EMAC_DATA_ALIGNMENT_MASK    ( portBYTE_ALIGNMENT - 1U )
#define EMAC_DATA_BUFFER_SIZE   ( ( ipTOTAL_ETHERNET_FRAME_SIZE + portBYTE_ALIGNMENT ) & ~EMAC_DATA_ALIGNMENT_MASK )
#define EMAC_TOTAL_ALIGNMENT_MASK   ( __SCB_DCACHE_LINE_SIZE - 1U )
#define EMAC_TOTAL_BUFFER_SIZE  ( ( EMAC_DATA_BUFFER_SIZE + ipBUFFER_PADDING + __SCB_DCACHE_LINE_SIZE ) & ~EMAC_TOTAL_ALIGNMENT_MASK )

typedef enum {
    eMacEventRx = 1 << 0,
    eMacEventTx = 1 << 1,
    eMacEventErrRx = 1 << 2,
    eMacEventErrTx = 1 << 3,
    eMacEventErrDma = 1 << 4,
    eMacEventErrEth = 1 << 5,
    eMacEventErrMac = 1 << 6,
    eMacEventAll = (1 << 7) - 1,
} eMAC_IF_EVENT;

typedef enum
{
    eMacEthInit,
    eMacPhyInit,
    eMacPhyStart,
    eMacTaskStart,
    eMacEthStart,
    eMacInitComplete
} eMAC_INIT_STATUS_TYPE;

/*-----------------------------------------------------------*/

static BaseType_t xSTM32_GetPhyLinkStatus( NetworkInterface_t * pxInterface );

static BaseType_t xSTM32_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface );

static BaseType_t xSTM32_NetworkInterfaceOutput( NetworkInterface_t * pxInterface, NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend );

static UBaseType_t prvNetworkInterfaceInput( void );

static void prvEMACHandlerTask( void * pvParameters ) __attribute__( ( __noreturn__ ) );

static BaseType_t prvAcceptPacket( const NetworkBufferDescriptor_t * const pxDescriptor );

static BaseType_t prvPhyReadReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t * pulValue );

static BaseType_t prvPhyWriteReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue );

static void prvEthernetUpdateConfig( void );

/* static void prvMACAddressConfig( ETH_HandleTypeDef * heth, uint32_t ulIndex, uint8_t * Addr ); */

NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t * pxInterface );

/*-----------------------------------------------------------*/

static ETH_HandleTypeDef xEthHandle;

static ETH_MACConfigTypeDef xMACConfig;

static ETH_DMADescTypeDef DMARxDscrTab[ ETH_RX_DESC_CNT ] __attribute__( ( section( EMAC_RX_DESCRIPTORS_SECTION ), aligned( portBYTE_ALIGNMENT ) ) );

static ETH_DMADescTypeDef DMATxDscrTab[ ETH_TX_DESC_CNT ] __attribute__( ( section( EMAC_TX_DESCRIPTORS_SECTION ), aligned( portBYTE_ALIGNMENT ) ) );

static NetworkInterface_t * pxMyInterface = NULL;

static TaskHandle_t xEMACTaskHandle;

static SemaphoreHandle_t xTxMutex;

static SemaphoreHandle_t xTxDescSem;

static EthernetPhy_t xPhyObject;

static const PhyProperties_t xPHYProperties = {
    .ucSpeed = PHY_SPEED_AUTO,
    .ucDuplex = PHY_DUPLEX_AUTO,
    .ucMDI_X = PHY_MDIX_AUTO,
};

/*-----------------------------------------------------------*/

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ EMAC_TOTAL_BUFFER_SIZE ] __attribute__( ( section( EMAC_BUFFERS_SECTION ), aligned( __SCB_DCACHE_LINE_SIZE ) ) );

    configASSERT( xBufferAllocFixedSize == pdTRUE );

    for( size_t ul = 0; ul < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ++ul )
    {
        pxNetworkBuffers[ ul ].pucEthernetBuffer = &( ucNetworkPackets[ ul ][ ipBUFFER_PADDING ] );
        *( ( uint32_t * ) &( ucNetworkPackets[ ul ][ 0 ] ) ) = ( uint32_t ) ( &( pxNetworkBuffers[ ul ] ) );
    }
}

/*-----------------------------------------------------------*/

NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t * pxInterface )
{
    static char pcName[ 17 ];

    ( void ) snprintf( pcName, sizeof( pcName ), "eth%u", ( unsigned ) xEMACIndex );

    ( void ) memset( pxInterface, '\0', sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;
    pxInterface->pvArgument = ( void * ) xEMACIndex;
    pxInterface->pfInitialise = xSTM32_NetworkInterfaceInitialise;
    pxInterface->pfOutput = xSTM32_NetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = xSTM32_GetPhyLinkStatus;

    ( void ) FreeRTOS_AddNetworkInterface( pxInterface );

    pxMyInterface = pxInterface;

    return pxInterface;
}

/*-----------------------------------------------------------*/

static BaseType_t xSTM32_GetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    ( void ) pxInterface;

    BaseType_t xReturn = pdFAIL;

    if( xPhyObject.ulLinkStatusMask != 0U )
    {
        xReturn = pdPASS;
    }

    return xReturn;
}

/*-----------------------------------------------------------*/

static BaseType_t xSTM32_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    BaseType_t xInitResult = pdFAIL;
    BaseType_t xResult;
    HAL_StatusTypeDef xHalResult;
    /* BaseType_t xMACEntry = ETH_MAC_ADDRESS1; */ /* ETH_MAC_ADDRESS0 reserved for the primary MAC-address. */

    static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMacEthInit;

    switch( xMacInitStatus )
    {
        default:
            configASSERT( pdFALSE );
            break;

        case eMacEthInit:
            xEthHandle.Instance = ETH;

            const NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
            if( pxEndPoint == NULL )
            {
                break;
            }

            xEthHandle.Init.MACAddr = ( uint8_t * ) pxEndPoint->xMACAddress.ucBytes;
            xEthHandle.Init.MediaInterface = HAL_ETH_RMII_MODE;
            xEthHandle.Init.TxDesc = DMATxDscrTab;
            xEthHandle.Init.RxDesc = DMARxDscrTab;
            xEthHandle.Init.RxBuffLen = EMAC_DATA_BUFFER_SIZE;

            ( void ) memset( &DMATxDscrTab, 0, sizeof( DMATxDscrTab ) );
            ( void ) memset( &DMARxDscrTab, 0, sizeof( DMARxDscrTab ) );

            #if defined( STM32F7 ) || defined( STM32F4 )
                /* This function doesn't get called in Fxx driver */
                HAL_ETH_SetMDIOClockRange( &xEthHandle );
            #endif

            xHalResult = HAL_ETH_Init( &xEthHandle );
            if( xHalResult != HAL_OK )
            {
                /* &xEthHandle != NULL
                xEthHandle.ErrorCode == HAL_ETH_ERROR_TIMEOUT */
                break;
            }
            configASSERT( xEthHandle.ErrorCode == HAL_ETH_ERROR_NONE );
            configASSERT( xEthHandle.gState == HAL_ETH_STATE_READY );

            xMacInitStatus = eMacPhyInit;
            /* fallthrough */

        case eMacPhyInit:
            vPhyInitialise( &xPhyObject, ( xApplicationPhyReadHook_t ) prvPhyReadReg, ( xApplicationPhyWriteHook_t ) prvPhyWriteReg );

            xResult = xPhyDiscover( &xPhyObject );
            if( xResult == 0 )
            {
                break;
            }

            xMacInitStatus = eMacPhyStart;
            /* fallthrough */

        case eMacPhyStart:
            xResult = xPhyConfigure( &xPhyObject, &xPHYProperties );
            if( xResult != 0 )
            {
                break;
            }

            if ( xSTM32_GetPhyLinkStatus( pxInterface ) == pdFAIL )
            {
                xResult = xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) );
                /* TODO: xPhyStartAutoNegotiation always returns 0, Should return -1 if xPhyGetMask == 0 ? */
                configASSERT( xResult == 0 );
                if ( xSTM32_GetPhyLinkStatus( pxInterface ) == pdFAIL )
                {
                    break;
                }
            }

            xHalResult = HAL_ETH_GetMACConfig( &xEthHandle , &xMACConfig );
            configASSERT( xHalResult == HAL_OK );
            if( xHalResult != HAL_OK )
            {
                break;
            }
            xMACConfig.DuplexMode = ( xPhyObject.xPhyProperties.ucDuplex == PHY_DUPLEX_FULL ) ? ETH_FULLDUPLEX_MODE : ETH_HALFDUPLEX_MODE;
            xMACConfig.Speed = ( xPhyObject.xPhyProperties.ucSpeed == PHY_SPEED_10 ) ? ETH_SPEED_10M : ETH_SPEED_100M;
            xMACConfig.ChecksumOffload = ( FunctionalState ) ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM != 0 );
            xHalResult = HAL_ETH_SetMACConfig( &xEthHandle, &xMACConfig );
            configASSERT( xHalResult == HAL_OK );
            if( xHalResult != HAL_OK )
            {
                break;
            }

            xMacInitStatus = eMacTaskStart;
            /* fallthrough */

        case eMacTaskStart:
            if( xTxMutex == NULL )
            {
                #if ( configSUPPORT_STATIC_ALLOCATION != 0 )
                {
                    static StaticSemaphore_t xTxMutexBuf;
                    xTxMutex = xSemaphoreCreateMutexStatic( &xTxMutexBuf );
                }
                #else
                    xTxMutex = xSemaphoreCreateMutex();
                #endif
                configASSERT( xTxMutex != NULL );
                if( xTxMutex == NULL )
                {
                    break;
                }
                vQueueAddToRegistry( xTxMutex, "TXMutex" );
            }

            if( xTxDescSem == NULL )
            {
                #if ( configSUPPORT_STATIC_ALLOCATION != 0 )
                {
                    static StaticSemaphore_t xTxDescSemBuf;
                    xTxDescSem = xSemaphoreCreateCountingStatic( ( UBaseType_t ) ETH_TX_DESC_CNT, ( UBaseType_t ) ETH_TX_DESC_CNT, &xTxDescSemBuf );
                }
                #else
                    xTxDescSem = xSemaphoreCreateCounting(
                        ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS,
                        ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS
                    );
                #endif
                configASSERT( xTxDescSem != NULL );
                if( xTxDescSem == NULL )
                {
                    break;
                }
                vQueueAddToRegistry( xTxDescSem, "xTxDescSem" );
            }

            if( xEMACTaskHandle == NULL )
            {
                #if ( configSUPPORT_STATIC_ALLOCATION != 0 )
                {
                    static StackType_t uxEMACTaskStack[ ( 2 * configMINIMAL_STACK_SIZE ) ];
                    static StaticTask_t xEMACTaskTCB;
                    xEMACTaskHandle = xTaskCreateStatic(
                        prvEMACHandlerTask,
                        "EMAC",
                        ( 2 * configMINIMAL_STACK_SIZE ), /* ipconfigEMAC_TASK_STACK_SIZE */
                        NULL,
                        ( configMAX_PRIORITIES - 1 ),
                        uxEMACTaskStack,
                        &xEMACTaskTCB
                    );
                }
                #else
                    xResult = xTaskCreate(
                        prvEMACHandlerTask,
                        "EMAC",
                        ( 2 * configMINIMAL_STACK_SIZE ), /* ipconfigEMAC_TASK_STACK_SIZE */
                        NULL,
                        ( configMAX_PRIORITIES - 1 ),
                        &xEMACTaskHandle
                    );
                    configASSERT( xResult == pdPASS );
                #endif
                configASSERT( xEMACTaskHandle != NULL );
                if( xEMACTaskHandle == NULL )
                {
                    break;
                }
            }

            xMacInitStatus = eMacEthStart;
            /* fallthrough */

        case eMacEthStart:
            if( xEthHandle.gState != HAL_ETH_STATE_STARTED )
            {
                xHalResult = HAL_ETH_Start_IT( &xEthHandle );
                configASSERT( xHalResult == HAL_OK );
                if( xHalResult != HAL_OK )
                {
                    break;
                }
            }
            configASSERT( xEthHandle.gState == HAL_ETH_STATE_STARTED );
            configASSERT( xEthHandle.RxDescList.ItMode == 1U );

            xMacInitStatus = eMacInitComplete;
            /* fallthrough */

        case eMacInitComplete:
            configASSERT( xEthHandle.gState != HAL_ETH_STATE_ERROR );
            if( xSTM32_GetPhyLinkStatus( pxInterface ) == pdPASS )
            {
                xInitResult = pdPASS;
            }
    }

    return xInitResult;
}

/*-----------------------------------------------------------*/

static BaseType_t xSTM32_NetworkInterfaceOutput( NetworkInterface_t * pxInterface, NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend )
{
    BaseType_t xResult = pdFAIL;
    configASSERT( pxDescriptor != NULL );
    configASSERT( xReleaseAfterSend != pdFALSE );   /* Zero-Copy Only */
    iptraceNETWORK_INTERFACE_OUTPUT( pxDescriptor->xDataLength, pxDescriptor->pucEthernetBuffer );

    if( ( pxDescriptor != NULL ) && ( pxDescriptor->pucEthernetBuffer != NULL ) && ( pxDescriptor->xDataLength <= EMAC_DATA_BUFFER_SIZE ) )
    {
        if( xSTM32_GetPhyLinkStatus( pxInterface ) != pdFAIL )
        {
            static ETH_TxPacketConfig xTxConfig = {
                .CRCPadCtrl = ETH_CRC_PAD_INSERT,
                #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM != 0 )
                    .Attributes = ETH_TX_PACKETS_FEATURES_CRCPAD | ETH_TX_PACKETS_FEATURES_CSUM,
                    .ChecksumCtrl = ETH_CHECKSUM_IPHDR_PAYLOAD_INSERT_PHDR_CALC,
                #else
                    .Attributes = ETH_TX_PACKETS_FEATURES_CRCPAD,
                    .ChecksumCtrl = ETH_CHECKSUM_DISABLE,
                #endif
            };

            /*ETH_BufferTypeDef xTxBuffer[ ETH_TX_DESC_CNT ];
            memset( &xTxBuffer, 0, sizeof( xTxBuffer ) );
            NetworkBufferDescriptor_t * pxCurDescriptor = pxDescriptor;
            xTxConfig.Length = 0;
            for( size_t i = 0; i < ETH_TX_DESC_CNT; i++ )
            {
                if( pxCurDescriptor == NULL )
                {
                    break;
                }
                xTxBuffer[ i ].buffer = ( uint8_t * ) pxCurDescriptor->pucEthernetBuffer;
                xTxBuffer[ i ].len = pxCurDescriptor->xDataLength;
                xTxConfig.Length += pxCurDescriptor->xDataLength;
                if( i > 0 )
                {
                    xTxBuffer[ i - 1 ].next = &xTxBuffer[ i ];
                }
                if( pxCurDescriptor->pxNextBuffer == NULL )
                {
                    xTxBuffer[ i ].next = NULL;
                }
                pxCurDescriptor = pxDescriptor->pxNextBuffer;
            }

            xTxConfig.TxBuffer = xTxBuffer;
            xTxConfig.pData = pxDescriptor;*/

            ETH_BufferTypeDef xTxBuffer = {
                .buffer = ( uint8_t * ) pxDescriptor->pucEthernetBuffer,
                .len = pxDescriptor->xDataLength,
                .next = NULL
            };

            xTxConfig.Length = xTxBuffer.len;
            xTxConfig.TxBuffer = &xTxBuffer;
            xTxConfig.pData = pxDescriptor;

            if( xSemaphoreTake( xTxDescSem, pdMS_TO_TICKS( 200U ) ) != pdFALSE )
            {
                if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( 50U ) ) != pdFALSE )
                {
                    HAL_StatusTypeDef xHalResult = HAL_ETH_Transmit_IT( &xEthHandle, &xTxConfig );
                    xSemaphoreGive( xTxMutex );
                    if( xHalResult == HAL_OK )
                    {
                        /* Released later in deferred task by calling HAL_ETH_ReleaseTxPacket */
                        xReleaseAfterSend = pdFALSE;
                        xResult = pdPASS;
                    }
                    else
                    {
                        ( void ) xSemaphoreGive( xTxDescSem );
                        configASSERT( xEthHandle.ErrorCode != HAL_ETH_ERROR_PARAM );
                        if( xEthHandle.gState != HAL_ETH_STATE_STARTED )
                        {
                            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Eth Not Started\n" ) );
                        }
                        if( xEthHandle.ErrorCode & HAL_ETH_ERROR_BUSY )
                        {
                            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Tx Busy\n" ) );
                            xHalResult = HAL_ETH_ReleaseTxPacket( &xEthHandle );
                            configASSERT( xHalResult == HAL_OK );
                        }
                    }
                }
                else
                {
                    xSemaphoreGive( xTxDescSem );
                    FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Process Busy\n" ) );
                }
            }
            else
            {
                FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: No Descriptors Available\n" ) );
            }
        }
        else
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Link Down\n" ) );
        }
    }
    else
    {
        FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Invalid Buffer\n" ) );
    }

    if( xReleaseAfterSend != pdFALSE )
    {
        vReleaseNetworkBufferAndDescriptor( pxDescriptor );
    }

    /*if( xResult == pdFAIL )
    {
        FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Failed\n" ) );
        xTaskNotify( xEMACTaskHandle, eMacEventErrTx, eSetBits );
    }*/

    return xResult;
}

/*-----------------------------------------------------------*/

static UBaseType_t prvNetworkInterfaceInput( void )
{
    UBaseType_t xResult = 0;
    #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
        NetworkBufferDescriptor_t * pxStartDescriptor = NULL;
        NetworkBufferDescriptor_t * pxEndDescriptor = NULL;
    #endif
    NetworkBufferDescriptor_t * pxCurDescriptor = NULL;

    while ( ( HAL_ETH_ReadData( &xEthHandle, ( void ** ) &pxCurDescriptor ) == HAL_OK ) )
    {
        /* configASSERT( xEthHandle.RxDescList.RxDataLength <= EMAC_DATA_BUFFER_SIZE ); */
        if( pxCurDescriptor == NULL )
        {
            /* Buffer was dropped, ignore packet */
            continue;
        }
        iptraceNETWORK_INTERFACE_INPUT( pxCurDescriptor->xDataLength, pxCurDescriptor->pucEthernetBuffer );
        ++xResult;
        pxCurDescriptor->pxInterface = pxMyInterface;
        pxCurDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint( pxCurDescriptor->pxInterface, pxCurDescriptor->pucEthernetBuffer );
        #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
            if ( pxStartDescriptor == NULL )
            {
                pxStartDescriptor = pxCurDescriptor;
            }
            else if ( pxEndDescriptor != NULL )
            {
                pxEndDescriptor->pxNextBuffer = pxCurDescriptor;
            }
            pxEndDescriptor = pxCurDescriptor;
        #else
            xRxEvent.pvData = ( void * ) pxCurDescriptor;
            if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 20U ) != pdPASS )
            {
                iptraceETHERNET_RX_EVENT_LOST();
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInput: xSendEventStructToIPTask failed\n" ) );
                vReleaseNetworkBufferAndDescriptor( pxCurDescriptor );
            }
        #endif
    }

    #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
        if( xResult > 0 )
        {
            const IPStackEvent_t xRxEvent = {
                .eEventType = eNetworkRxEvent,
                .pvData = ( void * ) pxStartDescriptor,
            };
            if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 100U ) != pdPASS )
            {
                iptraceETHERNET_RX_EVENT_LOST();
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInput: xSendEventStructToIPTask failed\n" ) );
                NetworkBufferDescriptor_t * pxDescriptorToClear = pxStartDescriptor;
                do {
                    NetworkBufferDescriptor_t * pxNext = pxDescriptorToClear->pxNextBuffer;
                    vReleaseNetworkBufferAndDescriptor( pxDescriptorToClear );
                    pxDescriptorToClear = pxNext;
                } while( pxDescriptorToClear != NULL );
            }
        }
    #endif

    if( xResult == 0 )
    {
        ( void ) xTaskNotify( xEMACTaskHandle, eMacEventErrRx, eSetBits );
    }

    configASSERT( xEthHandle.ErrorCode != HAL_ETH_ERROR_PARAM );
    if( xEthHandle.gState != HAL_ETH_STATE_STARTED )
    {
        ( void ) xTaskNotify( xEMACTaskHandle, eMacEventErrEth, eSetBits );
    }

    return ( BaseType_t ) ( xResult > 0 );
}

/*-----------------------------------------------------------*/

static void prvEMACHandlerTask( void * pvParameters )
{
    ( void ) pvParameters;

    for( ;; )
    {
        BaseType_t xResult = 0U;
        uint32_t ulISREvents = 0U;

        if ( xTaskNotifyWait( 0U, eMacEventAll, &ulISREvents, pdMS_TO_TICKS( 100UL ) ) == pdTRUE )
        {
            HAL_StatusTypeDef xHalResult;

            if( ( ulISREvents & eMacEventRx ) != 0 )
            {
                xResult = ( prvNetworkInterfaceInput() > 0 );
            }

            if( ( ulISREvents & eMacEventTx ) != 0 )
            {
                if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( 1000U ) ) != pdFALSE )
                {
                    xHalResult = HAL_ETH_ReleaseTxPacket( &xEthHandle );
                    configASSERT( xHalResult == HAL_OK );
                    ( void ) xSemaphoreGive( xTxMutex );
                }
            }
            if( ( ulISREvents & eMacEventErrTx ) != 0 )
            {
                if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( 1000U ) ) != pdFALSE )
                {
                    xHalResult = HAL_ETH_ReleaseTxPacket( &xEthHandle );
                    configASSERT( xHalResult == HAL_OK );
                    while( ETH_TX_DESC_CNT - uxQueueMessagesWaiting( ( QueueHandle_t ) xTxDescSem ) > xEthHandle.TxDescList.BuffersInUse )
                    {
                        ( void ) xSemaphoreGive( xTxDescSem );
                    }
                }
            }

            if( ( ulISREvents & eMacEventErrRx ) != 0 )
            {
                /*do {
                    xResult = ( prvNetworkInterfaceInput() > 0 );
                } while ( xResult != pdFALSE );
                xResult = pdTRUE;*/
            }

            if( ( ulISREvents & eMacEventErrEth ) != 0 )
            {
                /* xEthHandle.gState */
                /* xEthHandle.ErrorCode */
            }

            if( ( ulISREvents & eMacEventErrMac ) != 0 )
            {
                /* xEthHandle.MACErrorCode */
            }

            if( ( ulISREvents & eMacEventErrDma ) != 0 )
            {
                /* TODO: Does this recover from fatal bus error? */
                if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( 5000U ) ) != pdFALSE )
                {
                    /* xEthHandle.DMAErrorCode */
                    xEthHandle.gState = HAL_ETH_STATE_STARTED;
                    xHalResult = HAL_ETH_Stop_IT( &xEthHandle );
                    configASSERT( xHalResult == HAL_OK );
                    configASSERT( xEthHandle.gState == HAL_ETH_STATE_READY );
                    configASSERT( xEthHandle.RxDescList.ItMode == 0U);
                    xHalResult = HAL_ETH_DeInit( &xEthHandle );
                    configASSERT( xHalResult == HAL_OK );
                    configASSERT( xEthHandle.gState == HAL_ETH_STATE_RESET );
                    xHalResult = HAL_ETH_Init( &xEthHandle );
                    configASSERT( xHalResult == HAL_OK );
                    configASSERT( xEthHandle.ErrorCode == HAL_ETH_ERROR_NONE );
                    configASSERT( xEthHandle.gState == HAL_ETH_STATE_READY );
                    xHalResult = HAL_ETH_Start_IT( &xEthHandle );
                    configASSERT( xHalResult == HAL_OK );
                    configASSERT( xEthHandle.gState == HAL_ETH_STATE_STARTED );
                    configASSERT( xEthHandle.RxDescList.ItMode == 1U);
                    xSemaphoreGive( xTxMutex );
                }
            }

            (void) xHalResult;
        }

        if( xPhyCheckLinkStatus( &xPhyObject, xResult ) != pdFALSE )
        {
            if( xEthHandle.gState != HAL_ETH_STATE_BUSY )
            {
                prvEthernetUpdateConfig();
            }
        }
    }
}

/*-----------------------------------------------------------*/

static BaseType_t prvAcceptPacket( const NetworkBufferDescriptor_t * const pxDescriptor )
{
    BaseType_t xResult = pdFALSE;

    uint32_t pErrorCode = 0;
    const HAL_StatusTypeDef xHalResult = HAL_ETH_GetRxDataErrorCode( &xEthHandle, &pErrorCode );
    configASSERT( xHalResult == HAL_OK );
    (void) xHalResult;

    /* Fxx - ETH_DMARXDESC_DBE | ETH_DMARXDESC_RE | ETH_DMARXDESC_OE  | ETH_DMARXDESC_RWT | ETH_DMARXDESC_LC | ETH_DMARXDESC_CE | ETH_DMARXDESC_DE | ETH_DMARXDESC_IPV4HCE */
    /* Hxx - ETH_DMARXNDESCWBF_DE | ETH_DMARXNDESCWBF_RE | ETH_DMARXNDESCWBF_OE | ETH_DMARXNDESCWBF_RWT | ETH_DMARXNDESCWBF_GP | ETH_DMARXNDESCWBF_CE */

    if ( pErrorCode == 0 )
    {
        const eFrameProcessingResult_t xFrameProcessingResult = ipCONSIDER_FRAME_FOR_PROCESSING( pxDescriptor->pucEthernetBuffer );
        if( xFrameProcessingResult == eProcessBuffer )
        {
            xResult = pdTRUE;
        }
        else
        {
            /* Other Enum Values Are Invalid */
            configASSERT( xFrameProcessingResult == eReleaseBuffer );
        }
    }

    return xResult;
}

/*-----------------------------------------------------------*/

static BaseType_t prvPhyReadReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t * pulValue )
{
    BaseType_t xResult = -1;
    if( HAL_ETH_ReadPHYRegister( &xEthHandle, ( uint32_t ) xAddress, ( uint32_t ) xRegister, pulValue ) == HAL_OK )
    {
        xResult = 0;
    }
    return xResult;
}

/*-----------------------------------------------------------*/

static BaseType_t prvPhyWriteReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue )
{
    BaseType_t xResult = -1;
    if( HAL_ETH_WritePHYRegister( &xEthHandle, ( uint32_t ) xAddress, ( uint32_t ) xRegister, ulValue ) == HAL_OK )
    {
        xResult = 0;
    }
    return xResult;
}

/*-----------------------------------------------------------*/

static void prvEthernetUpdateConfig( void )
{
    BaseType_t xResult;
    HAL_StatusTypeDef xHalResult;

    if( xSTM32_GetPhyLinkStatus( pxMyInterface ) != pdFAIL )
    {
        xResult = xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) );
        configASSERT( xResult == 0 );

        xHalResult = HAL_ETH_GetMACConfig( &xEthHandle , &xMACConfig );
        configASSERT( xHalResult == HAL_OK );

        xMACConfig.DuplexMode = ( xPhyObject.xPhyProperties.ucDuplex == PHY_DUPLEX_FULL ) ? ETH_FULLDUPLEX_MODE : ETH_HALFDUPLEX_MODE;
        xMACConfig.Speed = ( xPhyObject.xPhyProperties.ucSpeed == PHY_SPEED_10 ) ? ETH_SPEED_10M : ETH_SPEED_100M;

        xHalResult = HAL_ETH_SetMACConfig( &xEthHandle, &xMACConfig );
        configASSERT( xHalResult == HAL_OK );

        xHalResult = HAL_ETH_Start_IT( &xEthHandle );
        configASSERT( xHalResult == HAL_OK );
    }
    else
    {
        /* iptraceNETWORK_INTERFACE_STATUS_CHANGE(); */
        xHalResult = HAL_ETH_Stop_IT( &xEthHandle );
        configASSERT( xHalResult == HAL_OK );

        #if ( ipconfigSUPPORT_NETWORK_DOWN_EVENT != 0 )
            FreeRTOS_NetworkDown( pxMyInterface );
        #endif
    }

    (void) xHalResult;
    (void) xResult;
}

/*-----------------------------------------------------------*/

/*static void prvMACAddressConfig( ETH_HandleTypeDef * heth, uint32_t ulIndex, uint8_t * addr )
{
    uint32_t ulTempReg;

    ( void ) heth;

    ulTempReg = 0x80000000ul | ( ( uint32_t ) addr[ 5 ] << 8 ) | ( uint32_t ) addr[ 4 ];

    ( *( __IO uint32_t * ) ( ( uint32_t ) ( ETH_MAC_ADDR_HBASE + ulIndex ) ) ) = ulTempReg;

    ulTempReg = ( ( uint32_t ) addr[ 3 ] << 24 ) | ( ( uint32_t ) addr[ 2 ] << 16 ) | ( ( uint32_t ) addr[ 1 ] << 8 ) | addr[ 0 ];

    ( *( __IO uint32_t * ) ( ( uint32_t ) ( ETH_MAC_ADDR_LBASE + ulIndex ) ) ) = ulTempReg;
}*/

/*-----------------------------------------------------------*/

void ETH_IRQHandler( void )
{
    HAL_ETH_IRQHandler( &xEthHandle );
}

/*-----------------------------------------------------------*/

void HAL_ETH_ErrorCallback( ETH_HandleTypeDef *heth )
{
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    if( heth->ErrorCode & HAL_ETH_ERROR_DMA )
    {
        if( heth->DMAErrorCode )
        {
             /*volatile uint32_t errs = heth->Instance->DMASR;
             #if defined ( STM32H5 ) || defined ( STM32H7 )
                ETH_DMARXNDESCWBF_ERRORS_MASK
             #elif defined ( STM32F4 ) || defined ( STM32F7 )
                 HAL_StatusTypeDef HAL_ETH_GetRxDataErrorCode(ETH_HandleTypeDef *heth, uint32_t *pErrorCode)
                ETH_DMARXDESC_ERRORS_MASK
            #endif*/
            /*ETH_DMA_RX_NO_ERROR_FLAG
            ETH_DMA_RX_DESC_READ_ERROR_FLAG
            ETH_DMA_RX_DESC_WRITE_ERROR_FLAG
            ETH_DMA_RX_BUFFER_READ_ERROR_FLAG
            ETH_DMA_RX_BUFFER_WRITE_ERROR_FLAG
            ETH_DMA_TX_NO_ERROR_FLAG
            ETH_DMA_TX_DESC_READ_ERROR_FLAG
            ETH_DMA_TX_DESC_WRITE_ERROR_FLAG
            ETH_DMA_TX_BUFFER_READ_ERROR_FLAG
            ETH_DMA_TX_BUFFER_WRITE_ERROR_FLAG
            ETH_DMA_CONTEXT_DESC_ERROR_FLAG
            ETH_DMA_FATAL_BUS_ERROR_FLAG
            ETH_DMA_EARLY_TX_IT_FLAG
            ETH_DMA_RX_WATCHDOG_TIMEOUT_FLAG
            ETH_DMA_RX_PROCESS_STOPPED_FLAG
            ETH_DMA_RX_BUFFER_UNAVAILABLE_FLAG
            ETH_DMA_TX_PROCESS_STOPPED_FLAG
            ETH_DMA_OVERFLOW_RXFIFOCOUNTER
            ETH_DMA_OVERFLOW_MISSEDFRAMECOUNTER*/

            if( heth->gState == HAL_ETH_STATE_ERROR )
            {
                /* fatal bus error occurred */
                /* Fxx - ETH_DMASR_FBES | ETH_DMASR_TPS | ETH_DMASR_RPS */
                /* Hxx - ETH_DMACSR_FBE | ETH_DMACSR_TPS | ETH_DMACSR_RPS */
                ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrDma, eSetBits, &xHigherPriorityTaskWoken );
            }
            else
            {
                /* Fxx - ETH_DMASR_ETS | ETH_DMASR_RWTS | ETH_DMASR_RBUS | ETH_DMASR_AIS */
                /* Hxx - ETH_DMACSR_CDE | ETH_DMACSR_ETI | ETH_DMACSR_RWT | ETH_DMACSR_RBU | ETH_DMACSR_AIS */
                #if defined( STM32F4 ) || defined ( STM32F7 )
                    if( ( heth->DMAErrorCode & ETH_DMASR_TBUS ) == ETH_DMASR_TBUS)
                    {
                        ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrTx, eSetBits, &xHigherPriorityTaskWoken );
                    }

                    if( ( heth->DMAErrorCode & ETH_DMASR_RBUS ) == ETH_DMASR_RBUS)
                    {
                        ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrRx, eSetBits, &xHigherPriorityTaskWoken );
                        /*ETH_DRIBBLE_BIT_ERROR
                        ETH_RECEIVE_ERROR
                        ETH_RECEIVE_OVERFLOW
                        ETH_WATCHDOG_TIMEOUT
                        ETH_GIANT_PACKET
                        ETH_CRC_ERROR
                        ETH_VLAN_FILTER_PASS
                        ETH_DEST_ADDRESS_FAIL
                        ETH_SOURCE_ADDRESS_FAIL*/
                    }
                #endif
            }
        }
    }

    if( heth->ErrorCode & HAL_ETH_ERROR_MAC )
    {
        if( heth->MACErrorCode )
        {
            /*ETH_RECEIVE_WATCHDOG_TIMEOUT
            ETH_EXECESSIVE_COLLISIONS
            ETH_LATE_COLLISIONS
            ETH_EXECESSIVE_DEFERRAL
            ETH_LOSS_OF_CARRIER
            ETH_NO_CARRIER
            ETH_TRANSMIT_JABBR_TIMEOUT*/
            ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrMac, eSetBits, &xHigherPriorityTaskWoken );
        }
    }
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}

/*-----------------------------------------------------------*/

void HAL_ETH_RxCpltCallback( ETH_HandleTypeDef * heth )
{
    static size_t uxMostRXDescsUsed = 0U;

    const size_t uxRxUsed = heth->RxDescList.RxDescCnt;

    if( uxMostRXDescsUsed < uxRxUsed )
    {
        uxMostRXDescsUsed = uxRxUsed;
    }

    iptraceNETWORK_INTERFACE_RECEIVE();

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventRx, eSetBits, &xHigherPriorityTaskWoken );
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}

/*-----------------------------------------------------------*/

void HAL_ETH_RxAllocateCallback( uint8_t **buff )
{
    const NetworkBufferDescriptor_t * pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( EMAC_DATA_BUFFER_SIZE, pdMS_TO_TICKS( 200U ) );
    if( pxBufferDescriptor != NULL )
    {
        *buff = pxBufferDescriptor->pucEthernetBuffer;
    }
    else
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxAllocateCallback: failed\n" ) );
    }
}

/*-----------------------------------------------------------*/

void HAL_ETH_RxLinkCallback( void **pStart, void **pEnd, uint8_t *buff, uint16_t Length )
{
    NetworkBufferDescriptor_t ** const pStartDescriptor = ( NetworkBufferDescriptor_t ** ) pStart;
    NetworkBufferDescriptor_t ** const pEndDescriptor = ( NetworkBufferDescriptor_t ** ) pEnd;
    NetworkBufferDescriptor_t * const pxCurDescriptor = pxPacketBuffer_to_NetworkBuffer( ( const void * ) buff );
    if ( Length <= EMAC_DATA_BUFFER_SIZE && prvAcceptPacket( pxCurDescriptor ) == pdTRUE )
    {
        pxCurDescriptor->xDataLength = Length;
        #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
            pxCurDescriptor->pxNextBuffer = NULL;
        #endif
        if( *pStartDescriptor == NULL )
        {
            *pStartDescriptor = pxCurDescriptor;
        }
        #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
            else if( pEndDescriptor != NULL )
            {
                ( *pEndDescriptor )->pxNextBuffer = pxCurDescriptor;
            }
        #endif
        *pEndDescriptor = pxCurDescriptor;
        /* Only single buffer packets are supported */
        configASSERT( *pStartDescriptor == *pEndDescriptor );
    }
    else
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxLinkCallback: Buffer Dropped\n" ) );
        NetworkBufferDescriptor_t * pxDescriptorToClear = pxCurDescriptor;
        do {
            #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
                NetworkBufferDescriptor_t * const pxNext = pxDescriptorToClear->pxNextBuffer;
            #else
                NetworkBufferDescriptor_t * const pxNext = NULL;
            #endif
            vReleaseNetworkBufferAndDescriptor( pxDescriptorToClear );
            pxDescriptorToClear = pxNext;
        } while( pxDescriptorToClear != NULL );
    }
}

/*-----------------------------------------------------------*/

void HAL_ETH_TxCpltCallback( ETH_HandleTypeDef * heth )
{
    static size_t uxMostTXDescsUsed = 0U;

    const size_t uxTxUsed = heth->TxDescList.BuffersInUse;

    if( uxMostTXDescsUsed < uxTxUsed )
    {
        uxMostTXDescsUsed = uxTxUsed;
    }

    iptraceNETWORK_INTERFACE_TRANSMIT();

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    /* vTaskNotifyGiveIndexedFromISR( xEMACTaskHandle, TX_INDEX, &xHigherPriorityTaskWoken ); */
    ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventTx, eSetBits, &xHigherPriorityTaskWoken );
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );

    /* if( xBufferAllocFixedSize == pdTRUE )
    {
        if( xSemaphoreTakeFromISR( xTxMutex, &xHigherPriorityTaskWoken ) != pdFALSE )
        {
            const HAL_StatusTypeDef xHalResult = HAL_ETH_ReleaseTxPacket( &xEthHandle );
            configASSERT( xHalResult == HAL_OK );
            ( void ) xSemaphoreGiveFromISR( xTxMutex, &xHigherPriorityTaskWoken );
            portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
        }
    } */
}

/*-----------------------------------------------------------*/

void HAL_ETH_TxFreeCallback( uint32_t *buff )
{
    NetworkBufferDescriptor_t * const pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) buff;
    vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    ( void ) xSemaphoreGive( xTxDescSem );

    /*
    if( xBufferAllocFixedSize == pdTRUE )
    {
        BaseType_t xHigherPriorityTaskWoken = pdFALSE;
        ( void ) xReleaseNetworkBufferFromISR( pxNetworkBuffer );
        ( void ) xSemaphoreGiveFromISR( xTxDescSem, &xHigherPriorityTaskWoken );
        portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
    }
    */
}

/*-----------------------------------------------------------*/
