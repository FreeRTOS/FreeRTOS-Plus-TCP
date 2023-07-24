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
    #include "stm32f4xx_hal_eth.h"
#elif defined( STM32F7 )
    #include "stm32f7xx_hal_eth.h"
#elif defined( STM32H7 )
    #include "stm32h7xx_hal_eth.h"
#elif defined( STM32H5 )
    /* Untested */
    #include "stm32h5xx_hal_eth.h"
#else
    #error Unknown STM32 Family for NetworkInterface
#endif

/*-----------------------------------------------------------*/

/* TODO: This should be made moved from FreeRTOS_IP.c to FreeRTOS_IP_Private.h
 * so that all the network interfaces don't have to keep defining it. */
#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/*-----------------------------------------------------------*/

#define EMAC_DATA_BUFFER_SIZE    ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER )
#define EMAC_TOTAL_BUFFER_SIZE    ( ( EMAC_DATA_BUFFER_SIZE + ipBUFFER_PADDING + 31U ) & ~0x1FuL )

#define EMAC_IF_RX_EVENT    1UL
#define EMAC_IF_TX_EVENT    2UL
#define EMAC_IF_TX_ERR_EVENT    4UL
#define EMAC_IF_RX_ERR_EVENT    8UL
#define EMAC_IF_DMA_ERR_EVENT    16UL
#define EMAC_IF_ETH_ERR_EVENT    32UL
#define EMAC_IF_MAC_ERR_EVENT    64UL
#define EMAC_IF_ALL_EVENT    ( EMAC_IF_RX_EVENT | EMAC_IF_TX_EVENT | EMAC_IF_TX_ERR_EVENT | EMAC_IF_RX_ERR_EVENT | EMAC_IF_DMA_ERR_EVENT | EMAC_IF_ETH_ERR_EVENT | EMAC_IF_MAC_ERR_EVENT )

typedef enum
{
    eMACEthInit,
    eMACPhyInit,
    eMACPhyStart,
    eMACTaskStart,
    eMACEthStart,
    eMACInitComplete
} eMAC_INIT_STATUS_TYPE;

/*-----------------------------------------------------------*/

static BaseType_t xSTM32_GetPhyLinkStatus( NetworkInterface_t * pxInterface );

NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t * pxInterface );

static BaseType_t xSTM32_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface );

static BaseType_t xSTM32_NetworkInterfaceOutput( NetworkInterface_t * pxInterface, NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend );

static UBaseType_t prvNetworkInterfaceInput( void );

static void prvEMACHandlerTask( void * pvParameters ) __attribute__( ( __noreturn__ ) );

static BaseType_t prvAcceptPacket( NetworkBufferDescriptor_t * pxDescriptor );

static BaseType_t prvPhyReadReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t * pulValue );

static BaseType_t prvPhyWriteReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue );

static void prvEthernetUpdateConfig( void );

/* static void prvMACAddressConfig( ETH_HandleTypeDef * heth, uint32_t ulIndex, uint8_t * Addr ); */

#if ( ipconfigIPv4_BACKWARD_COMPATIBLE != 0 )
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t * pxInterface )
    {
        return pxSTM32_FillInterfaceDescriptor( xEMACIndex, pxInterface );
    }
#endif

/*-----------------------------------------------------------*/

static ETH_HandleTypeDef xEthHandle;

static ETH_MACConfigTypeDef xMACConfig;

static ETH_DMADescTypeDef DMARxDscrTab[ ETH_RX_DESC_CNT ] __attribute__( ( section( ".RxDescripSection" ), aligned( 4 ) ) );

static ETH_DMADescTypeDef DMATxDscrTab[ ETH_TX_DESC_CNT ] __attribute__( ( section( ".TxDescripSection" ), aligned( 4 ) ) );

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
    static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ EMAC_TOTAL_BUFFER_SIZE ] __attribute__( ( section( ".EthBuffersSection" ), aligned( 32 ) ) );

    for( size_t ul = 0; ul < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ul++ )
    {
        pxNetworkBuffers[ ul ].pucEthernetBuffer = &( ucNetworkPackets[ ul ][ ipBUFFER_PADDING ] );
        *( ( uint32_t * ) &( ucNetworkPackets[ ul ][ 0 ] ) ) = ( uint32_t ) ( &( pxNetworkBuffers[ ul ] ) );
    }
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

NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t * pxInterface )
{
    static char pcName[ 17 ];

    snprintf( pcName, sizeof( pcName ), "eth%u", ( unsigned ) xEMACIndex );

    memset( pxInterface, '\0', sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;
    pxInterface->pvArgument = ( void * ) xEMACIndex;
    pxInterface->pfInitialise = xSTM32_NetworkInterfaceInitialise;
    pxInterface->pfOutput = xSTM32_NetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = xSTM32_GetPhyLinkStatus;

    FreeRTOS_AddNetworkInterface( pxInterface );

    return pxInterface;
}

/*-----------------------------------------------------------*/

static BaseType_t xSTM32_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    BaseType_t xInitResult = pdFAIL;
    BaseType_t xResult;
    HAL_StatusTypeDef xHalResult;
    NetworkEndPoint_t * pxEndPoint;
    /* BaseType_t xMACEntry = ETH_MAC_ADDRESS1; */ /* ETH_MAC_ADDRESS0 reserved for the primary MAC-address. */

    static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMACEthInit;

    switch( xMacInitStatus )
    {
        default:
            configASSERT( pdFALSE );
            break;

        case eMACEthInit:
            pxMyInterface = pxInterface;

            pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
            configASSERT( pxEndPoint != NULL );

            xEthHandle.Instance = ETH;
            xEthHandle.Init.MACAddr = ( uint8_t * ) pxEndPoint->xMACAddress.ucBytes; /* FreeRTOS_GetMACAddress(); */
            xEthHandle.Init.MediaInterface = HAL_ETH_RMII_MODE;
            xEthHandle.Init.TxDesc = DMATxDscrTab;
            xEthHandle.Init.RxDesc = DMARxDscrTab;
            xEthHandle.Init.RxBuffLen = EMAC_DATA_BUFFER_SIZE;

            memset( &DMATxDscrTab, 0, sizeof( DMATxDscrTab ) );
            memset( &DMARxDscrTab, 0, sizeof( DMARxDscrTab ) );

            #if defined( STM32F7 ) || defined( STM32F4 )
                /* This function doesn't get called in Fxx driver */
                HAL_ETH_SetMDIOClockRange( &xEthHandle );
            #endif

            xHalResult = HAL_ETH_Init( &xEthHandle );
            if( xHalResult != HAL_OK )
            {
                break;
            }
            configASSERT( xEthHandle.ErrorCode == HAL_ETH_ERROR_NONE );
            configASSERT( xEthHandle.gState == HAL_ETH_STATE_READY );

            xMacInitStatus = eMACPhyInit;
            /* Fallthrough */

        case eMACPhyInit:
            vPhyInitialise( &xPhyObject, ( xApplicationPhyReadHook_t ) prvPhyReadReg, ( xApplicationPhyWriteHook_t ) prvPhyWriteReg );

            xResult = xPhyDiscover( &xPhyObject );
            if( xResult == 0 )
            {
                break;
            }

            xResult = xPhyConfigure( &xPhyObject, &xPHYProperties );
            if( xResult != 0 )
            {
                break;
            }

            xMacInitStatus = eMACPhyStart;
            /* Fallthrough */

        case eMACPhyStart:
            if ( xSTM32_GetPhyLinkStatus( pxInterface ) == pdFAIL )
            {
                xResult = xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) );
                /* TODO: xPhyStartAutoNegotiation always returns 0, Should return -1 if xPhyGetMask == 0 ? */
                configASSERT( xResult == 0 );
                if ( xSTM32_GetPhyLinkStatus( pxMyInterface ) == pdFAIL )
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

            xMacInitStatus = eMACTaskStart;
            /* Fallthrough */

        case eMACTaskStart:
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
                        ( 2 * configMINIMAL_STACK_SIZE ),
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
                        ( 2 * configMINIMAL_STACK_SIZE ),
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

            xMacInitStatus = eMACEthStart;
            /* Fallthrough */

        case eMACEthStart:
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
            configASSERT( xEthHandle.RxDescList.ItMode == 1U);

            xMacInitStatus = eMACInitComplete;
            /* Fallthrough */

        case eMACInitComplete:
            configASSERT( xEthHandle.gState != HAL_ETH_STATE_ERROR );
            xInitResult = pdPASS;
    }

    return xInitResult;
}

/*-----------------------------------------------------------*/

static BaseType_t xSTM32_NetworkInterfaceOutput( NetworkInterface_t * pxInterface, NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend )
{
    BaseType_t xResult = pdFAIL;
    configASSERT( pxDescriptor != NULL );
    /* Zero-Copy Only */
    configASSERT( xReleaseAfterSend != pdFALSE );

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
                        xSemaphoreGive( xTxDescSem );
                        configASSERT( xEthHandle.ErrorCode != HAL_ETH_ERROR_PARAM );
                        if( xEthHandle.gState != HAL_ETH_STATE_STARTED )
                        {
                            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Eth Not Started\n" ) );
                        }
                        if( xEthHandle.ErrorCode & HAL_ETH_ERROR_BUSY )
                        {
                            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Tx Busy\n" ) );
                            HAL_ETH_ReleaseTxPacket( &xEthHandle );
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
        xTaskNotify( xEMACTaskHandle, EMAC_IF_TX_ERR_EVENT, eSetBits );
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
    IPStackEvent_t xRxEvent = {
        .eEventType = eNetworkRxEvent,
        .pvData = NULL
    };
    while ( ( HAL_ETH_ReadData( &xEthHandle, ( void ** ) &pxCurDescriptor ) == HAL_OK ) )
    {
        /*configASSERT( xEthHandle.RxDescList.RxDataLength <= EMAC_DATA_BUFFER_SIZE );*/
        xResult++;
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
                vReleaseNetworkBufferAndDescriptor( pxStartDescriptor );
            }
        #endif
    }


    #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
        if( xResult > 0 )
        {
            pxStartDescriptor->pxInterface = pxMyInterface;
            pxStartDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint( pxMyInterface, pxStartDescriptor->pucEthernetBuffer );
            xRxEvent.pvData = ( void * ) pxStartDescriptor;
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
        xTaskNotify( xEMACTaskHandle, EMAC_IF_RX_ERR_EVENT, eSetBits );
    }

    configASSERT( xEthHandle.ErrorCode != HAL_ETH_ERROR_PARAM );
    if( xEthHandle.gState != HAL_ETH_STATE_STARTED )
    {
        xTaskNotify( xEMACTaskHandle, EMAC_IF_ETH_ERR_EVENT, eSetBits );
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

        if ( xTaskNotifyWait( 0U, EMAC_IF_ALL_EVENT, &ulISREvents, pdMS_TO_TICKS( 100UL ) ) == pdTRUE )
        {
            HAL_StatusTypeDef xHalResult;

            if( ( ulISREvents & EMAC_IF_RX_EVENT ) != 0 )
            {
                iptraceNETWORK_INTERFACE_RECEIVE();
                xResult = ( prvNetworkInterfaceInput() > 0 );
            }

            if( ( ulISREvents & EMAC_IF_TX_EVENT ) != 0 )
            {
                iptraceNETWORK_INTERFACE_TRANSMIT();
                if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( 1000U ) ) != pdFALSE )
                {
                    xHalResult = HAL_ETH_ReleaseTxPacket( &xEthHandle );
                    configASSERT( xHalResult == HAL_OK );
                    xSemaphoreGive( xTxMutex );
                }
            }
            if( ( ulISREvents & EMAC_IF_TX_ERR_EVENT ) != 0 )
            {
                if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( 1000U ) ) != pdFALSE )
                {
                    xHalResult = HAL_ETH_ReleaseTxPacket( &xEthHandle );
                    configASSERT( xHalResult == HAL_OK );
                    while( ETH_TX_DESC_CNT - uxQueueMessagesWaiting( ( QueueHandle_t ) xTxDescSem ) > xEthHandle.TxDescList.BuffersInUse )
                    {
                        xSemaphoreGive( xTxDescSem );
                    }
                }
            }

            if( ( ulISREvents & EMAC_IF_RX_ERR_EVENT ) != 0 )
            {
                /*do {
                    xResult = ( prvNetworkInterfaceInput() > 0 );
                } while ( xResult != pdFALSE );
                xResult = pdTRUE;*/
            }

            if( ( ulISREvents & EMAC_IF_ETH_ERR_EVENT ) != 0 )
            {
                /* xEthHandle.gState */
                /* xEthHandle.ErrorCode */
            }

            if( ( ulISREvents & EMAC_IF_MAC_ERR_EVENT ) != 0 )
            {
                /* xEthHandle.MACErrorCode */
            }

            if( ( ulISREvents & EMAC_IF_DMA_ERR_EVENT ) != 0 )
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
        }

        if( xPhyCheckLinkStatus( &xPhyObject, xResult ) != pdFALSE )
        {
            prvEthernetUpdateConfig();

            /*
             #if ( ipconfigSUPPORT_NETWORK_DOWN_EVENT != 0 )
                {
                    if( xGetPhyLinkStatus() == pdFALSE )
                    {
                        FreeRTOS_NetworkDown();
                    }
                }
            */
        }
    }
}

/*-----------------------------------------------------------*/

static BaseType_t prvAcceptPacket( NetworkBufferDescriptor_t * pxDescriptor )
{
    BaseType_t xResult = pdFALSE;

    uint32_t pErrorCode = 0;
    HAL_StatusTypeDef xHalResult = HAL_ETH_GetRxDataErrorCode( &xEthHandle, &pErrorCode );
    configASSERT( xHalResult == HAL_OK );
    /* Fxx - ETH_DMARXDESC_DBE | ETH_DMARXDESC_RE | ETH_DMARXDESC_OE  | ETH_DMARXDESC_RWT | ETH_DMARXDESC_LC | ETH_DMARXDESC_CE | ETH_DMARXDESC_DE | ETH_DMARXDESC_IPV4HCE */
    /* Hxx - ETH_DMARXNDESCWBF_DE | ETH_DMARXNDESCWBF_RE | ETH_DMARXNDESCWBF_OE | ETH_DMARXNDESCWBF_RWT | ETH_DMARXNDESCWBF_GP | ETH_DMARXNDESCWBF_CE */

    if ( pErrorCode == 0 )
    {
        eFrameProcessingResult_t xFrameProcessingResult = ipCONSIDER_FRAME_FOR_PROCESSING( pxDescriptor->pucEthernetBuffer );
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
    }
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

void HAL_ETH_RxCpltCallback( ETH_HandleTypeDef * heth )
{
    static size_t uxMostRXDescsUsed = 0U;

    const size_t uxRxUsed = heth->RxDescList.RxDescCnt;

    if( uxMostRXDescsUsed < uxRxUsed )
    {
        uxMostRXDescsUsed = uxRxUsed;
    }

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_RX_EVENT, eSetBits, &xHigherPriorityTaskWoken );
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
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

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
//  vTaskNotifyGiveIndexedFromISR( xEMACTaskHandle, TX_INDEX, &xHigherPriorityTaskWoken );
    xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_TX_EVENT, eSetBits, &xHigherPriorityTaskWoken );
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}

/*-----------------------------------------------------------*/

void HAL_ETH_ErrorCallback( ETH_HandleTypeDef *heth )
{
    // volatile uint32_t errs = heth->Instance->DMASR;
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    if( HAL_ETH_GetError( heth ) & HAL_ETH_ERROR_DMA )
    {
        if( HAL_ETH_GetDMAError( heth ) )
        {
            if( heth->gState == HAL_ETH_STATE_ERROR )
            {
                /* fatal bus error occurred */
                /* Fxx - ETH_DMASR_FBES | ETH_DMASR_TPS | ETH_DMASR_RPS */
                /* Hxx - ETH_DMACSR_FBE | ETH_DMACSR_TPS | ETH_DMACSR_RPS */
                xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_DMA_ERR_EVENT, eSetBits, &xHigherPriorityTaskWoken );
            }
            else
            {
                /* Fxx - ETH_DMASR_ETS | ETH_DMASR_RWTS | ETH_DMASR_RBUS | ETH_DMASR_AIS */
                /* Hxx - ETH_DMACSR_CDE | ETH_DMACSR_ETI | ETH_DMACSR_RWT | ETH_DMACSR_RBU | ETH_DMACSR_AIS */
                #if defined( STM32F4 ) || defined ( STM32F7 )
                    if((HAL_ETH_GetDMAError(heth) & ETH_DMASR_TBUS) == ETH_DMASR_TBUS)
                    {
                        xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_TX_ERR_EVENT, eSetBits, &xHigherPriorityTaskWoken );
                    }

                    if((HAL_ETH_GetDMAError(heth) & ETH_DMASR_RBUS) == ETH_DMASR_RBUS)
                    {
                        xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_RX_ERR_EVENT, eSetBits, &xHigherPriorityTaskWoken );
                    }
                #endif
            }
        }
    }

    #if defined( STM32H7 ) || defined ( STM32H5 )
        if( HAL_ETH_GetError( heth ) & HAL_ETH_ERROR_MAC )
        {
            if( HAL_ETH_GetMACError( heth ) )
            {
                xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_MAC_ERR_EVENT, eSetBits, &xHigherPriorityTaskWoken );
            }
        }
    #endif
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}

/*-----------------------------------------------------------*/

void HAL_ETH_RxAllocateCallback( uint8_t **buff )
{
    NetworkBufferDescriptor_t * pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( EMAC_DATA_BUFFER_SIZE, pdMS_TO_TICKS( 200U ) );
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
    NetworkBufferDescriptor_t ** pStartDescriptor = ( NetworkBufferDescriptor_t ** ) pStart;
    NetworkBufferDescriptor_t ** pEndDescriptor = ( NetworkBufferDescriptor_t ** ) pEnd;
    NetworkBufferDescriptor_t * pxCurDescriptor = pxPacketBuffer_to_NetworkBuffer( ( const void * ) buff );
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
                NetworkBufferDescriptor_t * pxNext = pxDescriptorToClear->pxNextBuffer;
            #else
                NetworkBufferDescriptor_t * pxNext = NULL;
            #endif
            vReleaseNetworkBufferAndDescriptor( pxDescriptorToClear );
            pxDescriptorToClear = pxNext;
        } while( pxDescriptorToClear != NULL );
    }
}

/*-----------------------------------------------------------*/

void HAL_ETH_TxFreeCallback( uint32_t *buff )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) buff;
    vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    xSemaphoreGive( xTxDescSem );
}

/*-----------------------------------------------------------*/
