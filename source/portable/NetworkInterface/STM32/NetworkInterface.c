/*
 * Some constants, hardware definitions and comments taken from ST's HAL driver
 * library, COPYRIGHT(c) 2017 STMicroelectronics.
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
#elif defined( STM32F2 )
    #error This NetworkInterface is incompatible with STM32F2 - Use Legacy NetworkInterface
#else
    #error Unknown STM32 Family for NetworkInterface
#endif

/*-----------------------------------------------------------*/

#if ( ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 ) || ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 ) )
    #if ( ipconfigPORT_SUPPRESS_WARNING == 0 )
        #warning Consider enabling checksum offloading for NetworkInterface
    #endif
#endif

#if ( ( ipconfigNETWORK_MTU < ETH_MIN_PAYLOAD ) || ( ipconfigNETWORK_MTU > ETH_MAX_PAYLOAD ) )
    #if ( ipconfigPORT_SUPPRESS_WARNING == 0 )
        #warning Unsupported ipconfigNETWORK_MTU size
    #endif
#endif

/*-----------------------------------------------------------*/

#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
    #define niEMAC_CONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )   eProcessBuffer
#else
    #define niEMAC_CONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )   eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

#define niEMAC_TX_DESC_SECTION    ".TxDescripSection"
#define niEMAC_RX_DESC_SECTION    ".RxDescripSection"
#define niEMAC_BUFFERS_SECTION    ".EthBuffersSection"

/*
 * TODO: Cache Handling
 * This is only for F7 which uses M7, H5 uses M33, how does this work with dual core H7 M7/M4?
 * Can probably align by portBYTE_ALIGNMENT if not cached
 */
#ifdef __SCB_DCACHE_LINE_SIZE
    #define niEMAC_CACHE_LINE_SIZE  __SCB_DCACHE_LINE_SIZE
#else
    #define niEMAC_CACHE_LINE_SIZE  32U
#endif

#define niEMAC_DATA_BUFFER_SIZE   ( ( ipTOTAL_ETHERNET_FRAME_SIZE + portBYTE_ALIGNMENT ) & ~portBYTE_ALIGNMENT_MASK )
#define niEMAC_TOTAL_ALIGNMENT_MASK   ( niEMAC_CACHE_LINE_SIZE - 1U )
#define niEMAC_TOTAL_BUFFER_SIZE  ( ( niEMAC_DATA_BUFFER_SIZE + ipBUFFER_PADDING + niEMAC_CACHE_LINE_SIZE ) & ~niEMAC_TOTAL_ALIGNMENT_MASK )

#define niEMAC_MAX_BLOCK_TIME_MS    100U
#define niEMAC_DESCRIPTOR_WAIT_TIME_MS    200U

#define niEMAC_TASK_NAME    "EMAC_STM32"
#define niEMAC_TASK_PRIORITY    ( configMAX_PRIORITIES - 1 )
#define niEMAC_TASK_STACK_SIZE    ( 4U * configMINIMAL_STACK_SIZE )

#define niEMAC_TX_MUTEX_NAME    "EMAC_TxMutex"
#define niEMAC_TX_DESC_SEM_NAME    "EMAC_TxDescSem"

#define niEMAC_AUTO_NEGOTIATION    1
#define niEMAC_AUTO_CROSS    1

#if ( niEMAC_AUTO_NEGOTIATION == 0 )
    #define niEMAC_CROSSED_LINK    1
    #define niEMAC_USE_100MB    1
    #define niEMAC_USE_FULL_DUPLEX    1
#endif

#define niEMAC_USE_RMII 1


/*-----------------------------------------------------------*/

/* Interrupt events to process: reception, transmission and error handling. */
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
    eMacEthInit, /* Must initialise ETH. */
    eMacPhyInit, /* Must initialise PHY. */
    eMacPhyStart, /* Must start PHY. */
    eMacTaskStart, /* Must start deferred interrupt handler task. */
    eMacEthStart, /* Must start ETH. */
    eMacInitComplete /* Initialisation was successful. */
} eMAC_INIT_STATUS_TYPE;

/*-----------------------------------------------------------*/

NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t * pxInterface );

static BaseType_t prvNetworkInterfaceInitialise( NetworkInterface_t * pxInterface );

static BaseType_t prvNetworkInterfaceOutput( NetworkInterface_t * pxInterface, NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend );

static UBaseType_t prvNetworkInterfaceInput( void );

static portTASK_FUNCTION_PROTO( prvEMACHandlerTask, pvParameters ) __NO_RETURN;

static BaseType_t prvAcceptPacket( const NetworkBufferDescriptor_t * const pxDescriptor );

static BaseType_t prvGetPhyLinkStatus( NetworkInterface_t * pxInterface );

static BaseType_t prvPhyReadReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t * pulValue );

static BaseType_t prvPhyWriteReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue );

static void prvEthernetUpdateConfig( void );

static void prvMACAddressConfig( ETH_HandleTypeDef * heth, const uint8_t * Addr );

/*-----------------------------------------------------------*/

static ETH_HandleTypeDef xEthHandle;

static ETH_DMADescTypeDef xDMADescRx[ ETH_RX_DESC_CNT ] __ALIGNED( portBYTE_ALIGNMENT ) __attribute__( ( section( niEMAC_RX_DESC_SECTION ) ) );

static ETH_DMADescTypeDef xDMADescTx[ ETH_TX_DESC_CNT ] __ALIGNED( portBYTE_ALIGNMENT ) __attribute__( ( section( niEMAC_TX_DESC_SECTION ) ) );

static NetworkInterface_t * pxMyInterface = NULL;

static TaskHandle_t xEMACTaskHandle;

static SemaphoreHandle_t xTxMutex, xTxDescSem;

static EthernetPhy_t xPhyObject;

static const PhyProperties_t xPHYProperties = {
    #if ( niEMAC_AUTO_NEGOTIATION != 0 )
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
    #else
        #if ( niEMAC_USE_100MB != 0 )
            .ucSpeed = PHY_SPEED_100,
        #else
            .ucSpeed = PHY_SPEED_10,
        #endif

        #if ( niEMAC_USE_FULL_DUPLEX != 0 )
            .ucDuplex = PHY_DUPLEX_FULL,
        #else
            .ucDuplex = PHY_DUPLEX_HALF,
        #endif
    #endif /* if ( niEMAC_AUTO_NEGOTIATION != 0 ) */

    #if ( niEMAC_AUTO_NEGOTIATION != 0 ) && ( niEMAC_AUTO_CROSS != 0 )
        .ucMDI_X = PHY_MDIX_AUTO,
    #elif ( niEMAC_CROSSED_LINK != 0 )
        .ucMDI_X = PHY_MDIX_CROSSED,
    #else
        .ucMDI_X = PHY_MDIX_DIRECT,
    #endif
};

/*-----------------------------------------------------------*/

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ niEMAC_TOTAL_BUFFER_SIZE ] __ALIGNED( niEMAC_CACHE_LINE_SIZE ) __attribute__( ( section( niEMAC_BUFFERS_SECTION ) ) );

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
    pxInterface->pfInitialise = prvNetworkInterfaceInitialise;
    pxInterface->pfOutput = prvNetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = prvGetPhyLinkStatus;

    ( void ) FreeRTOS_AddNetworkInterface( pxInterface );

    pxMyInterface = pxInterface;

    return pxInterface;
}

/*-----------------------------------------------------------*/

static BaseType_t prvGetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    ( void ) pxInterface;

    BaseType_t xReturn = pdFALSE;

    if( xPhyObject.ulLinkStatusMask != 0U )
    {
        xReturn = pdTRUE;
    }

    return xReturn;
}

/*-----------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    BaseType_t xInitResult = pdFAIL;
    BaseType_t xResult;
    HAL_StatusTypeDef xHalResult;

    static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMacEthInit;

    switch( xMacInitStatus )
    {
        default:
            configASSERT( pdFALSE );
            break;

        case eMacEthInit:
            xEthHandle.Instance = ETH;

            NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
            if( pxEndPoint == NULL )
            {
                break;
            }

            xEthHandle.Init.MACAddr = ( uint8_t * ) pxEndPoint->xMACAddress.ucBytes;
            #if ( niEMAC_USE_RMII != 0 )
                xEthHandle.Init.MediaInterface = HAL_ETH_RMII_MODE;
            #else
                xEthHandle.Init.MediaInterface = HAL_ETH_MII_MODE;
            #endif
            xEthHandle.Init.TxDesc = xDMADescTx;
            xEthHandle.Init.RxDesc = xDMADescRx;
            xEthHandle.Init.RxBuffLen = niEMAC_DATA_BUFFER_SIZE;
            configASSERT( xEthHandle.Init.RxBuffLen <= ETH_MAX_PACKET_SIZE );

            ( void ) memset( &xDMADescTx, 0, sizeof( xDMADescTx ) );
            ( void ) memset( &xDMADescRx, 0, sizeof( xDMADescRx ) );

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

            #if 0
                ETH_MACFilterConfigTypeDef xFilterConfig;
                xHalResult = HAL_ETH_GetMACFilterConfig( &xEthHandle, &xFilterConfig );
                configASSERT( xHalResult == HAL_OK );

                xFilterConfig.HashUnicast = ENABLE;
                xFilterConfig.HashMulticast = ENABLE;
                xHalResult = HAL_ETH_SetMACFilterConfig( &xEthHandle, &xFilterConfig );
                configASSERT( xHalResult == HAL_OK );

                const uint32_t ulHashTable = 0x00;
                xHalResult = HAL_ETH_SetHashTable( &xEthHandle, &ulHashTable );
                configASSERT( xHalResult == HAL_OK );
            #endif

            #if ( ipconfigUSE_MDNS != 0 )
                prvMACAddressConfig( &xEthHandle, ( uint8_t * ) xMDNS_MacAddress.ucBytes );
                #if ( ipconfigUSE_IPv6 != 0 )
                    prvMACAddressConfig( &xEthHandle, ( uint8_t * ) xMDNS_MACAddressIPv6.ucBytes );
                #endif
            #endif

            #if ( ipconfigUSE_LLMNR != 0 )
                prvMACAddressConfig( &xEthHandle, ( uint8_t * ) xLLMNR_MacAddress.ucBytes );
                #if ( ipconfigUSE_IPv6 != 0 )
                    prvMACAddressConfig( &xEthHandle, ( uint8_t * ) xLLMNR_MacAddressIPv6.ucBytes );
                #endif
            #endif

            for(; pxEndPoint != NULL; pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
            {
                #if ( ipconfigUSE_IPv6 != 0 )
                    if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
                    {
                        const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = {
                            0x33,
                            0x33,
                            0xff,
                            pxEndPoint->ipv6_settings.xIPAddress.ucBytes[ 13 ],
                            pxEndPoint->ipv6_settings.xIPAddress.ucBytes[ 14 ],
                            pxEndPoint->ipv6_settings.xIPAddress.ucBytes[ 15 ]
                        };
                        prvMACAddressConfig( &xEthHandle, ucMACAddress );
                    }
                #else
                    if( xEthHandle.Init.MACAddr != ( uint8_t * ) pxEndPoint->xMACAddress.ucBytes )
                    {
                        prvMACAddressConfig( &xEthHandle, pxEndPoint->xMACAddress.ucBytes );
                    }
                #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
            }

            #if ( ipconfigUSE_IPv6 != 0 )
                const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x33, 0x33, 0, 0, 0, 0x01 };
                prvMACAddressConfig( &xEthHandle, ucMACAddress );
            #endif

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

            if( prvGetPhyLinkStatus( pxInterface ) == pdFALSE )
            {
                #if ( niEMAC_AUTO_NEGOTIATION != 0 )
                    /* TODO: xPhyStartAutoNegotiation always returns 0, Should return -1 if xPhyGetMask == 0 ? */
                    xResult = xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) );
                #else
                    /* Use predefined (fixed) configuration. */
                    xResult = xPhyFixedValue( &xPhyObject, xPhyGetMask( &xPhyObject ) );
                #endif

                configASSERT( xResult == 0 );
                if ( prvGetPhyLinkStatus( pxInterface ) == pdFALSE )
                {
                    break;
                }
            }

            ETH_MACConfigTypeDef xMACConfig;
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
                    static StaticSemaphore_t xTxMutexBuf;
                    xTxMutex = xSemaphoreCreateMutexStatic( &xTxMutexBuf );
                #else
                    xTxMutex = xSemaphoreCreateMutex();
                #endif
                configASSERT( xTxMutex != NULL );
                if( xTxMutex == NULL )
                {
                    break;
                }
                vQueueAddToRegistry( xTxMutex, niEMAC_TX_MUTEX_NAME );
            }

            if( xTxDescSem == NULL )
            {
                #if ( configSUPPORT_STATIC_ALLOCATION != 0 )
                    static StaticSemaphore_t xTxDescSemBuf;
                    xTxDescSem = xSemaphoreCreateCountingStatic(
                        ( UBaseType_t ) ETH_TX_DESC_CNT,
                        ( UBaseType_t ) ETH_TX_DESC_CNT,
                        &xTxDescSemBuf
                    );
                #else
                    xTxDescSem = xSemaphoreCreateCounting(
                        ( UBaseType_t ) ETH_TX_DESC_CNT,
                        ( UBaseType_t ) ETH_TX_DESC_CNT
                    );
                #endif
                configASSERT( xTxDescSem != NULL );
                if( xTxDescSem == NULL )
                {
                    break;
                }
                vQueueAddToRegistry( xTxDescSem, niEMAC_TX_DESC_SEM_NAME );
            }

            if( xEMACTaskHandle == NULL )
            {
                #if ( configSUPPORT_STATIC_ALLOCATION != 0 )
                    static StackType_t uxEMACTaskStack[ niEMAC_TASK_STACK_SIZE ];
                    static StaticTask_t xEMACTaskTCB;
                    xEMACTaskHandle = xTaskCreateStatic(
                        prvEMACHandlerTask,
                        niEMAC_TASK_NAME,
                        niEMAC_TASK_STACK_SIZE,
                        NULL,
                        niEMAC_TASK_PRIORITY,
                        uxEMACTaskStack,
                        &xEMACTaskTCB
                    );
                #else
                    xResult = xTaskCreate(
                        prvEMACHandlerTask,
                        niEMAC_TASK_NAME,
                        niEMAC_TASK_STACK_SIZE,
                        NULL,
                        niEMAC_TASK_PRIORITY,
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
            if( prvGetPhyLinkStatus( pxInterface ) == pdTRUE )
            {
                xInitResult = pdPASS;
            }
    }

    return xInitResult;
}

/*-----------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceOutput( NetworkInterface_t * pxInterface, NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend )
{
    BaseType_t xResult = pdFAIL;
    configASSERT( pxDescriptor != NULL );
    /* Zero-Copy Only */
    configASSERT( xReleaseAfterSend != pdFALSE );
    iptraceNETWORK_INTERFACE_OUTPUT( pxDescriptor->xDataLength, pxDescriptor->pucEthernetBuffer );

    if( ( pxDescriptor != NULL ) && ( pxDescriptor->pucEthernetBuffer != NULL ) && ( pxDescriptor->xDataLength <= niEMAC_DATA_BUFFER_SIZE ) )
    {
        if( prvGetPhyLinkStatus( pxInterface ) != pdFAIL )
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

            ETH_BufferTypeDef xTxBuffer = {
                .buffer = ( uint8_t * ) pxDescriptor->pucEthernetBuffer,
                .len = pxDescriptor->xDataLength,
                .next = NULL
            };
            configASSERT( xTxBuffer.len <= ETH_MAX_PACKET_SIZE );

            xTxConfig.Length = xTxBuffer.len;
            xTxConfig.TxBuffer = &xTxBuffer;
            xTxConfig.pData = pxDescriptor;

            if( xSemaphoreTake( xTxDescSem, pdMS_TO_TICKS( niEMAC_DESCRIPTOR_WAIT_TIME_MS ) ) != pdFALSE )
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

    if( ( pxDescriptor != NULL ) && ( xReleaseAfterSend != pdFALSE ) )
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
        /* configASSERT( xEthHandle.RxDescList.RxDataLength <= niEMAC_DATA_BUFFER_SIZE ); */
        if( pxCurDescriptor == NULL )
        {
            /* Buffer was dropped, ignore packet */
            continue;
        }
        iptraceNETWORK_INTERFACE_INPUT( pxCurDescriptor->xDataLength, pxCurDescriptor->pucEthernetBuffer );
        ++xResult;
        pxCurDescriptor->pxInterface = pxMyInterface;
        pxCurDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint( pxCurDescriptor->pxInterface, pxCurDescriptor->pucEthernetBuffer );
        /* TODO: check pxEndPoint exists? Check it earlier before getting buffer? */
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
            if( xSendEventStructToIPTask( &xRxEvent, niEMAC_MAX_BLOCK_TIME_MS ) != pdPASS )
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

    return ( ( BaseType_t ) ( xResult > 0 ) );
}

/*-----------------------------------------------------------*/

static portTASK_FUNCTION( prvEMACHandlerTask, pvParameters )
{
    ( void ) pvParameters;

    for( ;; )
    {
        BaseType_t xResult = 0U;
        uint32_t ulISREvents = 0U;

        if ( xTaskNotifyWait( 0U, eMacEventAll, &ulISREvents, pdMS_TO_TICKS( niEMAC_MAX_BLOCK_TIME_MS ) ) == pdTRUE )
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

    /* Fxx - ETH_DMARXDESC_DBE | ETH_DMARXDESC_RE | ETH_DMARXDESC_OE | ETH_DMARXDESC_RWT | ETH_DMARXDESC_LC | ETH_DMARXDESC_CE | ETH_DMARXDESC_DE | ETH_DMARXDESC_IPV4HCE */
    /* Hxx - ETH_DMARXNDESCWBF_DE | ETH_DMARXNDESCWBF_RE | ETH_DMARXNDESCWBF_OE | ETH_DMARXNDESCWBF_RWT | ETH_DMARXNDESCWBF_GP | ETH_DMARXNDESCWBF_CE */

    if ( pErrorCode == 0 )
    {
        /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS, ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES */
        /* ETH_IP_PAYLOAD_UNKNOWN */
        const eFrameProcessingResult_t xFrameProcessingResult = niEMAC_CONSIDER_FRAME_FOR_PROCESSING( pxDescriptor->pucEthernetBuffer );
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
    BaseType_t xResult = pdTRUE;

    if( HAL_ETH_ReadPHYRegister( &xEthHandle, ( uint32_t ) xAddress, ( uint32_t ) xRegister, pulValue ) == HAL_OK )
    {
        xResult = pdFALSE;
    }

    return xResult;
}

/*-----------------------------------------------------------*/

static BaseType_t prvPhyWriteReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue )
{
    BaseType_t xResult = pdTRUE;

    if( HAL_ETH_WritePHYRegister( &xEthHandle, ( uint32_t ) xAddress, ( uint32_t ) xRegister, ulValue ) == HAL_OK )
    {
        xResult = pdFALSE;
    }

    return xResult;
}

/*-----------------------------------------------------------*/

static void prvEthernetUpdateConfig( void )
{
    BaseType_t xResult;
    HAL_StatusTypeDef xHalResult;

    if( prvGetPhyLinkStatus( pxMyInterface ) != pdFAIL )
    {
        #if ( niEMAC_AUTO_NEGOTIATION != 0 )
            /* TODO: xPhyStartAutoNegotiation always returns 0, Should return -1 if xPhyGetMask == 0 ? */
            xResult = xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) );
        #else
            /* Use predefined (fixed) configuration. */
            xResult = xPhyFixedValue( &xPhyObject, xPhyGetMask( &xPhyObject ) );
        #endif
        configASSERT( xResult == 0 );

        ETH_MACConfigTypeDef xMACConfig;
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

static void prvMACAddressConfig( ETH_HandleTypeDef * heth, const uint8_t * addr )
{
    /* ETH_MAC_ADDRESS0 reserved for the primary MAC-address. */
    static BaseType_t xMACEntry = ETH_MAC_ADDRESS1;

    switch(xMACEntry)
    {
        case ETH_MAC_ADDRESS1:
            HAL_ETH_SetSourceMACAddrMatch( &xEthHandle, ETH_MAC_ADDRESS1, addr );
            xMACEntry = ETH_MAC_ADDRESS2;
            break;

        case ETH_MAC_ADDRESS2:
            HAL_ETH_SetSourceMACAddrMatch( &xEthHandle, ETH_MAC_ADDRESS2, addr );
            xMACEntry = ETH_MAC_ADDRESS3;
            break;

        case ETH_MAC_ADDRESS3:
            HAL_ETH_SetSourceMACAddrMatch( &xEthHandle, ETH_MAC_ADDRESS3, addr );
            xMACEntry = ETH_MAC_ADDRESS0;
            break;

        case ETH_MAC_ADDRESS0:
            /* fallthrough */

        default:
            break;
    }
}

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
            if( heth->gState == HAL_ETH_STATE_ERROR )
            {
                /* Fatal bus error occurred */
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
                    }
                #endif
            }
        }
    }

    if( heth->ErrorCode & HAL_ETH_ERROR_MAC )
    {
        if( heth->MACErrorCode )
        {
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
    const NetworkBufferDescriptor_t * pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( niEMAC_DATA_BUFFER_SIZE, pdMS_TO_TICKS( niEMAC_DESCRIPTOR_WAIT_TIME_MS ) );
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
    if ( Length <= niEMAC_DATA_BUFFER_SIZE && prvAcceptPacket( pxCurDescriptor ) == pdTRUE )
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
    ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventTx, eSetBits, &xHigherPriorityTaskWoken );
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}

/*-----------------------------------------------------------*/

void HAL_ETH_TxFreeCallback( uint32_t *buff )
{
    NetworkBufferDescriptor_t * const pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) buff;
    vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    ( void ) xSemaphoreGive( xTxDescSem );
}

/*-----------------------------------------------------------*/
