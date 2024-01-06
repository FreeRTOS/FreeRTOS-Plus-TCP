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

/*===========================================================================*/
/*                             Config Checks                                 */
/*===========================================================================*/

#if ( ipconfigIS_DISABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM ) || ipconfigIS_DISABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM ) )
    #if ( ipconfigIS_DISABLED( ipconfigPORT_SUPPRESS_WARNING ) )
        #warning Consider enabling checksum offloading for NetworkInterface
    #endif
#endif

#if ( ( ipconfigNETWORK_MTU < ETH_MIN_PAYLOAD ) || ( ipconfigNETWORK_MTU > ETH_MAX_PAYLOAD ) )
    #if ( ipconfigIS_DISABLED( ipconfigPORT_SUPPRESS_WARNING ) )
        #warning Unsupported ipconfigNETWORK_MTU size
    #endif
#endif

#if ( ipconfigIS_DISABLED( configUSE_TASK_NOTIFICATIONS ) )
    #error Task Notifications must be enabled for NetworkInterface
#endif

#ifndef HAL_ETH_MODULE_ENABLED
    #error HAL_ETH_MODULE_ENABLED must be enabled for NetworkInterface
#endif

/*===========================================================================*/
/*                                  Macros                                   */
/*===========================================================================*/

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

#define niEMAC_DATA_BUFFER_SIZE     ( ( ipTOTAL_ETHERNET_FRAME_SIZE + portBYTE_ALIGNMENT ) & ( ( uint32_t ) ~portBYTE_ALIGNMENT_MASK ) )
#define niEMAC_TOTAL_ALIGNMENT_MASK ( niEMAC_CACHE_LINE_SIZE - 1U )
#define niEMAC_TOTAL_BUFFER_SIZE    ( ( niEMAC_DATA_BUFFER_SIZE + ipBUFFER_PADDING + niEMAC_CACHE_LINE_SIZE ) & ~niEMAC_TOTAL_ALIGNMENT_MASK )

#define niEMAC_MAX_BLOCK_TIME_MS        100U
#define niEMAC_DESCRIPTOR_WAIT_TIME_MS  200U

#define niEMAC_TASK_NAME        "EMAC_STM32"
#define niEMAC_TASK_PRIORITY    ( configMAX_PRIORITIES - 1 )
#define niEMAC_TASK_STACK_SIZE  ( 4U * configMINIMAL_STACK_SIZE )

#define niEMAC_TX_MUTEX_NAME    "EMAC_TxMutex"
#define niEMAC_TX_DESC_SEM_NAME "EMAC_TxDescSem"

/* #define niEMAC_PHY_COUNT        1 */

#define niEMAC_AUTO_NEGOTIATION ipconfigENABLE
#define niEMAC_USE_100MB        ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_NEGOTIATION ) )
#define niEMAC_USE_FULL_DUPLEX  ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_NEGOTIATION ) )
#define niEMAC_AUTO_CROSS       ( ipconfigENABLE && ipconfigIS_ENABLED( niEMAC_AUTO_NEGOTIATION  ) )
#define niEMAC_CROSSED_LINK     ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_CROSS  ) )

#define niEMAC_USE_RMII ipconfigENABLE

/*===========================================================================*/
/*                               typedefs                                    */
/*===========================================================================*/

/* Interrupt events to process: reception, transmission and error handling. */
typedef enum {
    eMacEventRx = 1 << 0,
    eMacEventTx = 1 << 1,
    eMacEventErrRx = 1 << 2,
    eMacEventErrTx = 1 << 3,
    eMacEventErrDma = 1 << 4,
    eMacEventErrEth = 1 << 5,
    eMacEventErrMac = 1 << 6,
    eMacEventAll = ( 1 << 7 ) - 1,
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

/* typedef struct xEMACData
{
    ETH_HandleTypeDef xEthHandle;
    EthernetPhy_t xPhyObject;
    TaskHandle_t xEMACTaskHandle;
    SemaphoreHandle_t xTxMutex, xTxDescSem;
    eMAC_INIT_STATUS_TYPE xMacInitStatus;
    BaseType_t xEMACIndex;
} EMACData_t; */

/*===========================================================================*/
/*                      Static Function Declarations                         */
/*===========================================================================*/

static BaseType_t prvPhyReadReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t * pulValue );
static BaseType_t prvPhyWriteReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue );

static BaseType_t prvGetPhyLinkStatus( NetworkInterface_t * pxInterface );
static BaseType_t prvNetworkInterfaceInitialise( NetworkInterface_t * pxInterface );
static BaseType_t prvNetworkInterfaceOutput( NetworkInterface_t * pxInterface, NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend );
/* static void prvAddAllowedMACAddress( const uint8_t * pucMacAddress ); */
/* static void prvRemoveAllowedMACAddress( const uint8_t * pucMacAddress ); */

static BaseType_t prvNetworkInterfaceInput( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface );
static portTASK_FUNCTION_PROTO( prvEMACHandlerTask, pvParameters ) __NO_RETURN;
static BaseType_t prvEMACTaskStart( NetworkInterface_t * pxInterface );

static BaseType_t prvEthConfigInit( ETH_HandleTypeDef * pxEthHandle, const NetworkInterface_t * pxInterface );
static void prvInitMACAddresses( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface );
static BaseType_t prvPhyStart( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface, EthernetPhy_t * pxPhyObject );

static BaseType_t prvMacUpdateConfig( ETH_HandleTypeDef * pxEthHandle, EthernetPhy_t * pxPhyObject );
static uint32_t prvComputeCRC32_MAC( const uint8_t * pucMAC );
static uint32_t prvComputeEthernet_MACHash( const uint8_t * pucMAC );
static void prvSetMAC_HashFilter( ETH_HandleTypeDef * pxEthHandle, const uint8_t * pucMAC );
static void prvMACAddressConfig( ETH_HandleTypeDef * pxEthHandle, uint8_t * pucAddr );

/* static BaseType_t prvAcceptPayload( ETH_HandleTypeDef * pxEthHandle, const uint8_t * const pucEthernetBuffer ); */
static BaseType_t prvAcceptPacket( const NetworkBufferDescriptor_t * const pxDescriptor, uint16_t usLength );

NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t * pxInterface );

/*===========================================================================*/
/*                      Static Variable Declarations                         */
/*===========================================================================*/

/* static EMACData_t xEMACData; */

static ETH_HandleTypeDef xEthHandle;

static EthernetPhy_t xPhyObject;

static TaskHandle_t xEMACTaskHandle;
static SemaphoreHandle_t xTxMutex, xTxDescSem;

static volatile BaseType_t xSwitchRequired;

static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMacEthInit;

/*===========================================================================*/
/*                              Phy Hooks                                    */
/*===========================================================================*/

static BaseType_t prvPhyReadReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t * pulValue )
{
    BaseType_t xResult = pdTRUE;

    if( HAL_ETH_ReadPHYRegister( &xEthHandle, ( uint32_t ) xAddress, ( uint32_t ) xRegister, pulValue ) == HAL_OK )
    {
        xResult = pdFALSE;
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvPhyWriteReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue )
{
    BaseType_t xResult = pdTRUE;

    if( HAL_ETH_WritePHYRegister( &xEthHandle, ( uint32_t ) xAddress, ( uint32_t ) xRegister, ulValue ) == HAL_OK )
    {
        xResult = pdFALSE;
    }

    return xResult;
}

/*===========================================================================*/
/*                      Network Interface Access Hooks                       */
/*===========================================================================*/

static BaseType_t prvGetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    ( void ) pxInterface;

    BaseType_t xReturn = pdFALSE;

    /* const BaseType_t xEMACIndex = *( ( BaseType_t * ) pxInterface->pvArgument ); */

    if( xPhyObject.ulLinkStatusMask != 0U )
    {
        xReturn = pdTRUE;
    }

    return xReturn;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    BaseType_t xInitResult = pdFAIL;
    ETH_HandleTypeDef * pxEthHandle = &xEthHandle;
    EthernetPhy_t * pxPhyObject = &xPhyObject;

    switch( xMacInitStatus )
    {
        default:
            configASSERT( pdFALSE );
            break;

        case eMacEthInit:
            if( prvEthConfigInit( pxEthHandle, pxInterface ) == pdFALSE )
            {
                break;
            }

            /*
            {
                ETH_DMAConfigTypeDef xDMAConfig;
                ( void ) HAL_ETH_GetDMAConfig( pxEthHandle, &xDMAConfig );
                xDMAConfig.
                if( HAL_ETH_SetDMAConfig( pxEthHandle, &xDMAConfig ) != HAL_OK )
                {
                    break;
                }
            }
            */

            prvInitMACAddresses( pxEthHandle, pxInterface );

            xMacInitStatus = eMacPhyInit;
            /* fallthrough */

        case eMacPhyInit:
            vPhyInitialise( pxPhyObject, ( xApplicationPhyReadHook_t ) prvPhyReadReg, ( xApplicationPhyWriteHook_t ) prvPhyWriteReg );

            if( xPhyDiscover( pxPhyObject ) == 0 )
            {
                break;
            }

            xMacInitStatus = eMacPhyStart;
            /* fallthrough */

        case eMacPhyStart:
            if( prvPhyStart( pxEthHandle, pxInterface, pxPhyObject ) == pdFALSE )
            {
                break;
            }

            xMacInitStatus = eMacTaskStart;
            /* fallthrough */

        case eMacTaskStart:
            if( prvEMACTaskStart( pxInterface ) == pdFALSE )
            {
                break;
            }

            xMacInitStatus = eMacEthStart;
            /* fallthrough */

        case eMacEthStart:
            if( pxEthHandle->gState != HAL_ETH_STATE_STARTED )
            {
                if( HAL_ETH_Start_IT( pxEthHandle ) != HAL_OK )
                {
                    break;
                }
            }

            xMacInitStatus = eMacInitComplete;
            /* fallthrough */

        case eMacInitComplete:
            if( prvGetPhyLinkStatus( pxInterface ) == pdTRUE )
            {
                xInitResult = pdPASS;
            }
    }

    return xInitResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceOutput( NetworkInterface_t * pxInterface, NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend )
{
    BaseType_t xResult = pdFAIL;
    ETH_HandleTypeDef * pxEthHandle = &xEthHandle;
    /* Zero-Copy Only */
    configASSERT( xReleaseAfterSend == pdTRUE );

    if( ( xMacInitStatus == eMacInitComplete ) && ( pxEthHandle->gState == HAL_ETH_STATE_STARTED ) )
    {
        if( ( pxDescriptor != NULL ) && ( pxDescriptor->pucEthernetBuffer != NULL ) && ( pxDescriptor->xDataLength <= niEMAC_DATA_BUFFER_SIZE ) )
        {
            if( prvGetPhyLinkStatus( pxInterface ) != pdFAIL )
            {
                if( xSemaphoreTake( xTxDescSem, pdMS_TO_TICKS( niEMAC_DESCRIPTOR_WAIT_TIME_MS ) ) != pdFALSE )
                {
                    if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( niEMAC_MAX_BLOCK_TIME_MS ) ) != pdFALSE )
                    {
                        static ETH_TxPacketConfig xTxConfig = {
                            .CRCPadCtrl = ETH_CRC_PAD_INSERT,
                            #if ( ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM ) )
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

                        xTxConfig.Length = xTxBuffer.len;
                        xTxConfig.TxBuffer = &xTxBuffer;
                        xTxConfig.pData = pxDescriptor;
                        if( HAL_ETH_Transmit_IT( pxEthHandle, &xTxConfig ) == HAL_OK )
                        {
                            /* Released later in deferred task by calling HAL_ETH_ReleaseTxPacket */
                            xReleaseAfterSend = pdFALSE;
                            xResult = pdPASS;
                        }
                        else
                        {
                            ( void ) xSemaphoreGive( xTxDescSem );
                            configASSERT( ( pxEthHandle->ErrorCode & HAL_ETH_ERROR_PARAM ) == 0 );
                            configASSERT( pxEthHandle->gState == HAL_ETH_STATE_STARTED );
                            if( pxEthHandle->ErrorCode & HAL_ETH_ERROR_BUSY )
                            {
                                FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Tx Busy\n" ) );
                            }
                        }
                        ( void ) xSemaphoreGive( xTxMutex );
                    }
                    else
                    {
                        ( void ) xSemaphoreGive( xTxDescSem );
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
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Invalid Descriptor\n" ) );
        }
    }
    else
    {
        FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Eth Not Started\n" ) );
    }

    if( ( pxDescriptor != NULL ) && ( xReleaseAfterSend == pdTRUE ) && ( xResult == pdFAIL ) )
    {
        vReleaseNetworkBufferAndDescriptor( pxDescriptor );
    }

    if( xResult == pdFAIL )
    {
        FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Failed\n" ) );
    }

    return xResult;
}

/*===========================================================================*/
/*                              EMAC Task                                    */
/*===========================================================================*/

static BaseType_t prvNetworkInterfaceInput( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface )
{
    UBaseType_t uxResult = 0;
    /* if( ( xMacInitStatus == eMacInitComplete ) && ( heth->gState == HAL_ETH_STATE_STARTED ) ) */
    #if ( ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) )
        NetworkBufferDescriptor_t * pxStartDescriptor = NULL;
        NetworkBufferDescriptor_t * pxEndDescriptor = NULL;
    #endif
    NetworkBufferDescriptor_t * pxCurDescriptor = NULL;
    IPStackEvent_t xRxEvent;
    xRxEvent.eEventType = eNetworkRxEvent;

    while( HAL_ETH_ReadData( pxEthHandle, ( void ** ) &pxCurDescriptor ) == HAL_OK )
    {
        if( pxCurDescriptor == NULL )
        {
            /* Buffer was dropped, ignore packet */
            continue;
        }
        configASSERT( pxEthHandle->RxDescList.RxDataLength <= niEMAC_DATA_BUFFER_SIZE );
        ++uxResult;
        pxCurDescriptor->pxInterface = pxInterface;
        pxCurDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint( pxCurDescriptor->pxInterface, pxCurDescriptor->pucEthernetBuffer );
        /* TODO: check pxEndPoint exists? Check it earlier before getting buffer? */
        #if ( ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) )
            if( pxStartDescriptor == NULL )
            {
                pxStartDescriptor = pxCurDescriptor;
            }
            else if( pxEndDescriptor != NULL )
            {
                pxEndDescriptor->pxNextBuffer = pxCurDescriptor;
            }
            pxEndDescriptor = pxCurDescriptor;
        #else
            xRxEvent.pvData = ( void * ) pxCurDescriptor;
            if( xSendEventStructToIPTask( &xRxEvent, pdMS_TO_TICKS( niEMAC_MAX_BLOCK_TIME_MS ) ) != pdPASS )
            {
                iptraceETHERNET_RX_EVENT_LOST();
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInput: xSendEventStructToIPTask failed\n" ) );
                vReleaseNetworkBufferAndDescriptor( pxCurDescriptor );
            }
        #endif /* if ( ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) ) */
    }

    #if ( ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) )
        if( uxResult > 0 )
        {
            xRxEvent.pvData = ( void * ) pxStartDescriptor;
            if( xSendEventStructToIPTask( &xRxEvent, pdMS_TO_TICKS( niEMAC_MAX_BLOCK_TIME_MS ) ) != pdPASS )
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
    #endif /* if ( ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) ) */

    if( uxResult == 0 )
    {
        configASSERT( ( pxEthHandle->ErrorCode & HAL_ETH_ERROR_PARAM ) == 0 );
        /*( void ) xTaskNotify( xEMACTaskHandle, eMacEventErrRx, eSetBits );

        if( pxEthHandle->gState != HAL_ETH_STATE_STARTED )
        {
            ( void ) xTaskNotify( xEMACTaskHandle, eMacEventErrEth, eSetBits );
        }*/
    }

    return ( ( BaseType_t ) ( uxResult > 0 ) );
}

/*---------------------------------------------------------------------------*/

static portTASK_FUNCTION( prvEMACHandlerTask, pvParameters )
{
    NetworkInterface_t * pxInterface = ( NetworkInterface_t * ) pvParameters;
    configASSERT( pxInterface );
    ETH_HandleTypeDef * pxEthHandle = &xEthHandle;
    EthernetPhy_t * pxPhyObject = &xPhyObject;

    /* iptraceEMAC_TASK_STARTING(); */

    for( ;; )
    {
        BaseType_t xResult = pdFALSE;
        uint32_t ulISREvents = 0U;

        if( xTaskNotifyWait( 0U, eMacEventAll, &ulISREvents, pdMS_TO_TICKS( niEMAC_MAX_BLOCK_TIME_MS ) ) == pdTRUE )
        {
            if( ( ulISREvents & eMacEventRx ) != 0 )
            {
                xResult = prvNetworkInterfaceInput( pxEthHandle, pxInterface );
            }

            if( ( ulISREvents & eMacEventTx ) != 0 )
            {
                if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( niEMAC_MAX_BLOCK_TIME_MS ) ) != pdFALSE )
                {
                    ( void ) HAL_ETH_ReleaseTxPacket( pxEthHandle );
                    ( void ) xSemaphoreGive( xTxMutex );
                }
            }

            if( ( ulISREvents & eMacEventErrRx ) != 0 )
            {
                /*do {
                    xResult = ( prvNetworkInterfaceInput() > 0 );
                } while ( xResult != pdFALSE );
                xResult = pdTRUE;*/
            }

            if( ( ulISREvents & eMacEventErrTx ) != 0 )
            {
                if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( niEMAC_MAX_BLOCK_TIME_MS ) ) != pdFALSE )
                {
                    ( void ) HAL_ETH_ReleaseTxPacket( pxEthHandle );
                    while( ETH_TX_DESC_CNT - uxQueueMessagesWaiting( ( QueueHandle_t ) xTxDescSem ) > pxEthHandle->TxDescList.BuffersInUse )
                    {
                        ( void ) xSemaphoreGive( xTxDescSem );
                    }
                }
            }

            if( ( ulISREvents & eMacEventErrEth ) != 0 )
            {
                /* pxEthHandle->gState == HAL_ETH_STATE_ERROR */
                /* configASSERT( ( pxEthHandle->ErrorCode & HAL_ETH_ERROR_PARAM ) == 0 ); */
            }

            if( ( ulISREvents & eMacEventErrMac ) != 0 )
            {
                /* pxEthHandle->ErrorCode & HAL_ETH_ERROR_MAC */
                /* pxEthHandle->MACErrorCode */
            }

            if( ( ulISREvents & eMacEventErrDma ) != 0 )
            {
                /* pxEthHandle->ErrorCode & HAL_ETH_ERROR_DMA */
                /* pxEthHandle->DMAErrorCode */
            }
        }

        /* pxEthHandle->gState == HAL_ETH_STATE_ERROR */
        /* configASSERT( ( pxEthHandle->ErrorCode & HAL_ETH_ERROR_PARAM ) == 0 ); */

        if( xPhyCheckLinkStatus( pxPhyObject, xResult ) != pdFALSE )
        {
            if( prvGetPhyLinkStatus( pxInterface ) != pdFALSE )
            {
                if( pxEthHandle->gState == HAL_ETH_STATE_READY )
                {
                    /* Link Was Down */
                    if( prvMacUpdateConfig( pxEthHandle, pxPhyObject ) != pdFALSE )
                    {
                        ( void ) HAL_ETH_Start_IT( pxEthHandle );
                    }
                }
            }
            else
            {
                ( void ) HAL_ETH_Stop_IT( pxEthHandle );
                #if ( ipconfigIS_ENABLED( ipconfigSUPPORT_NETWORK_DOWN_EVENT ) )
                    /* ( void ) HAL_ETH_DeInit( pxEthHandle );
                    xMacInitStatus = eMacEthInit; */
                    FreeRTOS_NetworkDown( pxInterface );
                #endif
            }
        }
    }
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvEMACTaskStart( NetworkInterface_t * pxInterface )
{
    BaseType_t xResult = pdFALSE;

    if( xTxMutex == NULL )
    {
        #if ( ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION ) )
            static StaticSemaphore_t xTxMutexBuf;
            xTxMutex = xSemaphoreCreateMutexStatic( &xTxMutexBuf );
        #else
            xTxMutex = xSemaphoreCreateMutex();
        #endif
        configASSERT( xTxMutex != NULL );
        vQueueAddToRegistry( xTxMutex, niEMAC_TX_MUTEX_NAME );
    }

    if( xTxDescSem == NULL )
    {
        #if ( ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION ) )
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
        vQueueAddToRegistry( xTxDescSem, niEMAC_TX_DESC_SEM_NAME );
    }

    if( xEMACTaskHandle == NULL && ( xTxMutex != NULL ) && ( xTxDescSem != NULL ) )
    {
        #if ( ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION ) )
            static StackType_t uxEMACTaskStack[ niEMAC_TASK_STACK_SIZE ];
            static StaticTask_t xEMACTaskTCB;
            xEMACTaskHandle = xTaskCreateStatic(
                prvEMACHandlerTask,
                niEMAC_TASK_NAME,
                niEMAC_TASK_STACK_SIZE,
                ( void * ) pxInterface,
                niEMAC_TASK_PRIORITY,
                uxEMACTaskStack,
                &xEMACTaskTCB
            );
        #else
            ( void ) xTaskCreate(
                prvEMACHandlerTask,
                niEMAC_TASK_NAME,
                niEMAC_TASK_STACK_SIZE,
                ( void * ) pxInterface,
                niEMAC_TASK_PRIORITY,
                &xEMACTaskHandle
            );
        #endif
    }

    if( xEMACTaskHandle != NULL )
    {
        xResult = pdTRUE;
    }

    return xResult;
}

/*===========================================================================*/
/*                               EMAC Init                                   */
/*===========================================================================*/

static BaseType_t prvEthConfigInit( ETH_HandleTypeDef * pxEthHandle, const NetworkInterface_t * pxInterface )
{
    BaseType_t xResult = pdFALSE;

    pxEthHandle->Instance = ETH;

    #if ( ipconfigIS_ENABLED( niEMAC_USE_RMII ) )
        pxEthHandle->Init.MediaInterface = HAL_ETH_RMII_MODE;
    #else
        pxEthHandle->Init.MediaInterface = HAL_ETH_MII_MODE;
    #endif

    pxEthHandle->Init.RxBuffLen = niEMAC_DATA_BUFFER_SIZE;
    configASSERT( pxEthHandle->Init.RxBuffLen <= ETH_MAX_PACKET_SIZE );
    configASSERT( pxEthHandle->Init.RxBuffLen % 4U == 0 );

    static ETH_DMADescTypeDef xDMADescRx[ ETH_RX_DESC_CNT ] __ALIGNED( portBYTE_ALIGNMENT ) __attribute__( ( section( niEMAC_RX_DESC_SECTION ) ) );
    static ETH_DMADescTypeDef xDMADescTx[ ETH_TX_DESC_CNT ] __ALIGNED( portBYTE_ALIGNMENT ) __attribute__( ( section( niEMAC_TX_DESC_SECTION ) ) );

    pxEthHandle->Init.TxDesc = xDMADescTx;
    pxEthHandle->Init.RxDesc = xDMADescRx;

    ( void ) memset( &xDMADescTx, 0, sizeof( xDMADescTx ) );
    ( void ) memset( &xDMADescRx, 0, sizeof( xDMADescRx ) );

    const NetworkEndPoint_t * const pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
    if( pxEndPoint != NULL )
    {
        pxEthHandle->Init.MACAddr = ( uint8_t * ) pxEndPoint->xMACAddress.ucBytes;

        #if defined( STM32F7 ) || defined( STM32F4 )
            /* This function doesn't get called in Fxx driver */
            HAL_ETH_SetMDIOClockRange( pxEthHandle );
        #endif

        if( HAL_ETH_Init( pxEthHandle ) == HAL_OK )
        {
            xResult = pdTRUE;
        }
        /* else
        {
            pxEthHandle->ErrorCode & HAL_ETH_ERROR_TIMEOUT
        } */
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static void prvInitMACAddresses( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface )
{
    /* #if ( ipconfigIS_ENABLEDipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES ) )
        ETH_MACFilterConfigTypeDef xFilterConfig;
        ( void ) HAL_ETH_GetMACFilterConfig( pxEthHandle, &xFilterConfig );
    #endif */

    #if ( ipconfigIS_ENABLED( ipconfigUSE_MDNS ) )
        prvMACAddressConfig( pxEthHandle, xMDNS_MacAddress.ucBytes );
        #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
            prvMACAddressConfig( pxEthHandle, xMDNS_MACAddressIPv6.ucBytes );
        #endif
    #endif

    #if ( ipconfigIS_ENABLED( ipconfigUSE_LLMNR ) )
        prvMACAddressConfig( pxEthHandle, xLLMNR_MacAddress.ucBytes );
        #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
            prvMACAddressConfig( pxEthHandle, xLLMNR_MacAddressIPv6.ucBytes );
        #endif
    #endif

    for( NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface ); pxEndPoint != NULL; pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
    {
        #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
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
                prvMACAddressConfig( pxEthHandle, ucMACAddress );
            }
        #else
            if( pxEthHandle->Init.MACAddr != ( uint8_t * ) pxEndPoint->xMACAddress.ucBytes )
            {
                prvMACAddressConfig( pxEthHandle, pxEndPoint->xMACAddress.ucBytes );
            }
        #endif /* if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) ) */
    }

    #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
        prvMACAddressConfig( pxEthHandle, pcLOCAL_ALL_NODES_MULTICAST_MAC.ucBytes );
    #endif

    /* #if ( ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES ) )
        ( void ) HAL_ETH_SetMACFilterConfig( pxEthHandle, &xFilterConfig );
    #endif */
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvPhyStart( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface, EthernetPhy_t * pxPhyObject )
{
    BaseType_t xResult = pdFALSE;

    if( prvGetPhyLinkStatus( pxInterface ) == pdFALSE )
    {
        const PhyProperties_t xPhyProperties = {
            #if ( ipconfigIS_ENABLED( niEMAC_AUTO_NEGOTIATION ) )
                .ucSpeed = PHY_SPEED_AUTO,
                .ucDuplex = PHY_DUPLEX_AUTO,
            #else
                .ucSpeed = ipconfigIS_ENABLED( niEMAC_USE_100MB ) ? PHY_SPEED_100 : PHY_SPEED_10,
                .ucDuplex = ipconfigIS_ENABLED( niEMAC_USE_FULL_DUPLEX ) ? PHY_DUPLEX_FULL : PHY_DUPLEX_HALF,
            #endif

            #if ( ipconfigIS_ENABLED( niEMAC_AUTO_CROSS ) )
                .ucMDI_X = PHY_MDIX_AUTO,
            #elif ( ipconfigIS_ENABLED( niEMAC_CROSSED_LINK ) )
                .ucMDI_X = PHY_MDIX_CROSSED,
            #else
                .ucMDI_X = PHY_MDIX_DIRECT,
            #endif
        };

        if( xPhyConfigure( pxPhyObject, &xPhyProperties ) == 0 )
        {
            if( prvMacUpdateConfig( pxEthHandle, pxPhyObject ) != pdFALSE )
            {
                xResult = pdTRUE;
            }
        }
    }
    else
    {
        xResult = pdTRUE;
    }

    return xResult;
}

/*===========================================================================*/
/*                             MAC Helpers                                   */
/*===========================================================================*/

static BaseType_t prvMacUpdateConfig( ETH_HandleTypeDef * pxEthHandle, EthernetPhy_t * pxPhyObject )
{
    BaseType_t xResult = pdFALSE;

    if( pxEthHandle->gState == HAL_ETH_STATE_STARTED )
    {
        ( void ) HAL_ETH_Stop_IT( pxEthHandle );
    }

    ETH_MACConfigTypeDef xMACConfig;
    ( void ) HAL_ETH_GetMACConfig( pxEthHandle , &xMACConfig );
    xMACConfig.ChecksumOffload = ( FunctionalState ) ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM );

    #if ( ipconfigIS_ENABLED( niEMAC_AUTO_NEGOTIATION ) )
        /* TODO: xPhyStartAutoNegotiation always returns 0, Should return -1 if xPhyGetMask == 0 ? */
        ( void ) xPhyStartAutoNegotiation( pxPhyObject, xPhyGetMask( pxPhyObject ) );
        xMACConfig.DuplexMode = ( pxPhyObject->xPhyProperties.ucDuplex == PHY_DUPLEX_FULL ) ? ETH_FULLDUPLEX_MODE : ETH_HALFDUPLEX_MODE;
        xMACConfig.Speed = ( pxPhyObject->xPhyProperties.ucSpeed == PHY_SPEED_10 ) ? ETH_SPEED_10M : ETH_SPEED_100M;
    #else
        pxPhyObject->xPhyPreferences.ucSpeed = ipconfigIS_ENABLED( niEMAC_USE_100MB ) ? PHY_SPEED_100 : PHY_SPEED_10;
        pxPhyObject->xPhyPreferences.ucDuplex = ipconfigIS_ENABLED( niEMAC_USE_FULL_DUPLEX ) ? PHY_DUPLEX_FULL : PHY_DUPLEX_HALF;
        /* ucMDI_X unused */
        /* TODO: xPhyFixedValue always return 0 */
        ( void ) xPhyFixedValue( pxPhyObject, xPhyGetMask( pxPhyObject ) );
        xMACConfig.DuplexMode = pxPhyObject->xPhyPreferences.ucDuplex;
        xMACConfig.Speed = pxPhyObject->xPhyPreferences.ucSpeed;
    #endif

    if( HAL_ETH_SetMACConfig( pxEthHandle, &xMACConfig ) == HAL_OK )
    {
        xResult = pdTRUE;
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

/* Compute the CRC32 of the given MAC address as per IEEE 802.3 CRC32 */
static uint32_t prvComputeCRC32_MAC( const uint8_t * pucMAC )
{
    uint32_t ulCRC32 = 0xFFFFFFFF;

    for( UBaseType_t i = 0; i < 6; ++i )
    {
        ulCRC32 ^= ( uint32_t ) pucMAC[ i ];

        for( UBaseType_t j = 0; j < 8; ++j )
        {
            ulCRC32 >>= 1;
            if( ulCRC32 & 1 )
            {
                /* IEEE 802.3 CRC32 polynomial - 0x04C11DB7 */
                ulCRC32 ^= __RBIT( 0x04C11DB7 );
            }
        }
    }

    ulCRC32 = ~( ulCRC32 );
    return ulCRC32;
}

/*---------------------------------------------------------------------------*/

/* Compute the hash value of a given MAC address to index the bits in the Hash Table */
static uint32_t prvComputeEthernet_MACHash( const uint8_t * pucMAC )
{
    /* Calculate the 32-bit CRC for the MAC */
    const uint32_t ulCRC32 = prvComputeCRC32_MAC( pucMAC );

    /* Perform bitwise reversal on the CRC32 */
    const uint32_t ulHash = __RBIT( ulCRC32 );

    /* Take the upper 6 bits of the above result */
    return ( ulHash >> 26 );
}

/*---------------------------------------------------------------------------*/

/* Update the Hash Table Registers with hash value of the given MAC address */
static void prvSetMAC_HashFilter( ETH_HandleTypeDef * pxEthHandle, const uint8_t * pucMAC )
{
    static uint32_t ulHashTable[ 2 ];

    const uint32_t ulHash = prvComputeEthernet_MACHash( pucMAC );

    /* Use the upper or lower Hash Table Registers
     * to set the required bit based on the ulHash */
    if( ulHash < 32 )
    {
        ulHashTable[ 0 ] = ulHash;
    }
    else
    {
        ulHashTable[ 1 ] = ulHash;
    }

    ( void ) HAL_ETH_SetHashTable( pxEthHandle, ulHashTable );
}

/*---------------------------------------------------------------------------*/

static void prvMACAddressConfig( ETH_HandleTypeDef * pxEthHandle, uint8_t * pucAddr )
{
    /* ETH_MAC_ADDRESS0 reserved for the primary MAC-address. */
    static UBaseType_t uxMACEntry = ETH_MAC_ADDRESS1;

    switch( uxMACEntry )
    {
        case ETH_MAC_ADDRESS1:
            ( void ) HAL_ETH_SetSourceMACAddrMatch( pxEthHandle, uxMACEntry, pucAddr );
            uxMACEntry = ETH_MAC_ADDRESS2;
            break;

        case ETH_MAC_ADDRESS2:
            ( void ) HAL_ETH_SetSourceMACAddrMatch( pxEthHandle, uxMACEntry, pucAddr );
            uxMACEntry = ETH_MAC_ADDRESS3;
            break;

        case ETH_MAC_ADDRESS3:
            ( void ) HAL_ETH_SetSourceMACAddrMatch( pxEthHandle, uxMACEntry, pucAddr );
            uxMACEntry = ETH_MAC_ADDRESS0;
            break;

        case ETH_MAC_ADDRESS0:
            prvSetMAC_HashFilter( pxEthHandle, pucAddr );
            break;

        default:
            break;
    }
}

/*===========================================================================*/
/*                              Rx Helpers                                   */
/*===========================================================================*/

#if 0
#if ( defined( STM32F4 ) || defined( STM32F7 ) )
    #define ETH_IP_HEADER_IPV4   ETH_DMAPTPRXDESC_IPV4PR
    #define ETH_IP_HEADER_IPV6   ETH_DMAPTPRXDESC_IPV6PR

    #define ETH_IP_PAYLOAD_UNKNOWN   0x00000000U
    #define ETH_IP_PAYLOAD_UDP       ETH_DMAPTPRXDESC_IPPT_UDP
    #define ETH_IP_PAYLOAD_TCP       ETH_DMAPTPRXDESC_IPPT_TCP
    #define ETH_IP_PAYLOAD_ICMPN     ETH_DMAPTPRXDESC_IPPT_ICMP
#endif

static BaseType_t prvAcceptPayload( ETH_HandleTypeDef * pxEthHandle, const uint8_t * const pucEthernetBuffer )
{
    BaseType_t xResult = pdFALSE;

    #if ( ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS ) )
        const UBaseType_t uxPayloadType = READ_BIT( heth->RxDescList.pRxLastRxDesc, ETH_DMARXNDESCWBF_PT )
        const ProtocolPacket_t * pxProtPacket = ( const ProtocolPacket_t * ) pucEthernetBuffer;
        const IPHeader_t * pxIPHeader = &( pxProtPacket->xTCPPacket.xIPHeader );
        switch( uxPayloadType )
        {
            case ETH_IP_PAYLOAD_UNKNOWN:
            case ETH_IP_PAYLOAD_UDP:
                if( ( xPortHasUdpSocket( xUDPHeader->usDestinationPort ) )
                #if( ipconfigUSE_DNS == 1 ) * DNS is also UDP. *
                    || ( xUDPHeader->usSourcePort == FreeRTOS_ntohs( ipDNS_PORT ) )
                #endif
                #if( ipconfigUSE_LLMNR == 1 ) * LLMNR is also UDP. *
                    || ( xUDPHeader->usDestinationPort == FreeRTOS_ntohs( ipLLMNR_PORT ) )
                #endif
                #if( ipconfigUSE_NBNS == 1 ) * NBNS is also UDP. *
                    || ( xUDPHeader->usDestinationPort == FreeRTOS_ntohs( ipNBNS_PORT ) )
                #endif
                )
                {
                    xResult = pdTRUE;
                }
                else
                {
                    xResult = pdFALSE;
                }
                break;

            case ETH_IP_PAYLOAD_TCP:
            case ETH_IP_PAYLOAD_ICMPN:
            default:
        }
    #endif

    return xResult;
}
#endif

/*---------------------------------------------------------------------------*/

static BaseType_t prvAcceptPacket( const NetworkBufferDescriptor_t * const pxDescriptor, uint16_t usLength )
{
    BaseType_t xResult = pdFALSE;

    uint32_t ulErrorCode = 0;
    ( void ) HAL_ETH_GetRxDataErrorCode( &xEthHandle, &ulErrorCode );

    if ( ulErrorCode == 0 )
    {
        if( usLength <= niEMAC_DATA_BUFFER_SIZE )
        {
            /* if( prvAcceptPayload( &xEthHandle, pxDescriptor->pucEthernetBuffer ) != pdFALSE )
            {

            }
            else
            {
                FreeRTOS_debug_printf( ( "prvAcceptPacket: Payload discarded\n" ) );
            }
            */

            #if ( ipconfigIS_DISABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES ) )
                xResult = pdTRUE;
            #else
                /* TODO: Handle this in hardware via HAL_ETH_SetMACFilterConfig */
                if( eConsiderFrameForProcessing( pxDescriptor->pucEthernetBuffer ) == eProcessBuffer )
                {
                    xResult = pdTRUE;
                }
                else
                {
                    FreeRTOS_debug_printf( ( "prvAcceptPacket: Frame discarded\n" ) );
                }
            #endif
        }
        else
        {
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Packet size overflow\n" ) );
        }
    }
    else
    {
        FreeRTOS_debug_printf( ( "prvAcceptPacket: Rx Data Error\n" ) );
    }

    return xResult;
}

/*===========================================================================*/
/*                              IRQ Handlers                                 */
/*===========================================================================*/

void ETH_IRQHandler( void )
{
    traceISR_ENTER();

    xSwitchRequired = pdFALSE;
    HAL_ETH_IRQHandler( &xEthHandle );

    portYIELD_FROM_ISR( xSwitchRequired );
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_ErrorCallback( ETH_HandleTypeDef * pxEthHandle )
{
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    if( pxEthHandle->ErrorCode & HAL_ETH_ERROR_DMA )
    {
        if( pxEthHandle->DMAErrorCode )
        {
            if( pxEthHandle->gState == HAL_ETH_STATE_ERROR )
            {
                /* Fatal bus error occurred */
                /* eMacEventErrDma */
                ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrEth, eSetBits, &xHigherPriorityTaskWoken );
            }
            else
            {
                #if defined( STM32F4 ) || defined ( STM32F7 )
                    if( pxEthHandle->DMAErrorCode & ETH_DMASR_TBUS )
                    {
                        ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrTx, eSetBits, &xHigherPriorityTaskWoken );
                    }

                    if( pxEthHandle->DMAErrorCode & ETH_DMASR_RBUS )
                    {
                        /* ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrRx, eSetBits, &xHigherPriorityTaskWoken ); */
                    }
                #elif defined( STM32H5 ) || defined ( STM32H7 )
                    if( pxEthHandle->DMAErrorCode & ETH_DMACSR_TBU )
                    {
                        ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrTx, eSetBits, &xHigherPriorityTaskWoken );
                    }

                    if( pxEthHandle->DMAErrorCode & ETH_DMACSR_RBU )
                    {
                        /* ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrRx, eSetBits, &xHigherPriorityTaskWoken ); */
                    }
                #endif
            }
        }
    }

    if( pxEthHandle->ErrorCode & HAL_ETH_ERROR_MAC )
    {
        if( pxEthHandle->MACErrorCode )
        {
            /* ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrMac, eSetBits, &xHigherPriorityTaskWoken ); */
        }
    }

    configASSERT( ( pxEthHandle->ErrorCode & HAL_ETH_ERROR_PARAM ) == 0 );

    xSwitchRequired |= xHigherPriorityTaskWoken;
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_RxCpltCallback( ETH_HandleTypeDef * pxEthHandle )
{
    static size_t uxMostRXDescsUsed = 0U;

    const size_t uxRxUsed = pxEthHandle->RxDescList.RxDescCnt;

    if( uxMostRXDescsUsed < uxRxUsed )
    {
        uxMostRXDescsUsed = uxRxUsed;
    }

    iptraceNETWORK_INTERFACE_RECEIVE();

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventRx, eSetBits, &xHigherPriorityTaskWoken );
    xSwitchRequired |= xHigherPriorityTaskWoken;
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_TxCpltCallback( ETH_HandleTypeDef * pxEthHandle )
{
    static size_t uxMostTXDescsUsed = 0U;

    const size_t uxTxUsed = pxEthHandle->TxDescList.BuffersInUse;

    if( uxMostTXDescsUsed < uxTxUsed )
    {
        uxMostTXDescsUsed = uxTxUsed;
    }

    iptraceNETWORK_INTERFACE_TRANSMIT();

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventTx, eSetBits, &xHigherPriorityTaskWoken );
    xSwitchRequired |= xHigherPriorityTaskWoken;
}

/*===========================================================================*/
/*                            HAL Tx/Rx Callbacks                            */
/*===========================================================================*/

void HAL_ETH_RxAllocateCallback( uint8_t ** ppucBuff )
{
    const NetworkBufferDescriptor_t * pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( niEMAC_DATA_BUFFER_SIZE, pdMS_TO_TICKS( niEMAC_DESCRIPTOR_WAIT_TIME_MS ) );
    if( pxBufferDescriptor != NULL )
    {
        *ppucBuff = pxBufferDescriptor->pucEthernetBuffer;
    }
    else
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxAllocateCallback: failed\n" ) );
    }
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_RxLinkCallback( void ** pStart, void ** pEnd, uint8_t * buff, uint16_t usLength )
{
    NetworkBufferDescriptor_t ** const pStartDescriptor = ( NetworkBufferDescriptor_t ** ) pStart;
    NetworkBufferDescriptor_t ** const pEndDescriptor = ( NetworkBufferDescriptor_t ** ) pEnd;
    NetworkBufferDescriptor_t * const pxCurDescriptor = pxPacketBuffer_to_NetworkBuffer( ( const void * ) buff );
    if( prvAcceptPacket( pxCurDescriptor, usLength ) == pdTRUE )
    {
        pxCurDescriptor->xDataLength = usLength;
        #if ( ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) )
            pxCurDescriptor->pxNextBuffer = NULL;
        #endif
        if( *pStartDescriptor == NULL )
        {
            *pStartDescriptor = pxCurDescriptor;
        }
        #if ( ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) )
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
            #if ( ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) )
                NetworkBufferDescriptor_t * const pxNext = pxDescriptorToClear->pxNextBuffer;
            #else
                NetworkBufferDescriptor_t * const pxNext = NULL;
            #endif
            vReleaseNetworkBufferAndDescriptor( pxDescriptorToClear );
            pxDescriptorToClear = pxNext;
        } while( pxDescriptorToClear != NULL );
    }
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_TxFreeCallback( uint32_t * pulBuff )
{
    NetworkBufferDescriptor_t * const pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) pulBuff;
    vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    ( void ) xSemaphoreGive( xTxDescSem );
}

/*===========================================================================*/
/*                           Buffer Allocation                               */
/*===========================================================================*/

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ niEMAC_TOTAL_BUFFER_SIZE ] __ALIGNED( niEMAC_CACHE_LINE_SIZE ) __attribute__( ( section( niEMAC_BUFFERS_SECTION ) ) );

    configASSERT( xBufferAllocFixedSize == pdTRUE );

    for( size_t uxIndex = 0; uxIndex < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ++uxIndex )
    {
        pxNetworkBuffers[ uxIndex ].pucEthernetBuffer = &( ucNetworkPackets[ uxIndex ][ ipBUFFER_PADDING ] );
        *( ( uint32_t * ) &( ucNetworkPackets[ uxIndex ][ 0 ] ) ) = ( uint32_t ) ( &( pxNetworkBuffers[ uxIndex ] ) );
    }
}

/*===========================================================================*/
/*                      Network Interface Definition                         */
/*===========================================================================*/

NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t * pxInterface )
{
    static char pcName[ 17 ];

    ( void ) snprintf( pcName, sizeof( pcName ), "eth%u", ( unsigned ) xEMACIndex );

    ( void ) memset( pxInterface, '\0', sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;
    /* TODO: use pvArgument to get xEMACData? */
    /* xEMACData.xEMACIndex = xEMACIndex; */
    /* pxInterface->pvArgument = ( void * ) &xEMACData; */
    pxInterface->pvArgument = ( void * ) xEMACIndex;
    pxInterface->pfInitialise = prvNetworkInterfaceInitialise;
    pxInterface->pfOutput = prvNetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = prvGetPhyLinkStatus;
    /* pxInterface->pfAddAllowedMAC = prvAddAllowedMACAddress;
    pxInterface->pfRemoveAllowedMAC = prvRemoveAllowedMACAddress; */

    return FreeRTOS_AddNetworkInterface( pxInterface );
}

/*---------------------------------------------------------------------------*/
