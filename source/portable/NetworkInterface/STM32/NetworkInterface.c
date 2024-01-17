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

/*---------------------------------------------------------------------------*/

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
#include "FreeRTOS_ARP.h"
#if ipconfigIS_ENABLED( ipconfigUSE_MDNS ) || ipconfigIS_ENABLED( ipconfigUSE_LLMNR )
    #include "FreeRTOS_DNS.h"
#endif
#if ipconfigIS_ENABLED( ipconfigUSE_IPv6 )
    #include "FreeRTOS_ND.h"
#endif
#include "FreeRTOS_Routing.h"
#if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
    #include "FreeRTOS_Sockets.h"
#endif
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

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                             Config Checks                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#if ipconfigIS_DISABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM ) || ipconfigIS_DISABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM )
    #if ipconfigIS_DISABLED( ipconfigPORT_SUPPRESS_WARNING )
        #warning Consider enabling ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM/ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM for NetworkInterface
    #endif
#endif

#if ipconfigIS_DISABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES )
    #if ipconfigIS_DISABLED( ipconfigPORT_SUPPRESS_WARNING )
        #warning Consider enabling ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES for NetworkInterface
    #endif
#endif

#if defined( STM32H5 ) || defined ( STM32H7 )
    #if ipconfigIS_DISABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
        #if ipconfigIS_DISABLED( ipconfigPORT_SUPPRESS_WARNING )
            #warning Consider enabling ipconfigETHERNET_DRIVER_FILTERS_PACKETS for NetworkInterface
        #endif
    #endif
#endif

#if ( ipconfigNETWORK_MTU < ETH_MIN_PAYLOAD ) || ( ipconfigNETWORK_MTU > ETH_MAX_PAYLOAD )
    #if ipconfigIS_DISABLED( ipconfigPORT_SUPPRESS_WARNING )
        #warning Unsupported ipconfigNETWORK_MTU size
    #endif
#endif

#if ipconfigIS_DISABLED( configUSE_TASK_NOTIFICATIONS )
    #error Task Notifications must be enabled for NetworkInterface
#endif

#ifndef HAL_ETH_MODULE_ENABLED
    #error HAL_ETH_MODULE_ENABLED must be enabled for NetworkInterface
#endif

#if ( defined( STM32F4 ) || defined( STM32F7 ) ) && defined( ETH_RX_BUF_SIZE )
    #if ( niEMAC_DATA_BUFFER_SIZE != ETH_RX_BUF_SIZE )
        #warning "As of F7 V1.17.1 && F4 V1.28.0, a bug exists in the ETH HAL Driver where ETH_RX_BUF_SIZE is used instead of RxBuffLen, so ETH_RX_BUF_SIZE must == niEMAC_DATA_BUFFER_SIZE"
    #endif
#endif

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                                  Macros                                   */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#define niEMAC_TX_DESC_SECTION    ".TxDescripSection"
#define niEMAC_RX_DESC_SECTION    ".RxDescripSection"
#define niEMAC_BUFFERS_SECTION    ".EthBuffersSection"

/* TODO: Cache Handling, only for m7 */
#if __DCACHE_PRESENT
    #define niEMAC_CACHE_ENABLED    ( SCB->CCR & SCB_CCR_DC_Msk )
    #define niEMAC_ALIGNMENT        __SCB_DCACHE_LINE_SIZE
    #define niEMAC_ALIGNMENT_MASK   ( niEMAC_ALIGNMENT - 1U )
#else
    #define niEMAC_CACHE_ENABLED    pdFALSE
    #define niEMAC_ALIGNMENT        portBYTE_ALIGNMENT
    #define niEMAC_ALIGNMENT_MASK   portBYTE_ALIGNMENT_MASK
#endif

#define niEMAC_DATA_BUFFER_SIZE     ( ( ipTOTAL_ETHERNET_FRAME_SIZE + portBYTE_ALIGNMENT_MASK ) & ~portBYTE_ALIGNMENT_MASK )
#define niEMAC_TOTAL_BUFFER_SIZE    ( ( ( niEMAC_DATA_BUFFER_SIZE + ipBUFFER_PADDING ) + niEMAC_ALIGNMENT_MASK ) & ~niEMAC_ALIGNMENT_MASK )

#define niEMAC_MAX_BLOCK_TIME_MS        100U
#define niEMAC_DESCRIPTOR_WAIT_TIME_MS  200U

#define niEMAC_TASK_NAME        "EMAC_STM32"
#define niEMAC_TASK_PRIORITY    ( configMAX_PRIORITIES - 1 )
#define niEMAC_TASK_STACK_SIZE  ( 4U * configMINIMAL_STACK_SIZE )

#define niEMAC_TX_MUTEX_NAME    "EMAC_TxMutex"

#define niEMAC_AUTO_NEGOTIATION ipconfigENABLE
#define niEMAC_USE_100MB        ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_NEGOTIATION ) )
#define niEMAC_USE_FULL_DUPLEX  ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_NEGOTIATION ) )
#define niEMAC_AUTO_CROSS       ( ipconfigENABLE && ipconfigIS_ENABLED( niEMAC_AUTO_NEGOTIATION ) )
#define niEMAC_CROSSED_LINK     ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_CROSS ) )

#define niEMAC_USE_RMII ipconfigENABLE

#define niEMAC_MAX_LINKED_TX_PACKETS 1

/* IEEE 802.3 CRC32 polynomial - 0x04C11DB7 */
#define niEMAC_CRC_POLY 0x04C11DB7

/* TODO: Enabled and use interrupts for phy instead of polling? */
/*#define niPHY_ISR_AN_COMPLETE 0x0040
#define niPHY_ISR_LINK_DOWN 0x0010

#define niPHY_IMR_AN_COMPLETE 0x0040
#define niPHY_IMR_LINK_DOWN 0x0010*/

#define niEMAC_MAC_IS_MULTICAST( pucMacAddress ) ( ( pucMacAddress[ 0 ] & 1U ) != 0 )

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                               typedefs                                    */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

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
    SemaphoreHandle_t xTxMutex;
    BaseType_t xSwitchRequired;
    eMAC_INIT_STATUS_TYPE xMacInitStatus;
    BaseType_t xEMACIndex;
    MACAddress_t xMatchedMacAddresses[ 3 ];
    UBaseType_t uxMACEntry;
} EMACData_t; */

/* TODO: need a data structure to assist in adding/removing allowed addresses */

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                      Static Function Declarations                         */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

/* Phy Hooks */
static BaseType_t prvPhyReadReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t * pulValue );
static BaseType_t prvPhyWriteReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue );

/* Network Interface Access Hooks */
static BaseType_t prvGetPhyLinkStatus( NetworkInterface_t * pxInterface );
static BaseType_t prvNetworkInterfaceInitialise( NetworkInterface_t * pxInterface );
static BaseType_t prvNetworkInterfaceOutput( NetworkInterface_t * pxInterface, NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend );
static void prvAddAllowedMACAddress( const uint8_t * pucMacAddress );
//static void prvRemoveAllowedMACAddress( const uint8_t * pucMacAddress );

/* EMAC Task */
static BaseType_t prvNetworkInterfaceInput( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface );
static __NO_RETURN portTASK_FUNCTION_PROTO( prvEMACHandlerTask, pvParameters );
static BaseType_t prvEMACTaskStart( NetworkInterface_t * pxInterface );

/* EMAC Init */
static BaseType_t prvEthConfigInit( ETH_HandleTypeDef * pxEthHandle, const NetworkInterface_t * pxInterface );
static void prvInitMacAddresses( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface );
static BaseType_t prvPhyStart( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface, EthernetPhy_t * pxPhyObject );

/* EMAC Helpers */
static BaseType_t prvMacUpdateConfig( ETH_HandleTypeDef * pxEthHandle, EthernetPhy_t * pxPhyObject );
static uint32_t prvCalcCrc32( const uint8_t * pucMAC );
static void prvUpdateMacHashFilter( ETH_HandleTypeDef * pxEthHandle, const uint8_t * pucMAC );
static void prvReleaseNetworkBufferDescriptor( NetworkBufferDescriptor_t * const pxDescriptor );
static void prvSendRxEvent( NetworkBufferDescriptor_t * const pxDescriptor );

/* Filter Helpers */
/* #if ( defined( STM32H5 ) || defined ( STM32H7 ) ) && ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
    static void prvUpdatePacketFilter( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface );
#endif */
/* static BaseType_t prvAcceptPayload( ETH_HandleTypeDef * pxEthHandle, const uint8_t * const pucEthernetBuffer ); */
static BaseType_t prvAcceptPacket( const NetworkBufferDescriptor_t * const pxDescriptor, uint16_t usLength );

/* Network Interface Definition */
NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t * pxInterface );

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                      Static Variable Declarations                         */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

/* static EMACData_t xEMACData; */

static ETH_HandleTypeDef xEthHandle;

static EthernetPhy_t xPhyObject;

static TaskHandle_t xEMACTaskHandle;

static SemaphoreHandle_t xTxMutex;

static BaseType_t xSwitchRequired;

static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMacEthInit;

/* Store previously matched addresses for easy checking */
static MACAddress_t xMatchedMacAddresses[ 3 ] = { 0 };

/* ETH_MAC_ADDRESS0 reserved for the primary MAC-address. */
static UBaseType_t uxMACEntry = ETH_MAC_ADDRESS1;

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              Phy Hooks                                    */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

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

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                      Network Interface Access Hooks                       */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

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

            prvInitMacAddresses( pxEthHandle, pxInterface );

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

    do
    {
        if( ( pxDescriptor == NULL ) || ( pxDescriptor->pucEthernetBuffer == NULL ) || ( pxDescriptor->xDataLength > niEMAC_DATA_BUFFER_SIZE ) )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Invalid Descriptor\n" ) );
            break;
        }

        if( xCheckLoopback( pxDescriptor, xReleaseAfterSend ) != pdFALSE )
        {
            /* The packet has been sent back to the IP-task.
             * The IP-task will further handle it.
             * Do not release the descriptor. */
            xReleaseAfterSend = pdFALSE;
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Loopback\n" ) );
            break;
        }

        if( ( xMacInitStatus != eMacInitComplete ) || ( pxEthHandle->gState != HAL_ETH_STATE_STARTED ) )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Interface Not Started\n" ) );
            break;
        }

        if( prvGetPhyLinkStatus( pxInterface ) == pdFALSE )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Link Down\n" ) );
            break;
        }

        if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( niEMAC_MAX_BLOCK_TIME_MS ) ) == pdFALSE )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Process Busy\n" ) );
            /* TODO: Can we queue it? */
            break;
        }

        static ETH_TxPacketConfig xTxConfig = {
            .CRCPadCtrl = ETH_CRC_PAD_INSERT,
            #if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
                .Attributes = ETH_TX_PACKETS_FEATURES_CRCPAD | ETH_TX_PACKETS_FEATURES_CSUM,
                .ChecksumCtrl = ETH_CHECKSUM_IPHDR_PAYLOAD_INSERT_PHDR_CALC,
            #else
                .Attributes = ETH_TX_PACKETS_FEATURES_CRCPAD,
                .ChecksumCtrl = ETH_CHECKSUM_DISABLE,
            #endif
        };

        xTxConfig.pData = pxDescriptor;
        #if ipconfigIS_DISABLED( ipconfigUSE_LINKED_RX_MESSAGES )
            ETH_BufferTypeDef xTxBuffer = {
                .buffer = ( uint8_t * ) pxDescriptor->pucEthernetBuffer,
                .len = pxDescriptor->xDataLength,
                .next = NULL
            };

            xTxConfig.TxBuffer = &xTxBuffer;
            xTxConfig.Length = xTxBuffer.len;
        #else
            /* Support the possibility of linked Tx messages */
            ETH_BufferTypeDef xTxBuffer[ niEMAC_MAX_LINKED_TX_PACKETS ];

            xTxConfig.TxBuffer = xTxBuffer;
            xTxConfig.Length = 0;
            UBaseType_t uxIndex = 0;
            NetworkBufferDescriptor_t * pxCurDescriptor = pxDescriptor;
            while( pxCurDescriptor != NULL )
            {
                ETH_BufferTypeDef * pxCurTxBuffer = &xTxBuffer[ uxIndex++ ];
                pxCurTxBuffer->buffer = ( uint8_t * ) pxCurDescriptor->pucEthernetBuffer;
                pxCurTxBuffer->len = pxCurDescriptor->xDataLength;
                pxCurTxBuffer->next = ( uxIndex < ARRAY_SIZE( xTxBuffer ) ) ? &xTxBuffer[ uxIndex ] : NULL;
                xTxConfig.Length += pxCurTxBuffer->len;
                pxCurDescriptor = pxCurDescriptor->pxNextBuffer;
            };
        #endif

        if( HAL_ETH_Transmit_IT( pxEthHandle, &xTxConfig ) == HAL_OK )
        {
            /* Released later in deferred task by calling HAL_ETH_ReleaseTxPacket */
            xReleaseAfterSend = pdFALSE;
            xResult = pdPASS;
        }
        else
        {
            configASSERT( ( pxEthHandle->ErrorCode & HAL_ETH_ERROR_PARAM ) == 0 );
            configASSERT( pxEthHandle->gState == HAL_ETH_STATE_STARTED );
            if( pxEthHandle->ErrorCode & HAL_ETH_ERROR_BUSY )
            {
                FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Tx Busy\n" ) );
            }
        }
        ( void ) xSemaphoreGive( xTxMutex );

    } while( pdFALSE );

    if( xReleaseAfterSend == pdTRUE )
    {
        prvReleaseNetworkBufferDescriptor( pxDescriptor );
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static void prvAddAllowedMACAddress( const uint8_t * pucMacAddress )
{
    configASSERT( pucMacAddress );

    const BaseType_t xIsMulticast = niEMAC_MAC_IS_MULTICAST( pucMacAddress );

    BaseType_t xFound = pdFALSE;
    for( UBaseType_t uxIndex = 0; uxIndex < ARRAY_SIZE( xMatchedMacAddresses ); ++uxIndex )
    {
        /* Temporary inefficient method to avoid writing a HAL_ETH_GetSourceMACAddrMatch for Hx & Fx */
        if( memcmp( pucMacAddress, xMatchedMacAddresses[ uxIndex ].ucBytes, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
        {
            /* Already assigned this mac address */
            xFound = pdTRUE;
        }
    }

    if( xFound == pdFALSE )
    {
        ETH_HandleTypeDef * pxEthHandle = &xEthHandle;
        ETH_MACFilterConfigTypeDef xFilterConfig;
        ( void ) HAL_ETH_GetMACFilterConfig( pxEthHandle, &xFilterConfig );

        switch( uxMACEntry )
        {
            case ETH_MAC_ADDRESS1:
                ( void ) HAL_ETH_SetSourceMACAddrMatch( pxEthHandle, uxMACEntry, ( uint8_t * ) pucMacAddress );
                ( void ) memcpy( xMatchedMacAddresses[ 0 ].ucBytes, pucMacAddress, ipMAC_ADDRESS_LENGTH_BYTES );
                uxMACEntry = ETH_MAC_ADDRESS2;
                /* Only need to do this once, don't repeat for following addresses */
                if( xFilterConfig.HachOrPerfectFilter == DISABLE )
                {
                    xFilterConfig.HachOrPerfectFilter = ENABLE;
                    ( void ) HAL_ETH_SetMACFilterConfig( pxEthHandle, &xFilterConfig );
                }
                break;

            case ETH_MAC_ADDRESS2:
                ( void ) HAL_ETH_SetSourceMACAddrMatch( pxEthHandle, uxMACEntry, ( uint8_t * ) pucMacAddress );
                ( void ) memcpy( xMatchedMacAddresses[ 1 ].ucBytes, pucMacAddress, ipMAC_ADDRESS_LENGTH_BYTES );
                uxMACEntry = ETH_MAC_ADDRESS3;
                break;

            case ETH_MAC_ADDRESS3:
                ( void ) HAL_ETH_SetSourceMACAddrMatch( pxEthHandle, uxMACEntry, ( uint8_t * ) pucMacAddress );
                ( void ) memcpy( xMatchedMacAddresses[ 2 ].ucBytes, pucMacAddress, ipMAC_ADDRESS_LENGTH_BYTES );
                /* Just used to show that the address registers are filled */
                uxMACEntry = ETH_MAC_ADDRESS0;
                break;

            case ETH_MAC_ADDRESS0:
                prvUpdateMacHashFilter( pxEthHandle, pucMacAddress );
                if( xIsMulticast == pdTRUE )
                {
                    if( xFilterConfig.HashMulticast == DISABLE )
                    {
                        xFilterConfig.HashMulticast = ENABLE;
                        ( void ) HAL_ETH_SetMACFilterConfig( pxEthHandle, &xFilterConfig );
                    }
                }
                else
                {
                    if( xFilterConfig.HashUnicast == DISABLE )
                    {
                        xFilterConfig.HashUnicast = ENABLE;
                        ( void ) HAL_ETH_SetMACFilterConfig( pxEthHandle, &xFilterConfig );
                    }
                }
                break;

            default:
                configASSERT( pdFALSE );
                break;
        }
    }
}

/*---------------------------------------------------------------------------*/
#if 0
static void prvRemoveAllowedMACAddress( const uint8_t * pucMacAddress )
{
    configASSERT( pucMacAddress );

    /* const BaseType_t xIsMulticast = niEMAC_MAC_IS_MULTICAST( pucMacAddress ); */

    BaseType_t xFound = pdFALSE;
    for( UBaseType_t uxIndex = 0; uxIndex < ARRAY_SIZE( xMatchedMacAddresses ); ++uxIndex )
    {
        /* Temporary inefficient method to avoid writing a HAL_ETH_GetSourceMACAddrMatch for Hx & Fx */
        if( memcmp( pucMacAddress, xMatchedMacAddresses[ uxIndex ].ucBytes, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
        {
            /* Already assigned this mac address */
            xFound = pdTRUE;
        }
    }

    if( xFound == pdTRUE )
    {
        ETH_HandleTypeDef * pxEthHandle = &xEthHandle;
        ETH_MACFilterConfigTypeDef xFilterConfig;
        ( void ) HAL_ETH_GetMACFilterConfig( pxEthHandle, &xFilterConfig );

    }
}
#endif
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              EMAC Task                                    */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceInput( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface )
{
    UBaseType_t uxResult = 0;
    /* if( ( xMacInitStatus == eMacInitComplete ) && ( heth->gState == HAL_ETH_STATE_STARTED ) ) */
    #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
        NetworkBufferDescriptor_t * pxStartDescriptor = NULL;
        NetworkBufferDescriptor_t * pxEndDescriptor = NULL;
    #endif
    NetworkBufferDescriptor_t * pxCurDescriptor = NULL;

    while( HAL_ETH_ReadData( pxEthHandle, ( void ** ) &pxCurDescriptor ) == HAL_OK )
    {
        ++uxResult;
        if( pxCurDescriptor == NULL )
        {
            /* Buffer was dropped, ignore packet */
            continue;
        }
        configASSERT( pxEthHandle->RxDescList.RxDataLength <= niEMAC_DATA_BUFFER_SIZE );

        pxCurDescriptor->pxInterface = pxInterface;
        pxCurDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint( pxCurDescriptor->pxInterface, pxCurDescriptor->pucEthernetBuffer );
        #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
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
            prvSendRxEvent( pxCurDescriptor );
        #endif
    }

    #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
        if( uxResult > 0 )
        {
            prvSendRxEvent( pxStartDescriptor );
        }
    #endif

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

        /* #if ( defined( STM32H5 ) || defined ( STM32H7 ) ) && ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
            prvUpdatePacketFilter( pxEthHandle, pxInterface );
        #endif */

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
        #if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION )
            static StaticSemaphore_t xTxMutexBuf;
            xTxMutex = xSemaphoreCreateMutexStatic( &xTxMutexBuf );
        #else
            xTxMutex = xSemaphoreCreateMutex();
        #endif
        configASSERT( xTxMutex != NULL );
        vQueueAddToRegistry( xTxMutex, niEMAC_TX_MUTEX_NAME );
    }

    if( xEMACTaskHandle == NULL && ( xTxMutex != NULL ) )
    {
        #if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION )
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

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                               EMAC Init                                   */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static BaseType_t prvEthConfigInit( ETH_HandleTypeDef * pxEthHandle, const NetworkInterface_t * pxInterface )
{
    BaseType_t xResult = pdFALSE;

    pxEthHandle->Instance = ETH;

    #if ipconfigIS_ENABLED( niEMAC_USE_RMII )
        pxEthHandle->Init.MediaInterface = HAL_ETH_RMII_MODE;
    #else
        pxEthHandle->Init.MediaInterface = HAL_ETH_MII_MODE;
    #endif

    pxEthHandle->Init.RxBuffLen = niEMAC_DATA_BUFFER_SIZE;
    configASSERT( pxEthHandle->Init.RxBuffLen <= ETH_MAX_PACKET_SIZE );
    configASSERT( pxEthHandle->Init.RxBuffLen % 4U == 0 );
    #if ( defined( STM32F4 ) || defined( STM32F7 ) ) && defined( ETH_RX_BUF_SIZE )
        configASSERT( pxEthHandle->Init.RxBuffLen == ETH_RX_BUF_SIZE );
    #endif

    static ETH_DMADescTypeDef xDMADescTx[ ETH_TX_DESC_CNT ] __ALIGNED( portBYTE_ALIGNMENT ) __attribute__( ( section( niEMAC_TX_DESC_SECTION ) ) );
    static ETH_DMADescTypeDef xDMADescRx[ ETH_RX_DESC_CNT ] __ALIGNED( portBYTE_ALIGNMENT ) __attribute__( ( section( niEMAC_RX_DESC_SECTION ) ) );

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
    }

    /*
    ETH_DMAConfigTypeDef xDMAConfig;
    ( void ) HAL_ETH_GetDMAConfig( pxEthHandle, &xDMAConfig );
    xDMAConfig.
    if( HAL_ETH_SetDMAConfig( pxEthHandle, &xDMAConfig ) != HAL_OK )
    {
        break;
    }
    */

    /* #if defined( STM32H5 ) || defined ( STM32H7 )
        HAL_ETHEx_SetARPAddressMatch( pxEthHandle );
        HAL_ETHEx_EnableARPOffload( pxEthHandle );
    #endif */

    /* #if ( defined( STM32H5 ) || defined ( STM32H7 ) ) && ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
        prvUpdatePacketFilter( pxEthHandle, pxInterface );
    #endif */

    configASSERT( NVIC_GetEnableIRQ( ETH_IRQn ) != 0 );
    uint32_t ulPreemptPriority, ulSubPriority;
    HAL_NVIC_GetPriority( ETH_IRQn, HAL_NVIC_GetPriorityGrouping(), &ulPreemptPriority, &ulSubPriority );
    configASSERT( ulPreemptPriority >= configMAX_FREERTOS_INTERRUPT_PRIORITY );

    return xResult;
}

/*---------------------------------------------------------------------------*/

static void prvInitMacAddresses( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface )
{
    ETH_MACFilterConfigTypeDef xFilterConfig;
    ( void ) HAL_ETH_GetMACFilterConfig( pxEthHandle, &xFilterConfig );

    /* These are always disabled */
    xFilterConfig.SrcAddrFiltering = DISABLE;
    xFilterConfig.SrcAddrInverseFiltering = DISABLE;
    xFilterConfig.DestAddrInverseFiltering = DISABLE;
    xFilterConfig.BroadcastFilter = DISABLE;
    xFilterConfig.ControlPacketsFilter = DISABLE;

    /* All all if ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is disabled */
    xFilterConfig.PromiscuousMode = ipconfigIS_DISABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES ) ? ENABLE : DISABLE;
    xFilterConfig.ReceiveAllMode = ipconfigIS_DISABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES ) ? ENABLE : DISABLE;
    xFilterConfig.PassAllMulticast = ipconfigIS_DISABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES ) ? ENABLE : DISABLE;

    /* These are determined later, just set default disable */
    xFilterConfig.HachOrPerfectFilter = DISABLE;
    xFilterConfig.HashUnicast = DISABLE;
    xFilterConfig.HashMulticast = DISABLE;

    /* Update the initial configuration, it may be changed again in prvAddAllowedMACAddress */
    ( void ) HAL_ETH_SetMACFilterConfig( pxEthHandle, &xFilterConfig );

    /* If we are filtering frame types then handle placing target MAC Addresses in filters */
    #if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES )
        for( NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface ); pxEndPoint != NULL; pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
        {
            prvAddAllowedMACAddress( pxEndPoint->xMACAddress.ucBytes );
        }

        #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
            #if ipconfigIS_ENABLED( ipconfigUSE_MDNS )
                prvAddAllowedMACAddress( xMDNS_MacAddress.ucBytes );
            #endif
            #if ipconfigIS_ENABLED( ipconfigUSE_LLMNR )
                prvAddAllowedMACAddress( xLLMNR_MacAddress.ucBytes );
            #endif
        #endif

        #if ipconfigIS_ENABLED( ipconfigUSE_IPv6 )
            prvAddAllowedMACAddress( pcLOCAL_ALL_NODES_MULTICAST_MAC.ucBytes );
            #if ipconfigIS_ENABLED( ipconfigUSE_MDNS )
                prvAddAllowedMACAddress( xMDNS_MACAddressIPv6.ucBytes );
            #endif
            #if ipconfigIS_ENABLED( ipconfigUSE_LLMNR )
                prvAddAllowedMACAddress( xLLMNR_MacAddressIPv6.ucBytes );
            #endif
        #endif
    #endif
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvPhyStart( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface, EthernetPhy_t * pxPhyObject )
{
    BaseType_t xResult = pdFALSE;

    if( prvGetPhyLinkStatus( pxInterface ) == pdFALSE )
    {
        const PhyProperties_t xPhyProperties = {
            #if ipconfigIS_ENABLED( niEMAC_AUTO_NEGOTIATION )
                .ucSpeed = PHY_SPEED_AUTO,
                .ucDuplex = PHY_DUPLEX_AUTO,
            #else
                .ucSpeed = ipconfigIS_ENABLED( niEMAC_USE_100MB ) ? PHY_SPEED_100 : PHY_SPEED_10,
                .ucDuplex = ipconfigIS_ENABLED( niEMAC_USE_FULL_DUPLEX ) ? PHY_DUPLEX_FULL : PHY_DUPLEX_HALF,
            #endif

            #if ipconfigIS_ENABLED( niEMAC_AUTO_CROSS )
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

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                             EMAC Helpers                                  */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

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

    #if ipconfigIS_ENABLED( niEMAC_AUTO_NEGOTIATION )
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
static uint32_t prvCalcCrc32( const uint8_t * pucMAC )
{
    uint32_t ulCRC32 = 0xFFFFFFFF;

    for( uint8_t ucIndex = ipMAC_ADDRESS_LENGTH_BYTES; ucIndex > 0; --ucIndex )
    {
        ulCRC32 ^= ( uint32_t ) pucMAC[ ucIndex ];

        for( uint8_t ucJndex = 0; ucJndex < 8; ++ucJndex )
        {
            const BaseType_t xTemp = ulCRC32 & 1;
            ulCRC32 >>= 1;
            if( xTemp )
            {
                ulCRC32 ^= __RBIT( niEMAC_CRC_POLY );
            }
        }
    }

    /* Perform bitwise reversal on the CRC32 */
    return __RBIT( ~ulCRC32 );
}

/*---------------------------------------------------------------------------*/

/* Update the Hash Table Registers with hash value of the given MAC address */
static void prvUpdateMacHashFilter( ETH_HandleTypeDef * pxEthHandle, const uint8_t * pucMAC )
{
    static uint32_t ulHashTable[ 2 ];

    /* Calculate the 32-bit CRC for the MAC */
    const uint32_t ulHash = prvCalcCrc32( pucMAC );

    /* Take the upper 6 bits of the above result */
    const uint8_t ucEntry = ( ulHash >> 26 ) & 0x3F;

    /* Use the upper or lower Hash Table Registers
     * to set the required bit based on the ulHash */
    if( ucEntry < 32 )
    {
        ulHashTable[ 0 ] |= ( 1 << ucEntry );
    }
    else
    {
        ulHashTable[ 1 ] |= ( 1 << ( ucEntry % 32 ) );
    }

    ( void ) HAL_ETH_SetHashTable( pxEthHandle, ulHashTable );
}

/*---------------------------------------------------------------------------*/

static void prvReleaseNetworkBufferDescriptor( NetworkBufferDescriptor_t * const pxDescriptor )
{
    NetworkBufferDescriptor_t * pxDescriptorToClear = pxDescriptor;
    while( pxDescriptorToClear != NULL )
    {
        #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
            NetworkBufferDescriptor_t * const pxNext = pxDescriptorToClear->pxNextBuffer;
        #else
            NetworkBufferDescriptor_t * const pxNext = NULL;
        #endif
        vReleaseNetworkBufferAndDescriptor( pxDescriptorToClear );
        pxDescriptorToClear = pxNext;
    };
}

/*---------------------------------------------------------------------------*/

static void prvSendRxEvent( NetworkBufferDescriptor_t * const pxDescriptor )
{
    const IPStackEvent_t xRxEvent = {
        .eEventType = eNetworkRxEvent,
        .pvData = ( void * ) pxDescriptor
    };
    if( xSendEventStructToIPTask( &xRxEvent, pdMS_TO_TICKS( niEMAC_MAX_BLOCK_TIME_MS ) ) != pdPASS )
    {
        iptraceETHERNET_RX_EVENT_LOST();
        FreeRTOS_debug_printf( ( "prvSendRxEvent: xSendEventStructToIPTask failed\n" ) );
        prvReleaseNetworkBufferDescriptor( pxDescriptor );
    }
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                           Filter Helpers                                  */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#if 0

#if ( defined( STM32H5 ) || defined ( STM32H7 ) ) && ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )

/* TODO: Where to put this? Should it be triggered by a NetworkInterface_t hook? */
static void prvUpdatePacketFilter( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface )
{
    HAL_ETHEx_DisableL3L4Filtering( pxEthHandle );

    ETH_L3FilterConfigTypeDef xL3FilterConfig;
    ( void ) HAL_ETHEx_GetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_0, &xL3FilterConfig );

    xL3FilterConfig.Protocol = ETH_L3_IPV4_MATCH/ETH_L3_IPV6_MATCH;
    xL3FilterConfig.SrcAddrFilterMatch = ETH_L3_SRC_ADDR_PERFECT_MATCH_ENABLE/ETH_L3_SRC_ADDR_INVERSE_MATCH_ENABLE/ETH_L3_SRC_ADDR_MATCH_DISABLE;
    xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_PERFECT_MATCH_ENABLE/ETH_L3_DEST_ADDR_INVERSE_MATCH_ENABLE/ETH_L3_DEST_ADDR_MATCH_DISABLE;
    xL3FilterConfig.SrcAddrHigherBitsMatch = ;
    xL3FilterConfig.DestAddrHigherBitsMatch = ;
    #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )
        xL3FilterConfig.Ip4SrcAddr = ;
        xL3FilterConfig.Ip4DestAddr = ;
    #endif
    #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
        xL3FilterConfig.Ip6Addr = ;
    #endif

    ( void ) HAL_ETHEx_SetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_0, &xL3FilterConfig );


    ETH_L4FilterConfigTypeDef xL4FilterConfig;
    ( void ) HAL_ETHEx_GetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_0, &xL4FilterConfig );

    xL4FilterConfig.Protocol = ETH_L4_UDP_MATCH/ETH_L4_TCP_MATCH;
    xL4FilterConfig.SrcPortFilterMatch = ETH_L4_SRC_PORT_PERFECT_MATCH_ENABLE/ETH_L4_SRC_PORT_INVERSE_MATCH_ENABLE/ETH_L4_SRC_PORT_MATCH_DISABLE;
    xL4FilterConfig.DestPortFilterMatch = ETH_L4_DEST_PORT_PERFECT_MATCH_ENABLE/ETH_L4_DEST_PORT_INVERSE_MATCH_ENABLE/ETH_L4_DEST_PORT_MATCH_DISABLE;
    xL4FilterConfig.SourcePort = ;
    xL4FilterConfig.DestinationPort = ;

    ( void ) HAL_ETHEx_SetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_0, &xL4FilterConfig );

    HAL_ETHEx_EnableL3L4Filtering( pxEthHandle );
}

#endif /* if ( defined( STM32H5 ) || defined ( STM32H7 ) ) && ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS ) */

#endif

/*---------------------------------------------------------------------------*/

#if 0

#if defined( STM32F4 ) || defined( STM32F7 )
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

    #if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
        const UBaseType_t uxPayloadType = READ_BIT( heth->RxDescList.pRxLastRxDesc, ETH_DMARXNDESCWBF_PT )
        const ProtocolPacket_t * pxProtPacket = ( const ProtocolPacket_t * ) pucEthernetBuffer;
        const IPHeader_t * pxIPHeader = &( pxProtPacket->xTCPPacket.xIPHeader );
        switch( uxPayloadType )
        {
            case ETH_IP_PAYLOAD_UNKNOWN:
            case ETH_IP_PAYLOAD_UDP:
                if( ( xPortHasUdpSocket( xUDPHeader->usDestinationPort ) )
                #if ipconfigUSE_DNS == 1 * DNS is also UDP. *
                    || ( xUDPHeader->usSourcePort == FreeRTOS_ntohs( ipDNS_PORT ) )
                #endif
                #if ipconfigUSE_LLMNR == 1 * LLMNR is also UDP. *
                    || ( xUDPHeader->usDestinationPort == FreeRTOS_ntohs( ipLLMNR_PORT ) )
                #endif
                #if ipconfigUSE_NBNS == 1 * NBNS is also UDP. *
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

#endif /* if 0 */

/*---------------------------------------------------------------------------*/

static BaseType_t prvAcceptPacket( const NetworkBufferDescriptor_t * const pxDescriptor, uint16_t usLength )
{
    BaseType_t xResult = pdFALSE;
    do
    {
        uint32_t ulErrorCode = 0;
        ( void ) HAL_ETH_GetRxDataErrorCode( &xEthHandle, &ulErrorCode );
        if( ulErrorCode != 0 )
        {
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Rx Data Error\n" ) );
            break;
        }

        if( usLength > niEMAC_DATA_BUFFER_SIZE )
        {
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Packet size overflow\n" ) );
            break;
        }

        /* if( prvAcceptPayload( &xEthHandle, pxDescriptor->pucEthernetBuffer ) != pdTRUE )
        {
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Payload discarded\n" ) );
            break;
        } */

        #if ipconfigIS_DISABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES )
            if( eConsiderFrameForProcessing( pxDescriptor->pucEthernetBuffer ) != eProcessBuffer )
            {
                FreeRTOS_debug_printf( ( "prvAcceptPacket: Frame discarded\n" ) );
                break;
            }
        #else
            // prvUpdatePacketFilter should have set this filter up previously
        #endif

        xResult = pdTRUE;

    } while( pdFALSE );

    return xResult;
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              IRQ Handlers                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

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
                /* ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrEth, eSetBits, &xHigherPriorityTaskWoken ); */
            }
            else
            {
                #if defined( STM32F4 ) || defined ( STM32F7 )
                    if( pxEthHandle->DMAErrorCode & ETH_DMASR_TBUS )
                    {
                        /* ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrTx, eSetBits, &xHigherPriorityTaskWoken ); */
                    }

                    if( pxEthHandle->DMAErrorCode & ETH_DMASR_RBUS )
                    {
                        /* ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrRx, eSetBits, &xHigherPriorityTaskWoken ); */
                    }
                #elif defined( STM32H5 ) || defined ( STM32H7 )
                    if( pxEthHandle->DMAErrorCode & ETH_DMACSR_TBU )
                    {
                        /* ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventErrTx, eSetBits, &xHigherPriorityTaskWoken ); */
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

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                            HAL Tx/Rx Callbacks                            */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

void HAL_ETH_RxAllocateCallback( uint8_t ** ppucBuff )
{
    const NetworkBufferDescriptor_t * pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( niEMAC_DATA_BUFFER_SIZE, pdMS_TO_TICKS( niEMAC_DESCRIPTOR_WAIT_TIME_MS ) );
    if( pxBufferDescriptor != NULL )
    {
        /* TODO: Should any other checks be performed on pxBufferDescriptor? */
        *ppucBuff = pxBufferDescriptor->pucEthernetBuffer;
    }
    else
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxAllocateCallback: failed\n" ) );
    }
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_RxLinkCallback( void ** ppvStart, void ** ppvEnd, uint8_t * pucBuff, uint16_t usLength )
{
    NetworkBufferDescriptor_t ** const ppxStartDescriptor = ( NetworkBufferDescriptor_t ** ) ppvStart;
    NetworkBufferDescriptor_t ** const ppxEndDescriptor = ( NetworkBufferDescriptor_t ** ) ppvEnd;
    NetworkBufferDescriptor_t * const pxCurDescriptor = pxPacketBuffer_to_NetworkBuffer( ( const void * ) pucBuff );
    if( prvAcceptPacket( pxCurDescriptor, usLength ) == pdTRUE )
    {
        pxCurDescriptor->xDataLength = usLength;
        #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
            pxCurDescriptor->pxNextBuffer = NULL;
        #endif
        if( *ppxStartDescriptor == NULL )
        {
            *ppxStartDescriptor = pxCurDescriptor;
        }
        #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
            else if( ppxEndDescriptor != NULL )
            {
                ( *ppxEndDescriptor )->pxNextBuffer = pxCurDescriptor;
            }
        #endif
        *ppxEndDescriptor = pxCurDescriptor;
        /* Only single buffer packets are supported */
        configASSERT( *ppxStartDescriptor == *ppxEndDescriptor );
    }
    else
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxLinkCallback: Buffer Dropped\n" ) );
        prvReleaseNetworkBufferDescriptor( pxCurDescriptor );
    }
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_TxFreeCallback( uint32_t * pulBuff )
{
    NetworkBufferDescriptor_t * const pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) pulBuff;
    prvReleaseNetworkBufferDescriptor( pxNetworkBuffer );
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                           Buffer Allocation                               */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ niEMAC_TOTAL_BUFFER_SIZE ] __ALIGNED( niEMAC_ALIGNMENT ) __attribute__( ( section( niEMAC_BUFFERS_SECTION ) ) );

    configASSERT( xBufferAllocFixedSize == pdTRUE );

    for( size_t uxIndex = 0; uxIndex < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ++uxIndex )
    {
        pxNetworkBuffers[ uxIndex ].pucEthernetBuffer = &( ucNetworkPackets[ uxIndex ][ ipBUFFER_PADDING ] );
        *( ( uint32_t * ) &( ucNetworkPackets[ uxIndex ][ 0 ] ) ) = ( uint32_t ) ( &( pxNetworkBuffers[ uxIndex ] ) );
    }
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                      Network Interface Definition                         */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t * pxInterface )
{
    static char pcName[ 17 ];

    ( void ) snprintf( pcName, sizeof( pcName ), "eth%u", ( unsigned ) xEMACIndex );

    ( void ) memset( pxInterface, '\0', sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;
    /* TODO: use pvArgument to get xEMACData? */
    /* xEMACData.xEMACIndex = xEMACIndex; */
    /* pxInterface->pvArgument = ( void * ) &xEMACData; */
    /* pxInterface->pvArgument = pvPortMalloc( sizeof( EMACData_t ) ); */
    pxInterface->pvArgument = ( void * ) xEMACIndex;
    pxInterface->pfInitialise = prvNetworkInterfaceInitialise;
    pxInterface->pfOutput = prvNetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = prvGetPhyLinkStatus;
    /* pxInterface->pfAddAllowedMAC = prvAddAllowedMACAddress;
    pxInterface->pfRemoveAllowedMAC = prvRemoveAllowedMACAddress; */

    return FreeRTOS_AddNetworkInterface( pxInterface );
}

/*---------------------------------------------------------------------------*/

#if ipconfigIS_ENABLED( ipconfigIPv4_BACKWARD_COMPATIBLE )

/* Do not call the following function directly. It is there for downward compatibility.
 * The function FreeRTOS_IPInit() will call it to initialice the interface and end-point
 * objects.  See the description in FreeRTOS_Routing.h. */
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface )
    {
        pxSTM32_FillInterfaceDescriptor( xEMACIndex, pxInterface );
    }

#endif

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                          Sample HAL_ETH_MspInit                           */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#if 0

/**
  * @brief  Initializes the ETH MSP.
  * @param  heth: ETH handle
  * @retval None
*/
void HAL_ETH_MspInit( ETH_HandleTypeDef * heth )
{
    if( heth->Instance == ETH )
    {
        /* Enable ETHERNET clock */
        #if defined( STM32F4 ) || defined( STM32F7 )
            __HAL_RCC_ETH_CLK_ENABLE();
        #elif defined( STM32H5 )
            __HAL_RCC_ETH_CLK_ENABLE();
            __HAL_RCC_ETHTX_CLK_ENABLE();
            __HAL_RCC_ETHRX_CLK_ENABLE();
        #elif defined( STM32H7)
            __HAL_RCC_ETH1MAC_CLK_ENABLE();
            __HAL_RCC_ETH1TX_CLK_ENABLE();
            __HAL_RCC_ETH1RX_CLK_ENABLE();
        #endif

        /* Enable GPIOs clocks */
        __HAL_RCC_GPIOA_CLK_ENABLE();
        __HAL_RCC_GPIOB_CLK_ENABLE();
        __HAL_RCC_GPIOC_CLK_ENABLE();
        __HAL_RCC_GPIOD_CLK_ENABLE();
        __HAL_RCC_GPIOE_CLK_ENABLE();
        __HAL_RCC_GPIOF_CLK_ENABLE();
        __HAL_RCC_GPIOG_CLK_ENABLE();
        __HAL_RCC_GPIOH_CLK_ENABLE();

        /* Ethernet pins configuration ************************************************/
        /*
            Common Pins
            ETH_MDC ----------------------> ETH_MDC_Port, ETH_MDC_Pin
            ETH_MDIO --------------------->
            ETH_RXD0 --------------------->
            ETH_RXD1 --------------------->
            ETH_TX_EN -------------------->
            ETH_TXD0 --------------------->
            ETH_TXD1 --------------------->

            RMII Specific Pins
            ETH_REF_CLK ------------------>
            ETH_CRS_DV ------------------->

            MII Specific Pins
            ETH_RX_CLK ------------------->
            ETH_RX_ER -------------------->
            ETH_RX_DV -------------------->
            ETH_RXD2 --------------------->
            ETH_RXD3 --------------------->
            ETH_TX_CLK ------------------->
            ETH_TXD2 --------------------->
            ETH_TXD3 --------------------->
            ETH_CRS ---------------------->
            ETH_COL ---------------------->
        */

        GPIO_InitTypeDef GPIO_InitStructure = { 0 };
        GPIO_InitStructure.Speed = GPIO_SPEED_HIGH;
        GPIO_InitStructure.Mode = GPIO_MODE_AF_PP;
        GPIO_InitStructure.Pull = GPIO_NOPULL;
        GPIO_InitStructure.Alternate = GPIO_AF11_ETH;

        GPIO_InitStructure.Pin = ETH_MDC_Pin;
        HAL_GPIO_Init(ETH_MDC_Port, &GPIO_InitStructure);

        GPIO_InitStructure.Pin = ETH_MDIO_Pin;
        HAL_GPIO_Init(ETH_MDIO_Port, &GPIO_InitStructure);

        GPIO_InitStructure.Pin = ETH_RXD0_Pin;
        HAL_GPIO_Init(ETH_RXD0_Port, &GPIO_InitStructure);

        GPIO_InitStructure.Pin = ETH_RXD1_Pin;
        HAL_GPIO_Init(ETH_RXD1_Port, &GPIO_InitStructure);

        GPIO_InitStructure.Pin = ETH_TX_EN_Pin;
        HAL_GPIO_Init(ETH_TX_EN_Port, &GPIO_InitStructure);

        GPIO_InitStructure.Pin = ETH_TXD0_Pin;
        HAL_GPIO_Init(ETH_TXD0_Port, &GPIO_InitStructure);

        GPIO_InitStructure.Pin = ETH_TXD1_Pin;
        HAL_GPIO_Init(ETH_TXD1_Port, &GPIO_InitStructure);

        if( heth->Init.MediaInterface == HAL_ETH_RMII_MODE )
        {
            GPIO_InitStructure.Pin = ETH_REF_CLK_Pin;
            HAL_GPIO_Init(ETH_REF_CLK_Port, &GPIO_InitStructure);

            GPIO_InitStructure.Pin = ETH_CRS_DV_Pin;
            HAL_GPIO_Init(ETH_CRS_DV_Port, &GPIO_InitStructure);
        }
        else if( heth->Init.MediaInterface == HAL_ETH_MII_MODE )
        {
            GPIO_InitStructure.Pin = ETH_RX_CLK_Pin;
            HAL_GPIO_Init(ETH_RX_CLK_Port, &GPIO_InitStructure);

            GPIO_InitStructure.Pin = ETH_RX_ER_Pin;
            HAL_GPIO_Init(ETH_RX_ER_Port, &GPIO_InitStructure);

            GPIO_InitStructure.Pin = ETH_RX_DV_Pin;
            HAL_GPIO_Init(ETH_RX_DV_Port, &GPIO_InitStructure);

            GPIO_InitStructure.Pin = ETH_RXD2_Pin;
            HAL_GPIO_Init(ETH_RXD2_Port, &GPIO_InitStructure);

            GPIO_InitStructure.Pin = ETH_RXD3_Pin;
            HAL_GPIO_Init(ETH_RXD3_Port, &GPIO_InitStructure);

            GPIO_InitStructure.Pin = ETH_TX_CLK_Pin;
            HAL_GPIO_Init(ETH_TX_CLK_Port, &GPIO_InitStructure);

            GPIO_InitStructure.Pin = ETH_TXD2_Pin;
            HAL_GPIO_Init(ETH_TXD2_Port, &GPIO_InitStructure);

            GPIO_InitStructure.Pin = ETH_TXD3_Pin;
            HAL_GPIO_Init(ETH_TXD3_Port, &GPIO_InitStructure);

            GPIO_InitStructure.Pin = ETH_COL_Pin;
            HAL_GPIO_Init(ETH_COL_Port, &GPIO_InitStructure);

            GPIO_InitStructure.Pin = ETH_CRS_Pin;
            HAL_GPIO_Init(ETH_CRS_Port, &GPIO_InitStructure);
        }

        /* Enable the Ethernet global Interrupt */
        HAL_NVIC_SetPriority( ETH_IRQn, ( uint32_t ) configMAX_FREERTOS_INTERRUPT_PRIORITY, 0 );
        HAL_NVIC_EnableIRQ( ETH_IRQn );
    }
}

#endif /* if 0 */

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                            Sample MPU Config                              */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#if 0

void MPU_Config(void)
{
    /* TODO: Usage based on if niEMAC_CACHE_ENABLED */

    extern uint8_t __ETH_BUFFERS_START, __ETH_DESCRIPTORS_START;

    MPU_Region_InitTypeDef MPU_InitStruct;

    HAL_MPU_Disable();

    MPU_InitStruct.Enable = MPU_REGION_ENABLE;
    MPU_InitStruct.Number = MPU_REGION_NUMBER0;
    MPU_InitStruct.BaseAddress = ( uint32_t ) &__ETH_BUFFERS_START;
    MPU_InitStruct.Size = MPU_REGION_SIZE_128KB;
    MPU_InitStruct.SubRegionDisable = 0x0;
    MPU_InitStruct.TypeExtField = MPU_TEX_LEVEL1;
    MPU_InitStruct.AccessPermission = MPU_REGION_FULL_ACCESS;
    MPU_InitStruct.DisableExec = MPU_INSTRUCTION_ACCESS_DISABLE;
    MPU_InitStruct.IsShareable = MPU_ACCESS_NOT_SHAREABLE;
    MPU_InitStruct.IsCacheable = MPU_ACCESS_NOT_CACHEABLE;
    MPU_InitStruct.IsBufferable = MPU_ACCESS_NOT_BUFFERABLE;

    HAL_MPU_ConfigRegion(&MPU_InitStruct);

    MPU_InitStruct.Enable = MPU_REGION_ENABLE;
    MPU_InitStruct.Number = MPU_REGION_NUMBER1;
    MPU_InitStruct.BaseAddress = ( uint32_t ) &__ETH_DESCRIPTORS_START;
    MPU_InitStruct.Size = MPU_REGION_SIZE_1KB;
    MPU_InitStruct.SubRegionDisable = 0x0;
    MPU_InitStruct.TypeExtField = MPU_TEX_LEVEL0;
    MPU_InitStruct.AccessPermission = MPU_REGION_FULL_ACCESS;
    MPU_InitStruct.DisableExec = MPU_INSTRUCTION_ACCESS_DISABLE;
    MPU_InitStruct.IsShareable = MPU_ACCESS_NOT_SHAREABLE;
    MPU_InitStruct.IsCacheable = MPU_ACCESS_NOT_CACHEABLE;
    MPU_InitStruct.IsBufferable = MPU_ACCESS_BUFFERABLE;

    HAL_MPU_ConfigRegion(&MPU_InitStruct);

    HAL_MPU_Enable(MPU_PRIVILEGED_DEFAULT);
}

#endif /* if 0 */

/*---------------------------------------------------------------------------*/
