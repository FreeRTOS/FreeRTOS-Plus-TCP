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
    #error "This NetworkInterface is incompatible with STM32F2 - Use Legacy NetworkInterface"
#else
    #error "Unknown STM32 Family for NetworkInterface"
#endif

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                                Config                                     */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#if defined( STM32F7 ) || defined( STM32F4 )
    #define niEMAC_STM32FX
#elif defined( STM32H7 ) || defined( STM32H5 )
    #define niEMAC_STM32HX
#endif

#define niEMAC_TX_DESC_SECTION    ".TxDescripSection"
#define niEMAC_RX_DESC_SECTION    ".RxDescripSection"
#define niEMAC_BUFFERS_SECTION    ".EthBuffersSection"

#define niEMAC_DATA_ALIGNMENT        4U
#define niEMAC_DATA_ALIGNMENT_MASK   ( niEMAC_DATA_ALIGNMENT - 1U )
#define niEMAC_BUF_ALIGNMENT        32U
#define niEMAC_BUF_ALIGNMENT_MASK   ( niEMAC_BUF_ALIGNMENT - 1U )

#define niEMAC_DATA_BUFFER_SIZE     ( ( ipTOTAL_ETHERNET_FRAME_SIZE + niEMAC_DATA_ALIGNMENT_MASK ) & ~niEMAC_DATA_ALIGNMENT_MASK )
#define niEMAC_TOTAL_BUFFER_SIZE    ( ( ( niEMAC_DATA_BUFFER_SIZE + ipBUFFER_PADDING ) + niEMAC_BUF_ALIGNMENT_MASK ) & ~niEMAC_BUF_ALIGNMENT_MASK )

#define niEMAC_TASK_MAX_BLOCK_TIME_MS   100U
#define niEMAC_TX_MAX_BLOCK_TIME_MS     20U
#define niEMAC_RX_MAX_BLOCK_TIME_MS     20U
#define niEMAC_DESCRIPTOR_WAIT_TIME_MS  20U

#define niEMAC_TASK_NAME        "EMAC_STM32"
#define niEMAC_TASK_PRIORITY    ( configMAX_PRIORITIES - 1 )
#define niEMAC_TASK_STACK_SIZE  ( 4U * configMINIMAL_STACK_SIZE )

#define niEMAC_TX_MUTEX_NAME    "EMAC_TxMutex"
#define niEMAC_TX_DESC_SEM_NAME "EMAC_TxDescSem"

#define niEMAC_AUTO_NEGOTIATION ipconfigENABLE
#define niEMAC_USE_100MB        ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_NEGOTIATION ) )
#define niEMAC_USE_FULL_DUPLEX  ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_NEGOTIATION ) )

#define niEMAC_AUTO_CROSS       ( ipconfigENABLE && ipconfigIS_ENABLED( niEMAC_AUTO_NEGOTIATION ) )
#define niEMAC_CROSSED_LINK     ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_CROSS ) )

#define niEMAC_USE_RMII ipconfigENABLE

#ifdef niEMAC_STM32HX
    #define niEMAC_AUTO_LOW_POWER   ( ipconfigDISABLE && ipconfigIS_DISABLED( niEMAC_USE_RMII ) )
#endif

#define niEMAC_TCP_SEGMENTATION ipconfigDISABLE
#define niEMAC_ARP_OFFLOAD ipconfigDISABLE

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                             Config Checks                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#ifndef HAL_ETH_MODULE_ENABLED
    #error "HAL_ETH_MODULE_ENABLED must be enabled for NetworkInterface"
#endif

#if ipconfigIS_DISABLED( configUSE_TASK_NOTIFICATIONS )
    #error "Task Notifications must be enabled for NetworkInterface"
#endif

#if ipconfigIS_DISABLED( ipconfigZERO_COPY_TX_DRIVER )
    #error "ipconfigZERO_COPY_TX_DRIVER must be enabled for NetworkInterface"
#endif

#if ipconfigIS_DISABLED( ipconfigZERO_COPY_RX_DRIVER )
    #error "ipconfigZERO_COPY_RX_DRIVER must be enabled for NetworkInterface"
#endif

#if ( ipconfigNETWORK_MTU < ETH_MIN_PAYLOAD ) || ( ipconfigNETWORK_MTU > ETH_MAX_PAYLOAD )
    #error "Unsupported ipconfigNETWORK_MTU size for NetworkInterface"
#endif

#if defined( niEMAC_STM32HX )

    #if ( ETH_TX_DESC_CNT % 4 != 0 )
        #error "Invalid ETH_TX_DESC_CNT value for NetworkInterface, must be a multiple of 4"
    #endif

    #if ( ETH_RX_DESC_CNT % 4 != 0 )
        #error "Invalid ETH_RX_DESC_CNT value for NetworkInterface, must be a multiple of 4"
    #endif

#elif defined( niEMAC_STM32FX )

    #if defined( ETH_RX_BUF_SIZE )
        #if ipconfigIS_DISABLED( ipconfigPORT_SUPPRESS_WARNING )
            /* __STM32F7xx_HAL_VERSION, __STM32F4xx_HAL_VERSION */
            #warning "As of F7 V1.17.1 && F4 V1.28.0, a bug exists in the ETH HAL Driver where ETH_RX_BUF_SIZE is used instead of RxBuffLen, so ETH_RX_BUF_SIZE must == niEMAC_DATA_BUFFER_SIZE"
        #endif
    #endif

#endif

#if ipconfigIS_DISABLED( ipconfigPORT_SUPPRESS_WARNING )

    #if ipconfigIS_DISABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
        #warning "Consider enabling ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM for NetworkInterface"
    #endif

    #if ipconfigIS_DISABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM )
        #warning "Consider enabling ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM for NetworkInterface"
    #endif

    #if ipconfigIS_DISABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES )
        #warning "Consider enabling ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES for NetworkInterface"
    #endif

    #if ipconfigIS_DISABLED( ipconfigUSE_LINKED_RX_MESSAGES )
        #warning "Consider enabling ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES for NetworkInterface"
    #endif

#endif

/* TODO: There should be a universal check for use in network interfaces, similar to eConsiderFrameForProcessing.
 * So, don't use this macro, and filter anyways in the mean time. */
/* #if ipconfigIS_DISABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
    #if ipconfigIS_DISABLED( ipconfigPORT_SUPPRESS_WARNING )
        #warning "Consider enabling ipconfigETHERNET_DRIVER_FILTERS_PACKETS for NetworkInterface"
    #endif
#endif */

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                            Macros & Definitions                           */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#define niEMAC_BUFS_PER_DESC 2U

/* TODO: Enabled and use interrupts for phy instead of polling? */
/*#define niPHY_ISR_AN_COMPLETE 0x0040
#define niPHY_ISR_LINK_DOWN 0x0010

#define niPHY_IMR_AN_COMPLETE 0x0040
#define niPHY_IMR_LINK_DOWN 0x0010*/

/* IEEE 802.3 CRC32 polynomial - 0x04C11DB7 */
#define niEMAC_CRC_POLY 0x04C11DB7
#define niEMAC_MAC_IS_MULTICAST( MAC )  ( ( MAC[ 0 ] & 1U ) != 0 )
#define niEMAC_MAC_IS_UNICAST( MAC )    ( ( MAC[ 0 ] & 1U ) == 0 )
#define niEMAC_ADDRESS_HASH_BITS    64U
#define niEMAC_MAC_SRC_MATCH_COUNT  3U

#define niEMAC_DEBUG( X, MSG ) if( ( X ) != 0 ) { FreeRTOS_debug_printf( ( MSG ) ); }

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                               typedefs                                    */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

/* Interrupt events to process: reception, transmission and error handling. */
typedef enum {
    eMacEventNone = 0,
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
static void prvAddAllowedMACAddress( NetworkInterface_t * pxInterface, const uint8_t * pucMacAddress );
static void prvRemoveAllowedMACAddress( NetworkInterface_t * pxInterface, const uint8_t * pucMacAddress );

/* EMAC Task */
static BaseType_t prvNetworkInterfaceInput( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface );
static __NO_RETURN portTASK_FUNCTION_PROTO( prvEMACHandlerTask, pvParameters );
static BaseType_t prvEMACTaskStart( NetworkInterface_t * pxInterface );

/* EMAC Init */
static BaseType_t prvEthConfigInit( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface );
static void prvInitMacAddresses( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface );
#ifdef niEMAC_STM32HX
    static void prvInitPacketFilter( ETH_HandleTypeDef * pxEthHandle, const NetworkInterface_t * const pxInterface );
#endif
static BaseType_t prvPhyStart( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface, EthernetPhy_t * pxPhyObject );

/* MAC Filtering Helpers */
static uint32_t prvCalcCrc32( const uint8_t * const pucMACAddr );
static uint8_t prvGetMacHashIndex( const uint8_t * const pucMACAddr );
static void prvHAL_ETH_SetDestMACAddrMatch( ETH_HandleTypeDef * pxEthHandle, uint8_t ucIndex, const uint8_t * const pucMACAddr );
static void prvHAL_ETH_ClearDestMACAddrMatch( ETH_HandleTypeDef * pxEthHandle, uint8_t ucIndex );
static BaseType_t prvAddDestMACAddrMatch( ETH_HandleTypeDef * pxEthHandle, const uint8_t * const pucMACAddr );
static BaseType_t prvRemoveDestMACAddrMatch( ETH_HandleTypeDef * pxEthHandle, const uint8_t * const pucMACAddr );
static BaseType_t prvSetNewDestMACAddrMatch( ETH_HandleTypeDef * pxEthHandle, uint8_t ucHashIndex, const uint8_t * const pucMACAddr );
static void prvAddDestMACAddrHash( ETH_HandleTypeDef * pxEthHandle, uint8_t ucHashIndex );
static void prvRemoveDestMACAddrHash( ETH_HandleTypeDef * pxEthHandle, const uint8_t * const pucMACAddr );

/* EMAC Helpers */
static void prvReleaseTxPacket( ETH_HandleTypeDef * pxEthHandle );
static BaseType_t prvMacUpdateConfig( ETH_HandleTypeDef * pxEthHandle, EthernetPhy_t * pxPhyObject );
static void prvReleaseNetworkBufferDescriptor( NetworkBufferDescriptor_t * const pxDescriptor );
static void prvSendRxEvent( NetworkBufferDescriptor_t * const pxDescriptor );
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

/* static ETH_TxPacketConfig xTxConfig; */

static EthernetPhy_t xPhyObject;

static TaskHandle_t xEMACTaskHandle = NULL;

static SemaphoreHandle_t xTxMutex = NULL, xTxDescSem = NULL;

static BaseType_t xSwitchRequired = pdFALSE;

static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMacEthInit;

/* Src Mac Matching */
/* ETH_MAC_ADDRESS0 reserved for the primary MAC-address. */
static const uint32_t xSrcMatchRegOffets[ niEMAC_MAC_SRC_MATCH_COUNT ] = { ETH_MAC_ADDRESS1, ETH_MAC_ADDRESS2, ETH_MAC_ADDRESS3 };
static uint8_t ucSrcMatchCounters[ niEMAC_MAC_SRC_MATCH_COUNT ] = { 0U };
static uint8_t uxMACEntryIndex = 0;

/* Src Mac Hashing */
static uint32_t ulHashTable[ niEMAC_ADDRESS_HASH_BITS / 32 ];
static uint8_t ucAddrHashCounters[ niEMAC_ADDRESS_HASH_BITS ] = { 0U };

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

    /* const EMACData_t xEMACData = *( ( EMACData_t * ) pxInterface->pvArgument ); */

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
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInitialise: eMacEthInit failed\n" ) );
                break;
            }

            xMacInitStatus = eMacPhyInit;
            /* fallthrough */

        case eMacPhyInit:
            vPhyInitialise( pxPhyObject, ( xApplicationPhyReadHook_t ) prvPhyReadReg, ( xApplicationPhyWriteHook_t ) prvPhyWriteReg );

            if( xPhyDiscover( pxPhyObject ) == 0 )
            {
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInitialise: eMacPhyInit failed\n" ) );
                break;
            }

            xMacInitStatus = eMacPhyStart;
            /* fallthrough */

        case eMacPhyStart:
            if( prvPhyStart( pxEthHandle, pxInterface, pxPhyObject ) == pdFALSE )
            {
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInitialise: eMacPhyStart failed\n" ) );
                break;
            }

            xMacInitStatus = eMacTaskStart;
            /* fallthrough */

        case eMacTaskStart:
            if( prvEMACTaskStart( pxInterface ) == pdFALSE )
            {
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInitialise: eMacTaskStart failed\n" ) );
                break;
            }

            xMacInitStatus = eMacEthStart;
            /* fallthrough */

        case eMacEthStart:
            if( HAL_ETH_GetState( pxEthHandle ) != HAL_ETH_STATE_STARTED )
            {
                if( HAL_ETH_Start_IT( pxEthHandle ) != HAL_OK )
                {
                    FreeRTOS_debug_printf( ( "prvNetworkInterfaceInitialise: eMacEthStart failed\n" ) );
                    break;
                }
            }

            xMacInitStatus = eMacInitComplete;
            /* fallthrough */

        case eMacInitComplete:
            if( prvGetPhyLinkStatus( pxInterface ) != pdTRUE )
            {
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInitialise: eMacInitComplete failed\n" ) );
                break;
            }

            xInitResult = pdPASS;
    }

    return xInitResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceOutput( NetworkInterface_t * pxInterface, NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend )
{
    BaseType_t xResult = pdFAIL;
    /* Zero-Copy Only */
    configASSERT( xReleaseAfterSend == pdTRUE );

    do
    {
        ETH_HandleTypeDef * pxEthHandle = &xEthHandle;

        if( ( pxDescriptor == NULL ) || ( pxDescriptor->pucEthernetBuffer == NULL ) || ( pxDescriptor->xDataLength > niEMAC_DATA_BUFFER_SIZE ) )
        {
            /* TODO: if xDataLength is greater than niEMAC_DATA_BUFFER_SIZE, you can link buffers */
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

        if( prvGetPhyLinkStatus( pxInterface ) == pdFALSE )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Link Down\n" ) );
            break;
        }

        if( ( xMacInitStatus != eMacInitComplete ) || ( HAL_ETH_GetState( pxEthHandle ) != HAL_ETH_STATE_STARTED ) )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Interface Not Started\n" ) );
            break;
        }

        /* static ETH_BufferTypeDef xTxBuffers[ niEMAC_BUFS_PER_DESC * ETH_TX_DESC_CNT ] = { 0 }; */

        static ETH_TxPacketConfig xTxConfig = {
            .Attributes = ETH_TX_PACKETS_FEATURES_CRCPAD,
            .Length = 0U,
            .TxBuffer = NULL,
            /* .SrcAddrCtrl = ETH_SRC_ADDR_CONTROL_DISABLE, */
            .CRCPadCtrl = ETH_CRC_PAD_INSERT,
            .ChecksumCtrl = ETH_CHECKSUM_IPHDR_PAYLOAD_INSERT_PHDR_CALC,
            .MaxSegmentSize = ipconfigTCP_MSS,
            .PayloadLen = 0U,
            .TCPHeaderLen = 0U,
            .VlanTag = 0U,
            /* .VlanCtrl = ETH_VLAN_DISABLE, */
            .InnerVlanTag = 0U,
            /* .InnerVlanCtrl = ETH_INNER_VLAN_DISABLE, */
            .pData = NULL,
        };

        #if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
            xTxConfig.Attributes |= ETH_TX_PACKETS_FEATURES_CSUM;
        #endif

        const EthernetHeader_t * const pxEthHeader = ( const EthernetHeader_t * const ) pxDescriptor->pucEthernetBuffer;
        if( pxEthHeader->usFrameType == ipIPv4_FRAME_TYPE )
        {
            #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
                const IPPacket_t * const pxIPPacket = ( const IPPacket_t * const ) pxDescriptor->pucEthernetBuffer;
                /* ProtocolPacket_t * const pxIPPacket = ( ProtocolPacket_t * const ) pxDescriptor->pucEthernetBuffer; */
                /* ProtocolHeaders_t * const pxIPPacket = ( ProtocolHeaders_t * const ) pxDescriptor->pucEthernetBuffer; */

                if( pxIPPacket->xIPHeader.ucProtocol == ipPROTOCOL_ICMP )
                {
                    #if ipconfigIS_ENABLED( ipconfigREPLY_TO_INCOMING_PINGS ) || ipconfigIS_ENABLED( ipconfigSUPPORT_OUTGOING_PINGS )
                        ICMPPacket_t * const pxICMPPacket = ( ICMPPacket_t * const ) pxDescriptor->pucEthernetBuffer;
                        #if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
                            pxICMPPacket->xICMPHeader.usChecksum = 0U;
                        #endif
                        ( void ) pxICMPPacket;
                    #else
                        FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Unsupported ICMP\n" ) );
                    #endif
                }
                else if( pxIPPacket->xIPHeader.ucProtocol == ipPROTOCOL_TCP )
                {
                    #if ipconfigIS_ENABLED( ipconfigUSE_TCP )
                        TCPPacket_t * const pxTCPPacket = ( TCPPacket_t * const ) pxDescriptor->pucEthernetBuffer;
                        /* #if defined( niEMAC_STM32HX ) && ipconfigIS_ENABLED( niEMAC_TCP_SEGMENTATION )
                            xTxConfig.PayloadLen = pxDescriptor->xDataLength;
                            xTxConfig.TCPHeaderLen = ( pxTCPPacket->xIPHeader.ucVersionHeaderLength & ( uint8_t ) 0x0FU );
                            xTxConfig.Attributes |= ETH_TX_PACKETS_FEATURES_TSO;
                        #endif */
                        ( void ) pxTCPPacket;
                    #else
                        FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Unsupported TCP\n" ) );
                    #endif
                }
                else if( pxIPPacket->xIPHeader.ucProtocol == ipPROTOCOL_UDP )
                {
                    UDPPacket_t * const pxUDPPacket = ( UDPPacket_t * const ) pxDescriptor->pucEthernetBuffer;
                    ( void ) pxUDPPacket;
                }
            #else
                FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Unsupported IPv4\n" ) );
            #endif /* if ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) */
        }
        else if( pxEthHeader->usFrameType == ipIPv6_FRAME_TYPE )
        {
            #if ipconfigIS_ENABLED( ipconfigUSE_IPv6 )
                const IPPacket_IPv6_t * pxIPPacket_IPv6 = ( IPPacket_IPv6_t * ) pxDescriptor->pucEthernetBuffer;

                if( pxIPPacket_IPv6->xIPHeader.ucNextHeader == ipPROTOCOL_ICMP_IPv6 )
                {
                    #if ipconfigIS_ENABLED( ipconfigREPLY_TO_INCOMING_PINGS ) || ipconfigIS_ENABLED( ipconfigSUPPORT_OUTGOING_PINGS )
                        ICMPPacket_IPv6_t * const pxICMPPacket_IPv6 = ( ICMPPacket_IPv6_t * const ) pxDescriptor->pucEthernetBuffer;
                        #if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
                            pxICMPPacket_IPv6->xICMPHeaderIPv6.usChecksum = 0U;
                        #endif
                        ( void ) pxICMPPacket_IPv6;
                    #else
                        FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Unsupported ICMP\n" ) );
                    #endif
                }
                else if( pxIPPacket_IPv6->xIPHeader.ucNextHeader == ipPROTOCOL_TCP )
                {
                    #if ipconfigIS_ENABLED( ipconfigUSE_TCP )
                        TCPPacket_IPv6_t * const pxTCPPacket_IPv6 = ( TCPPacket_IPv6_t * const ) pxDescriptor->pucEthernetBuffer;
                        /* #if defined( niEMAC_STM32HX ) && ipconfigIS_ENABLED( niEMAC_TCP_SEGMENTATION )
                            xTxConfig.PayloadLen = pxDescriptor->xDataLength;
                            xTxConfig.TCPHeaderLen = sizeof( pxTCPPacket_IPv6->xTCPHeader );
                            xTxConfig.Attributes |= ETH_TX_PACKETS_FEATURES_TSO;
                        #endif */
                        ( void ) pxTCPPacket_IPv6;
                    #else
                        FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Unsupported TCP\n" ) );
                    #endif
                }
                else if( pxIPPacket_IPv6->xIPHeader.ucNextHeader == ipPROTOCOL_UDP )
                {
                    UDPPacket_t * const pxUDPPacket_IPv6 = ( UDPPacket_t * const ) pxDescriptor->pucEthernetBuffer;
                    ( void ) pxUDPPacket_IPv6;
                }
            #else
                FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Unsupported IPv6\n" ) );
            #endif /* if ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) */
        }
        else if( pxEthHeader->usFrameType == ipARP_FRAME_TYPE )
        {

        }

        ETH_BufferTypeDef xTxBuffer = {
            .buffer = pxDescriptor->pucEthernetBuffer,
            .len = pxDescriptor->xDataLength,
            .next = NULL
        };

        xTxConfig.pData = pxDescriptor;
        xTxConfig.TxBuffer = &xTxBuffer;
        xTxConfig.Length = xTxBuffer.len;

        if( xSemaphoreTake( xTxDescSem, pdMS_TO_TICKS( niEMAC_DESCRIPTOR_WAIT_TIME_MS ) ) == pdFALSE )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: No Descriptors Available\n" ) );
            break;
        }

        if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( niEMAC_TX_MAX_BLOCK_TIME_MS ) ) == pdFALSE )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Process Busy\n" ) );
            ( void ) xSemaphoreGive( xTxDescSem );
            /* TODO: Can we queue it? */
            break;
        }

        if( HAL_ETH_Transmit_IT( pxEthHandle, &xTxConfig ) == HAL_OK )
        {
            /* Released later in deferred task by calling HAL_ETH_ReleaseTxPacket */
            xReleaseAfterSend = pdFALSE;
            xResult = pdPASS;
        }
        else
        {
            ( void ) xSemaphoreGive( xTxDescSem );
            configASSERT( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_STARTED );
            niEMAC_DEBUG( ( HAL_ETH_GetError( pxEthHandle ) & HAL_ETH_ERROR_BUSY ) != 0, "xNetworkInterfaceOutput: Tx Busy\n" );
            /* Add to queue? */
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

static void prvAddAllowedMACAddress( NetworkInterface_t * pxInterface, const uint8_t * pucMacAddress )
{
    ETH_HandleTypeDef * pxEthHandle = &xEthHandle;

    /* TODO: group address filtering with Mask Byte Control */
    BaseType_t xResult = prvAddDestMACAddrMatch( pxEthHandle, pucMacAddress );

    if( xResult == pdFALSE )
    {
        const uint8_t ucHashIndex = prvGetMacHashIndex( pucMacAddress );

        xResult = prvSetNewDestMACAddrMatch( pxEthHandle, ucHashIndex, pucMacAddress );

        if( xResult == pdFALSE )
        {
            prvAddDestMACAddrHash( pxEthHandle, ucHashIndex );
        }
    }
}

/*---------------------------------------------------------------------------*/

static void prvRemoveAllowedMACAddress( NetworkInterface_t * pxInterface, const uint8_t * pucMacAddress )
{
    ETH_HandleTypeDef * pxEthHandle = &xEthHandle;

    const BaseType_t xResult = prvRemoveDestMACAddrMatch( pxEthHandle, pucMacAddress );

    if( xResult == pdFALSE )
    {
        prvRemoveDestMACAddrHash( pxEthHandle, pucMacAddress );
    }
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              EMAC Task                                    */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceInput( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface )
{
    BaseType_t xResult = pdFALSE;
    UBaseType_t uxCount = 0;
    #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
        NetworkBufferDescriptor_t * pxStartDescriptor = NULL;
        NetworkBufferDescriptor_t * pxEndDescriptor = NULL;
    #endif
    NetworkBufferDescriptor_t * pxCurDescriptor = NULL;
    if( ( xMacInitStatus == eMacInitComplete ) && ( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_STARTED ) )
    {
        while( HAL_ETH_ReadData( pxEthHandle, ( void ** ) &pxCurDescriptor ) == HAL_OK )
        {
            ++uxCount;
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
    }

    if( uxCount > 0 )
    {
        #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
            prvSendRxEvent( pxStartDescriptor );
        #endif
        xResult = pdTRUE;
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static portTASK_FUNCTION( prvEMACHandlerTask, pvParameters )
{
    NetworkInterface_t * pxInterface = ( NetworkInterface_t * ) pvParameters;
    ETH_HandleTypeDef * pxEthHandle = &xEthHandle;
    EthernetPhy_t * pxPhyObject = &xPhyObject;

    /* iptraceEMAC_TASK_STARTING(); */

    for( ;; )
    {
        BaseType_t xResult = pdFALSE;
        uint32_t ulISREvents = 0U;

        if( xTaskNotifyWait( 0U, eMacEventAll, &ulISREvents, pdMS_TO_TICKS( niEMAC_TASK_MAX_BLOCK_TIME_MS ) ) == pdTRUE )
        {
            if( ( ulISREvents & eMacEventRx ) != 0 )
            {
                xResult = prvNetworkInterfaceInput( pxEthHandle, pxInterface );
            }

            if( ( ulISREvents & eMacEventTx ) != 0 )
            {
                prvReleaseTxPacket( pxEthHandle );
            }

            if( ( ulISREvents & eMacEventErrRx ) != 0 )
            {
                xResult = prvNetworkInterfaceInput( pxEthHandle, pxInterface );
            }

            if( ( ulISREvents & eMacEventErrTx ) != 0 )
            {
                prvReleaseTxPacket( pxEthHandle );
            }

            if( ( ulISREvents & eMacEventErrEth ) != 0 )
            {
                configASSERT( ( HAL_ETH_GetError( pxEthHandle ) & HAL_ETH_ERROR_PARAM ) == 0 );
                if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_ERROR )
                {
                    /* Recover from critical error */
                    ( void ) HAL_ETH_Init( pxEthHandle );
                    ( void ) HAL_ETH_Start_IT( pxEthHandle );
                    xResult = prvNetworkInterfaceInput( pxEthHandle, pxInterface );
                }
            }

            /* if( ( ulISREvents & eMacEventErrMac ) != 0 ) */
            /* if( ( ulISREvents & eMacEventErrDma ) != 0 ) */
        }

        if( xPhyCheckLinkStatus( pxPhyObject, xResult ) != pdFALSE )
        {
            if( prvGetPhyLinkStatus( pxInterface ) != pdFALSE )
            {
                if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_ERROR )
                {
                    /* Recover from critical error */
                    ( void ) HAL_ETH_Init( pxEthHandle );
                }
                if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_READY )
                {
                    /* Link was down or critical error occurred */
                    if( prvMacUpdateConfig( pxEthHandle, pxPhyObject ) != pdFALSE )
                    {
                        ( void ) HAL_ETH_Start_IT( pxEthHandle );
                    }
                }
            }
            else
            {
                ( void ) HAL_ETH_Stop_IT( pxEthHandle );
                prvReleaseTxPacket( pxEthHandle );
                #if ( ipconfigIS_ENABLED( ipconfigSUPPORT_NETWORK_DOWN_EVENT ) )
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

static BaseType_t prvEthConfigInit( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface )
{
    BaseType_t xResult = pdFALSE;

    pxEthHandle->Instance = ETH;

    pxEthHandle->Init.MediaInterface = ipconfigIS_ENABLED( niEMAC_USE_RMII ) ? HAL_ETH_RMII_MODE : HAL_ETH_MII_MODE;

    pxEthHandle->Init.RxBuffLen = niEMAC_DATA_BUFFER_SIZE;
    configASSERT( pxEthHandle->Init.RxBuffLen <= ETH_MAX_PACKET_SIZE );
    configASSERT( pxEthHandle->Init.RxBuffLen % 4U == 0 );
    #if ( defined( niEMAC_STM32FX ) && defined( ETH_RX_BUF_SIZE ) )
        configASSERT( pxEthHandle->Init.RxBuffLen == ETH_RX_BUF_SIZE );
    #endif

    #ifdef niEMAC_STM32HX
        configASSERT( ETH_TX_DESC_CNT % 4 == 0 );
        configASSERT( ETH_RX_DESC_CNT % 4 == 0 );
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
        /* ipLOCAL_MAC_ADDRESS */
        pxEthHandle->Init.MACAddr = ( uint8_t * ) pxEndPoint->xMACAddress.ucBytes;

        #if defined( niEMAC_STM32FX )
            /* This function doesn't get called in Fxx driver */
            HAL_ETH_SetMDIOClockRange( pxEthHandle );
        #endif

        if( HAL_ETH_Init( pxEthHandle ) == HAL_OK )
        {
            /* xTxConfig.CRCPadCtrl = ETH_CRC_PAD_INSERT;
            xTxConfig.Attributes = ETH_TX_PACKETS_FEATURES_CRCPAD;
            #if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
                xTxConfig.Attributes |= ETH_TX_PACKETS_FEATURES_CSUM;
                xTxConfig.ChecksumCtrl = ETH_CHECKSUM_IPHDR_PAYLOAD_INSERT_PHDR_CALC;
            #else
                xTxConfig.ChecksumCtrl = ETH_CHECKSUM_DISABLE;
            #endif */

            ETH_MACConfigTypeDef xMACConfig;
            ( void ) HAL_ETH_GetMACConfig( pxEthHandle , &xMACConfig );
            xMACConfig.ChecksumOffload = ( FunctionalState ) ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM );
            #if defined( niEMAC_STM32FX )
                xMACConfig.AutomaticPadCRCStrip = ENABLE;
                xMACConfig.RetryTransmission = ENABLE;
            #elif defined( niEMAC_STM32HX )
                xMACConfig.CRCStripTypePacket = DISABLE;
            #endif
            ( void ) HAL_ETH_SetMACConfig( pxEthHandle, &xMACConfig );

            ETH_DMAConfigTypeDef xDMAConfig;
            ( void ) HAL_ETH_GetDMAConfig( pxEthHandle, &xDMAConfig );
            #if defined( niEMAC_STM32FX )
                xDMAConfig.EnhancedDescriptorFormat = ( FunctionalState ) ( ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM ) || ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM ) );
            #elif defined( niEMAC_STM32HX )
                xDMAConfig.SecondPacketOperate = ENABLE;
                /* #if ipconfigIS_ENABLED( ipconfigUSE_TCP ) && ipconfigIS_ENABLED( niEMAC_TCP_SEGMENTATION )
                    xDMAConfig.TCPSegmentation = ENABLE;
                    xDMAConfig.MaximumSegmentSize = ipconfigTCP_MSS;
                #endif */
            #endif
            ( void ) HAL_ETH_SetDMAConfig( pxEthHandle, &xDMAConfig );

            #if defined( niEMAC_STM32HX )
                prvInitPacketFilter( pxEthHandle, pxInterface );

                /* #if ipconfigIS_ENABLED( niEMAC_ARP_OFFLOAD )
                    HAL_ETHEx_DisableARPOffload( pxEthHandle );
                    HAL_ETHEx_SetARPAddressMatch( pxEthHandle, ulAddress );
                    HAL_ETHEx_EnableARPOffload( pxEthHandle );
                #endif */
            #endif

            prvInitMacAddresses( pxEthHandle, pxInterface );

            xResult = pdTRUE;
        }
    }

    if( xResult == pdTRUE )
    {
        #if defined( __DCACHE_PRESENT ) && ( __DCACHE_PRESENT == 1U )
            if( _FLD2VAL( SCB_CCR_DC, SCB->CCR ) != 0 )
            {
                #if defined( __MPU_PRESENT ) && ( __MPU_PRESENT == 1U )
                    configASSERT( _FLD2VAL( MPU_CTRL_ENABLE, MPU->CTRL ) != 0 );
                #else
                    configASSERT( pdFALSE );
                #endif
            }
        #endif

        const uint32_t ulPriority = NVIC_GetPriority( ETH_IRQn ) << ( 8 - configPRIO_BITS );
        if( ulPriority < configMAX_SYSCALL_INTERRUPT_PRIORITY )
        {
            FreeRTOS_debug_printf( ( "prvEthConfigInit: Incorrectly set ETH_IRQn priority\n" ) );
            NVIC_SetPriority( ETH_IRQn, configMAX_SYSCALL_INTERRUPT_PRIORITY >> ( 8 - configPRIO_BITS ) );
        }
        if( NVIC_GetEnableIRQ( ETH_IRQn ) == 0 )
        {
            FreeRTOS_debug_printf( ( "prvEthConfigInit: ETH_IRQn was not enabled by application\n" ) );
            HAL_NVIC_EnableIRQ( ETH_IRQn );
        }
    }
    else
    {
        #ifdef niEMAC_STM32FX
            configASSERT( __HAL_RCC_ETH_IS_CLK_ENABLED() != 0 );
        #elif defined( STM32H5 )
            configASSERT( __HAL_RCC_ETH_IS_CLK_ENABLED() != 0 );
            configASSERT( __HAL_RCC_ETHTX_IS_CLK_ENABLED() != 0 );
            configASSERT( __HAL_RCC_ETHRX_IS_CLK_ENABLED() != 0 );
        #elif defined( STM32H7)
            configASSERT( __HAL_RCC_ETH1MAC_IS_CLK_ENABLED() != 0 );
            configASSERT( __HAL_RCC_ETH1TX_IS_CLK_ENABLED() != 0 );
            configASSERT( __HAL_RCC_ETH1RX_IS_CLK_ENABLED() != 0 );
        #endif
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static void prvInitMacAddresses( ETH_HandleTypeDef * pxEthHandle, NetworkInterface_t * pxInterface )
{
    ETH_MACFilterConfigTypeDef xFilterConfig;
    ( void ) HAL_ETH_GetMACFilterConfig( pxEthHandle, &xFilterConfig );
    xFilterConfig.ReceiveAllMode = DISABLE;
    xFilterConfig.HachOrPerfectFilter = ENABLE;
    xFilterConfig.SrcAddrFiltering = DISABLE;
    xFilterConfig.SrcAddrInverseFiltering = DISABLE;
    #ifdef niEMAC_STM32FX
        /* Note: ETH_CTRLPACKETS_BLOCK_ALL is incorrectly defined in HAL ETH Driver as of F7 V1.17.1 && F4 V1.28.0 */
        xFilterConfig.ControlPacketsFilter = ETH_MACFFR_PCF_BlockAll;
    #else
        xFilterConfig.ControlPacketsFilter = ETH_CTRLPACKETS_BLOCK_ALL;
    #endif
    xFilterConfig.BroadcastFilter = ENABLE;
    xFilterConfig.PassAllMulticast = DISABLE;
    xFilterConfig.DestAddrInverseFiltering = DISABLE;
    xFilterConfig.HashMulticast = ENABLE;
    xFilterConfig.HashUnicast = ENABLE;
    xFilterConfig.PromiscuousMode = DISABLE;
    ( void ) HAL_ETH_SetMACFilterConfig( pxEthHandle, &xFilterConfig );

    NetworkEndPoint_t * pxEndPoint;
    for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface ); pxEndPoint != NULL; pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
    {
        prvAddAllowedMACAddress( pxInterface, pxEndPoint->xMACAddress.ucBytes );
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
}

/*---------------------------------------------------------------------------*/

#ifdef niEMAC_STM32HX

static void prvInitPacketFilter( ETH_HandleTypeDef * pxEthHandle, const NetworkInterface_t * const pxInterface )
{
    HAL_ETHEx_DisableL3L4Filtering( pxEthHandle );

    if( ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM ) )
    {
        ETH_MACConfigTypeDef xMACConfig;
        ( void ) HAL_ETH_GetMACConfig( pxEthHandle , &xMACConfig );
        if( xMACConfig.ChecksumOffload != ENABLE )
        {
            /* "The Layer 3 and Layer 4 Packet Filter feature automatically selects the IPC Full Checksum
            Offload Engine on the Receive side. When this feature is enabled, you must set the IPC bit." */
            xMACConfig.ChecksumOffload = ENABLE;
            ( void ) HAL_ETH_SetMACConfig( pxEthHandle , &xMACConfig );
        }
        configASSERT( xMACConfig.ChecksumOffload == ENABLE );

        if( ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES ) )
        {
            ETH_L3FilterConfigTypeDef xL3FilterConfig;

            /* Filter out all possibilities if frame type is disabled */
            if( ipconfigIS_DISABLED( ipconfigUSE_IPv4 ) )
            {
                /* Block IPv4 if it is disabled */
                ( void ) HAL_ETHEx_GetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_0, &xL3FilterConfig );
                xL3FilterConfig.Protocol = ETH_L3_IPV4_MATCH;
                xL3FilterConfig.SrcAddrFilterMatch = ETH_L3_SRC_ADDR_PERFECT_MATCH_ENABLE;
                xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_PERFECT_MATCH_ENABLE;
                xL3FilterConfig.SrcAddrHigherBitsMatch = 0x1FU;
                xL3FilterConfig.DestAddrHigherBitsMatch = 0x1FU;
                xL3FilterConfig.Ip4SrcAddr = ipBROADCAST_IP_ADDRESS;
                xL3FilterConfig.Ip4DestAddr = ipBROADCAST_IP_ADDRESS;
                ( void ) HAL_ETHEx_SetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_0, &xL3FilterConfig );
            }

            if( ipconfigIS_DISABLED( ipconfigUSE_IPv6 ) )
            {
                /* Block IPv6 if it is disabled */
                ( void ) HAL_ETHEx_GetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_1, &xL3FilterConfig );
                xL3FilterConfig.Protocol = ETH_L3_IPV6_MATCH;
                xL3FilterConfig.SrcAddrFilterMatch = ETH_L3_SRC_ADDR_PERFECT_MATCH_ENABLE;
                xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_PERFECT_MATCH_ENABLE;
                xL3FilterConfig.SrcAddrHigherBitsMatch = 0x1FU;
                xL3FilterConfig.DestAddrHigherBitsMatch = 0x1FU;
                xL3FilterConfig.Ip6Addr[ 0 ] = 0xFFFFFFFFU;
                xL3FilterConfig.Ip6Addr[ 1 ] = 0xFFFFFFFFU;
                xL3FilterConfig.Ip6Addr[ 2 ] = 0xFFFFFFFFU;
                xL3FilterConfig.Ip6Addr[ 3 ] = 0xFFFFFFFFU;
                ( void ) HAL_ETHEx_SetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_1, &xL3FilterConfig );
            }

            for( NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface ); pxEndPoint != NULL; pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
            {
                if( ENDPOINT_IS_IPv4( pxEndPoint ) )
                {
                    if( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )
                    {
                        ( void ) HAL_ETHEx_GetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_0, &xL3FilterConfig );
                        xL3FilterConfig.Protocol = ETH_L3_IPV4_MATCH;
                        xL3FilterConfig.SrcAddrFilterMatch = ETH_L3_SRC_ADDR_MATCH_DISABLE;
                        xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_MATCH_DISABLE;
                        xL3FilterConfig.SrcAddrHigherBitsMatch = 0U /* Don't Care */;
                        xL3FilterConfig.DestAddrHigherBitsMatch = 0x1FU;
                        xL3FilterConfig.Ip4SrcAddr = 0U /* Don't Care */;
                        xL3FilterConfig.Ip4DestAddr = pxEndPoint->ipv4_settings.ulIPAddress;
                        ( void ) HAL_ETHEx_SetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_0, &xL3FilterConfig );
                    }
                }
                else if( ENDPOINT_IS_IPv6( pxEndPoint ) )
                {
                    if( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
                    {
                        ( void ) HAL_ETHEx_GetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_1, &xL3FilterConfig );
                        xL3FilterConfig.Protocol = ETH_L3_IPV6_MATCH;
                        xL3FilterConfig.SrcAddrFilterMatch = ETH_L3_SRC_ADDR_MATCH_DISABLE;
                        xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_MATCH_DISABLE;
                        xL3FilterConfig.SrcAddrHigherBitsMatch = 0U; /* Don't Care */
                        xL3FilterConfig.DestAddrHigherBitsMatch = 0x1FU;
                        xL3FilterConfig.Ip6Addr[ 0 ] = 0xFFFFFFFFU;
                        xL3FilterConfig.Ip6Addr[ 1 ] = 0xFFFFFFFFU;
                        xL3FilterConfig.Ip6Addr[ 2 ] = 0xFFFFFFFFU;
                        xL3FilterConfig.Ip6Addr[ 3 ] = 0xFFFFFFFFU;
                        ( void ) HAL_ETHEx_SetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_1, &xL3FilterConfig );
                    }
                }
            }
        } /* if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES ) */

        if( ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS ) )
        {
            /* TODO: Let user to block certain port numbers */
            /* TODO: Live updated in task based on active sockets? */
            ETH_L4FilterConfigTypeDef xL4FilterConfig;

            /* Always allow all UDP */
            ( void ) HAL_ETHEx_GetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_0, &xL4FilterConfig );
            xL4FilterConfig.Protocol = ETH_L4_UDP_MATCH;
            xL4FilterConfig.SrcPortFilterMatch = ETH_L4_SRC_PORT_MATCH_DISABLE;
            xL4FilterConfig.DestPortFilterMatch = ETH_L4_SRC_PORT_MATCH_DISABLE;
            xL4FilterConfig.SourcePort = 0U;
            xL4FilterConfig.DestinationPort = 0U;
            ( void ) HAL_ETHEx_SetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_0, &xL4FilterConfig );

            if( ipconfigIS_DISABLED( ipconfigUSE_TCP ) )
            {
                /* Block TCP if it is disabled */
                ( void ) HAL_ETHEx_GetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_1, &xL4FilterConfig );
                xL4FilterConfig.Protocol = ETH_L4_TCP_MATCH;
                xL4FilterConfig.SrcPortFilterMatch = ETH_L4_SRC_PORT_PERFECT_MATCH_ENABLE;
                xL4FilterConfig.DestPortFilterMatch = ETH_L4_DEST_PORT_PERFECT_MATCH_ENABLE;
                xL4FilterConfig.SourcePort = 0xFFFFU;
                xL4FilterConfig.DestinationPort = 0xFFFFU;
                ( void ) HAL_ETHEx_SetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_1, &xL4FilterConfig );
            }
        }

        HAL_ETHEx_EnableL3L4Filtering( pxEthHandle );

    } /* if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM ) */
}

#endif /* ifdef niEMAC_STM32HX */

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
            #elif ipconfigIS_ENABLED( niEMAC_CROSSED_LINK )
                .ucMDI_X = PHY_MDIX_CROSSED,
            #else
                .ucMDI_X = PHY_MDIX_DIRECT,
            #endif
        };

        #if ipconfigIS_DISABLED( niEMAC_AUTO_NEGOTIATION )
            pxPhyObject->xPhyPreferences.ucSpeed = ipconfigIS_ENABLED( niEMAC_USE_100MB ) ? PHY_SPEED_100 : PHY_SPEED_10;
            pxPhyObject->xPhyPreferences.ucDuplex = ipconfigIS_ENABLED( niEMAC_USE_FULL_DUPLEX ) ? PHY_DUPLEX_FULL : PHY_DUPLEX_HALF;
        #endif

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
/*                           MAC Filtering Helpers                           */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

/* Compute the CRC32 of the given MAC address as per IEEE 802.3 CRC32 */
static uint32_t prvCalcCrc32( const uint8_t * const pucMACAddr )
{
    uint32_t ulCRC32 = 0xFFFFFFFFU;

    uint32_t ucIndex;
    for( ucIndex = ipMAC_ADDRESS_LENGTH_BYTES; ucIndex > 0; --ucIndex )
    {
        ulCRC32 ^= __RBIT( pucMACAddr[ ipMAC_ADDRESS_LENGTH_BYTES - ucIndex ] );

        uint8_t ucJndex;
        for( ucJndex = 8; ucJndex > 0; --ucJndex )
        {
            if( ulCRC32 & 0x80000000U )
            {
                ulCRC32 <<= 1;
                ulCRC32 ^= niEMAC_CRC_POLY;
            }
            else
            {
                ulCRC32 <<= 1;
            }
        }
    }

    return ~ulCRC32;
}

/*---------------------------------------------------------------------------*/

static uint8_t prvGetMacHashIndex( const uint8_t * const pucMACAddr )
{
    const uint32_t ulHash = prvCalcCrc32( pucMACAddr );
    const uint8_t ucHashIndex = ( ulHash >> 26 ) & 0x3FU;

    return ucHashIndex;
}

/*---------------------------------------------------------------------------*/

/* Needed since HAL Driver only provides source matching */
static void prvHAL_ETH_SetDestMACAddrMatch( ETH_HandleTypeDef * pxEthHandle, uint8_t ucIndex, const uint8_t * const pucMACAddr )
{
    /* Get mac addr high reg offset */
    const uint32_t macaddrhr = ((uint32_t) &(pxEthHandle->Instance->MACA0HR) + xSrcMatchRegOffets[ ucIndex ]);
    /* Get mac addr low reg offset */
    const uint32_t macaddrlr = ((uint32_t) &(pxEthHandle->Instance->MACA0LR) + xSrcMatchRegOffets[ ucIndex ]);

    /* Set MAC addr bits 32 to 47 */
    (*(__IO uint32_t *)macaddrhr) = (((uint32_t)(pucMACAddr[5]) << 8) | (uint32_t)pucMACAddr[4]);
    /* Set MAC addr bits 0 to 31 */
    (*(__IO uint32_t *)macaddrlr) = (((uint32_t)(pucMACAddr[3]) << 24) | ((uint32_t)(pucMACAddr[2]) << 16) |
                                     ((uint32_t)(pucMACAddr[1]) << 8) | (uint32_t)pucMACAddr[0]);

    /* Enable address and set source address bit */
    (*(__IO uint32_t *)macaddrhr) |= ETH_MACA1HR_AE;
}

/*---------------------------------------------------------------------------*/

static void prvHAL_ETH_ClearDestMACAddrMatch( ETH_HandleTypeDef * pxEthHandle, uint8_t ucIndex )
{
    /* Get mac addr high reg offset */
    const uint32_t macaddrhr = ((uint32_t) &(pxEthHandle->Instance->MACA0HR) + xSrcMatchRegOffets[ ucIndex ]);
    /* Get mac addr low reg offset */
    const uint32_t macaddrlr = ((uint32_t) &(pxEthHandle->Instance->MACA0LR) + xSrcMatchRegOffets[ ucIndex ]);

    /* Clears MAC addr bits 32 to 47 and ETH_MACAHR_AE */
    (*(__IO uint32_t *)macaddrhr) = 0;
    /* Clears MAC addr bits 0 to 31 */
    (*(__IO uint32_t *)macaddrlr) = 0;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvAddDestMACAddrMatch( ETH_HandleTypeDef * pxEthHandle, const uint8_t * const pucMACAddr )
{
    BaseType_t xResult = pdFALSE;

    uint8_t ucIndex;
    for( ucIndex = 0; ucIndex < niEMAC_MAC_SRC_MATCH_COUNT; ++ucIndex )
    {
        if( ucSrcMatchCounters[ ucIndex ] > 0U )
        {
            const uint32_t ulNewMacAddrHigh = ( pucMACAddr[ 5 ] << 8 ) | ( pucMACAddr[ 4 ] );
            const uint32_t ulNewMacAddrLow = ( pucMACAddr[ 3 ] << 24 ) | ( pucMACAddr[ 2 ] << 16 ) | ( pucMACAddr[ 1 ] << 8 ) | ( pucMACAddr[ 0 ] );

            const uint32_t ulMacAddrHigh = ( ( ( uint32_t ) &( pxEthHandle->Instance->MACA0HR ) + xSrcMatchRegOffets[ ucIndex ] ) & 0x0000FFFFU );
            const uint32_t ulMacAddrLow = ( ( uint32_t ) &( pxEthHandle->Instance->MACA0LR ) + xSrcMatchRegOffets[ ucIndex ]);

            if( ( ulNewMacAddrHigh == ulMacAddrHigh ) && ( ulNewMacAddrLow == ulMacAddrLow ) )
            {
                ++( ucSrcMatchCounters[ ucIndex ] );
                xResult = pdTRUE;
                break;
            }
        }
        else if( uxMACEntryIndex > niEMAC_MAC_SRC_MATCH_COUNT )
        {
            uxMACEntryIndex = niEMAC_MAC_SRC_MATCH_COUNT;
        }
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvRemoveDestMACAddrMatch( ETH_HandleTypeDef * pxEthHandle, const uint8_t * const pucMACAddr )
{
    BaseType_t xResult = pdFALSE;

    uint8_t ucIndex;
    for( ucIndex = 0; ucIndex < niEMAC_MAC_SRC_MATCH_COUNT; ++ucIndex )
    {
        if( ucSrcMatchCounters[ ucIndex ] > 0U )
        {
            const uint32_t ulNewMacAddrHigh = ( pucMACAddr[ 5 ] << 8 ) | ( pucMACAddr[ 4 ] );
            const uint32_t ulNewMacAddrLow = ( pucMACAddr[ 3 ] << 24 ) | ( pucMACAddr[ 2 ] << 16 ) | ( pucMACAddr[ 1 ] << 8 ) | ( pucMACAddr[ 0 ] );

            const uint32_t ulMacAddrHigh = ( ( ( uint32_t ) &( pxEthHandle->Instance->MACA0HR ) + xSrcMatchRegOffets[ ucIndex ] ) & 0x0000FFFFU );
            const uint32_t ulMacAddrLow = ( ( uint32_t ) &( pxEthHandle->Instance->MACA0LR ) + xSrcMatchRegOffets[ ucIndex ]);

            if( ( ulNewMacAddrHigh == ulMacAddrHigh ) && ( ulNewMacAddrLow == ulMacAddrLow ) )
            {
                if( ucSrcMatchCounters[ ucIndex ] < UINT8_MAX )
                {
                    if( --( ucSrcMatchCounters[ ucIndex ] ) == 0 )
                    {
                        prvHAL_ETH_ClearDestMACAddrMatch( pxEthHandle, ucIndex );
                    }
                }

                xResult = pdTRUE;
                break;
            }
        }
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvSetNewDestMACAddrMatch( ETH_HandleTypeDef * pxEthHandle, uint8_t ucHashIndex, const uint8_t * const pucMACAddr )
{
    BaseType_t xResult = pdFALSE;

    if( uxMACEntryIndex < niEMAC_MAC_SRC_MATCH_COUNT )
    {
        if( ucAddrHashCounters[ ucHashIndex ] == 0U )
        {
            prvHAL_ETH_SetDestMACAddrMatch( pxEthHandle, uxMACEntryIndex, pucMACAddr );
            ucSrcMatchCounters[ uxMACEntryIndex ] = 1U;
            xResult = pdTRUE;
        }
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static void prvAddDestMACAddrHash( ETH_HandleTypeDef * pxEthHandle, uint8_t ucHashIndex )
{
    if( ucAddrHashCounters[ ucHashIndex ] == 0 )
    {
        if( ucHashIndex & 0x20U )
        {
            ulHashTable[ 1 ] |= ( 1U << ( ucHashIndex & 0x1FU ) );
        }
        else
        {
            ulHashTable[ 0 ] |= ( 1U << ucHashIndex );
        }

        ( void ) HAL_ETH_SetHashTable( pxEthHandle, ulHashTable );
    }

    if( ucAddrHashCounters[ ucHashIndex ] < UINT8_MAX )
    {
        ++( ucAddrHashCounters[ ucHashIndex ] );
    }
}

/*---------------------------------------------------------------------------*/

static void prvRemoveDestMACAddrHash( ETH_HandleTypeDef * pxEthHandle, const uint8_t * const pucMACAddr )
{
    const uint8_t ucHashIndex = prvGetMacHashIndex( pucMACAddr );

    if( ucAddrHashCounters[ ucHashIndex ] > 0U )
    {
        if( ucAddrHashCounters[ ucHashIndex ] < UINT8_MAX )
        {
            if( --ucAddrHashCounters[ ucHashIndex ] == 0 )
            {
                if( ucHashIndex & 0x20U )
                {
                    ulHashTable[ 1 ] &= ~( 1U << ( ucHashIndex & 0x1FU ) );
                }
                else
                {
                    ulHashTable[ 0 ] &= ~( 1U << ucHashIndex );
                }

                ( void ) HAL_ETH_SetHashTable( pxEthHandle, ulHashTable );
            }
        }
    }
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              EMAC Helpers                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static void prvReleaseTxPacket( ETH_HandleTypeDef * pxEthHandle )
{
    if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( niEMAC_TX_MAX_BLOCK_TIME_MS ) ) != pdFALSE )
    {
        ( void ) HAL_ETH_ReleaseTxPacket( pxEthHandle );
        ( void ) xSemaphoreGive( xTxMutex );
    }
    else
    {
        FreeRTOS_debug_printf( ( "prvReleaseTxPacket: Failed\n" ) );
    }

    /* TODO: Is it possible for the semaphore and BuffersInUse to get out of sync? */
    /* while( ETH_TX_DESC_CNT - uxQueueMessagesWaiting( ( QueueHandle_t ) xTxDescSem ) > pxEthHandle->TxDescList.BuffersInUse )
    {
        ( void ) xSemaphoreGive( xTxDescSem );
    } */
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvMacUpdateConfig( ETH_HandleTypeDef * pxEthHandle, EthernetPhy_t * pxPhyObject )
{
    BaseType_t xResult = pdFALSE;

    if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_STARTED )
    {
        ( void ) HAL_ETH_Stop_IT( pxEthHandle );
    }

    ETH_MACConfigTypeDef xMACConfig;
    ( void ) HAL_ETH_GetMACConfig( pxEthHandle , &xMACConfig );

    #if ipconfigIS_ENABLED( niEMAC_AUTO_NEGOTIATION )
        ( void ) xPhyStartAutoNegotiation( pxPhyObject, xPhyGetMask( pxPhyObject ) );
    #else
        ( void ) xPhyFixedValue( pxPhyObject, xPhyGetMask( pxPhyObject ) );
    #endif
    xMACConfig.DuplexMode = ( pxPhyObject->xPhyProperties.ucDuplex == PHY_DUPLEX_FULL ) ? ETH_FULLDUPLEX_MODE : ETH_HALFDUPLEX_MODE;
    xMACConfig.Speed = ( pxPhyObject->xPhyProperties.ucSpeed == PHY_SPEED_10 ) ? ETH_SPEED_10M : ETH_SPEED_100M;

    if( HAL_ETH_SetMACConfig( pxEthHandle, &xMACConfig ) == HAL_OK )
    {
        xResult = pdTRUE;
    }

    #if ipconfigIS_ENABLED( niEMAC_AUTO_LOW_POWER )
        if( ( pxEthHandle->Init.MediaInterface = HAL_ETH_MII_MODE ) && ( xMACConfig.DuplexMode == ETH_FULLDUPLEX_MODE ) && ( xMACConfig.Speed == ETH_SPEED_100M ) )
        {
            HAL_ETHEx_EnterLPIMode( pxEthHandle, ENABLE, DISABLE );
        }
    #endif

    return xResult;
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
    if( xSendEventStructToIPTask( &xRxEvent, pdMS_TO_TICKS( niEMAC_RX_MAX_BLOCK_TIME_MS ) ) != pdPASS )
    {
        iptraceETHERNET_RX_EVENT_LOST();
        FreeRTOS_debug_printf( ( "prvSendRxEvent: xSendEventStructToIPTask failed\n" ) );
        prvReleaseNetworkBufferDescriptor( pxDescriptor );
    }
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvAcceptPacket( const NetworkBufferDescriptor_t * const pxDescriptor, uint16_t usLength )
{
    BaseType_t xResult = pdFALSE;
    do
    {
        if( pxDescriptor == NULL )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Null Descriptor\n" ) );
            break;
        }

        uint32_t ulErrorCode = 0;
        ( void ) HAL_ETH_GetRxDataErrorCode( &xEthHandle, &ulErrorCode );
        if( ulErrorCode != 0 )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Rx Data Error\n" ) );
            break;
        }
        /* if( ( ulErrorCode & ETH_DRIBBLE_BIT_ERROR ) != 0 )
        if( ( ulErrorCode & ETH_RECEIVE_ERROR ) != 0 )
        if( ( ulErrorCode & ETH_RECEIVE_OVERFLOW ) != 0 )
        if( ( ulErrorCode & ETH_WATCHDOG_TIMEOUT ) != 0 )
        if( ( ulErrorCode & ETH_GIANT_PACKET ) != 0 )
        if( ( ulErrorCode & ETH_CRC_ERROR ) != 0 ) */

        if( usLength > niEMAC_DATA_BUFFER_SIZE )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Packet size overflow\n" ) );
            break;
        }

        /* TODO: Should we do this even if it is handled in hardware too? */
        #if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES )
            if( eConsiderFrameForProcessing( pxDescriptor->pucEthernetBuffer ) != eProcessBuffer )
            {
                FreeRTOS_debug_printf( ( "prvAcceptPacket: Frame discarded\n" ) );
                break;
            }
        #endif

        /* TODO: Create a eConsiderPacketForProcessing */
        #if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
            if( eConsiderPacketForProcessing( pxDescriptor->pucEthernetBuffer ) != eProcessBuffer )
            {
                FreeRTOS_debug_printf( ( "prvAcceptPacket: Packet discarded\n" ) );
                break;
            }
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
    eMAC_IF_EVENT eErrorEvents = eMacEventNone;

    if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_ERROR )
    {
        /* Fatal bus error occurred */
        eErrorEvents |= eMacEventErrEth;
    }

    if( ( HAL_ETH_GetError( pxEthHandle ) & HAL_ETH_ERROR_DMA ) != 0 )
    {
        eErrorEvents |= eMacEventErrDma;
        /* if( pxEthHandle->DMAErrorCode & ETH_DMA_TX_PROCESS_STOPPED_FLAG ) */
        #ifdef niEMAC_STM32FX
            if( ( HAL_ETH_GetDMAError( pxEthHandle ) & ETH_DMASR_TBUS ) != 0 )
            {
                eErrorEvents |= eMacEventErrTx;
            }

            if( ( HAL_ETH_GetDMAError( pxEthHandle ) & ETH_DMASR_RBUS ) != 0 )
            {
                eErrorEvents |= eMacEventErrRx;
            }
        #elif defined( niEMAC_STM32HX )
            if( ( HAL_ETH_GetDMAError( pxEthHandle ) & ETH_DMACSR_TBU ) != 0 )
            {
                eErrorEvents |= eMacEventErrTx;
            }

            if( ( HAL_ETH_GetDMAError( pxEthHandle ) & ETH_DMA_RX_BUFFER_UNAVAILABLE_FLAG ) != 0 )
            {
                eErrorEvents |= eMacEventErrRx;
            }
        #endif
    }

    if( ( HAL_ETH_GetError( pxEthHandle ) & HAL_ETH_ERROR_MAC ) != 0 )
    {
        /*if( ( HAL_ETH_GetMACError( pxEthHandle ) & ETH_RECEIVE_WATCHDOG_TIMEOUT ) != 0 )
        if( ( HAL_ETH_GetMACError( pxEthHandle ) & ETH_EXECESSIVE_COLLISIONS ) != 0 )
        if( ( HAL_ETH_GetMACError( pxEthHandle ) & ETH_LATE_COLLISIONS ) != 0 )
        if( ( HAL_ETH_GetMACError( pxEthHandle ) & ETH_EXECESSIVE_DEFERRAL ) != 0 )
        if( ( HAL_ETH_GetMACError( pxEthHandle ) & ETH_LOSS_OF_CARRIER ) != 0 )
        if( ( HAL_ETH_GetMACError( pxEthHandle ) & ETH_NO_CARRIER ) != 0 )
        if( ( HAL_ETH_GetMACError( pxEthHandle ) & ETH_TRANSMIT_JABBR_TIMEOUT ) != 0 )*/
        eErrorEvents |= eMacEventErrMac;
    }

    if( ( xEMACTaskHandle != NULL ) && ( eErrorEvents != eMacEventNone ) )
    {
        BaseType_t xHigherPriorityTaskWoken = pdFALSE;
        ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eErrorEvents, eSetBits, &xHigherPriorityTaskWoken );
        xSwitchRequired |= xHigherPriorityTaskWoken;
    }
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

    if( xEMACTaskHandle != NULL )
    {
        BaseType_t xHigherPriorityTaskWoken = pdFALSE;
        ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventRx, eSetBits, &xHigherPriorityTaskWoken );
        xSwitchRequired |= xHigherPriorityTaskWoken;
    }
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

    if( xEMACTaskHandle != NULL )
    {
        BaseType_t xHigherPriorityTaskWoken = pdFALSE;
        ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eMacEventTx, eSetBits, &xHigherPriorityTaskWoken );
        xSwitchRequired |= xHigherPriorityTaskWoken;
    }
}

/*---------------------------------------------------------------------------*/

#ifdef niEMAC_STM32HX

void HAL_ETH_EEECallback( ETH_HandleTypeDef * pxEthHandle )
{
    switch( HAL_ETHEx_GetMACLPIEvent( pxEthHandle ) )
    {
        case ETH_TX_LPI_ENTRY:
        case ETH_TX_LPI_EXIT:
        case ETH_RX_LPI_ENTRY:
        case ETH_RX_LPI_EXIT:
            break;

        default:
            configASSERT( pdFALSE );
    }
}

#endif

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
    ( void ) xSemaphoreGive( xTxDescSem );
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                           Buffer Allocation                               */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ niEMAC_TOTAL_BUFFER_SIZE ] __ALIGNED( niEMAC_BUF_ALIGNMENT ) __attribute__( ( section( niEMAC_BUFFERS_SECTION ) ) );

    configASSERT( xBufferAllocFixedSize == pdTRUE );

    size_t uxIndex;
    for( uxIndex = 0; uxIndex < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ++uxIndex )
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
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t * pxInterface )
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
        #ifdef niEMAC_STM32FX
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
        GPIO_InitStructure.Speed = GPIO_SPEED_MEDIUM;
        HAL_GPIO_Init(ETH_MDC_Port, &GPIO_InitStructure);
        GPIO_InitStructure.Speed = GPIO_SPEED_HIGH;

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
        HAL_NVIC_SetPriority( ETH_IRQn, ( uint32_t ) configMAX_SYSCALL_INTERRUPT_PRIORITY, 0 );
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

#if defined( __MPU_PRESENT ) && ( __MPU_PRESENT == 1U )

void MPU_Config(void)
{
    MPU_Region_InitTypeDef MPU_InitStruct = {0};

    HAL_MPU_Disable();

    extern uint8_t __ETH_BUFFERS_START;

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


    extern uint8_t __ETH_DESCRIPTORS_START;

    MPU_InitStruct.Enable = MPU_REGION_ENABLE;
    MPU_InitStruct.Number = MPU_REGION_NUMBER1;
    MPU_InitStruct.BaseAddress = ( uint32_t ) &__ETH_DESCRIPTORS_START;
    MPU_InitStruct.Size = MPU_REGION_SIZE_1KB;
    MPU_InitStruct.SubRegionDisable = 0x0;
    MPU_InitStruct.TypeExtField = MPU_TEX_LEVEL0;
    MPU_InitStruct.AccessPermission = MPU_REGION_FULL_ACCESS;
    MPU_InitStruct.DisableExec = MPU_INSTRUCTION_ACCESS_DISABLE;
    MPU_InitStruct.IsShareable = MPU_ACCESS_SHAREABLE;
    MPU_InitStruct.IsCacheable = MPU_ACCESS_NOT_CACHEABLE;
    MPU_InitStruct.IsBufferable = MPU_ACCESS_BUFFERABLE;

    HAL_MPU_ConfigRegion(&MPU_InitStruct);

    HAL_MPU_Enable(MPU_PRIVILEGED_DEFAULT);
}

#endif /* if defined( __MPU_PRESENT ) && ( __MPU_PRESENT == 1U ) */

#endif /* if 0 */

/*---------------------------------------------------------------------------*/
