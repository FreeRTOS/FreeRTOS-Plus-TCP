/*
 * FreeRTOS+TCP
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
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
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
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"
#include "phyHandling.h"

/* ST includes. */
#if defined( STM32F1 )
    #include "stm32f1xx_hal.h"
#elif defined( STM32F2 )
    #include "stm32f2xx_hal.h"
#elif defined( STM32F4 )
    #include "stm32f4xx_hal.h"
#elif defined( STM32F7 )
    #include "stm32f7xx_hal.h"
#elif defined( STM32H7 )
    #include "stm32h7xx_hal.h"
#elif defined( STM32H7RS )
    #include "stm32h7rsxx_hal.h"
#elif defined( STM32H5 )
    #include "stm32h5xx_hal.h"
#elif defined( STM32N6 )
    #include "stm32n6xx_hal.h"
#else /* if defined( STM32F4 ) */
    #error "Unknown STM32 Family for NetworkInterface"
#endif /* if defined( STM32F4 ) */

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                                Config                                     */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#if defined( STM32F7 ) || defined( STM32F4 ) || defined( STM32F2 ) || defined( STM32F1 )
    #define niEMAC_STM32FX
#elif defined( STM32H7 ) || defined( STM32H7RS ) || defined( STM32H5 )
    #define niEMAC_STM32HX
#elif defined( STM32N6 )
    #define niEMAC_STM32NX
#endif

#if defined( niEMAC_STM32HX ) || defined( niEMAC_STM32NX )
    #define niEMAC_STM32HNX
#endif

#if defined( niEMAC_STM32NX )
    #define niEMAC_ETH_INSTANCE         ETH1
    #define niEMAC_ETH_IRQ_NUMBER       ETH1_IRQn
    #define niEMAC_ETH_IRQ_HANDLER      ETH1_IRQHandler
    #define niEMAC_DMA_CHANNEL_INDEX    ETH_DMA_CH0_IDX
    #define niEMAC_RX_CHANNEL_COUNT     ETH_DMA_RX_CH_CNT
    #define niEMAC_TX_CHANNEL_COUNT     ETH_DMA_TX_CH_CNT
    #define niEMAC_RX_DESC_LIST( pxHandle, ulChannel )    ( ( pxHandle )->RxDescList[ ( ulChannel ) ] )
    #define niEMAC_TX_DESC_LIST( pxHandle, ulChannel )    ( ( pxHandle )->TxDescList[ ( ulChannel ) ] )
#else
    #define niEMAC_ETH_INSTANCE        ETH
    #define niEMAC_ETH_IRQ_NUMBER      ETH_IRQn
    #define niEMAC_ETH_IRQ_HANDLER     ETH_IRQHandler
    #define niEMAC_DMA_CHANNEL_INDEX   0U
    #define niEMAC_RX_CHANNEL_COUNT    1U
    #define niEMAC_TX_CHANNEL_COUNT    1U
    #define niEMAC_RX_DESC_LIST( pxHandle, ulChannel )    ( ( pxHandle )->RxDescList )
    #define niEMAC_TX_DESC_LIST( pxHandle, ulChannel )    ( ( pxHandle )->TxDescList )
#endif /* if defined( niEMAC_STM32NX ) */

#if defined( STM32F1 )
    #define niEMAC_ETH_CLOCKS_ENABLED()               \
    ( ( __HAL_RCC_ETHMAC_IS_CLK_ENABLED() != 0 ) &&   \
      ( __HAL_RCC_ETHMACTX_IS_CLK_ENABLED() != 0 ) && \
      ( __HAL_RCC_ETHMACRX_IS_CLK_ENABLED() != 0 ) )
#elif defined( niEMAC_STM32FX )
    #define niEMAC_ETH_CLOCKS_ENABLED()    ( __HAL_RCC_ETH_IS_CLK_ENABLED() != 0 )
#elif defined( STM32H5 )
    #define niEMAC_ETH_CLOCKS_ENABLED()            \
    ( ( __HAL_RCC_ETH_IS_CLK_ENABLED() != 0 ) &&   \
      ( __HAL_RCC_ETHTX_IS_CLK_ENABLED() != 0 ) && \
      ( __HAL_RCC_ETHRX_IS_CLK_ENABLED() != 0 ) )
#elif defined( STM32H7 ) || defined( STM32H7RS )
    #define niEMAC_ETH_CLOCKS_ENABLED()              \
    ( ( __HAL_RCC_ETH1MAC_IS_CLK_ENABLED() != 0 ) && \
      ( __HAL_RCC_ETH1TX_IS_CLK_ENABLED() != 0 ) &&  \
      ( __HAL_RCC_ETH1RX_IS_CLK_ENABLED() != 0 ) )
#elif defined( niEMAC_STM32NX )
    #define niEMAC_ETH_CLOCKS_ENABLED()              \
    ( ( __HAL_RCC_ETH1_IS_CLK_ENABLED() != 0 ) &&    \
      ( __HAL_RCC_ETH1MAC_IS_CLK_ENABLED() != 0 ) && \
      ( __HAL_RCC_ETH1TX_IS_CLK_ENABLED() != 0 ) &&  \
      ( __HAL_RCC_ETH1RX_IS_CLK_ENABLED() != 0 ) )
#endif /* if defined( STM32F1 ) */

#ifndef niEMAC_HANDLER_TASK_NAME
    #define niEMAC_HANDLER_TASK_NAME    "EMAC_STM32"
#endif

#ifndef niEMAC_HANDLER_TASK_PRIORITY
    #define niEMAC_HANDLER_TASK_PRIORITY    ( configMAX_PRIORITIES - 1 )
#endif

#ifndef niEMAC_HANDLER_TASK_STACK_SIZE
    #ifdef configEMAC_TASK_STACK_SIZE
        #define niEMAC_HANDLER_TASK_STACK_SIZE    configEMAC_TASK_STACK_SIZE
    #else
        #define niEMAC_HANDLER_TASK_STACK_SIZE    ( 4U * configMINIMAL_STACK_SIZE )
    #endif
#endif

#ifndef niEMAC_TX_DESC_SECTION
    #define niEMAC_TX_DESC_SECTION    ".TxDescripSection"
#endif

#ifndef niEMAC_RX_DESC_SECTION
    #define niEMAC_RX_DESC_SECTION    ".RxDescripSection"
#endif

#ifndef niEMAC_BUFFERS_SECTION
    #define niEMAC_BUFFERS_SECTION    ".EthBuffersSection"
#endif

#ifndef niEMAC_TASK_MAX_BLOCK_TIME_MS
    #define niEMAC_TASK_MAX_BLOCK_TIME_MS    100U
#endif

#ifndef niEMAC_TX_MAX_BLOCK_TIME_MS
    #define niEMAC_TX_MAX_BLOCK_TIME_MS    20U
#endif

#ifndef niEMAC_RX_MAX_BLOCK_TIME_MS
    #define niEMAC_RX_MAX_BLOCK_TIME_MS    20U
#endif

#ifndef niDESCRIPTOR_WAIT_TIME_MS
    #define niDESCRIPTOR_WAIT_TIME_MS    20U
#endif

#define niEMAC_TX_MUTEX_NAME              "EMAC_TxMutex"
#define niEMAC_TX_DESC_SEM_NAME           "EMAC_TxDescSem"

#ifndef ipconfigETHERNET_AN_ENABLE
    #define ipconfigETHERNET_AN_ENABLE    ipconfigENABLE
#endif

#ifndef ipconfigETHERNET_USE_100MB
    #define ipconfigETHERNET_USE_100MB    ( ipconfigENABLE && ipconfigIS_DISABLED( ipconfigETHERNET_AN_ENABLE ) )
#endif

#ifndef ipconfigETHERNET_USE_FULL_DUPLEX
    #define ipconfigETHERNET_USE_FULL_DUPLEX    ( ipconfigENABLE && ipconfigIS_DISABLED( ipconfigETHERNET_AN_ENABLE ) )
#endif

#ifndef ipconfigETHERNET_AUTO_CROSS_ENABLE
    #define ipconfigETHERNET_AUTO_CROSS_ENABLE    ( ipconfigENABLE && ipconfigIS_ENABLED( ipconfigETHERNET_AN_ENABLE ) )
#endif

#ifndef ipconfigETHERNET_CROSSED_LINK
    #define ipconfigETHERNET_CROSSED_LINK    ( ipconfigENABLE && ipconfigIS_DISABLED( ipconfigETHERNET_AUTO_CROSS_ENABLE ) )
#endif

#ifndef ipconfigUSE_RGMII
    #define ipconfigUSE_RGMII    ipconfigDISABLE
#endif

#ifndef ipconfigUSE_RMII
    #define ipconfigUSE_RMII    ( ipconfigENABLE && ipconfigIS_DISABLED( ipconfigUSE_RGMII ) )
#endif

#ifndef iptraceEMAC_TASK_STARTING
    #ifdef ipconfigEMAC_TASK_HOOK
        #define iptraceEMAC_TASK_STARTING()    ipconfigEMAC_TASK_HOOK()
    #else
        #define iptraceEMAC_TASK_STARTING()    do {} while( 0 )
    #endif
#endif

#ifndef iptraceSTM32_ETH_RX_DESC_USAGE
    #define iptraceSTM32_ETH_RX_DESC_USAGE( ulChannel, uxDescriptorsUsed ) \
    do {                                                                    \
        ( void ) ( ulChannel );                                             \
        ( void ) ( uxDescriptorsUsed );                                     \
    } while( 0 )
#endif

#ifndef iptraceSTM32_ETH_TX_DESC_USAGE
    #define iptraceSTM32_ETH_TX_DESC_USAGE( ulChannel, uxDescriptorsUsed ) \
    do {                                                                    \
        ( void ) ( ulChannel );                                             \
        ( void ) ( uxDescriptorsUsed );                                     \
    } while( 0 )
#endif

#ifndef iptraceSTM32_ETH_FATAL_ERROR
    #define iptraceSTM32_ETH_FATAL_ERROR( ulHalErrorCode, ulDmaErrorCode, ulMacErrorCode ) \
    do {                                                                                       \
        ( void ) ( ulHalErrorCode );                                                           \
        ( void ) ( ulDmaErrorCode );                                                           \
        ( void ) ( ulMacErrorCode );                                                           \
    } while( 0 )
#endif

/* DMA descriptor sections must always be non-cacheable. Packet buffers may
 * instead use explicit cache maintenance by defining niEMAC_USE_MPU as
 * ipconfigDISABLE in the consuming project. */
#ifndef niEMAC_USE_MPU
    #define niEMAC_USE_MPU    ipconfigENABLE
#endif

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

#if ipconfigIS_DISABLED( configUSE_COUNTING_SEMAPHORES )
    #error "Counting Semaphores must be enabled for NetworkInterface"
#endif

#if ipconfigIS_DISABLED( configUSE_MUTEXES )
    #error "Mutexes must be enabled for NetworkInterface"
#endif

#if ipconfigIS_DISABLED( ipconfigZERO_COPY_TX_DRIVER )
    #error "ipconfigZERO_COPY_TX_DRIVER must be enabled for NetworkInterface"
#endif

#if ipconfigIS_DISABLED( ipconfigZERO_COPY_RX_DRIVER )
    #error "ipconfigZERO_COPY_RX_DRIVER must be enabled for NetworkInterface"
#endif

#if ( ( ipconfigETHERNET_AN_ENABLE != ipconfigENABLE ) && ( ipconfigETHERNET_AN_ENABLE != ipconfigDISABLE ) )
    #error "ipconfigETHERNET_AN_ENABLE must be ipconfigENABLE or ipconfigDISABLE"
#endif

#if ( ( ipconfigETHERNET_USE_100MB != ipconfigENABLE ) && ( ipconfigETHERNET_USE_100MB != ipconfigDISABLE ) )
    #error "ipconfigETHERNET_USE_100MB must be ipconfigENABLE or ipconfigDISABLE"
#endif

#if ( ( ipconfigETHERNET_USE_FULL_DUPLEX != ipconfigENABLE ) && ( ipconfigETHERNET_USE_FULL_DUPLEX != ipconfigDISABLE ) )
    #error "ipconfigETHERNET_USE_FULL_DUPLEX must be ipconfigENABLE or ipconfigDISABLE"
#endif

#if ( ( ipconfigETHERNET_AUTO_CROSS_ENABLE != ipconfigENABLE ) && ( ipconfigETHERNET_AUTO_CROSS_ENABLE != ipconfigDISABLE ) )
    #error "ipconfigETHERNET_AUTO_CROSS_ENABLE must be ipconfigENABLE or ipconfigDISABLE"
#endif

#if ( ( ipconfigETHERNET_CROSSED_LINK != ipconfigENABLE ) && ( ipconfigETHERNET_CROSSED_LINK != ipconfigDISABLE ) )
    #error "ipconfigETHERNET_CROSSED_LINK must be ipconfigENABLE or ipconfigDISABLE"
#endif

#if ( ( ipconfigUSE_RMII != ipconfigENABLE ) && ( ipconfigUSE_RMII != ipconfigDISABLE ) )
    #error "ipconfigUSE_RMII must be ipconfigENABLE or ipconfigDISABLE"
#endif

#if ( ( ipconfigUSE_RGMII != ipconfigENABLE ) && ( ipconfigUSE_RGMII != ipconfigDISABLE ) )
    #error "ipconfigUSE_RGMII must be ipconfigENABLE or ipconfigDISABLE"
#endif

#if ipconfigIS_ENABLED( ipconfigUSE_RMII ) && ipconfigIS_ENABLED( ipconfigUSE_RGMII )
    #error "Select only one of RMII or RGMII"
#endif

#if !defined( niEMAC_STM32NX ) && ipconfigIS_ENABLED( ipconfigUSE_RGMII )
    #error "RGMII is supported only by the STM32N6 Ethernet HAL"
#endif

#if ( ( niEMAC_USE_MPU != ipconfigENABLE ) && ( niEMAC_USE_MPU != ipconfigDISABLE ) )
    #error "niEMAC_USE_MPU must be ipconfigENABLE or ipconfigDISABLE"
#endif

#if ( ipconfigNETWORK_MTU < ETH_MIN_PAYLOAD ) || ( ipconfigNETWORK_MTU > ETH_MAX_PAYLOAD )
    #error "Unsupported ipconfigNETWORK_MTU size for NetworkInterface"
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
        #warning "Consider enabling ipconfigUSE_LINKED_RX_MESSAGES for NetworkInterface"
    #endif

#endif /* if ipconfigIS_DISABLED( ipconfigPORT_SUPPRESS_WARNING ) */

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                            Macros & Definitions                           */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#if ( defined( __MPU_PRESENT ) && ( __MPU_PRESENT == 1U ) )
    #define niEMAC_MPU
    #define niEMAC_MPU_ENABLED    ( _FLD2VAL( MPU_CTRL_ENABLE, MPU->CTRL ) != 0 )
#endif

#if ( defined( __DCACHE_PRESENT ) && ( __DCACHE_PRESENT == 1U ) )
    #define niEMAC_CACHEABLE
    #define niEMAC_CACHE_ENABLED                 ( _FLD2VAL( SCB_CCR_DC, SCB->CCR ) != 0 )
    #define niEMAC_CACHE_MAINTENANCE             ( ipconfigIS_DISABLED( niEMAC_USE_MPU ) && niEMAC_CACHE_ENABLED )
    #ifdef __SCB_DCACHE_LINE_SIZE
        #define niEMAC_DATA_ALIGNMENT            __SCB_DCACHE_LINE_SIZE
    #else
        #define niEMAC_DATA_ALIGNMENT            32U
    #endif
#else
    #define niEMAC_DATA_ALIGNMENT                portBYTE_ALIGNMENT
#endif

#define niEMAC_DATA_ALIGNMENT_MASK               ( niEMAC_DATA_ALIGNMENT - 1U )
#define niEMAC_BUF_ALIGNMENT                     32U
#define niEMAC_BUF_ALIGNMENT_MASK                ( niEMAC_BUF_ALIGNMENT - 1U )

#define niEMAC_DATA_BUFFER_SIZE                  ( ( ipTOTAL_ETHERNET_FRAME_SIZE + niEMAC_DATA_ALIGNMENT_MASK ) & ~niEMAC_DATA_ALIGNMENT_MASK )
#define niEMAC_TOTAL_BUFFER_SIZE                 ( ( ( niEMAC_DATA_BUFFER_SIZE + ipBUFFER_PADDING ) + niEMAC_BUF_ALIGNMENT_MASK ) & ~niEMAC_BUF_ALIGNMENT_MASK )

#define niEMAC_DMA_RX_BUFFER_UNAVAILABLE_FLAG    ETH_DMA_RX_BUFFER_UNAVAILABLE_FLAG

#if defined( niEMAC_STM32FX )

    #define niEMAC_DMA_TX_BUFFER_UNAVAILABLE_FLAG    ETH_DMASR_TBUS
    #define niEMAC_DMA_ERROR_MASK                    HAL_ETH_ERROR_DMA
    #define niEMAC_MAC_ADDRESS_ENABLE_FLAG           ETH_MACA1HR_AE

/* F1, F2, F4 and F7 do not provide the common filter aliases. */
    #undef ETH_CTRLPACKETS_BLOCK_ALL
    #define ETH_CTRLPACKETS_BLOCK_ALL    ETH_MACFFR_PCF_BlockAll

    #undef ETH_IP_HEADER_IPV4
    #define ETH_IP_HEADER_IPV4           ETH_DMAPTPRXDESC_IPV4PR

    #undef ETH_IP_HEADER_IPV6
    #define ETH_IP_HEADER_IPV6           ETH_DMAPTPRXDESC_IPV6PR

    #undef ETH_IP_PAYLOAD_UNKNOWN
    #define ETH_IP_PAYLOAD_UNKNOWN       0x0U

    #undef ETH_IP_PAYLOAD_UDP
    #define ETH_IP_PAYLOAD_UDP           ETH_DMAPTPRXDESC_IPPT_UDP

    #undef ETH_IP_PAYLOAD_TCP
    #define ETH_IP_PAYLOAD_TCP           ETH_DMAPTPRXDESC_IPPT_TCP

    #undef ETH_IP_PAYLOAD_ICMPN
    #define ETH_IP_PAYLOAD_ICMPN         ETH_DMAPTPRXDESC_IPPT_ICMP

#elif defined( niEMAC_STM32HX )

    #define niEMAC_DMA_TX_BUFFER_UNAVAILABLE_FLAG    ETH_DMACSR_TBU
    #define niEMAC_DMA_ERROR_MASK                    HAL_ETH_ERROR_DMA
    #define niEMAC_MAC_ADDRESS_ENABLE_FLAG           ETH_MACA1HR_AE

    #undef ETH_IP_PAYLOAD_IGMP
    #define ETH_IP_PAYLOAD_IGMP                      0x4U

#elif defined( niEMAC_STM32NX )

    #define niEMAC_DMA_TX_BUFFER_UNAVAILABLE_FLAG    ETH_DMACxSR_TBU
    #define niEMAC_DMA_ERROR_MASK                    ( HAL_ETH_ERROR_DMA_CH0 | HAL_ETH_ERROR_DMA_CH1 )
    #define niEMAC_MAC_ADDRESS_ENABLE_FLAG           ETH_MACAxHR_AE

    #undef ETH_IP_PAYLOAD_IGMP
    #define ETH_IP_PAYLOAD_IGMP                      0x4U

#endif /* family-specific compatibility definitions */

#define ETH_IP_PAYLOAD_MASK           0x7U

/* IEEE 802.3 CRC32 polynomial - 0x04C11DB7 */
#define niEMAC_CRC_POLY               0x04C11DB7
#define niEMAC_MAC_IS_MULTICAST( MAC )    ( ( MAC[ 0 ] & 1U ) != 0 )
#define niEMAC_MAC_IS_UNICAST( MAC )      ( ( MAC[ 0 ] & 1U ) == 0 )
#define niEMAC_ADDRESS_HASH_BITS      64U
#define niEMAC_MAC_DEST_MATCH_COUNT   3U

#if defined( niEMAC_STM32FX )
    /* F-series HAL expects [ high, low ]; newer HALs expect [ low, high ]. */
    #define niEMAC_HASH_TABLE_LOW_WORD_INDEX     1U
    #define niEMAC_HASH_TABLE_HIGH_WORD_INDEX    0U
#else
    #define niEMAC_HASH_TABLE_LOW_WORD_INDEX     0U
    #define niEMAC_HASH_TABLE_HIGH_WORD_INDEX    1U
#endif

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                               typedefs                                    */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

/* Interrupt events to process: reception, transmission and error handling. */
typedef enum
{
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
    eMacEthInit,     /* Must initialise ETH. */
    eMacPhyInit,     /* Must initialise PHY. */
    eMacPhyStart,    /* Must start PHY. */
    eMacTaskStart,   /* Must start deferred interrupt handler task. */
    eMacEthStart,    /* Must start ETH. */
    eMacInitComplete /* Initialisation was successful. */
} eMAC_INIT_STATUS_TYPE;

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                      Static Function Declarations                         */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

/* PHY Management */
static BaseType_t prvPhyReadReg( BaseType_t xAddress,
                                 BaseType_t xRegister,
                                 uint32_t * pulValue );
static BaseType_t prvPhyWriteReg( BaseType_t xAddress,
                                  BaseType_t xRegister,
                                  uint32_t ulValue );

static void prvForceRefreshPhyLinkStatus( EthernetPhy_t * pxPhyObject );
static BaseType_t prvPhyInit( EthernetPhy_t * pxPhyObject );
static BaseType_t prvPhyStart( ETH_HandleTypeDef * pxEthHandle,
                               EthernetPhy_t * pxPhyObject );

/* Network Interface Access Hooks */
static BaseType_t prvGetPhyLinkStatus( NetworkInterface_t * pxInterface );
static BaseType_t prvNetworkInterfaceInitialise( NetworkInterface_t * pxInterface );
static BaseType_t prvNetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                             NetworkBufferDescriptor_t * const pxDescriptor,
                                             BaseType_t xReleaseAfterSend );
static void prvAddAllowedMACAddress( NetworkInterface_t * pxInterface,
                                     const uint8_t * pucMacAddress );
static void prvRemoveAllowedMACAddress( NetworkInterface_t * pxInterface,
                                        const uint8_t * pucMacAddress );

/* EMAC Task */
static BaseType_t prvNetworkInterfaceInput( ETH_HandleTypeDef * pxEthHandle,
                                            NetworkInterface_t * pxInterface );
static __NO_RETURN portTASK_FUNCTION_PROTO( prvEMACHandlerTask,
                                            pvParameters );
static BaseType_t prvEMACTaskStart( NetworkInterface_t * pxInterface );

/* EMAC Recovery */
static void prvReportFatalError( ETH_HandleTypeDef * pxEthHandle,
                                 uint32_t ulMacErrorCode );
static BaseType_t prvRecoverFromCriticalError( ETH_HandleTypeDef * pxEthHandle,
                                               EthernetPhy_t * pxPhyObject );

/* EMAC Init */
static BaseType_t prvApplyMACDMAConfig( ETH_HandleTypeDef * pxEthHandle,
                                        const EthernetPhy_t * pxPhyObject );
static BaseType_t prvMacUpdateConfig( ETH_HandleTypeDef * pxEthHandle,
                                      EthernetPhy_t * pxPhyObject );
static BaseType_t prvEthConfigInit( ETH_HandleTypeDef * pxEthHandle,
                                    NetworkInterface_t * pxInterface );

/* MAC and Packet Filtering */
static BaseType_t prvConfigureMACAddressFilter( ETH_HandleTypeDef * pxEthHandle );
static BaseType_t prvInitMacAddresses( ETH_HandleTypeDef * pxEthHandle,
                                      NetworkInterface_t * pxInterface );
static BaseType_t prvRestoreMACAddressFilters( ETH_HandleTypeDef * pxEthHandle );
#ifdef niEMAC_STM32HNX
    static void prvInitPacketFilter( ETH_HandleTypeDef * pxEthHandle );
#endif
static uint32_t prvCalcCrc32( const uint8_t * const pucMACAddr );
static uint8_t prvGetMacHashIndex( const uint8_t * const pucMACAddr );
static void prvHAL_ETH_SetDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                            uint8_t ucIndex,
                                            const uint8_t * const pucMACAddr );
static void prvHAL_ETH_ClearDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                              uint8_t ucIndex );
static BaseType_t prvAddDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                          const uint8_t * const pucMACAddr );
static BaseType_t prvRemoveDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                             const uint8_t * const pucMACAddr );
static BaseType_t prvSetNewDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                             uint8_t ucHashIndex,
                                             const uint8_t * const pucMACAddr );
static void prvAddDestMACAddrHash( ETH_HandleTypeDef * pxEthHandle,
                                   uint8_t ucHashIndex );
static void prvRemoveDestMACAddrHash( ETH_HandleTypeDef * pxEthHandle,
                                      const uint8_t * const pucMACAddr );
static void prvResetMACAddressFilters( ETH_HandleTypeDef * pxEthHandle );

/* EMAC Helpers */
static void prvReleaseTxPacket( ETH_HandleTypeDef * pxEthHandle );
static void prvReleaseNetworkBufferDescriptor( NetworkBufferDescriptor_t * const pxDescriptor );
static void prvDiscardRxFrame( NetworkBufferDescriptor_t ** ppxStartDescriptor,
                               NetworkBufferDescriptor_t ** ppxEndDescriptor,
                               NetworkBufferDescriptor_t * pxCurrentDescriptor );
static void prvSendRxEvent( NetworkBufferDescriptor_t * const pxDescriptor );
static BaseType_t prvAcceptPacket( ETH_HandleTypeDef * pxEthHandle,
                                   NetworkInterface_t * pxInterface,
                                   NetworkBufferDescriptor_t * pxDescriptor );
static void prvNotifyEMACTaskFromISR( eMAC_IF_EVENT eEvents );

/* Cache Maintenance Helpers */
#ifdef niEMAC_CACHEABLE
    static void prvValidateCacheLineSize( void );
    static uintptr_t prvGetCacheAlignedRange( const void * pvAddress,
                                              size_t uxLength,
                                              size_t * puxAlignedLength );
    static void prvCacheCleanByAddr( const void * pvAddress,
                                     size_t uxLength );
    static void prvCacheCleanInvalidateByAddr( const void * pvAddress,
                                               size_t uxLength );
    static void prvCacheInvalidateByAddr( const void * pvAddress,
                                          size_t uxLength );
#endif

/* Network Interface Definition */
NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                      NetworkInterface_t * pxInterface );

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                      Static Variable Declarations                         */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

/* The HAL, PHY, task, and filter state below is shared by one Ethernet
 * peripheral instance. */
static ETH_HandleTypeDef xEthHandle;

static EthernetPhy_t xPhyObject;

static TaskHandle_t xEMACTaskHandle = NULL;
static SemaphoreHandle_t xTxMutex = NULL, xTxDescSem = NULL;

static volatile BaseType_t xSwitchRequired = pdFALSE;
static volatile BaseType_t xDropCurrentRxFrame = pdFALSE;
static volatile uint32_t ulPendingFatalHalErrorCode = 0U;
static volatile uint32_t ulPendingFatalDmaErrorCode = 0U;
static volatile uint32_t ulPendingMacErrorCode = 0U;

static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMacEthInit;

/* Destination MAC perfect matching */
static uint8_t ucDestMatchCounters[ niEMAC_MAC_DEST_MATCH_COUNT ] = { 0U };
static uint8_t ucDestMatchAddresses[ niEMAC_MAC_DEST_MATCH_COUNT ][ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0U };
/* Destination MAC hash matching */
static uint32_t ulHashTable[ niEMAC_ADDRESS_HASH_BITS / 32 ];
static uint8_t ucAddrHashCounters[ niEMAC_ADDRESS_HASH_BITS ] = { 0U };

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                         Cache Maintenance Helpers                         */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#ifdef niEMAC_CACHEABLE

    static void prvValidateCacheLineSize( void )
    {
        const uint32_t ulPreviousCacheSelection = SCB->CSSELR;
        uint32_t ulCacheLineSize;

        SCB->CSSELR = 0U; /* Select the level-one data or unified cache. */
        __DSB();
        ulCacheLineSize = 1UL << ( _FLD2VAL( SCB_CCSIDR_LINESIZE, SCB->CCSIDR ) + 4U );
        SCB->CSSELR = ulPreviousCacheSelection;
        __DSB();

        if( ulCacheLineSize != ( uint32_t ) niEMAC_DATA_ALIGNMENT )
        {
            configASSERT( pdFALSE );
        }
    }

/*---------------------------------------------------------------------------*/

    static uintptr_t prvGetCacheAlignedRange( const void * pvAddress,
                                              size_t uxLength,
                                              size_t * puxAlignedLength )
    {
        /* Retain explicit alignment for application-supplied CMSIS versions
         * whose cache maintenance functions require an aligned address. */
        const uintptr_t uxAddress = ( uintptr_t ) pvAddress;
        const uintptr_t uxLineStart = uxAddress & ~( ( uintptr_t ) niEMAC_DATA_ALIGNMENT_MASK );
        const uintptr_t uxLineEnd = ( uxAddress + uxLength + niEMAC_DATA_ALIGNMENT_MASK ) & ~( ( uintptr_t ) niEMAC_DATA_ALIGNMENT_MASK );

        *puxAlignedLength = uxLineEnd - uxLineStart;

        return uxLineStart;
    }

/*---------------------------------------------------------------------------*/

    static void prvCacheCleanByAddr( const void * pvAddress,
                                     size_t uxLength )
    {
        if( ( pvAddress != NULL ) && ( uxLength > 0U ) )
        {
            size_t uxAlignedLength;
            const uintptr_t uxLineStart = prvGetCacheAlignedRange( pvAddress, uxLength, &uxAlignedLength );
            SCB_CleanDCache_by_Addr( ( uint32_t * ) uxLineStart, ( int32_t ) uxAlignedLength );
        }
    }

/*---------------------------------------------------------------------------*/

    static void prvCacheCleanInvalidateByAddr( const void * pvAddress,
                                               size_t uxLength )
    {
        if( ( pvAddress != NULL ) && ( uxLength > 0U ) )
        {
            size_t uxAlignedLength;
            const uintptr_t uxLineStart = prvGetCacheAlignedRange( pvAddress, uxLength, &uxAlignedLength );
            SCB_CleanInvalidateDCache_by_Addr( ( uint32_t * ) uxLineStart, ( int32_t ) uxAlignedLength );
        }
    }

/*---------------------------------------------------------------------------*/

    static void prvCacheInvalidateByAddr( const void * pvAddress,
                                          size_t uxLength )
    {
        if( ( pvAddress != NULL ) && ( uxLength > 0U ) )
        {
            size_t uxAlignedLength;
            const uintptr_t uxLineStart = prvGetCacheAlignedRange( pvAddress, uxLength, &uxAlignedLength );
            SCB_InvalidateDCache_by_Addr( ( uint32_t * ) uxLineStart, ( int32_t ) uxAlignedLength );
        }
    }

#endif /* ifdef niEMAC_CACHEABLE */

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              PHY Management                              */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static BaseType_t prvPhyReadReg( BaseType_t xAddress,
                                 BaseType_t xRegister,
                                 uint32_t * pulValue )
{
    BaseType_t xResult = 0;

    if( HAL_ETH_ReadPHYRegister( &xEthHandle, ( uint32_t ) xAddress, ( uint32_t ) xRegister, pulValue ) != HAL_OK )
    {
        xResult = -1;
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvPhyWriteReg( BaseType_t xAddress,
                                  BaseType_t xRegister,
                                  uint32_t ulValue )
{
    BaseType_t xResult = 0;

    if( HAL_ETH_WritePHYRegister( &xEthHandle, ( uint32_t ) xAddress, ( uint32_t ) xRegister, ulValue ) != HAL_OK )
    {
        xResult = -1;
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static void prvForceRefreshPhyLinkStatus( EthernetPhy_t * pxPhyObject )
{
    vTaskSetTimeOutState( &( pxPhyObject->xLinkStatusTimer ) );
    pxPhyObject->xLinkStatusRemaining = 0U;
    ( void ) xPhyCheckLinkStatus( pxPhyObject, pdFALSE );
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvPhyInit( EthernetPhy_t * pxPhyObject )
{
    BaseType_t xResult = pdFAIL;

    vPhyInitialise( pxPhyObject, ( xApplicationPhyReadHook_t ) prvPhyReadReg, ( xApplicationPhyWriteHook_t ) prvPhyWriteReg );

    #if defined( niEMAC_STM32NX ) && ipconfigIS_ENABLED( ipconfigUSE_RGMII )
        vPhySetMaxSpeed( pxPhyObject, PHY_SPEED_1000 );
    #endif

    if( xPhyDiscover( pxPhyObject ) != 0 )
    {
        xResult = pdPASS;
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvPhyStart( ETH_HandleTypeDef * pxEthHandle,
                               EthernetPhy_t * pxPhyObject )
{
    BaseType_t xResult = pdFALSE;

    if( xPhyIsLinkUp( pxPhyObject ) == pdFALSE )
    {
        const PhyProperties_t xPhyProperties =
        {
            #if ipconfigIS_ENABLED( ipconfigETHERNET_AN_ENABLE )
                .ucSpeed  = PHY_SPEED_AUTO,
                .ucDuplex = PHY_DUPLEX_AUTO,
            #else
                .ucSpeed  = ipconfigIS_ENABLED( ipconfigETHERNET_USE_100MB ) ? PHY_SPEED_100 : PHY_SPEED_10,
                .ucDuplex = ipconfigIS_ENABLED( ipconfigETHERNET_USE_FULL_DUPLEX ) ? PHY_DUPLEX_FULL : PHY_DUPLEX_HALF,
            #endif

            #if ipconfigIS_ENABLED( ipconfigETHERNET_AUTO_CROSS_ENABLE )
                .ucMDI_X  = PHY_MDIX_AUTO,
            #elif ipconfigIS_ENABLED( ipconfigETHERNET_CROSSED_LINK )
                .ucMDI_X  = PHY_MDIX_CROSSED,
            #else
                .ucMDI_X  = PHY_MDIX_DIRECT,
            #endif
        };

        #if ipconfigIS_DISABLED( ipconfigETHERNET_AN_ENABLE )
            pxPhyObject->xPhyPreferences.ucSpeed = xPhyProperties.ucSpeed;
            pxPhyObject->xPhyPreferences.ucDuplex = xPhyProperties.ucDuplex;
            pxPhyObject->xPhyProperties = xPhyProperties;
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
/*                      Network Interface Access Hooks                       */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static BaseType_t prvGetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    ( void ) pxInterface;

    return xPhyIsLinkUp( &xPhyObject );
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

            if( prvPhyInit( pxPhyObject ) == pdFALSE )
            {
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInitialise: eMacPhyInit failed\n" ) );
                break;
            }

            xMacInitStatus = eMacPhyStart;
        /* fallthrough */

        case eMacPhyStart:

            if( prvPhyStart( pxEthHandle, pxPhyObject ) == pdFALSE )
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

            prvForceRefreshPhyLinkStatus( pxPhyObject );

            if( xPhyIsLinkUp( pxPhyObject ) != pdTRUE )
            {
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInitialise: eMacInitComplete failed\n" ) );
                break;
            }

            xInitResult = pdPASS;
    }

    return xInitResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                             NetworkBufferDescriptor_t * const pxDescriptor,
                                             BaseType_t xReleaseAfterSend )
{
    BaseType_t xResult = pdFAIL;
    ( void ) pxInterface;

    /* Zero-Copy Only */
    configASSERT( xReleaseAfterSend == pdTRUE );

    do
    {
        ETH_HandleTypeDef * pxEthHandle = &xEthHandle;

        if( ( pxDescriptor == NULL ) || ( pxDescriptor->pucEthernetBuffer == NULL ) ||
            ( pxDescriptor->xDataLength < sizeof( EthernetHeader_t ) ) ||
            ( pxDescriptor->xDataLength > niEMAC_DATA_BUFFER_SIZE ) )
        {
            /* Each FreeRTOS+TCP packet must fit in one contiguous network
             * buffer; scatter-gather transmission is unsupported. */
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Invalid Descriptor\n" ) );
            break;
        }

        if( xPhyIsLinkUp( &xPhyObject ) == pdFALSE )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Link Down\n" ) );
            break;
        }

        if( ( xMacInitStatus != eMacInitComplete ) || ( HAL_ETH_GetState( pxEthHandle ) != HAL_ETH_STATE_STARTED ) )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Interface Not Started\n" ) );
            break;
        }

        ETH_TxPacketConfigTypeDef xTxConfig =
        {
            .CRCPadCtrl = ETH_CRC_PAD_INSERT,
            .Attributes = ETH_TX_PACKETS_FEATURES_CRCPAD,
        };

        #if defined( niEMAC_STM32NX )
            xTxConfig.TxDMACh = niEMAC_DMA_CHANNEL_INDEX;
        #endif

        #if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
            xTxConfig.ChecksumCtrl = ETH_CHECKSUM_IPHDR_PAYLOAD_INSERT_PHDR_CALC;
            xTxConfig.Attributes |= ETH_TX_PACKETS_FEATURES_CSUM;
        #else
            xTxConfig.ChecksumCtrl = ETH_CHECKSUM_DISABLE;
        #endif

        const EthernetHeader_t * const pxEthHeader = ( const EthernetHeader_t * const ) pxDescriptor->pucEthernetBuffer;

        if( pxEthHeader->usFrameType == ipIPv4_FRAME_TYPE )
        {
            #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
                if( pxDescriptor->xDataLength < sizeof( IPPacket_t ) )
                {
                    FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Invalid IPv4 packet\n" ) );
                    break;
                }

                const IPPacket_t * const pxIPPacket = ( const IPPacket_t * const ) pxDescriptor->pucEthernetBuffer;

                if( pxIPPacket->xIPHeader.ucProtocol == ipPROTOCOL_ICMP )
                {
                    #if ipconfigIS_ENABLED( ipconfigREPLY_TO_INCOMING_PINGS ) || ipconfigIS_ENABLED( ipconfigSUPPORT_OUTGOING_PINGS )
                        if( pxDescriptor->xDataLength < sizeof( ICMPPacket_t ) )
                        {
                            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Invalid ICMP packet\n" ) );
                            break;
                        }

                        ICMPPacket_t * const pxICMPPacket = ( ICMPPacket_t * const ) pxDescriptor->pucEthernetBuffer;
                        #if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
                            pxICMPPacket->xICMPHeader.usChecksum = 0U;
                        #endif
                        ( void ) pxICMPPacket;
                    #else
                        FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Unsupported ICMP\n" ) );
                    #endif
                }
            #else /* if ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) */
                FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Unsupported IPv4\n" ) );
            #endif /* if ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) */
        }

        ETH_BufferTypeDef xTxBuffer =
        {
            .buffer = pxDescriptor->pucEthernetBuffer,
            .len    = pxDescriptor->xDataLength,
            .next   = NULL
        };

        xTxConfig.pData = pxDescriptor;
        xTxConfig.TxBuffer = &xTxBuffer;
        xTxConfig.Length = xTxBuffer.len;

        if( xSemaphoreTake( xTxDescSem, pdMS_TO_TICKS( niDESCRIPTOR_WAIT_TIME_MS ) ) == pdFALSE )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: No Descriptors Available\n" ) );
            break;
        }

        if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( niEMAC_TX_MAX_BLOCK_TIME_MS ) ) == pdFALSE )
        {
            FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: Process Busy\n" ) );
            ( void ) xSemaphoreGive( xTxDescSem );
            break;
        }

        #ifdef niEMAC_CACHEABLE
            if( niEMAC_CACHE_MAINTENANCE != 0 )
            {
                prvCacheCleanByAddr( xTxBuffer.buffer, xTxBuffer.len );
            }
        #endif

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
            /* Should be impossible if semaphores are correctly implemented */
            configASSERT( ( HAL_ETH_GetError( pxEthHandle ) & HAL_ETH_ERROR_BUSY ) == 0 );
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

static void prvAddAllowedMACAddress( NetworkInterface_t * pxInterface,
                                     const uint8_t * pucMacAddress )
{
    ETH_HandleTypeDef * pxEthHandle = &xEthHandle;
    ( void ) pxInterface;

    if( pucMacAddress == NULL )
    {
        return;
    }

    BaseType_t xMutexTaken = pdFALSE;

    /* The mutex is created after initial MAC setup. Once it exists, use it to
     * serialize runtime filter changes with fatal-error recovery. */
    if( xTxMutex != NULL )
    {
        xMutexTaken = xSemaphoreTake( xTxMutex, portMAX_DELAY );

        if( xMutexTaken == pdFALSE )
        {
            FreeRTOS_debug_printf( ( "prvAddAllowedMACAddress: Failed to take mutex\n" ) );
            return;
        }
    }

    /* Prefer exact destination matching while hardware slots are available.
     * Hash matching handles additional addresses without accepting the broad
     * address ranges introduced by mask-byte filtering. */
    BaseType_t xResult = prvAddDestMACAddrMatch( pxEthHandle->Instance, pucMacAddress );

    if( xResult == pdFALSE )
    {
        const uint8_t ucHashIndex = prvGetMacHashIndex( pucMacAddress );

        xResult = prvSetNewDestMACAddrMatch( pxEthHandle->Instance, ucHashIndex, pucMacAddress );

        if( xResult == pdFALSE )
        {
            prvAddDestMACAddrHash( pxEthHandle, ucHashIndex );
        }
    }

    if( xMutexTaken != pdFALSE )
    {
        ( void ) xSemaphoreGive( xTxMutex );
    }
}

/*---------------------------------------------------------------------------*/

static void prvRemoveAllowedMACAddress( NetworkInterface_t * pxInterface,
                                        const uint8_t * pucMacAddress )
{
    ETH_HandleTypeDef * pxEthHandle = &xEthHandle;
    ( void ) pxInterface;

    if( pucMacAddress == NULL )
    {
        return;
    }

    BaseType_t xMutexTaken = pdFALSE;

    if( xTxMutex != NULL )
    {
        xMutexTaken = xSemaphoreTake( xTxMutex, portMAX_DELAY );

        if( xMutexTaken == pdFALSE )
        {
            FreeRTOS_debug_printf( ( "prvRemoveAllowedMACAddress: Failed to take mutex\n" ) );
            return;
        }
    }

    const BaseType_t xResult = prvRemoveDestMACAddrMatch( pxEthHandle->Instance, pucMacAddress );

    if( xResult == pdFALSE )
    {
        prvRemoveDestMACAddrHash( pxEthHandle, pucMacAddress );
    }

    if( xMutexTaken != pdFALSE )
    {
        ( void ) xSemaphoreGive( xTxMutex );
    }
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              EMAC Task                                    */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceInput( ETH_HandleTypeDef * pxEthHandle,
                                            NetworkInterface_t * pxInterface )
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
        for( uint32_t ulChannel = 0; ulChannel < niEMAC_RX_CHANNEL_COUNT; ulChannel++ )
        {
            #if defined( niEMAC_STM32NX )
                pxEthHandle->RxOpCH = ulChannel;
            #endif

            for( ; ; )
            {
                xDropCurrentRxFrame = pdFALSE;
                pxCurDescriptor = NULL;

                if( HAL_ETH_ReadData( pxEthHandle, ( void ** ) &pxCurDescriptor ) != HAL_OK )
                {
                    break;
                }

                ++uxCount;

                if( xDropCurrentRxFrame != pdFALSE )
                {
                    xDropCurrentRxFrame = pdFALSE;
                    configASSERT( pxCurDescriptor == NULL );
                    continue;
                }

                if( pxCurDescriptor == NULL )
                {
                    /* Buffer was dropped, ignore packet */
                    continue;
                }

                if( prvAcceptPacket( pxEthHandle, pxInterface, pxCurDescriptor ) == pdFALSE )
                {
                    prvReleaseNetworkBufferDescriptor( pxCurDescriptor );
                    continue;
                }

                #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
                    pxCurDescriptor->pxNextBuffer = NULL;

                    if( pxStartDescriptor == NULL )
                    {
                        pxStartDescriptor = pxCurDescriptor;
                    }
                    else if( pxEndDescriptor != NULL )
                    {
                        pxEndDescriptor->pxNextBuffer = pxCurDescriptor;
                    }

                    pxEndDescriptor = pxCurDescriptor;
                #else /* if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) */
                    prvSendRxEvent( pxCurDescriptor );
                #endif /* if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) */
            }
        }

        #if defined( niEMAC_STM32NX )
            pxEthHandle->RxOpCH = niEMAC_DMA_CHANNEL_INDEX;
        #endif
    }

    if( uxCount > 0 )
    {
        #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
            if( pxStartDescriptor != NULL )
            {
                prvSendRxEvent( pxStartDescriptor );
            }
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
    BaseType_t xRecoveryRequired = pdFALSE;

    iptraceEMAC_TASK_STARTING();

    for( ; ; )
    {
        BaseType_t xResult = pdFALSE;
        uint32_t ulISREvents = 0U;
        uint32_t ulMacErrorCode = 0U;

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

            if( ( ulISREvents & eMacEventErrDma ) != 0 )
            {
                const uint32_t ulDmaError = HAL_ETH_GetDMAError( pxEthHandle );

                if( ( ( ulDmaError & niEMAC_DMA_TX_BUFFER_UNAVAILABLE_FLAG ) != 0U ) &&
                    ( ( ulISREvents & eMacEventErrTx ) == 0U ) )
                {
                    prvReleaseTxPacket( pxEthHandle );
                }

                if( ( ( ulDmaError & niEMAC_DMA_RX_BUFFER_UNAVAILABLE_FLAG ) != 0U ) &&
                    ( ( ulISREvents & eMacEventErrRx ) == 0U ) )
                {
                    xResult = prvNetworkInterfaceInput( pxEthHandle, pxInterface );
                }

                if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_ERROR )
                {
                    ulISREvents |= eMacEventErrEth;
                }
            }

            if( ( ulISREvents & eMacEventErrMac ) != 0 )
            {
                taskENTER_CRITICAL();
                ulMacErrorCode = ulPendingMacErrorCode;
                ulPendingMacErrorCode = 0U;
                taskEXIT_CRITICAL();

                if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_ERROR )
                {
                    ulISREvents |= eMacEventErrEth;
                }
                else if( ulMacErrorCode != 0U )
                {
                    FreeRTOS_debug_printf( ( "prvEMACHandlerTask: MAC error 0x%08lX\n",
                                             ( unsigned long ) ulMacErrorCode ) );
                }
            }

            if( ( ulISREvents & eMacEventErrEth ) != 0 )
            {
                if( ( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_ERROR ) &&
                    ( xRecoveryRequired == pdFALSE ) )
                {
                    prvReportFatalError( pxEthHandle, ulMacErrorCode );
                    xRecoveryRequired = pdTRUE;
                }
            }
        }

        if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_ERROR )
        {
            if( xRecoveryRequired == pdFALSE )
            {
                prvReportFatalError( pxEthHandle, ulMacErrorCode );
            }

            xRecoveryRequired = pdTRUE;
        }

        if( xRecoveryRequired != pdFALSE )
        {
            if( prvRecoverFromCriticalError( pxEthHandle, pxPhyObject ) != pdFALSE )
            {
                if( xPhyIsLinkUp( pxPhyObject ) == pdFALSE )
                {
                    xRecoveryRequired = pdFALSE;
                }
                else if( HAL_ETH_Start_IT( pxEthHandle ) == HAL_OK )
                {
                    xRecoveryRequired = pdFALSE;
                    xResult = prvNetworkInterfaceInput( pxEthHandle, pxInterface );
                }
                else
                {
                    FreeRTOS_debug_printf( ( "prvEMACHandlerTask: HAL_ETH_Start_IT failed after recovery\n" ) );
                }
            }
        }

        const BaseType_t xLinkStatusChanged = xPhyCheckLinkStatus( pxPhyObject, xResult );

        if( xPhyIsLinkUp( pxPhyObject ) != pdFALSE )
        {
            if( ( xRecoveryRequired == pdFALSE ) &&
                ( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_READY ) )
            {
                /* Link was down, or a previous start attempt failed. */
                if( prvMacUpdateConfig( pxEthHandle, pxPhyObject ) != pdFALSE )
                {
                    if( HAL_ETH_Start_IT( pxEthHandle ) != HAL_OK )
                    {
                        FreeRTOS_debug_printf( ( "prvEMACHandlerTask: HAL_ETH_Start_IT failed on link-up\n" ) );
                    }
                }
            }
        }
        else
        {
            BaseType_t xMACStopped = pdFALSE;

            if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_STARTED )
            {
                if( HAL_ETH_Stop_IT( pxEthHandle ) != HAL_OK )
                {
                    FreeRTOS_debug_printf( ( "prvEMACHandlerTask: HAL_ETH_Stop_IT failed on link-down\n" ) );
                }
                else
                {
                    xMACStopped = pdTRUE;
                }
            }

            if( ( xMACStopped != pdFALSE ) || ( xLinkStatusChanged != pdFALSE ) )
            {
                prvReleaseTxPacket( pxEthHandle );
            }

            if( xLinkStatusChanged != pdFALSE )
            {
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
        #if ( configQUEUE_REGISTRY_SIZE > 0 )
            vQueueAddToRegistry( xTxMutex, niEMAC_TX_MUTEX_NAME );
        #endif
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
        #endif /* if ( ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION ) ) */
        configASSERT( xTxDescSem != NULL );
        #if ( configQUEUE_REGISTRY_SIZE > 0 )
            vQueueAddToRegistry( xTxDescSem, niEMAC_TX_DESC_SEM_NAME );
        #endif
    }

    if( ( xEMACTaskHandle == NULL ) && ( xTxMutex != NULL ) && ( xTxDescSem != NULL ) )
    {
        #if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION )
            static StackType_t uxEMACTaskStack[ niEMAC_HANDLER_TASK_STACK_SIZE ];
            static StaticTask_t xEMACTaskTCB;
            xEMACTaskHandle = xTaskCreateStatic(
                prvEMACHandlerTask,
                niEMAC_HANDLER_TASK_NAME,
                niEMAC_HANDLER_TASK_STACK_SIZE,
                ( void * ) pxInterface,
                niEMAC_HANDLER_TASK_PRIORITY,
                uxEMACTaskStack,
                &xEMACTaskTCB
                );
        #else /* if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION ) */
            ( void ) xTaskCreate(
                prvEMACHandlerTask,
                niEMAC_HANDLER_TASK_NAME,
                niEMAC_HANDLER_TASK_STACK_SIZE,
                ( void * ) pxInterface,
                niEMAC_HANDLER_TASK_PRIORITY,
                &xEMACTaskHandle
                );
        #endif /* if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION ) */
    }

    if( xEMACTaskHandle != NULL )
    {
        xResult = pdTRUE;
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                               EMAC Recovery                               */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static void prvReportFatalError( ETH_HandleTypeDef * pxEthHandle,
                                 uint32_t ulMacErrorCode )
{
    uint32_t ulHalErrorCode;
    uint32_t ulDmaErrorCode;

    taskENTER_CRITICAL();
    ulHalErrorCode = ulPendingFatalHalErrorCode;
    ulDmaErrorCode = ulPendingFatalDmaErrorCode;
    ulMacErrorCode |= ulPendingMacErrorCode;
    ulPendingFatalHalErrorCode = 0U;
    ulPendingFatalDmaErrorCode = 0U;
    ulPendingMacErrorCode = 0U;
    taskEXIT_CRITICAL();

    if( ulHalErrorCode == 0U )
    {
        ulHalErrorCode = HAL_ETH_GetError( pxEthHandle );
    }

    if( ( ulDmaErrorCode == 0U ) &&
        ( ( ulHalErrorCode & niEMAC_DMA_ERROR_MASK ) != 0U ) )
    {
        ulDmaErrorCode = HAL_ETH_GetDMAError( pxEthHandle );
    }

    iptraceSTM32_ETH_FATAL_ERROR( ulHalErrorCode, ulDmaErrorCode, ulMacErrorCode );

    if( ( ulHalErrorCode | ulDmaErrorCode | ulMacErrorCode ) != 0U )
    {
        FreeRTOS_debug_printf( ( "prvReportFatalError: HAL error 0x%08lX, DMA error 0x%08lX, MAC error 0x%08lX\n",
                                 ( unsigned long ) ulHalErrorCode,
                                 ( unsigned long ) ulDmaErrorCode,
                                 ( unsigned long ) ulMacErrorCode ) );
    }
    else
    {
        FreeRTOS_debug_printf( ( "prvReportFatalError: HAL entered the error state without an error code\n" ) );
    }

    configASSERT( ( ulHalErrorCode & HAL_ETH_ERROR_PARAM ) == 0U );
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvRecoverFromCriticalError( ETH_HandleTypeDef * pxEthHandle,
                                               EthernetPhy_t * pxPhyObject )
{
    BaseType_t xResult = pdFALSE;
    NetworkBufferDescriptor_t * pxTxPackets[ ETH_TX_DESC_CNT ] = { NULL };
    NetworkBufferDescriptor_t * pxPartialRxPackets[ niEMAC_RX_CHANNEL_COUNT ] = { NULL };
    uint8_t * pucRxBuffers[ niEMAC_RX_CHANNEL_COUNT ][ ETH_RX_DESC_CNT ] = { { NULL } };

    if( ( xTxMutex == NULL ) || ( xTxDescSem == NULL ) ||
        ( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( niEMAC_TX_MAX_BLOCK_TIME_MS ) ) == pdFALSE ) )
    {
        FreeRTOS_debug_printf( ( "prvRecoverFromCriticalError: Failed to take TX mutex\n" ) );
        return pdFALSE;
    }

    xDropCurrentRxFrame = pdFALSE;

    ETH_TxDescListTypeDef * const pxTxDescList = &( niEMAC_TX_DESC_LIST( pxEthHandle, niEMAC_DMA_CHANNEL_INDEX ) );

    #if defined( niEMAC_STM32NX )
        pxEthHandle->TxOpCH = niEMAC_DMA_CHANNEL_INDEX;
    #endif
    const uint32_t ulTxBuffersInUse = HAL_ETH_GetTxBuffersNumber( pxEthHandle );

    for( UBaseType_t uxIndex = 0U; uxIndex < ( UBaseType_t ) ETH_TX_DESC_CNT; uxIndex++ )
    {
        pxTxPackets[ uxIndex ] = ( NetworkBufferDescriptor_t * ) pxTxDescList->PacketAddress[ uxIndex ];
    }

    for( uint32_t ulChannel = 0U; ulChannel < niEMAC_RX_CHANNEL_COUNT; ulChannel++ )
    {
        ETH_RxDescListTypeDef * const pxRxDescList = &( niEMAC_RX_DESC_LIST( pxEthHandle, ulChannel ) );

        pxPartialRxPackets[ ulChannel ] = ( NetworkBufferDescriptor_t * ) pxRxDescList->pRxStart;

        for( UBaseType_t uxIndex = 0U; uxIndex < ( UBaseType_t ) ETH_RX_DESC_CNT; uxIndex++ )
        {
            ETH_DMADescTypeDef * const pxRxDesc = ( ETH_DMADescTypeDef * ) ( uintptr_t ) pxRxDescList->RxDesc[ uxIndex ];

            if( pxRxDesc != NULL )
            {
                pucRxBuffers[ ulChannel ][ uxIndex ] = ( uint8_t * ) ( uintptr_t ) pxRxDesc->BackupAddr0;
            }
        }
    }

    if( HAL_ETH_Init( pxEthHandle ) != HAL_OK )
    {
        FreeRTOS_debug_printf( ( "prvRecoverFromCriticalError: HAL_ETH_Init failed\n" ) );
    }
    else
    {
        UBaseType_t uxPacketsReleased = 0U;

        #if defined( niEMAC_STM32FX )
            /* F-series HAL_ETH_Init() does not restore the MDIO clock divider. */
            HAL_ETH_SetMDIOClockRange( pxEthHandle );
        #endif

        /* HAL reinitialisation has stopped DMA and reset the descriptors, so
         * their zero-copy buffers can now be safely returned. */
        for( UBaseType_t uxIndex = 0U; uxIndex < ( UBaseType_t ) ETH_TX_DESC_CNT; uxIndex++ )
        {
            pxTxDescList->PacketAddress[ uxIndex ] = NULL;

            if( pxTxPackets[ uxIndex ] != NULL )
            {
                prvReleaseNetworkBufferDescriptor( pxTxPackets[ uxIndex ] );
                uxPacketsReleased++;
            }
        }

        if( uxPacketsReleased != ( UBaseType_t ) ulTxBuffersInUse )
        {
            FreeRTOS_debug_printf( ( "prvRecoverFromCriticalError: TX buffer bookkeeping mismatch\n" ) );
            configASSERT( uxPacketsReleased == ( UBaseType_t ) ulTxBuffersInUse );
        }

        pxTxDescList->BuffersInUse = 0U;
        pxTxDescList->releaseIndex = 0U;
        pxTxDescList->CurrentPacketAddress = NULL;

        for( uint32_t ulIndex = 0U; ulIndex < ulTxBuffersInUse; ulIndex++ )
        {
            const BaseType_t xGiveResult = xSemaphoreGive( xTxDescSem );

            configASSERT( xGiveResult == pdTRUE );

            if( xGiveResult == pdFALSE )
            {
                break;
            }
        }

        for( uint32_t ulChannel = 0U; ulChannel < niEMAC_RX_CHANNEL_COUNT; ulChannel++ )
        {
            ETH_RxDescListTypeDef * const pxRxDescList = &( niEMAC_RX_DESC_LIST( pxEthHandle, ulChannel ) );

            pxRxDescList->pRxStart = NULL;
            pxRxDescList->pRxEnd = NULL;
            pxRxDescList->RxDataLength = 0U;
            pxRxDescList->pRxLastRxDesc = 0U;

            prvReleaseNetworkBufferDescriptor( pxPartialRxPackets[ ulChannel ] );

            for( UBaseType_t uxIndex = 0U; uxIndex < ( UBaseType_t ) ETH_RX_DESC_CNT; uxIndex++ )
            {
                if( pucRxBuffers[ ulChannel ][ uxIndex ] != NULL )
                {
                    NetworkBufferDescriptor_t * const pxDescriptor = pxPacketBuffer_to_NetworkBuffer( ( const void * ) pucRxBuffers[ ulChannel ][ uxIndex ] );

                    configASSERT( pxDescriptor != NULL );

                    if( pxDescriptor != NULL )
                    {
                        prvReleaseNetworkBufferDescriptor( pxDescriptor );
                    }
                }
            }
        }

        if( prvApplyMACDMAConfig( pxEthHandle, pxPhyObject ) == pdFALSE )
        {
            FreeRTOS_debug_printf( ( "prvRecoverFromCriticalError: Failed to restore MAC/DMA configuration\n" ) );
        }
        else
        {
            #if defined( niEMAC_STM32HNX )
                prvInitPacketFilter( pxEthHandle );
            #endif

            xResult = prvRestoreMACAddressFilters( pxEthHandle );
        }
    }

    ( void ) xSemaphoreGive( xTxMutex );

    return xResult;
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                                 EMAC Init                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static BaseType_t prvApplyMACDMAConfig( ETH_HandleTypeDef * pxEthHandle,
                                        const EthernetPhy_t * pxPhyObject )
{
    ETH_MACConfigTypeDef xMACConfig = { 0 };

    if( HAL_ETH_GetMACConfig( pxEthHandle, &xMACConfig ) != HAL_OK )
    {
        FreeRTOS_debug_printf( ( "prvApplyMACDMAConfig: HAL_ETH_GetMACConfig failed\n" ) );
        return pdFALSE;
    }

    if( pxPhyObject != NULL )
    {
        xMACConfig.DuplexMode = ( pxPhyObject->xPhyProperties.ucDuplex == PHY_DUPLEX_FULL ) ? ETH_FULLDUPLEX_MODE : ETH_HALFDUPLEX_MODE;

        switch( pxPhyObject->xPhyProperties.ucSpeed )
        {
            case PHY_SPEED_10:
                xMACConfig.Speed = ETH_SPEED_10M;
                #if defined( niEMAC_STM32NX )
                    xMACConfig.PortSelect = ENABLE;
                #endif
                break;

            case PHY_SPEED_100:
                xMACConfig.Speed = ETH_SPEED_100M;
                #if defined( niEMAC_STM32NX )
                    xMACConfig.PortSelect = ENABLE;
                #endif
                break;

            #if defined( niEMAC_STM32NX )
                case PHY_SPEED_1000:
                    xMACConfig.Speed = ETH_SPEED_1000M;
                    xMACConfig.PortSelect = DISABLE;
                    break;
            #endif

            default:
                FreeRTOS_debug_printf( ( "prvApplyMACDMAConfig: unsupported PHY speed %u\n",
                                         ( unsigned int ) pxPhyObject->xPhyProperties.ucSpeed ) );
                return pdFALSE;
        }
    }

    xMACConfig.ChecksumOffload = ( FunctionalState ) ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM );
    xMACConfig.CRCStripTypePacket = DISABLE;
    xMACConfig.AutomaticPadCRCStrip = ENABLE;
    xMACConfig.RetryTransmission = ENABLE;

    if( HAL_ETH_SetMACConfig( pxEthHandle, &xMACConfig ) != HAL_OK )
    {
        FreeRTOS_debug_printf( ( "prvApplyMACDMAConfig: HAL_ETH_SetMACConfig failed\n" ) );
        return pdFALSE;
    }

    ETH_DMAConfigTypeDef xDMAConfig = { 0 };

    if( HAL_ETH_GetDMAConfig( pxEthHandle, &xDMAConfig ) != HAL_OK )
    {
        FreeRTOS_debug_printf( ( "prvApplyMACDMAConfig: HAL_ETH_GetDMAConfig failed\n" ) );
        return pdFALSE;
    }

    #if defined( niEMAC_STM32FX )
        xDMAConfig.EnhancedDescriptorFormat = ( FunctionalState ) ( ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM ) || ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM ) );
    #elif defined( niEMAC_STM32HX )
        xDMAConfig.SecondPacketOperate = ENABLE;
    #elif defined( niEMAC_STM32NX )
        for( uint32_t ulChannel = 0; ulChannel < ETH_DMA_CH_CNT; ulChannel++ )
        {
            xDMAConfig.DMACh[ ulChannel ].SecondPacketOperate = ENABLE;
        }
    #endif /* if defined( niEMAC_STM32FX ) */

    if( HAL_ETH_SetDMAConfig( pxEthHandle, &xDMAConfig ) != HAL_OK )
    {
        FreeRTOS_debug_printf( ( "prvApplyMACDMAConfig: HAL_ETH_SetDMAConfig failed\n" ) );
        return pdFALSE;
    }

    return pdTRUE;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvMacUpdateConfig( ETH_HandleTypeDef * pxEthHandle,
                                      EthernetPhy_t * pxPhyObject )
{
    BaseType_t xResult = pdFALSE;
    BaseType_t xPhyResult;

    if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_STARTED )
    {
        if( HAL_ETH_Stop_IT( pxEthHandle ) != HAL_OK )
        {
            FreeRTOS_debug_printf( ( "prvMacUpdateConfig: HAL_ETH_Stop_IT failed\n" ) );
            return pdFALSE;
        }
    }

    #if ipconfigIS_ENABLED( ipconfigETHERNET_AN_ENABLE )
        xPhyResult = xPhyStartAutoNegotiation( pxPhyObject, xPhyGetMask( pxPhyObject ) );
    #else
        xPhyResult = xPhyFixedValue( pxPhyObject, xPhyGetMask( pxPhyObject ) );
    #endif

    if( ( xPhyResult == 0 ) && ( prvApplyMACDMAConfig( pxEthHandle, pxPhyObject ) != pdFALSE ) )
    {
        xResult = pdTRUE;
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvEthConfigInit( ETH_HandleTypeDef * pxEthHandle,
                                    NetworkInterface_t * pxInterface )
{
    BaseType_t xResult = pdFALSE;

    #ifdef niEMAC_CACHEABLE
        if( niEMAC_CACHE_ENABLED )
        {
            prvValidateCacheLineSize();
        }
    #endif

    pxEthHandle->Instance = niEMAC_ETH_INSTANCE;
    #if defined( niEMAC_STM32NX ) && ipconfigIS_ENABLED( ipconfigUSE_RGMII )
        pxEthHandle->Init.MediaInterface = HAL_ETH_RGMII_MODE;
    #elif ipconfigIS_ENABLED( ipconfigUSE_RMII )
        pxEthHandle->Init.MediaInterface = HAL_ETH_RMII_MODE;
    #else
        pxEthHandle->Init.MediaInterface = HAL_ETH_MII_MODE;
    #endif
    pxEthHandle->Init.RxBuffLen = niEMAC_DATA_BUFFER_SIZE;

    /* RxBuffLen includes alignment padding, so compare the unpadded frame size
     * against the Ethernet maximum. */
    configASSERT( ipTOTAL_ETHERNET_FRAME_SIZE <= ETH_MAX_PACKET_SIZE );
    configASSERT( pxEthHandle->Init.RxBuffLen >= ipTOTAL_ETHERNET_FRAME_SIZE );
    configASSERT( pxEthHandle->Init.RxBuffLen % 4U == 0 );
    #if defined( niEMAC_STM32NX )
        static ETH_DMADescTypeDef xDMADescTx[ ETH_DMA_TX_CH_CNT ][ ETH_TX_DESC_CNT ] __ALIGNED( niEMAC_DATA_ALIGNMENT ) __attribute__( ( section( niEMAC_TX_DESC_SECTION ) ) );
        static ETH_DMADescTypeDef xDMADescRx[ ETH_DMA_RX_CH_CNT ][ ETH_RX_DESC_CNT ] __ALIGNED( niEMAC_DATA_ALIGNMENT ) __attribute__( ( section( niEMAC_RX_DESC_SECTION ) ) );

        for( uint32_t ulChannel = 0; ulChannel < ETH_DMA_TX_CH_CNT; ulChannel++ )
        {
            configASSERT( ( ( uintptr_t ) xDMADescTx[ ulChannel ] & niEMAC_DATA_ALIGNMENT_MASK ) == 0U );
            pxEthHandle->Init.TxDesc[ ulChannel ] = xDMADescTx[ ulChannel ];
        }

        for( uint32_t ulChannel = 0; ulChannel < ETH_DMA_RX_CH_CNT; ulChannel++ )
        {
            configASSERT( ( ( uintptr_t ) xDMADescRx[ ulChannel ] & niEMAC_DATA_ALIGNMENT_MASK ) == 0U );
            pxEthHandle->Init.RxDesc[ ulChannel ] = xDMADescRx[ ulChannel ];
        }
    #else /* if defined( niEMAC_STM32NX ) */
        static ETH_DMADescTypeDef xDMADescTx[ ETH_TX_DESC_CNT ] __ALIGNED( niEMAC_DATA_ALIGNMENT ) __attribute__( ( section( niEMAC_TX_DESC_SECTION ) ) );
        static ETH_DMADescTypeDef xDMADescRx[ ETH_RX_DESC_CNT ] __ALIGNED( niEMAC_DATA_ALIGNMENT ) __attribute__( ( section( niEMAC_RX_DESC_SECTION ) ) );
        configASSERT( ( ( uintptr_t ) xDMADescTx & niEMAC_DATA_ALIGNMENT_MASK ) == 0U );
        configASSERT( ( ( uintptr_t ) xDMADescRx & niEMAC_DATA_ALIGNMENT_MASK ) == 0U );
        pxEthHandle->Init.TxDesc = xDMADescTx;
        pxEthHandle->Init.RxDesc = xDMADescRx;
    #endif /* if defined( niEMAC_STM32NX ) */
    ( void ) memset( &xDMADescTx, 0, sizeof( xDMADescTx ) );
    ( void ) memset( &xDMADescRx, 0, sizeof( xDMADescRx ) );

    const NetworkEndPoint_t * const pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );

    if( pxEndPoint != NULL )
    {
        pxEthHandle->Init.MACAddr = ( uint8_t * ) pxEndPoint->xMACAddress.ucBytes;

        if( HAL_ETH_Init( pxEthHandle ) == HAL_OK )
        {
            #if defined( niEMAC_STM32NX )
                /* Clocks are now enabled by HAL_ETH_MspInit(). Check the
                 * hardware capacities before starting any DMA channel; the
                 * descriptor arrays remain sized by the HAL configuration. */
                const uint32_t ulRxChannels = HAL_ETHEx_GetRxDMAChNumber( pxEthHandle );
                const uint32_t ulTxChannels = HAL_ETHEx_GetTxDMAChNumber( pxEthHandle );
                const uint32_t ulRxQueues = HAL_ETHEx_GetRxMTLQNumber( pxEthHandle );
                const uint32_t ulTxQueues = HAL_ETHEx_GetTxMTLQNumber( pxEthHandle );

                if( ( ETH_DMA_RX_CH_CNT > ulRxChannels ) ||
                    ( ETH_DMA_TX_CH_CNT > ulTxChannels ) ||
                    ( ETH_DMA_CH_CNT > ulRxChannels ) ||
                    ( ETH_DMA_CH_CNT > ulTxChannels ) ||
                    ( ETH_MTL_RX_Q_CNT > ulRxQueues ) ||
                    ( ETH_MTL_TX_Q_CNT > ulTxQueues ) )
                {
                    FreeRTOS_debug_printf( ( "prvEthConfigInit: Configured DMA channels or MTL queues exceed hardware capacity\n" ) );
                    return pdFALSE;
                }
            #endif

            #if defined( niEMAC_STM32FX )
                /* This function doesn't get called in Fxx driver */
                HAL_ETH_SetMDIOClockRange( pxEthHandle );
            #endif

            if( prvApplyMACDMAConfig( pxEthHandle, NULL ) != pdFALSE )
            {
                #if defined( niEMAC_STM32HNX )
                    prvInitPacketFilter( pxEthHandle );
                #endif

                if( prvInitMacAddresses( pxEthHandle, pxInterface ) != pdFALSE )
                {
                    xResult = pdTRUE;
                }
            }
        }
    }

    if( xResult == pdTRUE )
    {
        #ifdef niEMAC_CACHEABLE
            if( niEMAC_CACHE_ENABLED && ipconfigIS_ENABLED( niEMAC_USE_MPU ) )
            {
                #ifdef niEMAC_MPU
                    configASSERT( niEMAC_MPU_ENABLED != 0 );
                #else
                    configASSERT( pdFALSE );
                #endif
            }
        #endif

        #ifdef configPRIO_BITS
            const uint32_t ulPrioBits = configPRIO_BITS;
        #else
            const uint32_t ulPrioBits = __NVIC_PRIO_BITS;
        #endif
        const uint32_t ulPriority = NVIC_GetPriority( niEMAC_ETH_IRQ_NUMBER ) << ( 8U - ulPrioBits );

        if( ulPriority < configMAX_SYSCALL_INTERRUPT_PRIORITY )
        {
            FreeRTOS_debug_printf( ( "prvEthConfigInit: Incorrectly set Ethernet IRQ priority\n" ) );
            NVIC_SetPriority( niEMAC_ETH_IRQ_NUMBER, configMAX_SYSCALL_INTERRUPT_PRIORITY >> ( 8U - ulPrioBits ) );
        }

        if( NVIC_GetEnableIRQ( niEMAC_ETH_IRQ_NUMBER ) == 0 )
        {
            FreeRTOS_debug_printf( ( "prvEthConfigInit: Ethernet IRQ was not enabled by application\n" ) );
            HAL_NVIC_EnableIRQ( niEMAC_ETH_IRQ_NUMBER );
        }

        configASSERT( niEMAC_ETH_CLOCKS_ENABLED() );
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                         MAC and Packet Filtering                          */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static BaseType_t prvConfigureMACAddressFilter( ETH_HandleTypeDef * pxEthHandle )
{
    ETH_MACFilterConfigTypeDef xFilterConfig = { 0 };

    if( HAL_ETH_GetMACFilterConfig( pxEthHandle, &xFilterConfig ) != HAL_OK )
    {
        FreeRTOS_debug_printf( ( "prvConfigureMACAddressFilter: HAL_ETH_GetMACFilterConfig failed\n" ) );
        return pdFALSE;
    }

    xFilterConfig.ReceiveAllMode = DISABLE;
    xFilterConfig.HachOrPerfectFilter = ENABLE;
    xFilterConfig.SrcAddrFiltering = DISABLE;
    xFilterConfig.SrcAddrInverseFiltering = DISABLE;
    xFilterConfig.ControlPacketsFilter = ETH_CTRLPACKETS_BLOCK_ALL;
    xFilterConfig.BroadcastFilter = DISABLE;
    xFilterConfig.PassAllMulticast = DISABLE;
    xFilterConfig.DestAddrInverseFiltering = DISABLE;
    xFilterConfig.HashMulticast = ENABLE;
    xFilterConfig.HashUnicast = ENABLE;
    xFilterConfig.PromiscuousMode = DISABLE;

    if( HAL_ETH_SetMACFilterConfig( pxEthHandle, &xFilterConfig ) != HAL_OK )
    {
        FreeRTOS_debug_printf( ( "prvConfigureMACAddressFilter: HAL_ETH_SetMACFilterConfig failed\n" ) );
        return pdFALSE;
    }

    return pdTRUE;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvInitMacAddresses( ETH_HandleTypeDef * pxEthHandle,
                                      NetworkInterface_t * pxInterface )
{
    if( prvConfigureMACAddressFilter( pxEthHandle ) == pdFALSE )
    {
        return pdFALSE;
    }

    prvResetMACAddressFilters( pxEthHandle );

    NetworkEndPoint_t * pxEndPoint;

    for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface ); pxEndPoint != NULL; pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
    {
        prvAddAllowedMACAddress( pxInterface, pxEndPoint->xMACAddress.ucBytes );
    }

    #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
        #if ipconfigIS_ENABLED( ipconfigUSE_MDNS )
            prvAddAllowedMACAddress( pxInterface, xMDNS_MacAddress.ucBytes );
        #endif
        #if ipconfigIS_ENABLED( ipconfigUSE_LLMNR )
            prvAddAllowedMACAddress( pxInterface, xLLMNR_MacAddress.ucBytes );
        #endif
    #endif

    #if ipconfigIS_ENABLED( ipconfigUSE_IPv6 )
        prvAddAllowedMACAddress( pxInterface, pcLOCAL_ALL_NODES_MULTICAST_MAC );
        #if ipconfigIS_ENABLED( ipconfigUSE_MDNS )
            prvAddAllowedMACAddress( pxInterface, xMDNS_MacAddressIPv6.ucBytes );
        #endif
        #if ipconfigIS_ENABLED( ipconfigUSE_LLMNR )
            prvAddAllowedMACAddress( pxInterface, xLLMNR_MacAddressIPv6.ucBytes );
        #endif
    #endif

    return pdTRUE;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvRestoreMACAddressFilters( ETH_HandleTypeDef * pxEthHandle )
{
    if( prvConfigureMACAddressFilter( pxEthHandle ) == pdFALSE )
    {
        return pdFALSE;
    }

    for( uint8_t ucIndex = 0U; ucIndex < niEMAC_MAC_DEST_MATCH_COUNT; ucIndex++ )
    {
        if( ucDestMatchCounters[ ucIndex ] > 0U )
        {
            prvHAL_ETH_SetDestMACAddrMatch( pxEthHandle->Instance, ucIndex, ucDestMatchAddresses[ ucIndex ] );
        }
        else
        {
            prvHAL_ETH_ClearDestMACAddrMatch( pxEthHandle->Instance, ucIndex );
        }
    }

    if( HAL_ETH_SetHashTable( pxEthHandle, ulHashTable ) != HAL_OK )
    {
        FreeRTOS_debug_printf( ( "prvRestoreMACAddressFilters: HAL_ETH_SetHashTable failed\n" ) );
        return pdFALSE;
    }

    return pdTRUE;
}

/*---------------------------------------------------------------------------*/

#ifdef niEMAC_STM32HNX

    static void prvInitPacketFilter( ETH_HandleTypeDef * pxEthHandle )
    {
        HAL_ETHEx_DisableL3L4Filtering( pxEthHandle );

        #if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM )
        {
            const uint8_t ucFilterCount = _FLD2VAL( ETH_MACHWF1R_L3L4FNUM, pxEthHandle->Instance->MACHWF1R );

            if( ucFilterCount > 0 )
            {
                ETH_MACConfigTypeDef xMACConfig = { 0 };

                if( HAL_ETH_GetMACConfig( pxEthHandle, &xMACConfig ) != HAL_OK )
                {
                    FreeRTOS_debug_printf( ( "prvInitPacketFilter: HAL_ETH_GetMACConfig failed\n" ) );
                    return;
                }

                if( xMACConfig.ChecksumOffload != ENABLE )
                {
                    /* "The Layer 3 and Layer 4 Packet Filter feature automatically selects the IPC Full Checksum
                     * Offload Engine on the Receive side. When this feature is enabled, you must set the IPC bit." */
                    xMACConfig.ChecksumOffload = ENABLE;

                    if( HAL_ETH_SetMACConfig( pxEthHandle, &xMACConfig ) != HAL_OK )
                    {
                        FreeRTOS_debug_printf( ( "prvInitPacketFilter: HAL_ETH_SetMACConfig failed\n" ) );
                        return;
                    }
                }

                #if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES )
                {
                    #if ipconfigIS_DISABLED( ipconfigUSE_IPv4 ) || ipconfigIS_DISABLED( ipconfigUSE_IPv6 )
                        ETH_L3FilterConfigTypeDef xL3FilterConfig = { 0 };
                    #endif

                    /* Filter out all possibilities if frame type is disabled */
                    #if ipconfigIS_DISABLED( ipconfigUSE_IPv4 )
                        /* Block IPv4 if it is disabled */
                        if( HAL_ETHEx_GetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_0, &xL3FilterConfig ) != HAL_OK )
                        {
                            FreeRTOS_debug_printf( ( "prvInitPacketFilter: HAL_ETHEx_GetL3FilterConfig failed\n" ) );
                            return;
                        }
                        xL3FilterConfig.Protocol = ETH_L3_IPV4_MATCH;
                        xL3FilterConfig.SrcAddrFilterMatch = ETH_L3_SRC_ADDR_PERFECT_MATCH_ENABLE;
                        xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_PERFECT_MATCH_ENABLE;
                        xL3FilterConfig.SrcAddrHigherBitsMatch = 0x1FU;
                        xL3FilterConfig.DestAddrHigherBitsMatch = 0x1FU;
                        xL3FilterConfig.Ip4SrcAddr = FREERTOS_INADDR_BROADCAST;
                        xL3FilterConfig.Ip4DestAddr = FREERTOS_INADDR_BROADCAST;
                        if( HAL_ETHEx_SetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_0, &xL3FilterConfig ) != HAL_OK )
                        {
                            FreeRTOS_debug_printf( ( "prvInitPacketFilter: HAL_ETHEx_SetL3FilterConfig failed\n" ) );
                            return;
                        }
                    #endif /* if ipconfigIS_DISABLED( ipconfigUSE_IPv4 ) */

                    #if ipconfigIS_DISABLED( ipconfigUSE_IPv6 )
                        /* Block IPv6 if it is disabled */
                        if( HAL_ETHEx_GetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_1, &xL3FilterConfig ) != HAL_OK )
                        {
                            FreeRTOS_debug_printf( ( "prvInitPacketFilter: HAL_ETHEx_GetL3FilterConfig failed\n" ) );
                            return;
                        }
                        xL3FilterConfig.Protocol = ETH_L3_IPV6_MATCH;
                        xL3FilterConfig.SrcAddrFilterMatch = ETH_L3_SRC_ADDR_PERFECT_MATCH_ENABLE;
                        xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_PERFECT_MATCH_ENABLE;
                        xL3FilterConfig.SrcAddrHigherBitsMatch = 0x1FU;
                        xL3FilterConfig.DestAddrHigherBitsMatch = 0x1FU;
                        xL3FilterConfig.Ip6Addr[ 0 ] = 0xFFFFFFFFU;
                        xL3FilterConfig.Ip6Addr[ 1 ] = 0xFFFFFFFFU;
                        xL3FilterConfig.Ip6Addr[ 2 ] = 0xFFFFFFFFU;
                        xL3FilterConfig.Ip6Addr[ 3 ] = 0xFFFFFFFFU;
                        if( HAL_ETHEx_SetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_1, &xL3FilterConfig ) != HAL_OK )
                        {
                            FreeRTOS_debug_printf( ( "prvInitPacketFilter: HAL_ETHEx_SetL3FilterConfig failed\n" ) );
                            return;
                        }
                    #endif /* if ipconfigIS_DISABLED( ipconfigUSE_IPv6 ) */

                    /* Endpoint address acceptance remains in the software
                     * packet filter because the two shared L3 hardware slots
                     * cannot represent an arbitrary endpoint list. */
                }
                #endif /* if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES ) */

                #if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
                {
                    /* These hardware filters gate transport protocols only.
                     * Socket-aware port acceptance remains in the software
                     * packet filter because the two shared L4 slots cannot
                     * represent the active socket set. */
                    ETH_L4FilterConfigTypeDef xL4FilterConfig = { 0 };

                    /* Always allow all UDP */
                    if( HAL_ETHEx_GetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_0, &xL4FilterConfig ) != HAL_OK )
                    {
                        FreeRTOS_debug_printf( ( "prvInitPacketFilter: HAL_ETHEx_GetL4FilterConfig failed\n" ) );
                        return;
                    }
                    xL4FilterConfig.Protocol = ETH_L4_UDP_MATCH;
                    xL4FilterConfig.SrcPortFilterMatch = ETH_L4_SRC_PORT_MATCH_DISABLE;
                    xL4FilterConfig.DestPortFilterMatch = ETH_L4_DEST_PORT_MATCH_DISABLE;
                    xL4FilterConfig.SourcePort = 0U;
                    xL4FilterConfig.DestinationPort = 0U;
                    if( HAL_ETHEx_SetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_0, &xL4FilterConfig ) != HAL_OK )
                    {
                        FreeRTOS_debug_printf( ( "prvInitPacketFilter: HAL_ETHEx_SetL4FilterConfig failed\n" ) );
                        return;
                    }

                    #if ipconfigIS_DISABLED( ipconfigUSE_TCP )
                        /* Block TCP if it is disabled */
                        if( HAL_ETHEx_GetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_1, &xL4FilterConfig ) != HAL_OK )
                        {
                            FreeRTOS_debug_printf( ( "prvInitPacketFilter: HAL_ETHEx_GetL4FilterConfig failed\n" ) );
                            return;
                        }
                        xL4FilterConfig.Protocol = ETH_L4_TCP_MATCH;
                        xL4FilterConfig.SrcPortFilterMatch = ETH_L4_SRC_PORT_PERFECT_MATCH_ENABLE;
                        xL4FilterConfig.DestPortFilterMatch = ETH_L4_DEST_PORT_PERFECT_MATCH_ENABLE;
                        xL4FilterConfig.SourcePort = 0xFFFFU;
                        xL4FilterConfig.DestinationPort = 0xFFFFU;
                        if( HAL_ETHEx_SetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_1, &xL4FilterConfig ) != HAL_OK )
                        {
                            FreeRTOS_debug_printf( ( "prvInitPacketFilter: HAL_ETHEx_SetL4FilterConfig failed\n" ) );
                            return;
                        }
                    #endif
                }
                #endif /* if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS ) */

                HAL_ETHEx_EnableL3L4Filtering( pxEthHandle );
            }
        }
        #endif /* if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM ) */
    }

#endif /* ifdef niEMAC_STM32HNX */

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
    const uint8_t ucHashIndex = ( uint8_t ) ( ( ulHash >> 26 ) & 0x3FU );

    return ucHashIndex;
}

/*---------------------------------------------------------------------------*/

/* The HAL exposes source-address matching, but receive filtering requires
 * destination-address matching. Program the destination registers directly. */
static void prvHAL_ETH_SetDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                            uint8_t ucIndex,
                                            const uint8_t * const pucMACAddr )
{
    configASSERT( ucIndex < niEMAC_MAC_DEST_MATCH_COUNT );
    const uint32_t ulMacAddrHigh = ( ( uint32_t ) pucMACAddr[ 5 ] << 8 ) | ( uint32_t ) pucMACAddr[ 4 ];
    const uint32_t ulMacAddrLow = ( ( uint32_t ) pucMACAddr[ 3 ] << 24 ) | ( ( uint32_t ) pucMACAddr[ 2 ] << 16 ) | ( ( uint32_t ) pucMACAddr[ 1 ] << 8 ) | ( uint32_t ) pucMACAddr[ 0 ];

    /* MACA0HR/MACA0LR reserved for the primary MAC-address. */
    const uintptr_t uxMacRegHigh = ( uintptr_t ) &( pxEthInstance->MACA1HR ) + ( 8U * ucIndex );
    const uintptr_t uxMacRegLow = ( uintptr_t ) &( pxEthInstance->MACA1LR ) + ( 8U * ucIndex );
    ( void ) memcpy( ucDestMatchAddresses[ ucIndex ], pucMACAddr, ipMAC_ADDRESS_LENGTH_BYTES );
    ( *( __IO uint32_t * ) uxMacRegHigh ) = niEMAC_MAC_ADDRESS_ENABLE_FLAG | ulMacAddrHigh;
    ( *( __IO uint32_t * ) uxMacRegLow ) = ulMacAddrLow;
}

/*---------------------------------------------------------------------------*/

static void prvHAL_ETH_ClearDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                              uint8_t ucIndex )
{
    configASSERT( ucIndex < niEMAC_MAC_DEST_MATCH_COUNT );
    const uintptr_t uxMacRegHigh = ( uintptr_t ) &( pxEthInstance->MACA1HR ) + ( 8U * ucIndex );
    const uintptr_t uxMacRegLow = ( uintptr_t ) &( pxEthInstance->MACA1LR ) + ( 8U * ucIndex );
    ( *( __IO uint32_t * ) uxMacRegHigh ) = 0U;
    ( *( __IO uint32_t * ) uxMacRegLow ) = 0U;
    ( void ) memset( ucDestMatchAddresses[ ucIndex ], 0, ipMAC_ADDRESS_LENGTH_BYTES );
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvAddDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                          const uint8_t * const pucMACAddr )
{
    BaseType_t xResult = pdFALSE;
    ( void ) pxEthInstance;

    uint8_t ucIndex;

    for( ucIndex = 0; ucIndex < niEMAC_MAC_DEST_MATCH_COUNT; ++ucIndex )
    {
        if( ucDestMatchCounters[ ucIndex ] > 0U )
        {
            if( memcmp( ucDestMatchAddresses[ ucIndex ], pucMACAddr, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
            {
                if( ucDestMatchCounters[ ucIndex ] < UINT8_MAX )
                {
                    ++( ucDestMatchCounters[ ucIndex ] );
                }

                xResult = pdTRUE;
                break;
            }
        }
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvRemoveDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                             const uint8_t * const pucMACAddr )
{
    BaseType_t xResult = pdFALSE;

    uint8_t ucIndex;

    for( ucIndex = 0; ucIndex < niEMAC_MAC_DEST_MATCH_COUNT; ++ucIndex )
    {
        if( ucDestMatchCounters[ ucIndex ] > 0U )
        {
            if( memcmp( ucDestMatchAddresses[ ucIndex ], pucMACAddr, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
            {
                /* A saturated reference count cannot be decremented safely: its
                 * true value is unknown. Keep accepting the address instead of
                 * clearing an entry that may still have users. */
                if( ( ucDestMatchCounters[ ucIndex ] < UINT8_MAX ) &&
                    ( --( ucDestMatchCounters[ ucIndex ] ) == 0U ) )
                {
                    prvHAL_ETH_ClearDestMACAddrMatch( pxEthInstance, ucIndex );
                }

                xResult = pdTRUE;
                break;
            }
        }
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvSetNewDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                             uint8_t ucHashIndex,
                                             const uint8_t * const pucMACAddr )
{
    BaseType_t xResult = pdFALSE;

    if( ucAddrHashCounters[ ucHashIndex ] == 0U )
    {
        uint8_t ucIndex;

        for( ucIndex = 0U; ucIndex < niEMAC_MAC_DEST_MATCH_COUNT; ++ucIndex )
        {
            if( ucDestMatchCounters[ ucIndex ] == 0U )
            {
                prvHAL_ETH_SetDestMACAddrMatch( pxEthInstance, ucIndex, pucMACAddr );
                ucDestMatchCounters[ ucIndex ] = 1U;
                xResult = pdTRUE;
                break;
            }
        }
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static void prvAddDestMACAddrHash( ETH_HandleTypeDef * pxEthHandle,
                                   uint8_t ucHashIndex )
{
    if( ucAddrHashCounters[ ucHashIndex ] == 0 )
    {
        if( ( ucHashIndex & 0x20U ) != 0U )
        {
            ulHashTable[ niEMAC_HASH_TABLE_HIGH_WORD_INDEX ] |= ( 1U << ( ucHashIndex & 0x1FU ) );
        }
        else
        {
            ulHashTable[ niEMAC_HASH_TABLE_LOW_WORD_INDEX ] |= ( 1U << ucHashIndex );
        }

        HAL_ETH_SetHashTable( pxEthHandle, ulHashTable );
    }

    if( ucAddrHashCounters[ ucHashIndex ] < UINT8_MAX )
    {
        ++( ucAddrHashCounters[ ucHashIndex ] );
    }
}

/*---------------------------------------------------------------------------*/

static void prvRemoveDestMACAddrHash( ETH_HandleTypeDef * pxEthHandle,
                                      const uint8_t * const pucMACAddr )
{
    const uint8_t ucHashIndex = prvGetMacHashIndex( pucMACAddr );

    if( ucAddrHashCounters[ ucHashIndex ] > 0U )
    {
        if( ( ucAddrHashCounters[ ucHashIndex ] < UINT8_MAX ) &&
            ( --( ucAddrHashCounters[ ucHashIndex ] ) == 0U ) )
        {
            if( ( ucHashIndex & 0x20U ) != 0U )
            {
                ulHashTable[ niEMAC_HASH_TABLE_HIGH_WORD_INDEX ] &= ~( 1U << ( ucHashIndex & 0x1FU ) );
            }
            else
            {
                ulHashTable[ niEMAC_HASH_TABLE_LOW_WORD_INDEX ] &= ~( 1U << ucHashIndex );
            }

            ( void ) HAL_ETH_SetHashTable( pxEthHandle, ulHashTable );
        }
    }
}

/*---------------------------------------------------------------------------*/

static void prvResetMACAddressFilters( ETH_HandleTypeDef * pxEthHandle )
{
    ( void ) memset( ucDestMatchCounters, 0, sizeof( ucDestMatchCounters ) );
    ( void ) memset( ucDestMatchAddresses, 0, sizeof( ucDestMatchAddresses ) );
    ( void ) memset( ulHashTable, 0, sizeof( ulHashTable ) );
    ( void ) memset( ucAddrHashCounters, 0, sizeof( ucAddrHashCounters ) );

    if( ( pxEthHandle == NULL ) || ( pxEthHandle->Instance == NULL ) )
    {
        return;
    }

    for( uint8_t ucIndex = 0U; ucIndex < niEMAC_MAC_DEST_MATCH_COUNT; ++ucIndex )
    {
        prvHAL_ETH_ClearDestMACAddrMatch( pxEthHandle->Instance, ucIndex );
    }

    if( HAL_ETH_SetHashTable( pxEthHandle, ulHashTable ) != HAL_OK )
    {
        FreeRTOS_debug_printf( ( "prvResetMACAddressFilters: HAL_ETH_SetHashTable failed\n" ) );
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
        uint32_t ulBuffersReleased = 0U;

        #if defined( niEMAC_STM32NX )
            pxEthHandle->TxOpCH = niEMAC_DMA_CHANNEL_INDEX;
        #endif

        /* Each transmission consumes one HAL buffer and one semaphore slot. */
        const uint32_t ulBuffersBeforeRelease = HAL_ETH_GetTxBuffersNumber( pxEthHandle );
        const HAL_StatusTypeDef xReleaseStatus = HAL_ETH_ReleaseTxPacket( pxEthHandle );
        const uint32_t ulBuffersAfterRelease = HAL_ETH_GetTxBuffersNumber( pxEthHandle );

        configASSERT( xReleaseStatus == HAL_OK );
        configASSERT( ulBuffersAfterRelease <= ulBuffersBeforeRelease );

        if( ( xReleaseStatus == HAL_OK ) && ( ulBuffersAfterRelease <= ulBuffersBeforeRelease ) )
        {
            ulBuffersReleased = ulBuffersBeforeRelease - ulBuffersAfterRelease;
        }

        for( uint32_t ulIndex = 0U; ulIndex < ulBuffersReleased; ulIndex++ )
        {
            const BaseType_t xGiveResult = xSemaphoreGive( xTxDescSem );

            configASSERT( xGiveResult == pdTRUE );

            if( xGiveResult != pdTRUE )
            {
                break;
            }
        }

        ( void ) xSemaphoreGive( xTxMutex );
    }
    else
    {
        FreeRTOS_debug_printf( ( "prvReleaseTxPacket: Failed\n" ) );
    }
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
    }
}

/*---------------------------------------------------------------------------*/

static void prvDiscardRxFrame( NetworkBufferDescriptor_t ** ppxStartDescriptor,
                               NetworkBufferDescriptor_t ** ppxEndDescriptor,
                               NetworkBufferDescriptor_t * pxCurrentDescriptor )
{
    NetworkBufferDescriptor_t * pxStartDescriptor = NULL;

    if( ppxStartDescriptor != NULL )
    {
        pxStartDescriptor = *ppxStartDescriptor;
        *ppxStartDescriptor = NULL;
    }

    if( ppxEndDescriptor != NULL )
    {
        *ppxEndDescriptor = NULL;
    }

    if( pxStartDescriptor != NULL )
    {
        prvReleaseNetworkBufferDescriptor( pxStartDescriptor );
    }

    /* HAL supplies the current descriptor before linking it into the partial
     * frame, so it must be released separately. */
    if( ( pxCurrentDescriptor != NULL ) && ( pxCurrentDescriptor != pxStartDescriptor ) )
    {
        prvReleaseNetworkBufferDescriptor( pxCurrentDescriptor );
    }

    xDropCurrentRxFrame = pdTRUE;
}

/*---------------------------------------------------------------------------*/

static void prvSendRxEvent( NetworkBufferDescriptor_t * const pxDescriptor )
{
    const IPStackEvent_t xRxEvent =
    {
        .eEventType = eNetworkRxEvent,
        .pvData     = ( void * ) pxDescriptor
    };

    if( xSendEventStructToIPTask( &xRxEvent, pdMS_TO_TICKS( niEMAC_RX_MAX_BLOCK_TIME_MS ) ) != pdPASS )
    {
        iptraceETHERNET_RX_EVENT_LOST();
        FreeRTOS_debug_printf( ( "prvSendRxEvent: xSendEventStructToIPTask failed\n" ) );
        prvReleaseNetworkBufferDescriptor( pxDescriptor );
    }
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvAcceptPacket( ETH_HandleTypeDef * pxEthHandle,
                                   NetworkInterface_t * pxInterface,
                                   NetworkBufferDescriptor_t * pxDescriptor )
{
    BaseType_t xResult = pdFALSE;

    do
    {
        if( ( pxEthHandle == NULL ) || ( pxInterface == NULL ) ||
            ( pxDescriptor == NULL ) || ( pxDescriptor->pucEthernetBuffer == NULL ) )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Invalid argument\n" ) );
            break;
        }

        if( ( pxDescriptor->xDataLength < sizeof( EthernetHeader_t ) ) ||
            ( pxDescriptor->xDataLength > niEMAC_DATA_BUFFER_SIZE ) )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Invalid packet size\n" ) );
            break;
        }

        const EthernetHeader_t * const pxEthernetHeader = ( const EthernetHeader_t * const ) pxDescriptor->pucEthernetBuffer;
        size_t uxMinimumLength = sizeof( EthernetHeader_t );

        switch( pxEthernetHeader->usFrameType )
        {
            #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
                case ipARP_FRAME_TYPE:
                    uxMinimumLength = sizeof( ARPPacket_t );
                    break;

                case ipIPv4_FRAME_TYPE:
                    uxMinimumLength = sizeof( IPPacket_t );
                    break;
            #endif

            #if ipconfigIS_ENABLED( ipconfigUSE_IPv6 )
                case ipIPv6_FRAME_TYPE:
                    uxMinimumLength = sizeof( IPPacket_IPv6_t );
                    break;
            #endif

            default:
                break;
        }

        if( pxDescriptor->xDataLength < uxMinimumLength )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Packet too short\n" ) );
            break;
        }

        uint32_t ulErrorCode = 0U;

        if( HAL_ETH_GetRxDataErrorCode( pxEthHandle, &ulErrorCode ) != HAL_OK )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Failed to read Rx data error\n" ) );
            break;
        }

        if( ulErrorCode != 0U )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Rx data error\n" ) );
            break;
        }

        #if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES )
            if( eConsiderFrameForProcessing( pxDescriptor->pucEthernetBuffer ) != eProcessBuffer )
            {
                iptraceETHERNET_RX_EVENT_LOST();
                FreeRTOS_debug_printf( ( "prvAcceptPacket: Frame discarded\n" ) );
                break;
            }
        #endif

        pxDescriptor->pxInterface = pxInterface;
        pxDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint( pxInterface, pxDescriptor->pucEthernetBuffer );

        if( pxDescriptor->pxEndPoint == NULL )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: No matching endpoint\n" ) );
            break;
        }

        #if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
            if( eConsiderPacketForProcessing( pxDescriptor ) != eProcessBuffer )
            {
                iptraceETHERNET_RX_EVENT_LOST();
                FreeRTOS_debug_printf( ( "prvAcceptPacket: Packet discarded\n" ) );
                break;
            }
        #endif

        xResult = pdTRUE;
    } while( pdFALSE );

    return xResult;
}

/*---------------------------------------------------------------------------*/

static void prvNotifyEMACTaskFromISR( eMAC_IF_EVENT eEvents )
{
    if( ( xEMACTaskHandle != NULL ) && ( eEvents != eMacEventNone ) )
    {
        BaseType_t xHigherPriorityTaskWoken = pdFALSE;

        ( void ) xTaskNotifyFromISR( xEMACTaskHandle, eEvents, eSetBits, &xHigherPriorityTaskWoken );
        xSwitchRequired |= xHigherPriorityTaskWoken;
    }
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              IRQ Handlers                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

void niEMAC_ETH_IRQ_HANDLER( void )
{
    traceISR_ENTER();

    ETH_HandleTypeDef * pxEthHandle = &xEthHandle;

    xSwitchRequired = pdFALSE;

    if( pxEthHandle->Instance != NULL )
    {
        HAL_ETH_IRQHandler( pxEthHandle );
    }

    portYIELD_FROM_ISR( xSwitchRequired );
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_ErrorCallback( ETH_HandleTypeDef * pxEthHandle )
{
    eMAC_IF_EVENT eErrorEvents = eMacEventNone;
    const uint32_t ulErrorCode = HAL_ETH_GetError( pxEthHandle );
    uint32_t ulDmaErrorCode = 0U;

    if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_ERROR )
    {
        /* A fatal DMA or MAC error requires reinitialization in task context. */
        eErrorEvents |= eMacEventErrEth;
    }

    if( ( ulErrorCode & niEMAC_DMA_ERROR_MASK ) != 0 )
    {
        eErrorEvents |= eMacEventErrDma;
        ulDmaErrorCode = HAL_ETH_GetDMAError( pxEthHandle );

        if( ( ulDmaErrorCode & niEMAC_DMA_TX_BUFFER_UNAVAILABLE_FLAG ) != 0 )
        {
            eErrorEvents |= eMacEventErrTx;
        }

        if( ( ulDmaErrorCode & niEMAC_DMA_RX_BUFFER_UNAVAILABLE_FLAG ) != 0 )
        {
            eErrorEvents |= eMacEventErrRx;
        }
    }

    if( ( eErrorEvents & eMacEventErrEth ) != 0 )
    {
        /* N6 invokes this callback separately for each DMA channel. */
        ulPendingFatalHalErrorCode |= ulErrorCode;
        ulPendingFatalDmaErrorCode |= ulDmaErrorCode;
    }

    if( ( ulErrorCode & HAL_ETH_ERROR_MAC ) != 0 )
    {
        /* Newer HALs clear MACErrorCode immediately after this callback. */
        ulPendingMacErrorCode |= HAL_ETH_GetMACError( pxEthHandle );
        eErrorEvents |= eMacEventErrMac;
    }

    prvNotifyEMACTaskFromISR( eErrorEvents );
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_RxCpltCallback( ETH_HandleTypeDef * pxEthHandle )
{
    for( uint32_t ulChannel = 0; ulChannel < niEMAC_RX_CHANNEL_COUNT; ulChannel++ )
    {
        const size_t uxRxDescriptorsUsed = niEMAC_RX_DESC_LIST( pxEthHandle, ulChannel ).RxDescCnt;
        iptraceSTM32_ETH_RX_DESC_USAGE( ulChannel, uxRxDescriptorsUsed );
    }

    iptraceNETWORK_INTERFACE_RECEIVE();

    prvNotifyEMACTaskFromISR( eMacEventRx );
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_TxCpltCallback( ETH_HandleTypeDef * pxEthHandle )
{
    for( uint32_t ulChannel = 0; ulChannel < niEMAC_TX_CHANNEL_COUNT; ulChannel++ )
    {
        const size_t uxTxDescriptorsUsed = niEMAC_TX_DESC_LIST( pxEthHandle, ulChannel ).BuffersInUse;
        iptraceSTM32_ETH_TX_DESC_USAGE( ulChannel, uxTxDescriptorsUsed );
    }

    iptraceNETWORK_INTERFACE_TRANSMIT();

    prvNotifyEMACTaskFromISR( eMacEventTx );
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                            HAL Tx/Rx Callbacks                            */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

void HAL_ETH_RxAllocateCallback( uint8_t ** ppucBuff )
{
    if( ppucBuff == NULL )
    {
        return;
    }

    const NetworkBufferDescriptor_t * pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( niEMAC_DATA_BUFFER_SIZE, pdMS_TO_TICKS( niDESCRIPTOR_WAIT_TIME_MS ) );

    if( pxBufferDescriptor != NULL )
    {
        #ifdef niEMAC_CACHEABLE
            if( niEMAC_CACHE_MAINTENANCE != 0 )
            {
                /* The hidden network-buffer pointer can share the first cache
                 * line with the Ethernet payload. Clean it before invalidating
                 * the complete DMA receive range. */
                prvCacheCleanInvalidateByAddr( pxBufferDescriptor->pucEthernetBuffer, niEMAC_DATA_BUFFER_SIZE );
            }
        #endif
        *ppucBuff = pxBufferDescriptor->pucEthernetBuffer;
    }
    else
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxAllocateCallback: failed\n" ) );
        *ppucBuff = NULL;
    }
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_RxLinkCallback( void ** ppvStart,
                             void ** ppvEnd,
                             uint8_t * pucBuff,
                             uint16_t usLength )
{
    NetworkBufferDescriptor_t ** const ppxStartDescriptor = ( ppvStart != NULL ) ? ( NetworkBufferDescriptor_t ** ) ppvStart : NULL;
    NetworkBufferDescriptor_t ** const ppxEndDescriptor = ( ppvEnd != NULL ) ? ( NetworkBufferDescriptor_t ** ) ppvEnd : NULL;

    if( ( ppxStartDescriptor == NULL ) || ( ppxEndDescriptor == NULL ) )
    {
        NetworkBufferDescriptor_t * pxCurDescriptor = NULL;

        FreeRTOS_debug_printf( ( "HAL_ETH_RxLinkCallback: Invalid callback context\n" ) );

        if( pucBuff != NULL )
        {
            pxCurDescriptor = pxPacketBuffer_to_NetworkBuffer( ( const void * ) pucBuff );
        }

        prvDiscardRxFrame( ppxStartDescriptor, ppxEndDescriptor, pxCurDescriptor );
        return;
    }

    if( pucBuff == NULL )
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxLinkCallback: NULL buffer pointer\n" ) );
        prvDiscardRxFrame( ppxStartDescriptor, ppxEndDescriptor, NULL );
        return;
    }

    NetworkBufferDescriptor_t * const pxCurDescriptor = pxPacketBuffer_to_NetworkBuffer( ( const void * ) pucBuff );

    if( pxCurDescriptor == NULL )
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxLinkCallback: Invalid buffer descriptor\n" ) );
        prvDiscardRxFrame( ppxStartDescriptor, ppxEndDescriptor, NULL );
        return;
    }

    if( ( usLength == 0U ) || ( usLength > niEMAC_DATA_BUFFER_SIZE ) ||
        ( usLength > pxCurDescriptor->xDataLength ) )
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxLinkCallback: Invalid buffer length\n" ) );
        prvDiscardRxFrame( ppxStartDescriptor, ppxEndDescriptor, pxCurDescriptor );
        return;
    }

    #ifdef niEMAC_CACHEABLE
        if( niEMAC_CACHE_MAINTENANCE != 0 )
        {
            /* Invalidate DMA-written data before the packet is read by the CPU. */
            prvCacheInvalidateByAddr( pucBuff, usLength );
        }
    #endif

    if( xDropCurrentRxFrame != pdFALSE )
    {
        prvDiscardRxFrame( ppxStartDescriptor, ppxEndDescriptor, pxCurDescriptor );
        return;
    }

    if( *ppxStartDescriptor != NULL )
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxLinkCallback: Multi-buffer packets are unsupported\n" ) );
        prvDiscardRxFrame( ppxStartDescriptor, ppxEndDescriptor, pxCurDescriptor );
        return;
    }

    pxCurDescriptor->xDataLength = usLength;
    #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
        pxCurDescriptor->pxNextBuffer = NULL;
    #endif
    *ppxStartDescriptor = pxCurDescriptor;
    *ppxEndDescriptor = pxCurDescriptor;
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_TxFreeCallback( uint32_t * pulBuff )
{
    if( pulBuff != NULL )
    {
        NetworkBufferDescriptor_t * const pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) pulBuff;

        prvReleaseNetworkBufferDescriptor( pxNetworkBuffer );
    }
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                           Buffer Allocation                               */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

size_t uxNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ niEMAC_TOTAL_BUFFER_SIZE ] __ALIGNED( niEMAC_BUF_ALIGNMENT ) __attribute__( ( section( niEMAC_BUFFERS_SECTION ) ) );

    configASSERT( niEMAC_TOTAL_BUFFER_SIZE >= ipconfigETHERNET_MINIMUM_PACKET_BYTES );
    configASSERT( xBufferAllocFixedSize == pdTRUE );

    size_t uxIndex;

    for( uxIndex = 0; uxIndex < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ++uxIndex )
    {
        pxNetworkBuffers[ uxIndex ].pucEthernetBuffer = &( ucNetworkPackets[ uxIndex ][ ipBUFFER_PADDING ] );
        *( ( uint32_t * ) &( ucNetworkPackets[ uxIndex ][ 0 ] ) ) = ( uint32_t ) ( &( pxNetworkBuffers[ uxIndex ] ) );
    }

    return( niEMAC_TOTAL_BUFFER_SIZE - ipBUFFER_PADDING );
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                      Network Interface Definition                         */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                      NetworkInterface_t * pxInterface )
{
    static char pcName[ 17 ];

    ( void ) snprintf( pcName, sizeof( pcName ), "eth%u", ( unsigned ) xEMACIndex );

    ( void ) memset( pxInterface, '\0', sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;
    /* Preserve the interface index for API compatibility. Driver state is
     * single-instance, as documented with the static state declarations. */
    pxInterface->pvArgument = ( void * ) xEMACIndex;
    pxInterface->pfInitialise = prvNetworkInterfaceInitialise;
    pxInterface->pfOutput = prvNetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = prvGetPhyLinkStatus;

    pxInterface->pfAddAllowedMAC = prvAddAllowedMACAddress;
    pxInterface->pfRemoveAllowedMAC = prvRemoveAllowedMACAddress;

    return FreeRTOS_AddNetworkInterface( pxInterface );
}

/*---------------------------------------------------------------------------*/

#if ipconfigIS_ENABLED( ipconfigIPv4_BACKWARD_COMPATIBLE )

/* Do not call the following function directly. It is there for downward compatibility.
 * The function FreeRTOS_IPInit() will call it to initialize the interface and end-point
 * objects.  See the description in FreeRTOS_Routing.h. */
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface )
    {
        return pxSTM32_FillInterfaceDescriptor( xEMACIndex, pxInterface );
    }

#endif

/*---------------------------------------------------------------------------*/
