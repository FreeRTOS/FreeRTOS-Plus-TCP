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
#endif /* if defined( STM32F4 ) */

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

#define niEMAC_TASK_NAME                  "EMAC_STM32"
#ifndef niEMAC_TASK_PRIORITY
    #define niEMAC_TASK_PRIORITY          ( configMAX_PRIORITIES - 2 )
#endif
#define niEMAC_TASK_STACK_SIZE            ( 4U * configMINIMAL_STACK_SIZE )

#define niEMAC_TX_DESC_SECTION            ".TxDescripSection"
#define niEMAC_RX_DESC_SECTION            ".RxDescripSection"
#define niEMAC_BUFFERS_SECTION            ".EthBuffersSection"

#define niEMAC_TASK_MAX_BLOCK_TIME_MS     100U
#define niEMAC_TX_MAX_BLOCK_TIME_MS       20U
#define niEMAC_RX_MAX_BLOCK_TIME_MS       20U
#define niEMAC_DESCRIPTOR_WAIT_TIME_MS    20U
#define niEMAC_FILTER_REFRESH_TIME_MS     1000U

#define niEMAC_TX_MUTEX_NAME              "EMAC_TxMutex"
#define niEMAC_TX_DESC_SEM_NAME           "EMAC_TxDescSem"
#define niEMAC_TX_QUEUE_NAME              "EMAC_TxQueue"
#ifndef niEMAC_MAX_INTERFACE_NAMES
    #define niEMAC_MAX_INTERFACE_NAMES    1U
#endif
#define niEMAC_TX_QUEUE_LENGTH            ETH_TX_DESC_CNT
#define niEMAC_TX_BUFFERS_PER_DESC        2U
#define niEMAC_TX_MAX_BUFFER_FRAGMENTS    ( ETH_TX_DESC_CNT * niEMAC_TX_BUFFERS_PER_DESC )

#ifndef niEMAC_AUTO_NEGOTIATION
    #define niEMAC_AUTO_NEGOTIATION       ipconfigENABLE
#endif
#ifndef niEMAC_USE_100MB
    #define niEMAC_USE_100MB              ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_NEGOTIATION ) )
#endif
#ifndef niEMAC_USE_FULL_DUPLEX
    #define niEMAC_USE_FULL_DUPLEX        ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_NEGOTIATION ) )
#endif
#ifndef niEMAC_AUTO_CROSS
    #define niEMAC_AUTO_CROSS             ( ipconfigENABLE && ipconfigIS_ENABLED( niEMAC_AUTO_NEGOTIATION ) )
#endif
#ifndef niEMAC_CROSSED_LINK
    #define niEMAC_CROSSED_LINK           ( ipconfigENABLE && ipconfigIS_DISABLED( niEMAC_AUTO_CROSS ) )
#endif

#define niEMAC_USE_RMII                   ipconfigENABLE

#define niEMAC_USE_MPU                    ipconfigENABLE

#ifndef niEMAC_USE_ARP_OFFLOAD
    #define niEMAC_USE_ARP_OFFLOAD        ipconfigDISABLE
#endif

#ifndef niEMAC_USE_SOURCE_MAC_GUARD
    #define niEMAC_USE_SOURCE_MAC_GUARD   ipconfigDISABLE
#endif

#ifndef niEMAC_USE_VLAN_OFFLOAD
    #define niEMAC_USE_VLAN_OFFLOAD       ipconfigDISABLE
#endif

#ifndef niEMAC_VLAN_IDENTIFIER
    #define niEMAC_VLAN_IDENTIFIER        0U
#endif

#ifndef niEMAC_VLAN_RX_STRIP
    #define niEMAC_VLAN_RX_STRIP          ipconfigDISABLE
#endif

#ifndef niEMAC_VLAN_TX_MODE
    #if defined( ETH_VLAN_INSERT )
        #define niEMAC_VLAN_TX_MODE       ETH_VLAN_INSERT
    #else
        #define niEMAC_VLAN_TX_MODE       0U
    #endif
#endif

#ifndef niEMAC_USE_PTP
    #define niEMAC_USE_PTP                ipconfigDISABLE
#endif

#ifndef niEMAC_USE_TCP_SEGMENTATION
    #define niEMAC_USE_TCP_SEGMENTATION   ipconfigDISABLE
#endif

#ifndef niEMAC_TCP_SEGMENTATION_MSS
    #define niEMAC_TCP_SEGMENTATION_MSS   ipconfigTCP_MSS
#endif

#ifndef niEMAC_USE_FLOW_CONTROL
    #define niEMAC_USE_FLOW_CONTROL       ipconfigDISABLE
#endif

#ifndef niEMAC_FLOW_CONTROL_TX_ENABLE
    #define niEMAC_FLOW_CONTROL_TX_ENABLE ipconfigENABLE
#endif

#ifndef niEMAC_FLOW_CONTROL_RX_ENABLE
    #define niEMAC_FLOW_CONTROL_RX_ENABLE ipconfigENABLE
#endif

#ifndef niEMAC_FLOW_CONTROL_PAUSE_TIME
    #define niEMAC_FLOW_CONTROL_PAUSE_TIME 0x100U
#endif

#ifndef niEMAC_FLOW_CONTROL_PAUSE_LOW_THRESHOLD
    #if defined( ETH_PAUSELOWTHRESHOLD_MINUS_4 )
        #define niEMAC_FLOW_CONTROL_PAUSE_LOW_THRESHOLD ETH_PAUSELOWTHRESHOLD_MINUS_4
    #else
        #define niEMAC_FLOW_CONTROL_PAUSE_LOW_THRESHOLD 0U
    #endif
#endif

#ifndef niEMAC_TX_QUEUE_MODE
    #if defined( ETH_TRANSMITSTOREFORWARD )
        #define niEMAC_TX_QUEUE_MODE ETH_TRANSMITSTOREFORWARD
    #else
        #define niEMAC_TX_QUEUE_MODE 0U
    #endif
#endif

#ifndef niEMAC_RX_QUEUE_MODE
    #if defined( ETH_RECEIVESTOREFORWARD )
        #define niEMAC_RX_QUEUE_MODE ETH_RECEIVESTOREFORWARD
    #else
        #define niEMAC_RX_QUEUE_MODE 0U
    #endif
#endif

#ifndef niEMAC_USE_JUMBO_FRAMES
    #define niEMAC_USE_JUMBO_FRAMES       ipconfigDISABLE
#endif

#ifndef niEMAC_USE_2K_PACKETS
    #define niEMAC_USE_2K_PACKETS         ipconfigDISABLE
#endif

#ifndef niEMAC_USE_SAIC
    #define niEMAC_USE_SAIC               ipconfigDISABLE
#endif

#ifndef niEMAC_SAIC_DISABLED_CONTROL
    #if defined( ETH_SRC_ADDR_CONTROL_DISABLE )
        #define niEMAC_SAIC_DISABLED_CONTROL ETH_SRC_ADDR_CONTROL_DISABLE
    #elif defined( ETH_SOURCEADDRESS_DISABLE )
        #define niEMAC_SAIC_DISABLED_CONTROL ETH_SOURCEADDRESS_DISABLE
    #else
        #define niEMAC_SAIC_DISABLED_CONTROL 0U
    #endif
#endif

#ifndef niEMAC_SAIC_CONTROL
    #define niEMAC_SAIC_CONTROL niEMAC_SAIC_DISABLED_CONTROL
#endif

#ifndef niEMAC_USE_INNER_VLAN_OFFLOAD
    #define niEMAC_USE_INNER_VLAN_OFFLOAD ipconfigDISABLE
#endif

#ifndef niEMAC_INNER_VLAN_IDENTIFIER
    #define niEMAC_INNER_VLAN_IDENTIFIER  0U
#endif

#ifndef niEMAC_INNER_VLAN_DISABLED_MODE
    #if defined( ETH_INNER_VLAN_DISABLE )
        #define niEMAC_INNER_VLAN_DISABLED_MODE ETH_INNER_VLAN_DISABLE
    #elif defined( ETH_VLAN_DISABLE )
        #define niEMAC_INNER_VLAN_DISABLED_MODE ETH_VLAN_DISABLE
    #else
        #define niEMAC_INNER_VLAN_DISABLED_MODE 0U
    #endif
#endif

#ifndef niEMAC_INNER_VLAN_TX_MODE
    #define niEMAC_INNER_VLAN_TX_MODE niEMAC_INNER_VLAN_DISABLED_MODE
#endif

#ifndef niEMAC_PTP_EVENT_UDP_PORT
    #define niEMAC_PTP_EVENT_UDP_PORT     319U
#endif

#ifndef niEMAC_PTP_GENERAL_UDP_PORT
    #define niEMAC_PTP_GENERAL_UDP_PORT   320U
#endif

#ifndef niEMAC_USE_POWER_DOWN_MODE
    #define niEMAC_USE_POWER_DOWN_MODE    ipconfigDISABLE
#endif

#ifndef niEMAC_USE_LPI_MODE
    #define niEMAC_USE_LPI_MODE           ipconfigDISABLE
#endif

#ifndef niEMAC_USE_WAKEUP_FILTER
    #define niEMAC_USE_WAKEUP_FILTER      ipconfigDISABLE
#endif

#ifndef niEMAC_WAKEUP_FILTER_COUNT
    #define niEMAC_WAKEUP_FILTER_COUNT    0U
#endif

#ifndef niEMAC_WAKEUP_FILTER_WORD0
    #define niEMAC_WAKEUP_FILTER_WORD0    0U
#endif

#ifndef niEMAC_WAKEUP_FILTER_WORD1
    #define niEMAC_WAKEUP_FILTER_WORD1    0U
#endif

#ifndef niEMAC_WAKEUP_FILTER_WORD2
    #define niEMAC_WAKEUP_FILTER_WORD2    0U
#endif

#ifndef niEMAC_WAKEUP_FILTER_WORD3
    #define niEMAC_WAKEUP_FILTER_WORD3    0U
#endif

#ifndef niEMAC_WAKEUP_FILTER_WORD4
    #define niEMAC_WAKEUP_FILTER_WORD4    0U
#endif

#ifndef niEMAC_WAKEUP_FILTER_WORD5
    #define niEMAC_WAKEUP_FILTER_WORD5    0U
#endif

#ifndef niEMAC_WAKEUP_FILTER_WORD6
    #define niEMAC_WAKEUP_FILTER_WORD6    0U
#endif

#ifndef niEMAC_WAKEUP_FILTER_WORD7
    #define niEMAC_WAKEUP_FILTER_WORD7    0U
#endif

#if defined( niEMAC_STM32HX )
    #ifndef niEMAC_VLAN_TX_TAG_SELECT
        #define niEMAC_VLAN_TX_TAG_SELECT             ETH_OUTER_TX_VLANTAG
    #endif

    #ifndef niEMAC_VLAN_TX_TAG_FROM_DESCRIPTOR
        #define niEMAC_VLAN_TX_TAG_FROM_DESCRIPTOR    ipconfigENABLE
    #endif

    #ifndef niEMAC_VLAN_TX_SVLAN_TYPE
        #define niEMAC_VLAN_TX_SVLAN_TYPE             ipconfigDISABLE
    #endif

    #ifndef niEMAC_VLAN_TX_TAG_CONTROL
        #define niEMAC_VLAN_TX_TAG_CONTROL            ETH_VLANTAGCONTROL_INSERT
    #endif

    #ifndef niEMAC_VLAN_HASH_TABLE_ENABLE
        #define niEMAC_VLAN_HASH_TABLE_ENABLE         ipconfigDISABLE
    #endif

    #ifndef niEMAC_VLAN_HASH_TABLE
        #define niEMAC_VLAN_HASH_TABLE                0U
    #endif
#endif

#if defined( HAL_ETH_USE_PTP )

    #ifndef niEMAC_PTP_INIT_TIME_ENABLE
        #define niEMAC_PTP_INIT_TIME_ENABLE           ipconfigDISABLE
    #endif

    #ifndef niEMAC_PTP_INIT_TIME_SECONDS
        #define niEMAC_PTP_INIT_TIME_SECONDS          0U
    #endif

    #ifndef niEMAC_PTP_INIT_TIME_NANOSECONDS
        #define niEMAC_PTP_INIT_TIME_NANOSECONDS      0U
    #endif

    #ifndef niEMAC_PTP_INIT_OFFSET_ENABLE
        #define niEMAC_PTP_INIT_OFFSET_ENABLE         ipconfigDISABLE
    #endif

    #ifndef niEMAC_PTP_INIT_OFFSET_SIGN
        #define niEMAC_PTP_INIT_OFFSET_SIGN           HAL_ETH_PTP_POSITIVE_UPDATE
    #endif

    #ifndef niEMAC_PTP_INIT_OFFSET_SECONDS
        #define niEMAC_PTP_INIT_OFFSET_SECONDS        0U
    #endif

    #ifndef niEMAC_PTP_INIT_OFFSET_NANOSECONDS
        #define niEMAC_PTP_INIT_OFFSET_NANOSECONDS    0U
    #endif

    #ifndef niEMAC_PTP_TIMESTAMP_ALL
        #define niEMAC_PTP_TIMESTAMP_ALL              ipconfigDISABLE
    #endif

    #ifndef niEMAC_PTP_TIMESTAMP_MASTER
        #define niEMAC_PTP_TIMESTAMP_MASTER           ipconfigDISABLE
    #endif

    #ifndef niEMAC_PTP_TIMESTAMP_FILTER
        #define niEMAC_PTP_TIMESTAMP_FILTER           ipconfigDISABLE
    #endif

    #if defined( niEMAC_STM32HX )
        #ifndef niEMAC_PTP_TIMESTAMP_SNAPSHOTS
            #define niEMAC_PTP_TIMESTAMP_SNAPSHOTS            0U
        #endif

        #ifndef niEMAC_PTP_TIMESTAMP_CHECKSUM_CORRECTION
            #define niEMAC_PTP_TIMESTAMP_CHECKSUM_CORRECTION  ipconfigDISABLE
        #endif

        #ifndef niEMAC_PTP_TIMESTAMP_STATUS_MODE
            #define niEMAC_PTP_TIMESTAMP_STATUS_MODE          ipconfigENABLE
        #endif
    #endif

    #ifndef niEMAC_PTP_TX_TIMESTAMP_HOOK
        #define niEMAC_PTP_TX_TIMESTAMP_HOOK( pxInterface, pxDescriptor, pxTimestamp ) \
    do                                                                                   \
    {                                                                                    \
        ( void ) ( pxInterface );                                                        \
        ( void ) ( pxDescriptor );                                                       \
        ( void ) ( pxTimestamp );                                                        \
    } while( 0 )
    #endif

    #ifndef niEMAC_PTP_RX_TIMESTAMP_HOOK
        #define niEMAC_PTP_RX_TIMESTAMP_HOOK( pxInterface, pxDescriptor, pxTimestamp ) \
    do                                                                                   \
    {                                                                                    \
        ( void ) ( pxInterface );                                                        \
        ( void ) ( pxDescriptor );                                                       \
        ( void ) ( pxTimestamp );                                                        \
    } while( 0 )
    #endif

    #ifndef niEMAC_PTP_TIME_HOOK
        #define niEMAC_PTP_TIME_HOOK( pxInterface, pxTime ) \
    do                                                       \
    {                                                        \
        ( void ) ( pxInterface );                            \
        ( void ) ( pxTime );                                 \
    } while( 0 )
    #endif

#endif /* if defined( HAL_ETH_USE_PTP ) */

#ifndef niEMAC_WAKE_EVENT_HOOK
    #define niEMAC_WAKE_EVENT_HOOK( pxInterface, ulWakeSource ) \
    do                                                           \
    {                                                            \
        ( void ) ( pxInterface );                                \
        ( void ) ( ulWakeSource );                               \
    } while( 0 )
#endif

#ifndef niEMAC_LPI_EVENT_HOOK
    #define niEMAC_LPI_EVENT_HOOK( pxInterface, ulLPIEvent ) \
    do                                                        \
    {                                                         \
        ( void ) ( pxInterface );                             \
        ( void ) ( ulLPIEvent );                              \
    } while( 0 )
#endif

#ifndef niEMAC_USE_MMC_STATS
    #define niEMAC_USE_MMC_STATS           ipconfigDISABLE
#endif

#ifndef niEMAC_MMC_RESET_COUNTERS_ON_INIT
    #define niEMAC_MMC_RESET_COUNTERS_ON_INIT ipconfigENABLE
#endif

#ifndef niEMAC_MMC_RESET_ON_READ
    #define niEMAC_MMC_RESET_ON_READ       ipconfigDISABLE
#endif

#ifndef niEMAC_MMC_COUNTER_FREEZE
    #define niEMAC_MMC_COUNTER_FREEZE      ipconfigDISABLE
#endif

#ifndef niEMAC_MMC_RX_INTERRUPT_UNMASK
    #define niEMAC_MMC_RX_INTERRUPT_UNMASK 0U
#endif

#ifndef niEMAC_MMC_TX_INTERRUPT_UNMASK
    #define niEMAC_MMC_TX_INTERRUPT_UNMASK 0U
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

#if ipconfigIS_ENABLED( niEMAC_USE_JUMBO_FRAMES )
    #define niEMAC_MAX_PAYLOAD_SIZE ETH_JUMBO_FRAME_PAYLOAD
#elif ipconfigIS_ENABLED( niEMAC_USE_2K_PACKETS )
    #define niEMAC_MAX_PAYLOAD_SIZE 2000U
#else
    #define niEMAC_MAX_PAYLOAD_SIZE ETH_MAX_PAYLOAD
#endif

#if ( ipconfigNETWORK_MTU < ETH_MIN_PAYLOAD ) || ( ipconfigNETWORK_MTU > niEMAC_MAX_PAYLOAD_SIZE )
    #error "Unsupported ipconfigNETWORK_MTU size for NetworkInterface"
#endif

#if ipconfigIS_ENABLED( niEMAC_USE_TCP_SEGMENTATION )
    #if !defined( niEMAC_STM32HX )
        #error "niEMAC_USE_TCP_SEGMENTATION is only supported on STM32H5/H7"
    #endif

    #if ipconfigIS_DISABLED( ipconfigUSE_TCP )
        #error "niEMAC_USE_TCP_SEGMENTATION requires ipconfigUSE_TCP"
    #endif

    #if ( niEMAC_TCP_SEGMENTATION_MSS < 64U ) || ( niEMAC_TCP_SEGMENTATION_MSS > 0x3FFFU )
        #error "niEMAC_TCP_SEGMENTATION_MSS must be in [64, 16383]"
    #endif
#endif

#if ipconfigIS_ENABLED( niEMAC_USE_FLOW_CONTROL )
    #if ( niEMAC_FLOW_CONTROL_PAUSE_TIME > 0xFFFFU )
        #error "niEMAC_FLOW_CONTROL_PAUSE_TIME must be in [0, 65535]"
    #endif
#endif

#if ipconfigIS_ENABLED( niEMAC_USE_JUMBO_FRAMES ) && ipconfigIS_ENABLED( niEMAC_USE_2K_PACKETS )
    #error "niEMAC_USE_JUMBO_FRAMES and niEMAC_USE_2K_PACKETS cannot both be enabled"
#endif

#if ipconfigIS_ENABLED( niEMAC_USE_SAIC )
    #if !defined( niEMAC_STM32HX )
        #error "niEMAC_USE_SAIC is only supported on STM32H5/H7"
    #endif
#endif

#if ipconfigIS_ENABLED( niEMAC_USE_INNER_VLAN_OFFLOAD )
    #if !defined( niEMAC_STM32HX )
        #error "niEMAC_USE_INNER_VLAN_OFFLOAD is only supported on STM32H5/H7"
    #endif

    #if ipconfigIS_DISABLED( niEMAC_USE_VLAN_OFFLOAD )
        #error "niEMAC_USE_INNER_VLAN_OFFLOAD requires niEMAC_USE_VLAN_OFFLOAD"
    #endif

    #if ( niEMAC_INNER_VLAN_IDENTIFIER > 0x3FFFFU )
        #error "niEMAC_INNER_VLAN_IDENTIFIER must be in [0, 0x3FFFF]"
    #endif

    #if ( niEMAC_INNER_VLAN_IDENTIFIER != 0U ) && ( niEMAC_VLAN_IDENTIFIER == 0U )
        #error "niEMAC_USE_INNER_VLAN_OFFLOAD with non-zero niEMAC_INNER_VLAN_IDENTIFIER requires non-zero niEMAC_VLAN_IDENTIFIER"
    #endif
#endif

#if ( niEMAC_MMC_RX_INTERRUPT_UNMASK != 0U ) || ( niEMAC_MMC_TX_INTERRUPT_UNMASK != 0U )
    #error "MMC interrupt unmasking is not yet handled by NetworkInterface; keep niEMAC_MMC_RX_INTERRUPT_UNMASK and niEMAC_MMC_TX_INTERRUPT_UNMASK at 0"
#endif

#if ipconfigIS_DISABLED( ipconfigPORT_SUPPRESS_WARNING )

    #if ipconfigIS_DISABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
        #warning "Consider enabling ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM for NetworkInterface"
    #endif

    #if ipconfigIS_ENABLED( niEMAC_USE_TCP_SEGMENTATION ) && ipconfigIS_DISABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
        #warning "niEMAC_USE_TCP_SEGMENTATION requires ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM to be effective"
    #endif

    #if ipconfigIS_DISABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM )
        #warning "Consider enabling ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM for NetworkInterface"
    #endif

    #if ipconfigIS_DISABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES )
        #warning "Consider enabling ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES for NetworkInterface"
    #endif

/* Packet-level acceptance is still applied in this interface. The stack currently has no
 * universal compile-time capability check equivalent to eConsiderFrameForProcessing(). */

/* #if ipconfigIS_DISABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
 #warning "Consider enabling ipconfigETHERNET_DRIVER_FILTERS_PACKETS for NetworkInterface"
 #endif */

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
    #define niEMAC_CACHE_ENABLED         ( _FLD2VAL( SCB_CCR_DC, SCB->CCR ) != 0 )
    #define niEMAC_CACHE_MAINTENANCE     ( ipconfigIS_DISABLED( niEMAC_USE_MPU ) && niEMAC_CACHE_ENABLED )
    #ifdef __SCB_DCACHE_LINE_SIZE
        #define niEMAC_DATA_ALIGNMENT    __SCB_DCACHE_LINE_SIZE
    #else
        #define niEMAC_DATA_ALIGNMENT    32U
    #endif
#else
    #define niEMAC_DATA_ALIGNMENT        portBYTE_ALIGNMENT
#endif

#define niEMAC_DATA_ALIGNMENT_MASK       ( niEMAC_DATA_ALIGNMENT - 1U )
#define niEMAC_BUF_ALIGNMENT             32U
#define niEMAC_BUF_ALIGNMENT_MASK        ( niEMAC_BUF_ALIGNMENT - 1U )

#define niEMAC_DATA_BUFFER_SIZE          ( ( ipTOTAL_ETHERNET_FRAME_SIZE + niEMAC_DATA_ALIGNMENT_MASK ) & ~niEMAC_DATA_ALIGNMENT_MASK )
#define niEMAC_TOTAL_BUFFER_SIZE         ( ( ( niEMAC_DATA_BUFFER_SIZE + ipBUFFER_PADDING ) + niEMAC_BUF_ALIGNMENT_MASK ) & ~niEMAC_BUF_ALIGNMENT_MASK )

#if defined( niEMAC_STM32FX )

    #undef ETH_DMA_TX_BUFFER_UNAVAILABLE_FLAG
    #define ETH_DMA_TX_BUFFER_UNAVAILABLE_FLAG    ETH_DMASR_TBUS

/* Note: ETH_CTRLPACKETS_BLOCK_ALL is incorrectly defined in HAL ETH Driver as of F7 V1.17.1 && F4 V1.28.0 */
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

    #undef ETH_DMA_TX_BUFFER_UNAVAILABLE_FLAG
    #define ETH_DMA_TX_BUFFER_UNAVAILABLE_FLAG    ETH_DMACSR_TBU

    #undef ETH_IP_PAYLOAD_IGMP
    #define ETH_IP_PAYLOAD_IGMP                   0x4U

#endif /* if defined( niEMAC_STM32FX ) */

#define ETH_IP_PAYLOAD_MASK           0x7U

/* IEEE 802.3 CRC32 polynomial - 0x04C11DB7 */
#define niEMAC_CRC_POLY               0x04C11DB7
#define niEMAC_MAC_IS_MULTICAST( MAC )    ( ( MAC[ 0 ] & 1U ) != 0 )
#define niEMAC_MAC_IS_UNICAST( MAC )      ( ( MAC[ 0 ] & 1U ) == 0 )
#define niEMAC_ADDRESS_HASH_BITS      64U
#define niEMAC_MAC_SRC_MATCH_COUNT    3U

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
    eMacEventTxPending = 1 << 7,
    eMacEventAll = ( 1 << 8 ) - 1,
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

struct xEMACData;

typedef struct xTxPacketMeta
{
    struct xEMACData * pxEMACData;
    NetworkBufferDescriptor_t * pxDescriptor;
    size_t uxDescCount;
    BaseType_t xInUse;
} TxPacketMeta_t;

typedef struct xEMACData
{
    ETH_HandleTypeDef xEthHandle;
    EthernetPhy_t xPhyObject;
    TaskHandle_t xEMACTaskHandle;
    SemaphoreHandle_t xTxMutex;
    SemaphoreHandle_t xTxDescSem;
    QueueHandle_t xTxQueue;
    BaseType_t xSwitchRequired;
    BaseType_t xDropCurrentRxFrame;
    BaseType_t xVLANEnabled;
    BaseType_t xPowerDownActive;
    BaseType_t xLpiActive;
    BaseType_t xPTPConfigured;
    BaseType_t xPTPTimeInitialized;
    eMAC_INIT_STATUS_TYPE xMacInitStatus;
    BaseType_t xEMACIndex;
    TickType_t xLastFilterRefreshTick;
    uint16_t usVLANIdentifier;
    uint8_t ucSrcMatchCounters[ niEMAC_MAC_SRC_MATCH_COUNT ];
    uint8_t uxMACEntryIndex;
    uint32_t ulHashTable[ niEMAC_ADDRESS_HASH_BITS / 32 ];
    uint8_t ucAddrHashCounters[ niEMAC_ADDRESS_HASH_BITS ];
    uint32_t ulCurrentARPOffloadAddress;
    uint32_t ulCurrentL4FilterPort;
    uint32_t ulLastWakeUpSource;
    uint32_t ulLastLPIEvent;
#if defined( HAL_ETH_USE_PTP )
    ETH_TimeStampTypeDef xLastTxTimeStamp;
    ETH_TimeStampTypeDef xLastRxTimeStamp;
    ETH_TimeTypeDef xLastPTPTime;
#endif
    TxPacketMeta_t xTxPacketMeta[ ETH_TX_DESC_CNT ];
#if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION )
    StaticSemaphore_t xTxMutexBuf;
    StaticSemaphore_t xTxDescSemBuf;
    StaticQueue_t xTxQueueBuf;
    NetworkBufferDescriptor_t * pxTxQueueStorage[ niEMAC_TX_QUEUE_LENGTH ];
#endif
} EMACData_t;

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                      Static Function Declarations                         */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

/* Phy Hooks */
static BaseType_t prvPhyReadReg( BaseType_t xAddress,
                                 BaseType_t xRegister,
                                 uint32_t * pulValue );
static BaseType_t prvPhyWriteReg( BaseType_t xAddress,
                                  BaseType_t xRegister,
                                  uint32_t ulValue );

/* Network Interface Access Hooks */
static EMACData_t * prvGetEMACData( const NetworkInterface_t * pxInterface );
static EMACData_t * prvGetEMACDataByEthHandle( const ETH_HandleTypeDef * pxEthHandle );
static NetworkInterface_t * prvGetInterfaceByEMACData( const EMACData_t * pxEMACData );
#if defined( HAL_ETH_USE_PTP )
    static void prvCapturePTPTime( ETH_HandleTypeDef * pxEthHandle,
                                   EMACData_t * pxEMACData,
                                   NetworkInterface_t * pxInterface );
    #if ipconfigIS_ENABLED( niEMAC_USE_PTP )
        static BaseType_t prvShouldCapturePTPRxTimestamp( const NetworkBufferDescriptor_t * pxDescriptor );
    #endif
#endif
static void prvWakeEMACTaskFromISR( EMACData_t * pxEMACData,
                                    eMAC_IF_EVENT eEvents );
static void vForceRefreshPhyLinkStatus( EthernetPhy_t * pxPhyObject );
static BaseType_t prvGetPhyLinkStatus( NetworkInterface_t * pxInterface );
static BaseType_t prvNetworkInterfaceInitialise( NetworkInterface_t * pxInterface );
static BaseType_t prvNetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                             NetworkBufferDescriptor_t * const pxDescriptor,
                                             BaseType_t xReleaseAfterSend );
static void prvAddAllowedMACAddress( NetworkInterface_t * pxInterface,
                                     const uint8_t * pucMacAddress );
static void prvRemoveAllowedMACAddress( NetworkInterface_t * pxInterface,
                                        const uint8_t * pucMacAddress );

/* Error Recovery */
static void prvReconfigurePeripherals( ETH_HandleTypeDef * pxEthHandle,
                                       EMACData_t * pxEMACData,
                                       NetworkInterface_t * pxInterface );
static void prvRecoverFromCriticalError( ETH_HandleTypeDef * pxEthHandle,
                                         EMACData_t * pxEMACData,
                                         const EthernetPhy_t * pxPhyObject,
                                         NetworkInterface_t * pxInterface );

/* EMAC Task */
static BaseType_t prvNetworkInterfaceInput( ETH_HandleTypeDef * pxEthHandle,
                                            NetworkInterface_t * pxInterface );
static __NO_RETURN portTASK_FUNCTION_PROTO( prvEMACHandlerTask,
                                            pvParameters );
static BaseType_t prvEMACTaskStart( NetworkInterface_t * pxInterface );
static BaseType_t prvTransmitNetworkBuffer( NetworkInterface_t * pxInterface,
                                            NetworkBufferDescriptor_t * const pxDescriptor,
                                            BaseType_t xAllowQueue );
#if defined( niEMAC_STM32HX ) && ipconfigIS_ENABLED( niEMAC_USE_TCP_SEGMENTATION ) && ipconfigIS_ENABLED( ipconfigUSE_TCP )
    static BaseType_t prvSetTCPSegmentationConfig( const NetworkBufferDescriptor_t * pxDescriptor,
                                                   size_t uxTotalLength,
                                                   ETH_TxPacketConfigTypeDef * pxTxConfig );
#endif
static void prvProcessTxQueue( NetworkInterface_t * pxInterface );

/* EMAC Init */
static BaseType_t prvEthConfigInit( ETH_HandleTypeDef * pxEthHandle,
                                    NetworkInterface_t * pxInterface );
static BaseType_t prvApplyMACDMAConfig( ETH_HandleTypeDef * pxEthHandle,
                                        const EthernetPhy_t * pxPhyObject );
static void prvConfigureMMCStatistics( ETH_HandleTypeDef * pxEthHandle );
static void prvInitMacAddresses( ETH_HandleTypeDef * pxEthHandle,
                                 NetworkInterface_t * pxInterface );
static void prvConfigureVLAN( ETH_HandleTypeDef * pxEthHandle,
                              NetworkInterface_t * pxInterface );
#if defined( HAL_ETH_USE_PTP )
    static void prvConfigurePTP( ETH_HandleTypeDef * pxEthHandle,
                                 EMACData_t * pxEMACData );
#endif
static void prvConfigurePowerMode( ETH_HandleTypeDef * pxEthHandle,
                                   EMACData_t * pxEMACData,
                                   BaseType_t xLinkIsUp );
#ifdef niEMAC_STM32HX
    static void prvInitPacketFilter( ETH_HandleTypeDef * pxEthHandle,
                                     const NetworkInterface_t * const pxInterface );
#if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
    static void prvConfigureARPOffload( ETH_HandleTypeDef * pxEthHandle,
                                        const NetworkInterface_t * pxInterface );
#endif
#endif
static BaseType_t prvPhyInit( EthernetPhy_t * pxPhyObject );
static BaseType_t prvPhyStart( ETH_HandleTypeDef * pxEthHandle,
                               NetworkInterface_t * pxInterface,
                               EthernetPhy_t * pxPhyObject );

/* MAC Filtering Helpers */
static uint32_t prvCalcCrc32( const uint8_t * const pucMACAddr );
static uint8_t prvGetMacHashIndex( const uint8_t * const pucMACAddr );
static void prvHAL_ETH_SetDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                            uint8_t ucIndex,
                                            const uint8_t * const pucMACAddr );
static void prvHAL_ETH_ClearDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                              uint8_t ucIndex );
static BaseType_t prvAddDestMACAddrMatch( EMACData_t * pxEMACData,
                                          ETH_TypeDef * const pxEthInstance,
                                          const uint8_t * const pucMACAddr );
static BaseType_t prvRemoveDestMACAddrMatch( EMACData_t * pxEMACData,
                                             ETH_TypeDef * const pxEthInstance,
                                             const uint8_t * const pucMACAddr );
static BaseType_t prvSetNewDestMACAddrMatch( EMACData_t * pxEMACData,
                                             ETH_TypeDef * const pxEthInstance,
                                             uint8_t ucHashIndex,
                                             const uint8_t * const pucMACAddr );
static void prvAddDestMACAddrHash( EMACData_t * pxEMACData,
                                   ETH_HandleTypeDef * pxEthHandle,
                                   uint8_t ucHashIndex );
static void prvRemoveDestMACAddrHash( EMACData_t * pxEMACData,
                                      ETH_HandleTypeDef * pxEthHandle,
                                      const uint8_t * const pucMACAddr );

/* EMAC Helpers */
static void prvReleaseTxPacket( ETH_HandleTypeDef * pxEthHandle );
static BaseType_t prvMacUpdateConfig( ETH_HandleTypeDef * pxEthHandle,
                                      EthernetPhy_t * pxPhyObject );
static void prvReleaseNetworkBufferDescriptor( NetworkBufferDescriptor_t * const pxDescriptor );
static void prvSendRxEvent( NetworkBufferDescriptor_t * const pxDescriptor );
static BaseType_t prvAcceptPacket( EMACData_t * pxEMACData,
                                   const NetworkBufferDescriptor_t * const pxDescriptor,
                                   uint16_t usLength );
#if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
    static eFrameProcessingResult_t eConsiderPacketForProcessing( const uint8_t * const pucEthernetBuffer );
#endif

/* Network Interface Definition */
NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                      NetworkInterface_t * pxInterface );

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                      Static Variable Declarations                         */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static EMACData_t xEMACData[ niEMAC_MAX_INTERFACE_NAMES ];
static NetworkInterface_t * pxInterfaces[ niEMAC_MAX_INTERFACE_NAMES ] = { 0 };
static volatile EMACData_t * pxActiveEMACData = NULL;

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              Phy Hooks                                    */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static EMACData_t * prvGetEMACData( const NetworkInterface_t * pxInterface )
{
    if( pxInterface == NULL )
    {
        return NULL;
    }

    return ( EMACData_t * ) pxInterface->pvArgument;
}

static EMACData_t * prvGetEMACDataByEthHandle( const ETH_HandleTypeDef * pxEthHandle )
{
    if( pxEthHandle == NULL )
    {
        return NULL;
    }

    for( UBaseType_t uxIndex = 0U; uxIndex < niEMAC_MAX_INTERFACE_NAMES; uxIndex++ )
    {
        if( &( xEMACData[ uxIndex ].xEthHandle ) == pxEthHandle )
        {
            return &( xEMACData[ uxIndex ] );
        }
    }

    if( ( pxActiveEMACData != NULL ) && ( &( ( ( EMACData_t * ) pxActiveEMACData )->xEthHandle ) == pxEthHandle ) )
    {
        return ( EMACData_t * ) pxActiveEMACData;
    }

    return NULL;
}

static NetworkInterface_t * prvGetInterfaceByEMACData( const EMACData_t * pxEMACData )
{
    if( pxEMACData == NULL )
    {
        return NULL;
    }

    const UBaseType_t uxIndex = ( UBaseType_t ) pxEMACData->xEMACIndex;

    if( uxIndex >= niEMAC_MAX_INTERFACE_NAMES )
    {
        return NULL;
    }

    return pxInterfaces[ uxIndex ];
}

#if defined( HAL_ETH_USE_PTP )

    static void prvCapturePTPTime( ETH_HandleTypeDef * pxEthHandle,
                                   EMACData_t * pxEMACData,
                                   NetworkInterface_t * pxInterface )
    {
        if( ( pxEthHandle == NULL ) ||
            ( pxEMACData == NULL ) ||
            ( pxEMACData->xPTPConfigured == pdFALSE ) )
        {
            return;
        }

        ETH_TimeTypeDef xTime;

        if( HAL_ETH_PTP_GetTime( pxEthHandle, &xTime ) != HAL_OK )
        {
            return;
        }

        pxEMACData->xLastPTPTime = xTime;

        if( pxInterface == NULL )
        {
            pxInterface = prvGetInterfaceByEMACData( pxEMACData );
        }

        niEMAC_PTP_TIME_HOOK( pxInterface, &( pxEMACData->xLastPTPTime ) );
    }

    #if ipconfigIS_ENABLED( niEMAC_USE_PTP )

        static BaseType_t prvShouldCapturePTPRxTimestamp( const NetworkBufferDescriptor_t * pxDescriptor )
        {
            if( ( pxDescriptor == NULL ) ||
                ( pxDescriptor->pucEthernetBuffer == NULL ) ||
                ( pxDescriptor->xDataLength < sizeof( EthernetHeader_t ) ) )
            {
                return pdFALSE;
            }

            const EthernetHeader_t * const pxEthernetHeader = ( const EthernetHeader_t * const ) pxDescriptor->pucEthernetBuffer;

            if( pxEthernetHeader->usFrameType == ipIPv4_FRAME_TYPE )
            {
                #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
                {
                    if( pxDescriptor->xDataLength < sizeof( UDPPacket_t ) )
                    {
                        return pdFALSE;
                    }

                    const IPPacket_t * const pxIPPacket = ( const IPPacket_t * const ) pxDescriptor->pucEthernetBuffer;

                    if( pxIPPacket->xIPHeader.ucProtocol != ipPROTOCOL_UDP )
                    {
                        return pdFALSE;
                    }

                    const UDPPacket_t * const pxUDPPacket = ( const UDPPacket_t * const ) pxDescriptor->pucEthernetBuffer;
                    const uint16_t usSourcePort = FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usSourcePort );
                    const uint16_t usDestinationPort = FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usDestinationPort );

                    if( ( usSourcePort == niEMAC_PTP_EVENT_UDP_PORT ) ||
                        ( usSourcePort == niEMAC_PTP_GENERAL_UDP_PORT ) ||
                        ( usDestinationPort == niEMAC_PTP_EVENT_UDP_PORT ) ||
                        ( usDestinationPort == niEMAC_PTP_GENERAL_UDP_PORT ) )
                    {
                        return pdTRUE;
                    }
                }
                #endif
            }
            else if( pxEthernetHeader->usFrameType == ipIPv6_FRAME_TYPE )
            {
                #if ipconfigIS_ENABLED( ipconfigUSE_IPv6 )
                {
                    if( pxDescriptor->xDataLength < sizeof( UDPPacket_IPv6_t ) )
                    {
                        return pdFALSE;
                    }

                    const IPPacket_IPv6_t * const pxIPPacket_IPv6 = ( const IPPacket_IPv6_t * const ) pxDescriptor->pucEthernetBuffer;

                    if( pxIPPacket_IPv6->xIPHeader.ucNextHeader != ipPROTOCOL_UDP )
                    {
                        return pdFALSE;
                    }

                    const UDPPacket_IPv6_t * const pxUDPPacket_IPv6 = ( const UDPPacket_IPv6_t * const ) pxDescriptor->pucEthernetBuffer;
                    const uint16_t usSourcePort = FreeRTOS_ntohs( pxUDPPacket_IPv6->xUDPHeader.usSourcePort );
                    const uint16_t usDestinationPort = FreeRTOS_ntohs( pxUDPPacket_IPv6->xUDPHeader.usDestinationPort );

                    if( ( usSourcePort == niEMAC_PTP_EVENT_UDP_PORT ) ||
                        ( usSourcePort == niEMAC_PTP_GENERAL_UDP_PORT ) ||
                        ( usDestinationPort == niEMAC_PTP_EVENT_UDP_PORT ) ||
                        ( usDestinationPort == niEMAC_PTP_GENERAL_UDP_PORT ) )
                    {
                        return pdTRUE;
                    }
                }
                #endif
            }

            return pdFALSE;
        }

    #endif /* if ipconfigIS_ENABLED( niEMAC_USE_PTP ) */

#endif /* if defined( HAL_ETH_USE_PTP ) */

static void prvWakeEMACTaskFromISR( EMACData_t * pxEMACData,
                                    eMAC_IF_EVENT eEvents )
{
    if( ( pxEMACData == NULL ) ||
        ( pxEMACData->xEMACTaskHandle == NULL ) ||
        ( eEvents == eMacEventNone ) )
    {
        return;
    }

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    ( void ) xTaskNotifyFromISR( pxEMACData->xEMACTaskHandle, eEvents, eSetBits, &xHigherPriorityTaskWoken );
    pxEMACData->xSwitchRequired |= xHigherPriorityTaskWoken;
}

static BaseType_t prvPhyReadReg( BaseType_t xAddress,
                                 BaseType_t xRegister,
                                 uint32_t * pulValue )
{
    BaseType_t xResult = 0;

    if( ( pxActiveEMACData == NULL ) ||
        ( HAL_ETH_ReadPHYRegister( &( ( ( EMACData_t * ) pxActiveEMACData )->xEthHandle ), ( uint32_t ) xAddress, ( uint32_t ) xRegister, pulValue ) != HAL_OK ) )
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

    if( ( pxActiveEMACData == NULL ) ||
        ( HAL_ETH_WritePHYRegister( &( ( ( EMACData_t * ) pxActiveEMACData )->xEthHandle ), ( uint32_t ) xAddress, ( uint32_t ) xRegister, ulValue ) != HAL_OK ) )
    {
        xResult = -1;
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                      Network Interface Access Hooks                       */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

static void vForceRefreshPhyLinkStatus( EthernetPhy_t * pxPhyObject )
{
    vTaskSetTimeOutState( &( pxPhyObject->xLinkStatusTimer ) );
    pxPhyObject->xLinkStatusRemaining = 0U;
    xPhyCheckLinkStatus( pxPhyObject, pdFALSE );
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvGetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    const EMACData_t * pxEMACData = prvGetEMACData( pxInterface );

    if( ( pxEMACData != NULL ) && ( pxEMACData->xPhyObject.ulLinkStatusMask != 0U ) )
    {
        return pdTRUE;
    }

    return pdFALSE;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    EMACData_t * pxEMACData = prvGetEMACData( pxInterface );
    ETH_HandleTypeDef * pxEthHandle;
    EthernetPhy_t * pxPhyObject;
    BaseType_t xInitResult = pdFAIL;

    if( pxEMACData == NULL )
    {
        return pdFAIL;
    }

    pxActiveEMACData = pxEMACData;
    pxEthHandle = &( pxEMACData->xEthHandle );
    pxPhyObject = &( pxEMACData->xPhyObject );

    switch( pxEMACData->xMacInitStatus )
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

            pxEMACData->xMacInitStatus = eMacPhyInit;
        /* fallthrough */

        case eMacPhyInit:

            if( prvPhyInit( pxPhyObject ) == pdFALSE )
            {
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInitialise: eMacPhyInit failed\n" ) );
                break;
            }

            pxEMACData->xMacInitStatus = eMacPhyStart;
        /* fallthrough */

        case eMacPhyStart:

            if( prvPhyStart( pxEthHandle, pxInterface, pxPhyObject ) == pdFALSE )
            {
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInitialise: eMacPhyStart failed\n" ) );
                break;
            }

            pxEMACData->xMacInitStatus = eMacTaskStart;
        /* fallthrough */

        case eMacTaskStart:

            if( prvEMACTaskStart( pxInterface ) == pdFALSE )
            {
                FreeRTOS_debug_printf( ( "prvNetworkInterfaceInitialise: eMacTaskStart failed\n" ) );
                break;
            }

            pxEMACData->xMacInitStatus = eMacEthStart;
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

            prvConfigurePowerMode( pxEthHandle, pxEMACData, pdTRUE );

            pxEMACData->xMacInitStatus = eMacInitComplete;
        /* fallthrough */

        case eMacInitComplete:
            vForceRefreshPhyLinkStatus( pxPhyObject );

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

static BaseType_t prvNetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                             NetworkBufferDescriptor_t * const pxDescriptor,
                                             BaseType_t xReleaseAfterSend )
{
    /* Zero-Copy Only */
    configASSERT( xReleaseAfterSend == pdTRUE );

    const BaseType_t xResult = prvTransmitNetworkBuffer( pxInterface, pxDescriptor, pdTRUE );

    if( xResult != pdPASS )
    {
        prvReleaseNetworkBufferDescriptor( pxDescriptor );
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static TxPacketMeta_t * prvAllocateTxPacketMeta( EMACData_t * pxEMACData,
                                                 NetworkBufferDescriptor_t * pxDescriptor,
                                                 size_t uxDescCount )
{
    for( UBaseType_t uxIndex = 0U; uxIndex < ETH_TX_DESC_CNT; uxIndex++ )
    {
        TxPacketMeta_t * const pxTxMeta = &( pxEMACData->xTxPacketMeta[ uxIndex ] );

        if( pxTxMeta->xInUse == pdFALSE )
        {
            pxTxMeta->xInUse = pdTRUE;
            pxTxMeta->pxEMACData = pxEMACData;
            pxTxMeta->pxDescriptor = pxDescriptor;
            pxTxMeta->uxDescCount = uxDescCount;
            return pxTxMeta;
        }
    }

    return NULL;
}

static BaseType_t prvQueueTxPacket( EMACData_t * pxEMACData,
                                    NetworkBufferDescriptor_t * pxDescriptor )
{
    if( ( pxEMACData->xTxQueue == NULL ) ||
        ( xQueueSendToBack( pxEMACData->xTxQueue, &pxDescriptor, 0U ) != pdPASS ) )
    {
        return pdFAIL;
    }

    if( pxEMACData->xEMACTaskHandle != NULL )
    {
        ( void ) xTaskNotify( pxEMACData->xEMACTaskHandle, eMacEventTxPending, eSetBits );
    }

    return pdPASS;
}

#if defined( niEMAC_STM32HX ) && ipconfigIS_ENABLED( niEMAC_USE_TCP_SEGMENTATION ) && ipconfigIS_ENABLED( ipconfigUSE_TCP )

    static BaseType_t prvSetTCPSegmentationConfig( const NetworkBufferDescriptor_t * pxDescriptor,
                                                   size_t uxTotalLength,
                                                   ETH_TxPacketConfigTypeDef * pxTxConfig )
    {
        if( ( pxDescriptor == NULL ) ||
            ( pxDescriptor->pucEthernetBuffer == NULL ) ||
            ( pxTxConfig == NULL ) ||
            ( pxDescriptor->xDataLength < sizeof( EthernetHeader_t ) ) )
        {
            return pdFALSE;
        }

        const uint8_t * const pucEthernetBuffer = pxDescriptor->pucEthernetBuffer;
        const EthernetHeader_t * const pxEthernetHeader = ( const EthernetHeader_t * const ) pucEthernetBuffer;
        size_t uxHeaderPrefix = 0U;
        size_t uxTCPHeaderLengthBytes = 0U;

        if( pxEthernetHeader->usFrameType == ipIPv4_FRAME_TYPE )
        {
            #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
            {
                if( pxDescriptor->xDataLength < sizeof( IPPacket_t ) )
                {
                    return pdFALSE;
                }

                const IPPacket_t * const pxIPPacket = ( const IPPacket_t * const ) pucEthernetBuffer;

                if( pxIPPacket->xIPHeader.ucProtocol != ipPROTOCOL_TCP )
                {
                    return pdFALSE;
                }

                const size_t uxIPHeaderLength = ( size_t ) ( pxIPPacket->xIPHeader.ucVersionHeaderLength & 0x0FU ) << 2U;

                if( uxIPHeaderLength < ipSIZE_OF_IPv4_HEADER )
                {
                    return pdFALSE;
                }

                uxHeaderPrefix = sizeof( EthernetHeader_t ) + uxIPHeaderLength;
            }
            #else
                return pdFALSE;
            #endif
        }
        else if( pxEthernetHeader->usFrameType == ipIPv6_FRAME_TYPE )
        {
            #if ipconfigIS_ENABLED( ipconfigUSE_IPv6 )
            {
                if( pxDescriptor->xDataLength < sizeof( IPPacket_IPv6_t ) )
                {
                    return pdFALSE;
                }

                const IPPacket_IPv6_t * const pxIPPacket_IPv6 = ( const IPPacket_IPv6_t * const ) pucEthernetBuffer;

                if( pxIPPacket_IPv6->xIPHeader.ucNextHeader != ipPROTOCOL_TCP )
                {
                    return pdFALSE;
                }

                uxHeaderPrefix = sizeof( EthernetHeader_t ) + ipSIZE_OF_IPv6_HEADER;
            }
            #else
                return pdFALSE;
            #endif
        }
        else
        {
            return pdFALSE;
        }

        if( pxDescriptor->xDataLength < ( uxHeaderPrefix + sizeof( TCPHeader_t ) ) )
        {
            return pdFALSE;
        }

        const TCPHeader_t * const pxTCPHeader = ( const TCPHeader_t * const ) &( pucEthernetBuffer[ uxHeaderPrefix ] );
        uxTCPHeaderLengthBytes = ( size_t ) ( pxTCPHeader->ucTCPOffset & 0xF0U ) >> 2U;

        if( ( uxTCPHeaderLengthBytes < ipSIZE_OF_TCP_HEADER ) ||
            ( uxTCPHeaderLengthBytes > 60U ) ||
            ( ( uxTCPHeaderLengthBytes & 0x03U ) != 0U ) ||
            ( pxDescriptor->xDataLength < ( uxHeaderPrefix + uxTCPHeaderLengthBytes ) ) )
        {
            return pdFALSE;
        }

        const size_t uxPayloadLength = ( uxTotalLength > ( uxHeaderPrefix + uxTCPHeaderLengthBytes ) ) ?
                                       ( uxTotalLength - ( uxHeaderPrefix + uxTCPHeaderLengthBytes ) ) :
                                       0U;

        if( uxPayloadLength <= niEMAC_TCP_SEGMENTATION_MSS )
        {
            return pdFALSE;
        }

        const size_t uxTCPHeaderLengthWords = uxTCPHeaderLengthBytes >> 2U;

        if( ( uxTCPHeaderLengthWords < 5U ) || ( uxTCPHeaderLengthWords > 15U ) )
        {
            return pdFALSE;
        }

        configASSERT( uxPayloadLength <= UINT32_MAX );
        pxTxConfig->Attributes |= ETH_TX_PACKETS_FEATURES_TSO;
        pxTxConfig->MaxSegmentSize = ( uint32_t ) niEMAC_TCP_SEGMENTATION_MSS;
        pxTxConfig->PayloadLen = ( uint32_t ) uxPayloadLength;
        pxTxConfig->TCPHeaderLen = ( uint32_t ) uxTCPHeaderLengthWords;
        return pdTRUE;
    }

#endif /* if defined( niEMAC_STM32HX ) && ipconfigIS_ENABLED( niEMAC_USE_TCP_SEGMENTATION ) && ipconfigIS_ENABLED( ipconfigUSE_TCP ) */

static BaseType_t prvTransmitNetworkBuffer( NetworkInterface_t * pxInterface,
                                            NetworkBufferDescriptor_t * const pxDescriptor,
                                            BaseType_t xAllowQueue )
{
    EMACData_t * pxEMACData = prvGetEMACData( pxInterface );

    if( ( pxEMACData == NULL ) ||
        ( pxDescriptor == NULL ) ||
        ( pxDescriptor->pucEthernetBuffer == NULL ) ||
        ( pxDescriptor->xDataLength == 0U ) )
    {
        FreeRTOS_debug_printf( ( "prvTransmitNetworkBuffer: Invalid Descriptor\n" ) );
        return pdFAIL;
    }

    ETH_HandleTypeDef * const pxEthHandle = &( pxEMACData->xEthHandle );

    if( prvGetPhyLinkStatus( pxInterface ) == pdFALSE )
    {
        FreeRTOS_debug_printf( ( "prvTransmitNetworkBuffer: Link Down\n" ) );
        return pdFAIL;
    }

    if( ( pxEMACData->xMacInitStatus != eMacInitComplete ) ||
        ( HAL_ETH_GetState( pxEthHandle ) != HAL_ETH_STATE_STARTED ) )
    {
        FreeRTOS_debug_printf( ( "prvTransmitNetworkBuffer: Interface Not Started\n" ) );
        return pdFAIL;
    }

    ETH_BufferTypeDef xTxBuffers[ niEMAC_TX_MAX_BUFFER_FRAGMENTS ];
    size_t uxTxBufferCount = 0U;
    size_t uxTxDescCount;
    size_t uxTotalLength = 0U;
    const NetworkBufferDescriptor_t * pxTxPart = pxDescriptor;

    while( pxTxPart != NULL )
    {
        if( pxTxPart->pucEthernetBuffer == NULL )
        {
            return pdFAIL;
        }

        size_t uxPartLength = pxTxPart->xDataLength;
        uint8_t * pucPartBuffer = pxTxPart->pucEthernetBuffer;

        while( uxPartLength > 0U )
        {
            if( uxTxBufferCount >= niEMAC_TX_MAX_BUFFER_FRAGMENTS )
            {
                FreeRTOS_debug_printf( ( "prvTransmitNetworkBuffer: Fragmentation overflow\n" ) );
                return pdFAIL;
            }

            const size_t uxCurrentLength = ( uxPartLength > niEMAC_DATA_BUFFER_SIZE ) ? niEMAC_DATA_BUFFER_SIZE : uxPartLength;

            xTxBuffers[ uxTxBufferCount ].buffer = pucPartBuffer;
            xTxBuffers[ uxTxBufferCount ].len = ( uint32_t ) uxCurrentLength;
            xTxBuffers[ uxTxBufferCount ].next = NULL;

            if( uxTxBufferCount > 0U )
            {
                xTxBuffers[ uxTxBufferCount - 1U ].next = &( xTxBuffers[ uxTxBufferCount ] );
            }

            uxTxBufferCount++;
            uxTotalLength += uxCurrentLength;
            uxPartLength -= uxCurrentLength;
            pucPartBuffer = &( pucPartBuffer[ uxCurrentLength ] );
        }

        pxTxPart = pxTxPart->pxNextBuffer;
    }

    if( uxTxBufferCount == 0U )
    {
        return pdFAIL;
    }

    uxTxDescCount = ( uxTxBufferCount + ( niEMAC_TX_BUFFERS_PER_DESC - 1U ) ) / niEMAC_TX_BUFFERS_PER_DESC;

    size_t uxTaken = 0U;

    for( ; uxTaken < uxTxDescCount; uxTaken++ )
    {
        if( xSemaphoreTake( pxEMACData->xTxDescSem, pdMS_TO_TICKS( niEMAC_DESCRIPTOR_WAIT_TIME_MS ) ) == pdFALSE )
        {
            break;
        }
    }

    if( uxTaken != uxTxDescCount )
    {
        while( uxTaken-- > 0U )
        {
            ( void ) xSemaphoreGive( pxEMACData->xTxDescSem );
        }

        if( ( xAllowQueue != pdFALSE ) && ( prvQueueTxPacket( pxEMACData, ( NetworkBufferDescriptor_t * ) pxDescriptor ) == pdPASS ) )
        {
            return pdPASS;
        }

        FreeRTOS_debug_printf( ( "prvTransmitNetworkBuffer: No Descriptors Available\n" ) );
        return pdFAIL;
    }

    if( xSemaphoreTake( pxEMACData->xTxMutex, pdMS_TO_TICKS( niEMAC_TX_MAX_BLOCK_TIME_MS ) ) == pdFALSE )
    {
        for( size_t uxIndex = 0U; uxIndex < uxTxDescCount; uxIndex++ )
        {
            ( void ) xSemaphoreGive( pxEMACData->xTxDescSem );
        }

        if( ( xAllowQueue != pdFALSE ) && ( prvQueueTxPacket( pxEMACData, ( NetworkBufferDescriptor_t * ) pxDescriptor ) == pdPASS ) )
        {
            return pdPASS;
        }

        FreeRTOS_debug_printf( ( "prvTransmitNetworkBuffer: Process Busy\n" ) );
        return pdFAIL;
    }

    ETH_TxPacketConfigTypeDef xTxConfig =
    {
        .CRCPadCtrl = ETH_CRC_PAD_INSERT,
        .Attributes = ETH_TX_PACKETS_FEATURES_CRCPAD,
        .SrcAddrCtrl = niEMAC_SAIC_DISABLED_CONTROL,
        .InnerVlanCtrl = niEMAC_INNER_VLAN_DISABLED_MODE,
    };
    size_t uxContextDescCount = 0U;

    #if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
        xTxConfig.ChecksumCtrl = ETH_CHECKSUM_IPHDR_PAYLOAD_INSERT_PHDR_CALC;
        xTxConfig.Attributes |= ETH_TX_PACKETS_FEATURES_CSUM;
    #else
        xTxConfig.ChecksumCtrl = ETH_CHECKSUM_DISABLE;
    #endif

    #if ipconfigIS_ENABLED( niEMAC_USE_VLAN_OFFLOAD )
        if( pxEMACData->xVLANEnabled != pdFALSE )
        {
            xTxConfig.Attributes |= ETH_TX_PACKETS_FEATURES_VLANTAG;
            xTxConfig.VlanTag = ( uint32_t ) pxEMACData->usVLANIdentifier;
            xTxConfig.VlanCtrl = niEMAC_VLAN_TX_MODE;
            #if defined( niEMAC_STM32HX )
                uxContextDescCount = 1U;

                #if ipconfigIS_ENABLED( niEMAC_USE_INNER_VLAN_OFFLOAD )
                    if( ( niEMAC_INNER_VLAN_IDENTIFIER & 0x3FFFFU ) != 0U )
                    {
                        xTxConfig.Attributes |= ETH_TX_PACKETS_FEATURES_INNERVLANTAG;
                        xTxConfig.InnerVlanTag = ( uint32_t ) ( niEMAC_INNER_VLAN_IDENTIFIER & 0x3FFFFU );
                        xTxConfig.InnerVlanCtrl = ( uint32_t ) niEMAC_INNER_VLAN_TX_MODE;
                    }
                #endif
            #endif
        }
    #endif

    #if ipconfigIS_ENABLED( niEMAC_USE_SAIC )
        xTxConfig.Attributes |= ETH_TX_PACKETS_FEATURES_SAIC;
        xTxConfig.SrcAddrCtrl = ( uint32_t ) niEMAC_SAIC_CONTROL;
    #endif

    const EthernetHeader_t * const pxEthHeader = ( const EthernetHeader_t * const ) pxDescriptor->pucEthernetBuffer;

    if( pxEthHeader->usFrameType == ipIPv4_FRAME_TYPE )
    {
        #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
            const IPPacket_t * const pxIPPacket = ( const IPPacket_t * const ) pxDescriptor->pucEthernetBuffer;

            if( pxIPPacket->xIPHeader.ucProtocol == ipPROTOCOL_ICMP )
            {
                #if ipconfigIS_ENABLED( ipconfigREPLY_TO_INCOMING_PINGS ) || ipconfigIS_ENABLED( ipconfigSUPPORT_OUTGOING_PINGS )
                    ICMPPacket_t * const pxICMPPacket = ( ICMPPacket_t * const ) pxDescriptor->pucEthernetBuffer;
                    #if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
                        pxICMPPacket->xICMPHeader.usChecksum = 0U;
                    #endif
                    ( void ) pxICMPPacket;
                #else
                    ( void ) xSemaphoreGive( pxEMACData->xTxMutex );

                    for( size_t uxIndex = 0U; uxIndex < uxTxDescCount; uxIndex++ )
                    {
                        ( void ) xSemaphoreGive( pxEMACData->xTxDescSem );
                    }

                    return pdFAIL;
                #endif
            }
        #else
            ( void ) xSemaphoreGive( pxEMACData->xTxMutex );

            for( size_t uxIndex = 0U; uxIndex < uxTxDescCount; uxIndex++ )
            {
                ( void ) xSemaphoreGive( pxEMACData->xTxDescSem );
            }

            return pdFAIL;
        #endif
    }

    #if defined( niEMAC_STM32HX ) && ipconfigIS_ENABLED( niEMAC_USE_TCP_SEGMENTATION ) && ipconfigIS_ENABLED( ipconfigUSE_TCP ) && ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM )
        if( prvSetTCPSegmentationConfig( pxDescriptor, uxTotalLength, &xTxConfig ) != pdFALSE )
        {
            uxContextDescCount = 1U;
        }
    #endif

    if( uxContextDescCount > 0U )
    {
        if( xSemaphoreTake( pxEMACData->xTxDescSem, pdMS_TO_TICKS( niEMAC_DESCRIPTOR_WAIT_TIME_MS ) ) == pdFALSE )
        {
            ( void ) xSemaphoreGive( pxEMACData->xTxMutex );

            for( size_t uxIndex = 0U; uxIndex < uxTxDescCount; uxIndex++ )
            {
                ( void ) xSemaphoreGive( pxEMACData->xTxDescSem );
            }

            if( ( xAllowQueue != pdFALSE ) && ( prvQueueTxPacket( pxEMACData, ( NetworkBufferDescriptor_t * ) pxDescriptor ) == pdPASS ) )
            {
                return pdPASS;
            }

            FreeRTOS_debug_printf( ( "prvTransmitNetworkBuffer: No Descriptors Available\n" ) );
            return pdFAIL;
        }

        uxTxDescCount += uxContextDescCount;
    }

    #ifdef niEMAC_CACHEABLE
        if( niEMAC_CACHE_MAINTENANCE != 0 )
        {
            for( size_t uxIndex = 0U; uxIndex < uxTxBufferCount; uxIndex++ )
            {
                const uintptr_t uxDataStart = ( uintptr_t ) xTxBuffers[ uxIndex ].buffer;
                const uintptr_t uxLineStart = uxDataStart & ~niEMAC_DATA_ALIGNMENT_MASK;
                const ptrdiff_t uxDataOffset = uxDataStart - uxLineStart;
                const size_t uxLength = ( size_t ) xTxBuffers[ uxIndex ].len + ( size_t ) uxDataOffset;
                SCB_CleanDCache_by_Addr( ( uint32_t * ) uxLineStart, uxLength );
            }
        }
    #endif

    TxPacketMeta_t * const pxTxMeta = prvAllocateTxPacketMeta( pxEMACData, ( NetworkBufferDescriptor_t * ) pxDescriptor, uxTxDescCount );

    if( pxTxMeta == NULL )
    {
        ( void ) xSemaphoreGive( pxEMACData->xTxMutex );

        for( size_t uxIndex = 0U; uxIndex < uxTxDescCount; uxIndex++ )
        {
            ( void ) xSemaphoreGive( pxEMACData->xTxDescSem );
        }

        if( ( xAllowQueue != pdFALSE ) && ( prvQueueTxPacket( pxEMACData, ( NetworkBufferDescriptor_t * ) pxDescriptor ) == pdPASS ) )
        {
            return pdPASS;
        }

        return pdFAIL;
    }

    xTxConfig.pData = pxTxMeta;
    xTxConfig.TxBuffer = &( xTxBuffers[ 0 ] );
    xTxConfig.Length = ( uint32_t ) uxTotalLength;

    #if defined( HAL_ETH_USE_PTP ) && ipconfigIS_ENABLED( niEMAC_USE_PTP )
        if( pxEMACData->xPTPConfigured != pdFALSE )
        {
            ( void ) HAL_ETH_PTP_InsertTxTimestamp( pxEthHandle );
        }
    #endif

    if( HAL_ETH_Transmit_IT( pxEthHandle, &xTxConfig ) == HAL_OK )
    {
        ( void ) xSemaphoreGive( pxEMACData->xTxMutex );
        return pdPASS;
    }

    pxTxMeta->xInUse = pdFALSE;
    pxTxMeta->pxEMACData = NULL;
    pxTxMeta->pxDescriptor = NULL;
    pxTxMeta->uxDescCount = 0U;

    ( void ) xSemaphoreGive( pxEMACData->xTxMutex );

    for( size_t uxIndex = 0U; uxIndex < uxTxDescCount; uxIndex++ )
    {
        ( void ) xSemaphoreGive( pxEMACData->xTxDescSem );
    }

    if( ( xAllowQueue != pdFALSE ) &&
        ( ( HAL_ETH_GetError( pxEthHandle ) & HAL_ETH_ERROR_BUSY ) != 0U ) &&
        ( prvQueueTxPacket( pxEMACData, ( NetworkBufferDescriptor_t * ) pxDescriptor ) == pdPASS ) )
    {
        return pdPASS;
    }

    return pdFAIL;
}

static void prvProcessTxQueue( NetworkInterface_t * pxInterface )
{
    EMACData_t * const pxEMACData = prvGetEMACData( pxInterface );

    if( ( pxEMACData == NULL ) || ( pxEMACData->xTxQueue == NULL ) )
    {
        return;
    }

    NetworkBufferDescriptor_t * pxQueuedDescriptor;

    while( xQueuePeek( pxEMACData->xTxQueue, &pxQueuedDescriptor, 0U ) == pdPASS )
    {
        if( prvTransmitNetworkBuffer( pxInterface, pxQueuedDescriptor, pdFALSE ) != pdPASS )
        {
            break;
        }

        ( void ) xQueueReceive( pxEMACData->xTxQueue, &pxQueuedDescriptor, 0U );
    }
}

/*---------------------------------------------------------------------------*/

static void prvAddAllowedMACAddress( NetworkInterface_t * pxInterface,
                                     const uint8_t * pucMacAddress )
{
    EMACData_t * const pxEMACData = prvGetEMACData( pxInterface );

    if( pxEMACData == NULL )
    {
        return;
    }

    ETH_HandleTypeDef * const pxEthHandle = &( pxEMACData->xEthHandle );

    /* Keep this path as exact address/hash programming. Mask-byte-control group mode
     * can unintentionally widen the accepted destination set for multi-endpoint use. */
    BaseType_t xResult = prvAddDestMACAddrMatch( pxEMACData, pxEthHandle->Instance, pucMacAddress );

    if( xResult == pdFALSE )
    {
        const uint8_t ucHashIndex = prvGetMacHashIndex( pucMacAddress );

        xResult = prvSetNewDestMACAddrMatch( pxEMACData, pxEthHandle->Instance, ucHashIndex, pucMacAddress );

        if( xResult == pdFALSE )
        {
            prvAddDestMACAddrHash( pxEMACData, pxEthHandle, ucHashIndex );
        }
    }
}

/*---------------------------------------------------------------------------*/

static void prvRemoveAllowedMACAddress( NetworkInterface_t * pxInterface,
                                        const uint8_t * pucMacAddress )
{
    EMACData_t * const pxEMACData = prvGetEMACData( pxInterface );

    if( pxEMACData == NULL )
    {
        return;
    }

    ETH_HandleTypeDef * const pxEthHandle = &( pxEMACData->xEthHandle );

    const BaseType_t xResult = prvRemoveDestMACAddrMatch( pxEMACData, pxEthHandle->Instance, pucMacAddress );

    if( xResult == pdFALSE )
    {
        prvRemoveDestMACAddrHash( pxEMACData, pxEthHandle, pucMacAddress );
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
    EMACData_t * const pxEMACData = prvGetEMACData( pxInterface );
    BaseType_t xResult = pdFALSE;
    UBaseType_t uxCount = 0;

    #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
        NetworkBufferDescriptor_t * pxStartDescriptor = NULL;
        NetworkBufferDescriptor_t * pxEndDescriptor = NULL;
    #endif
    NetworkBufferDescriptor_t * pxCurDescriptor = NULL;

    if( ( pxEMACData != NULL ) &&
        ( pxEMACData->xMacInitStatus == eMacInitComplete ) &&
        ( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_STARTED ) )
    {
        pxActiveEMACData = pxEMACData;

        while( HAL_ETH_ReadData( pxEthHandle, ( void ** ) &pxCurDescriptor ) == HAL_OK )
        {
            if( pxCurDescriptor == NULL )
            {
                /* Buffer was dropped, ignore packet */
                pxEMACData->xDropCurrentRxFrame = pdFALSE;
                continue;
            }

            if( pxEMACData->xDropCurrentRxFrame != pdFALSE )
            {
                pxEMACData->xDropCurrentRxFrame = pdFALSE;
                prvReleaseNetworkBufferDescriptor( pxCurDescriptor );
                continue;
            }

            ++uxCount;

            configASSERT( pxCurDescriptor->xDataLength > 0U );

            #if defined( HAL_ETH_USE_PTP ) && ipconfigIS_ENABLED( niEMAC_USE_PTP )
                if( pxEMACData->xPTPConfigured != pdFALSE )
                {
                    if( prvShouldCapturePTPRxTimestamp( pxCurDescriptor ) != pdFALSE )
                    {
                        ETH_TimeStampTypeDef xRxTimeStamp;

                        if( HAL_ETH_PTP_GetRxTimestamp( pxEthHandle, &xRxTimeStamp ) == HAL_OK )
                        {
                            pxEMACData->xLastRxTimeStamp = xRxTimeStamp;
                            prvCapturePTPTime( pxEthHandle, pxEMACData, pxInterface );
                            niEMAC_PTP_RX_TIMESTAMP_HOOK( pxInterface, pxCurDescriptor, &( pxEMACData->xLastRxTimeStamp ) );
                        }
                    }
                }
            #endif

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
            #else /* if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) */
                prvSendRxEvent( pxCurDescriptor );
            #endif /* if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES ) */
        }
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

static void prvReconfigurePeripherals( ETH_HandleTypeDef * pxEthHandle,
                                       EMACData_t * pxEMACData,
                                       NetworkInterface_t * pxInterface )
{
    prvConfigureVLAN( pxEthHandle, pxInterface );
    #if defined( HAL_ETH_USE_PTP )
        prvConfigurePTP( pxEthHandle, pxEMACData );
    #else
        ( void ) pxEMACData;
    #endif
    #if defined( niEMAC_STM32HX )
        prvInitPacketFilter( pxEthHandle, pxInterface );
    #endif
    #if defined( niEMAC_STM32HX ) && ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
        prvConfigureARPOffload( pxEthHandle, pxInterface );
    #endif
}

/*---------------------------------------------------------------------------*/

static void prvRecoverFromCriticalError( ETH_HandleTypeDef * pxEthHandle,
                                         EMACData_t * pxEMACData,
                                         const EthernetPhy_t * pxPhyObject,
                                         NetworkInterface_t * pxInterface )
{
    #if defined( HAL_ETH_USE_PTP )
        pxEMACData->xPTPConfigured = pdFALSE;
        pxEMACData->xPTPTimeInitialized = pdFALSE;
    #endif
    ( void ) HAL_ETH_Init( pxEthHandle );
    ( void ) prvApplyMACDMAConfig( pxEthHandle, pxPhyObject );
    prvReconfigurePeripherals( pxEthHandle, pxEMACData, pxInterface );
}

/*---------------------------------------------------------------------------*/

static portTASK_FUNCTION( prvEMACHandlerTask, pvParameters )
{
    NetworkInterface_t * pxInterface = ( NetworkInterface_t * ) pvParameters;
    EMACData_t * const pxEMACData = prvGetEMACData( pxInterface );

    if( pxEMACData == NULL )
    {
        vTaskDelete( NULL );
    }

    pxActiveEMACData = pxEMACData;
    ETH_HandleTypeDef * const pxEthHandle = &( pxEMACData->xEthHandle );
    EthernetPhy_t * const pxPhyObject = &( pxEMACData->xPhyObject );

    /* iptraceEMAC_TASK_STARTING(); */

    for( ; ; )
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
                prvProcessTxQueue( pxInterface );
            }

            if( ( ulISREvents & eMacEventErrRx ) != 0 )
            {
                xResult = prvNetworkInterfaceInput( pxEthHandle, pxInterface );
            }

            if( ( ulISREvents & eMacEventErrTx ) != 0 )
            {
                prvReleaseTxPacket( pxEthHandle );
                prvProcessTxQueue( pxInterface );
            }

            if( ( ulISREvents & eMacEventErrDma ) != 0 )
            {
                const uint32_t ulDmaError = HAL_ETH_GetDMAError( pxEthHandle );
                FreeRTOS_debug_printf( ( "prvEMACHandlerTask: DMA error event\n" ) );

                if( ( ( ulDmaError & ETH_DMA_TX_BUFFER_UNAVAILABLE_FLAG ) != 0U ) &&
                    ( ( ulISREvents & eMacEventErrTx ) == 0U ) )
                {
                    prvReleaseTxPacket( pxEthHandle );
                    prvProcessTxQueue( pxInterface );
                }

                if( ( ( ulDmaError & ETH_DMA_RX_BUFFER_UNAVAILABLE_FLAG ) != 0U ) &&
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
                FreeRTOS_debug_printf( ( "prvEMACHandlerTask: MAC error event\n" ) );

                if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_ERROR )
                {
                    ulISREvents |= eMacEventErrEth;
                }
            }

            if( ( ulISREvents & eMacEventErrEth ) != 0 )
            {
                configASSERT( ( HAL_ETH_GetError( pxEthHandle ) & HAL_ETH_ERROR_PARAM ) == 0 );

                if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_ERROR )
                {
                    prvRecoverFromCriticalError( pxEthHandle, pxEMACData, pxPhyObject, pxInterface );
                    #if ipconfigIS_ENABLED( niEMAC_USE_POWER_DOWN_MODE )
                        if( pxEMACData->xPowerDownActive != pdFALSE )
                        {
                            HAL_ETH_ExitPowerDownMode( pxEthHandle );
                            pxEMACData->xPowerDownActive = pdFALSE;
                        }
                    #endif
                    ( void ) HAL_ETH_Start_IT( pxEthHandle );
                    prvConfigurePowerMode( pxEthHandle, pxEMACData, pdTRUE );
                    xResult = prvNetworkInterfaceInput( pxEthHandle, pxInterface );
                }
            }

            if( ( ulISREvents & eMacEventTxPending ) != 0 )
            {
                prvProcessTxQueue( pxInterface );
            }
        }

        pxActiveEMACData = pxEMACData;

        if( xPhyCheckLinkStatus( pxPhyObject, xResult ) != pdFALSE )
        {
            if( prvGetPhyLinkStatus( pxInterface ) != pdFALSE )
            {
                if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_ERROR )
                {
                    prvRecoverFromCriticalError( pxEthHandle, pxEMACData, pxPhyObject, pxInterface );
                }

                if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_READY )
                {
                    /* Link was down or critical error occurred */
                    if( prvMacUpdateConfig( pxEthHandle, pxPhyObject ) != pdFALSE )
                    {
                        prvReconfigurePeripherals( pxEthHandle, pxEMACData, pxInterface );
                        #if ipconfigIS_ENABLED( niEMAC_USE_POWER_DOWN_MODE )
                            if( pxEMACData->xPowerDownActive != pdFALSE )
                            {
                                HAL_ETH_ExitPowerDownMode( pxEthHandle );
                                pxEMACData->xPowerDownActive = pdFALSE;
                            }
                        #endif
                        ( void ) HAL_ETH_Start_IT( pxEthHandle );
                        prvConfigurePowerMode( pxEthHandle, pxEMACData, pdTRUE );
                        prvProcessTxQueue( pxInterface );
                    }
                }
            }
            else
            {
                prvConfigurePowerMode( pxEthHandle, pxEMACData, pdFALSE );
                ( void ) HAL_ETH_Stop_IT( pxEthHandle );
                prvReleaseTxPacket( pxEthHandle );
                #if ( ipconfigIS_ENABLED( ipconfigSUPPORT_NETWORK_DOWN_EVENT ) )
                    FreeRTOS_NetworkDown( pxInterface );
                #endif
            }
        }

        #if defined( niEMAC_STM32HX ) && ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
            if( pxEMACData->xMacInitStatus == eMacInitComplete )
            {
                const HAL_ETH_StateTypeDef xEthState = HAL_ETH_GetState( pxEthHandle );

                if( ( xEthState == HAL_ETH_STATE_READY ) || ( xEthState == HAL_ETH_STATE_STARTED ) )
                {
                    const TickType_t xNow = xTaskGetTickCount();

                    if( ( xNow - pxEMACData->xLastFilterRefreshTick ) >= pdMS_TO_TICKS( niEMAC_FILTER_REFRESH_TIME_MS ) )
                    {
                        #if defined( niEMAC_STM32HX )
                            prvInitPacketFilter( pxEthHandle, pxInterface );
                        #endif
                        prvConfigureARPOffload( pxEthHandle, pxInterface );
                        pxEMACData->xLastFilterRefreshTick = xNow;
                    }
                }
            }
        #endif

        prvProcessTxQueue( pxInterface );
    }
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvEMACTaskStart( NetworkInterface_t * pxInterface )
{
    EMACData_t * const pxEMACData = prvGetEMACData( pxInterface );
    BaseType_t xResult = pdFALSE;

    if( pxEMACData == NULL )
    {
        return pdFALSE;
    }

    if( pxEMACData->xTxMutex == NULL )
    {
        #if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION )
            pxEMACData->xTxMutex = xSemaphoreCreateMutexStatic( &( pxEMACData->xTxMutexBuf ) );
        #else
            pxEMACData->xTxMutex = xSemaphoreCreateMutex();
        #endif
        configASSERT( pxEMACData->xTxMutex != NULL );
        #if ( configQUEUE_REGISTRY_SIZE > 0 )
            vQueueAddToRegistry( pxEMACData->xTxMutex, niEMAC_TX_MUTEX_NAME );
        #endif
    }

    if( pxEMACData->xTxDescSem == NULL )
    {
        #if ( ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION ) )
            pxEMACData->xTxDescSem = xSemaphoreCreateCountingStatic(
                ( UBaseType_t ) ETH_TX_DESC_CNT,
                ( UBaseType_t ) ETH_TX_DESC_CNT,
                &( pxEMACData->xTxDescSemBuf )
                );
        #else
            pxEMACData->xTxDescSem = xSemaphoreCreateCounting(
                ( UBaseType_t ) ETH_TX_DESC_CNT,
                ( UBaseType_t ) ETH_TX_DESC_CNT
                );
        #endif /* if ( ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION ) ) */
        configASSERT( pxEMACData->xTxDescSem != NULL );
        #if ( configQUEUE_REGISTRY_SIZE > 0 )
            vQueueAddToRegistry( pxEMACData->xTxDescSem, niEMAC_TX_DESC_SEM_NAME );
        #endif
    }

    if( pxEMACData->xTxQueue == NULL )
    {
        #if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION )
            pxEMACData->xTxQueue = xQueueCreateStatic(
                niEMAC_TX_QUEUE_LENGTH,
                sizeof( NetworkBufferDescriptor_t * ),
                ( uint8_t * ) pxEMACData->pxTxQueueStorage,
                &( pxEMACData->xTxQueueBuf ) );
        #else
            pxEMACData->xTxQueue = xQueueCreate(
                niEMAC_TX_QUEUE_LENGTH,
                sizeof( NetworkBufferDescriptor_t * ) );
        #endif
        configASSERT( pxEMACData->xTxQueue != NULL );
        #if ( configQUEUE_REGISTRY_SIZE > 0 )
            vQueueAddToRegistry( pxEMACData->xTxQueue, niEMAC_TX_QUEUE_NAME );
        #endif
    }

    if( ( pxEMACData->xEMACTaskHandle == NULL ) &&
        ( pxEMACData->xTxMutex != NULL ) &&
        ( pxEMACData->xTxDescSem != NULL ) &&
        ( pxEMACData->xTxQueue != NULL ) )
    {
        #if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION )
            static StackType_t uxEMACTaskStack[ niEMAC_MAX_INTERFACE_NAMES ][ niEMAC_TASK_STACK_SIZE ];
            static StaticTask_t xEMACTaskTCB[ niEMAC_MAX_INTERFACE_NAMES ];
            const UBaseType_t uxIndex = ( UBaseType_t ) pxEMACData->xEMACIndex;
            pxEMACData->xEMACTaskHandle = xTaskCreateStatic(
                prvEMACHandlerTask,
                niEMAC_TASK_NAME,
                niEMAC_TASK_STACK_SIZE,
                ( void * ) pxInterface,
                niEMAC_TASK_PRIORITY,
                uxEMACTaskStack[ uxIndex ],
                &( xEMACTaskTCB[ uxIndex ] )
                );
        #else /* if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION ) */
            ( void ) xTaskCreate(
                prvEMACHandlerTask,
                niEMAC_TASK_NAME,
                niEMAC_TASK_STACK_SIZE,
                ( void * ) pxInterface,
                niEMAC_TASK_PRIORITY,
                &( pxEMACData->xEMACTaskHandle )
                );
        #endif /* if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION ) */
    }

    if( pxEMACData->xEMACTaskHandle != NULL )
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

static void prvConfigureMMCStatistics( ETH_HandleTypeDef * pxEthHandle )
{
    if( ( pxEthHandle == NULL ) || ( pxEthHandle->Instance == NULL ) )
    {
        return;
    }

    #if ipconfigIS_ENABLED( niEMAC_USE_MMC_STATS )
        #if defined( ETH_MMCCR_CR ) && ipconfigIS_ENABLED( niEMAC_MMC_RESET_COUNTERS_ON_INIT )
            SET_BIT( pxEthHandle->Instance->MMCCR, ETH_MMCCR_CR );
        #endif

        #if defined( ETH_MMCCR_ROR )
            if( ipconfigIS_ENABLED( niEMAC_MMC_RESET_ON_READ ) )
            {
                SET_BIT( pxEthHandle->Instance->MMCCR, ETH_MMCCR_ROR );
            }
            else
            {
                CLEAR_BIT( pxEthHandle->Instance->MMCCR, ETH_MMCCR_ROR );
            }
        #endif

        #if defined( ETH_MMCCR_MCF )
            if( ipconfigIS_ENABLED( niEMAC_MMC_COUNTER_FREEZE ) )
            {
                SET_BIT( pxEthHandle->Instance->MMCCR, ETH_MMCCR_MCF );
            }
            else
            {
                CLEAR_BIT( pxEthHandle->Instance->MMCCR, ETH_MMCCR_MCF );
            }
        #endif

        #if defined( ETH_MMCRIMR_RGUFM ) || defined( ETH_MMCRIMR_RXLPITRCIM )
            if( niEMAC_MMC_RX_INTERRUPT_UNMASK != 0U )
            {
                CLEAR_BIT( pxEthHandle->Instance->MMCRIMR, niEMAC_MMC_RX_INTERRUPT_UNMASK );
            }
        #endif

        #if defined( ETH_MMCTIMR_TGFM ) || defined( ETH_MMCTIMR_TXLPITRCIM )
            if( niEMAC_MMC_TX_INTERRUPT_UNMASK != 0U )
            {
                CLEAR_BIT( pxEthHandle->Instance->MMCTIMR, niEMAC_MMC_TX_INTERRUPT_UNMASK );
            }
        #endif
    #endif
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvApplyMACDMAConfig( ETH_HandleTypeDef * pxEthHandle,
                                        const EthernetPhy_t * pxPhyObject )
{
    if( pxEthHandle == NULL )
    {
        return pdFALSE;
    }

    ETH_MACConfigTypeDef xMACConfig;

    if( HAL_ETH_GetMACConfig( pxEthHandle, &xMACConfig ) != HAL_OK )
    {
        return pdFALSE;
    }

    if( pxPhyObject != NULL )
    {
        xMACConfig.DuplexMode = ( pxPhyObject->xPhyProperties.ucDuplex == PHY_DUPLEX_FULL ) ? ETH_FULLDUPLEX_MODE : ETH_HALFDUPLEX_MODE;
        xMACConfig.Speed = ( pxPhyObject->xPhyProperties.ucSpeed == PHY_SPEED_10 ) ? ETH_SPEED_10M : ETH_SPEED_100M;
    }

    xMACConfig.ChecksumOffload = ( FunctionalState ) ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM );
    xMACConfig.CRCStripTypePacket = DISABLE;
    xMACConfig.AutomaticPadCRCStrip = ENABLE;
    xMACConfig.RetryTransmission = ENABLE;
    xMACConfig.Support2KPacket = ( FunctionalState ) ipconfigIS_ENABLED( niEMAC_USE_2K_PACKETS );
    xMACConfig.JumboPacket = ( FunctionalState ) ipconfigIS_ENABLED( niEMAC_USE_JUMBO_FRAMES );

    if( ipconfigIS_ENABLED( niEMAC_USE_JUMBO_FRAMES ) )
    {
        xMACConfig.GiantPacketSizeLimitControl = DISABLE;
    }

    if( ipconfigIS_ENABLED( niEMAC_USE_FLOW_CONTROL ) )
    {
        xMACConfig.TransmitFlowControl = ( FunctionalState ) ipconfigIS_ENABLED( niEMAC_FLOW_CONTROL_TX_ENABLE );
        xMACConfig.ReceiveFlowControl = ( FunctionalState ) ipconfigIS_ENABLED( niEMAC_FLOW_CONTROL_RX_ENABLE );
        xMACConfig.PauseTime = ( uint32_t ) niEMAC_FLOW_CONTROL_PAUSE_TIME;
        xMACConfig.PauseLowThreshold = ( uint32_t ) niEMAC_FLOW_CONTROL_PAUSE_LOW_THRESHOLD;
    }
    else
    {
        xMACConfig.TransmitFlowControl = DISABLE;
        xMACConfig.ReceiveFlowControl = DISABLE;
    }

    xMACConfig.TransmitQueueMode = ( uint32_t ) niEMAC_TX_QUEUE_MODE;
    xMACConfig.ReceiveQueueMode = ( uint32_t ) niEMAC_RX_QUEUE_MODE;

    if( HAL_ETH_SetMACConfig( pxEthHandle, &xMACConfig ) != HAL_OK )
    {
        return pdFALSE;
    }

    ETH_DMAConfigTypeDef xDMAConfig;

    if( HAL_ETH_GetDMAConfig( pxEthHandle, &xDMAConfig ) != HAL_OK )
    {
        return pdFALSE;
    }

    #if defined( niEMAC_STM32FX )
        xDMAConfig.EnhancedDescriptorFormat = ( FunctionalState ) ( ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM ) || ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM ) );
    #elif defined( niEMAC_STM32HX )
        xDMAConfig.SecondPacketOperate = ENABLE;
        #if ipconfigIS_ENABLED( niEMAC_USE_TCP_SEGMENTATION ) && ipconfigIS_ENABLED( ipconfigUSE_TCP )
            xDMAConfig.TCPSegmentation = ENABLE;
            xDMAConfig.MaximumSegmentSize = ( uint32_t ) niEMAC_TCP_SEGMENTATION_MSS;
        #else
            xDMAConfig.TCPSegmentation = DISABLE;
        #endif
    #endif

    if( HAL_ETH_SetDMAConfig( pxEthHandle, &xDMAConfig ) != HAL_OK )
    {
        return pdFALSE;
    }

    prvConfigureMMCStatistics( pxEthHandle );

    return pdTRUE;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvEthConfigInit( ETH_HandleTypeDef * pxEthHandle,
                                    NetworkInterface_t * pxInterface )
{
    EMACData_t * const pxEMACData = prvGetEMACData( pxInterface );
    BaseType_t xResult = pdFALSE;

    if( pxEMACData == NULL )
    {
        return pdFALSE;
    }

    pxActiveEMACData = pxEMACData;
    ( void ) memset( pxEMACData->ucSrcMatchCounters, 0, sizeof( pxEMACData->ucSrcMatchCounters ) );
    ( void ) memset( pxEMACData->ulHashTable, 0, sizeof( pxEMACData->ulHashTable ) );
    ( void ) memset( pxEMACData->ucAddrHashCounters, 0, sizeof( pxEMACData->ucAddrHashCounters ) );
    pxEMACData->uxMACEntryIndex = 0U;
    pxEMACData->ulCurrentARPOffloadAddress = 0U;
    pxEMACData->ulCurrentL4FilterPort = UINT32_MAX;
    pxEMACData->xDropCurrentRxFrame = pdFALSE;
    pxEMACData->xVLANEnabled = pdFALSE;
    pxEMACData->xPowerDownActive = pdFALSE;
    pxEMACData->xLpiActive = pdFALSE;
    pxEMACData->xPTPConfigured = pdFALSE;
    pxEMACData->xPTPTimeInitialized = pdFALSE;
    pxEMACData->xLastFilterRefreshTick = 0U;
    pxEMACData->usVLANIdentifier = 0U;
    pxEMACData->ulLastWakeUpSource = 0U;
    pxEMACData->ulLastLPIEvent = 0U;
    #if defined( HAL_ETH_USE_PTP )
        ( void ) memset( &( pxEMACData->xLastTxTimeStamp ), 0, sizeof( pxEMACData->xLastTxTimeStamp ) );
        ( void ) memset( &( pxEMACData->xLastRxTimeStamp ), 0, sizeof( pxEMACData->xLastRxTimeStamp ) );
        ( void ) memset( &( pxEMACData->xLastPTPTime ), 0, sizeof( pxEMACData->xLastPTPTime ) );
    #endif

    pxEthHandle->Instance = ETH;
    pxEthHandle->Init.MediaInterface = ipconfigIS_ENABLED( niEMAC_USE_RMII ) ? HAL_ETH_RMII_MODE : HAL_ETH_MII_MODE;
    pxEthHandle->Init.RxBuffLen = niEMAC_DATA_BUFFER_SIZE;
    /* Rx buffers may be cache-line aligned and larger than ETH_MAX_PACKET_SIZE. */
    configASSERT( pxEthHandle->Init.RxBuffLen >= ipTOTAL_ETHERNET_FRAME_SIZE );
    configASSERT( pxEthHandle->Init.RxBuffLen % 4U == 0 );

    static ETH_DMADescTypeDef xDMADescTx[ niEMAC_MAX_INTERFACE_NAMES ][ ETH_TX_DESC_CNT ] __ALIGNED( portBYTE_ALIGNMENT ) __attribute__( ( section( niEMAC_TX_DESC_SECTION ) ) );
    static ETH_DMADescTypeDef xDMADescRx[ niEMAC_MAX_INTERFACE_NAMES ][ ETH_RX_DESC_CNT ] __ALIGNED( portBYTE_ALIGNMENT ) __attribute__( ( section( niEMAC_RX_DESC_SECTION ) ) );
    pxEthHandle->Init.TxDesc = xDMADescTx[ pxEMACData->xEMACIndex ];
    pxEthHandle->Init.RxDesc = xDMADescRx[ pxEMACData->xEMACIndex ];
    ( void ) memset( &xDMADescTx[ pxEMACData->xEMACIndex ], 0, sizeof( xDMADescTx[ pxEMACData->xEMACIndex ] ) );
    ( void ) memset( &xDMADescRx[ pxEMACData->xEMACIndex ], 0, sizeof( xDMADescRx[ pxEMACData->xEMACIndex ] ) );

    const NetworkEndPoint_t * const pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );

    if( pxEndPoint != NULL )
    {
        pxEthHandle->Init.MACAddr = ( uint8_t * ) pxEndPoint->xMACAddress.ucBytes;

        if( HAL_ETH_Init( pxEthHandle ) == HAL_OK )
        {
            prvConfigureVLAN( pxEthHandle, pxInterface );
            #if defined( HAL_ETH_USE_PTP )
                prvConfigurePTP( pxEthHandle, pxEMACData );
            #endif

            #if defined( niEMAC_STM32FX )
                /* This function doesn't get called in Fxx driver */
                HAL_ETH_SetMDIOClockRange( pxEthHandle );
            #endif

            if( prvApplyMACDMAConfig( pxEthHandle, NULL ) == pdFALSE )
            {
                return pdFALSE;
            }

            #if defined( niEMAC_STM32HX )
                prvInitPacketFilter( pxEthHandle, pxInterface );
                #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
                    prvConfigureARPOffload( pxEthHandle, pxInterface );
                #endif
            #endif

            prvInitMacAddresses( pxEthHandle, pxInterface );

            xResult = pdTRUE;
        }
    }

    if( xResult == pdTRUE )
    {
        #ifdef niEMAC_CACHEABLE
            if( niEMAC_CACHE_ENABLED )
            {
                #ifdef niEMAC_MPU
                    configASSERT( niEMAC_MPU_ENABLED != 0 );
                #else
                    configASSERT( pdFALSE );
                #endif
                /* _FLD2VAL( SCB_CCSIDR_LINESIZE, SCB->CCSIDR ) */
            }
        #endif

        #ifdef configPRIO_BITS
            const uint32_t ulPrioBits = configPRIO_BITS;
        #else
            const uint32_t ulPrioBits = __NVIC_PRIO_BITS;
        #endif
        const uint32_t ulPriority = NVIC_GetPriority( ETH_IRQn ) << ( 8U - ulPrioBits );

        if( ulPriority < configMAX_SYSCALL_INTERRUPT_PRIORITY )
        {
            FreeRTOS_debug_printf( ( "prvEthConfigInit: Incorrectly set ETH_IRQn priority\n" ) );
            NVIC_SetPriority( ETH_IRQn, configMAX_SYSCALL_INTERRUPT_PRIORITY >> ( 8U - ulPrioBits ) );
        }

        if( NVIC_GetEnableIRQ( ETH_IRQn ) == 0 )
        {
            FreeRTOS_debug_printf( ( "prvEthConfigInit: ETH_IRQn was not enabled by application\n" ) );
            HAL_NVIC_EnableIRQ( ETH_IRQn );
        }

        #ifdef niEMAC_STM32FX
            configASSERT( __HAL_RCC_ETH_IS_CLK_ENABLED() != 0 );
        #elif defined( STM32H5 )
            configASSERT( __HAL_RCC_ETH_IS_CLK_ENABLED() != 0 );
            configASSERT( __HAL_RCC_ETHTX_IS_CLK_ENABLED() != 0 );
            configASSERT( __HAL_RCC_ETHRX_IS_CLK_ENABLED() != 0 );
        #elif defined( STM32H7 )
            configASSERT( __HAL_RCC_ETH1MAC_IS_CLK_ENABLED() != 0 );
            configASSERT( __HAL_RCC_ETH1TX_IS_CLK_ENABLED() != 0 );
            configASSERT( __HAL_RCC_ETH1RX_IS_CLK_ENABLED() != 0 );
        #endif
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static void prvInitMacAddresses( ETH_HandleTypeDef * pxEthHandle,
                                 NetworkInterface_t * pxInterface )
{
    ETH_MACFilterConfigTypeDef xFilterConfig;
    NetworkEndPoint_t * pxFirstEndPoint = FreeRTOS_FirstEndPoint( pxInterface );

    ( void ) HAL_ETH_GetMACFilterConfig( pxEthHandle, &xFilterConfig );
    xFilterConfig.ReceiveAllMode = DISABLE;
    xFilterConfig.HachOrPerfectFilter = ENABLE;
    #if ipconfigIS_ENABLED( niEMAC_USE_SOURCE_MAC_GUARD ) && defined( ETH_MAC_ADDRESS0 )
    {
        const uint8_t * pucSourceMac = NULL;

        if( pxFirstEndPoint != NULL )
        {
            pucSourceMac = pxFirstEndPoint->xMACAddress.ucBytes;
        }
        else
        {
            pucSourceMac = pxEthHandle->Init.MACAddr;
        }

        if( ( pucSourceMac != NULL ) &&
            ( HAL_ETH_SetSourceMACAddrMatch( pxEthHandle, ETH_MAC_ADDRESS0, pucSourceMac ) == HAL_OK ) )
        {
            /* Conservative mode: only reject frames whose source MAC matches our own. */
            xFilterConfig.SrcAddrFiltering = ENABLE;
            xFilterConfig.SrcAddrInverseFiltering = ENABLE;
        }
        else
        {
            /* Fail-open: never tighten filtering when guard cannot be configured. */
            xFilterConfig.SrcAddrFiltering = DISABLE;
            xFilterConfig.SrcAddrInverseFiltering = DISABLE;
            FreeRTOS_debug_printf( ( "prvInitMacAddresses: Source MAC guard disabled (setup failed)\n" ) );
        }
    }
    #else
        xFilterConfig.SrcAddrFiltering = DISABLE;
        xFilterConfig.SrcAddrInverseFiltering = DISABLE;
    #endif
    xFilterConfig.ControlPacketsFilter = ETH_CTRLPACKETS_BLOCK_ALL;
    xFilterConfig.BroadcastFilter = ENABLE;
    xFilterConfig.PassAllMulticast = DISABLE;
    xFilterConfig.DestAddrInverseFiltering = DISABLE;
    xFilterConfig.HashMulticast = ENABLE;
    xFilterConfig.HashUnicast = ENABLE;
    xFilterConfig.PromiscuousMode = DISABLE;
    ( void ) HAL_ETH_SetMACFilterConfig( pxEthHandle, &xFilterConfig );

    NetworkEndPoint_t * pxEndPoint;

    for( pxEndPoint = pxFirstEndPoint; pxEndPoint != NULL; pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
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
}

/*---------------------------------------------------------------------------*/

static void prvConfigureVLAN( ETH_HandleTypeDef * pxEthHandle,
                              NetworkInterface_t * pxInterface )
{
    ( void ) pxInterface;
    EMACData_t * const pxEMACData = prvGetEMACDataByEthHandle( pxEthHandle );

    if( pxEMACData == NULL )
    {
        return;
    }

    #if ipconfigIS_ENABLED( niEMAC_USE_VLAN_OFFLOAD )
        const uint16_t usVlan = ( uint16_t ) ( niEMAC_VLAN_IDENTIFIER & 0x0FFFU );

        pxEMACData->usVLANIdentifier = usVlan;
        pxEMACData->xVLANEnabled = ( usVlan != 0U ) ? pdTRUE : pdFALSE;

        if( pxEMACData->xVLANEnabled != pdFALSE )
        {
            HAL_ETH_SetRxVLANIdentifier( pxEthHandle, ETH_VLANTAGCOMPARISON_12BIT, usVlan );

            #if defined( niEMAC_STM32HX )
                ETH_RxVLANConfigTypeDef xRxVLANConfig;

                if( HAL_ETHEx_GetRxVLANConfig( pxEthHandle, &xRxVLANConfig ) == HAL_OK )
                {
                    xRxVLANConfig.VLANTagHashTableMatch = DISABLE;
                    xRxVLANConfig.VLANTagInStatus = ENABLE;
                    xRxVLANConfig.VLANTagInverceMatch = DISABLE;
                    xRxVLANConfig.VLANTypeCheck = ETH_VLANTYPECHECK_CVLAN;
                    xRxVLANConfig.StripVLANTag = ipconfigIS_ENABLED( niEMAC_VLAN_RX_STRIP ) ? ETH_VLANTAGRXSTRIPPING_ALWAYS : ETH_VLANTAGRXSTRIPPING_NONE;
                    ( void ) HAL_ETHEx_SetRxVLANConfig( pxEthHandle, &xRxVLANConfig );
                }

                ETH_TxVLANConfigTypeDef xTxVLANConfig =
                {
                    .SourceTxDesc = ipconfigIS_ENABLED( niEMAC_VLAN_TX_TAG_FROM_DESCRIPTOR ) ? ENABLE : DISABLE,
                    .SVLANType = ipconfigIS_ENABLED( niEMAC_VLAN_TX_SVLAN_TYPE ) ? ENABLE : DISABLE,
                    .VLANTagControl = niEMAC_VLAN_TX_TAG_CONTROL
                };

                ( void ) HAL_ETHEx_SetTxVLANConfig( pxEthHandle, niEMAC_VLAN_TX_TAG_SELECT, &xTxVLANConfig );
                HAL_ETHEx_SetTxVLANIdentifier( pxEthHandle, niEMAC_VLAN_TX_TAG_SELECT, usVlan );
                #if ipconfigIS_ENABLED( niEMAC_VLAN_HASH_TABLE_ENABLE )
                    HAL_ETHEx_SetVLANHashTable( pxEthHandle, niEMAC_VLAN_HASH_TABLE & 0xFFFFU );
                #endif
                ( void ) HAL_ETHEx_GetTxVLANConfig( pxEthHandle, niEMAC_VLAN_TX_TAG_SELECT, &xTxVLANConfig );
                HAL_ETHEx_EnableVLANProcessing( pxEthHandle );
            #endif
        }
        else
        {
            #if defined( niEMAC_STM32HX )
                ETH_TxVLANConfigTypeDef xTxVLANConfig =
                {
                    .SourceTxDesc = DISABLE,
                    .SVLANType = DISABLE,
                    .VLANTagControl = ETH_VLANTAGCONTROL_NONE
                };

                ( void ) HAL_ETHEx_SetTxVLANConfig( pxEthHandle, niEMAC_VLAN_TX_TAG_SELECT, &xTxVLANConfig );
                HAL_ETHEx_SetTxVLANIdentifier( pxEthHandle, niEMAC_VLAN_TX_TAG_SELECT, 0U );
                HAL_ETHEx_DisableVLANProcessing( pxEthHandle );
            #endif
        }
    #else
        pxEMACData->xVLANEnabled = pdFALSE;
        pxEMACData->usVLANIdentifier = 0U;
    #endif
}

/*---------------------------------------------------------------------------*/

#if defined( HAL_ETH_USE_PTP )

    static void prvConfigurePTP( ETH_HandleTypeDef * pxEthHandle,
                                 EMACData_t * pxEMACData )
    {
        if( ( pxEMACData == NULL ) || ( pxEthHandle == NULL ) )
        {
            return;
        }

        #if ipconfigIS_ENABLED( niEMAC_USE_PTP )
            ETH_PTP_ConfigTypeDef xPTPConfig;

            if( HAL_ETH_PTP_GetConfig( pxEthHandle, &xPTPConfig ) == HAL_OK )
            {
                pxEMACData->xPTPConfigured = ( xPTPConfig.Timestamp == ENABLE ) ? pdTRUE : pdFALSE;
            }
            else
            {
                pxEMACData->xPTPConfigured = pdFALSE;
                pxEMACData->xPTPTimeInitialized = pdFALSE;
            }

            if( pxEMACData->xPTPConfigured == pdFALSE )
            {
                pxEMACData->xPTPTimeInitialized = pdFALSE;

                xPTPConfig =
                {
                    .Timestamp = ENABLE,
                    .TimestampUpdateMode = ENABLE,
                    .TimestampInitialize = DISABLE,
                    .TimestampUpdate = DISABLE,
                    .TimestampAddendUpdate = ENABLE,
                    .TimestampAll = ipconfigIS_ENABLED( niEMAC_PTP_TIMESTAMP_ALL ) ? ENABLE : DISABLE,
                    .TimestampRolloverMode = DISABLE,
                    .TimestampV2 = ENABLE,
                    .TimestampEthernet = ENABLE,
                    .TimestampIPv6 = ENABLE,
                    .TimestampIPv4 = ENABLE,
                    .TimestampEvent = ENABLE,
                    .TimestampMaster = ipconfigIS_ENABLED( niEMAC_PTP_TIMESTAMP_MASTER ) ? ENABLE : DISABLE,
                    .TimestampFilter = ipconfigIS_ENABLED( niEMAC_PTP_TIMESTAMP_FILTER ) ? ENABLE : DISABLE,
                    #if defined( niEMAC_STM32HX )
                        .TimestampSnapshots = niEMAC_PTP_TIMESTAMP_SNAPSHOTS,
                        .TimestampChecksumCorrection = ipconfigIS_ENABLED( niEMAC_PTP_TIMESTAMP_CHECKSUM_CORRECTION ) ? ENABLE : DISABLE,
                        .TimestampStatusMode = ipconfigIS_ENABLED( niEMAC_PTP_TIMESTAMP_STATUS_MODE ) ? ENABLE : DISABLE,
                    #endif
                    .TimestampAddend = 0x80000000U,
                    .TimestampSubsecondInc = 43U
                };

                if( HAL_ETH_PTP_SetConfig( pxEthHandle, &xPTPConfig ) == HAL_OK )
                {
                    pxEMACData->xPTPConfigured = pdTRUE;
                    pxEMACData->xPTPTimeInitialized = pdFALSE;
                }
            }

            if( pxEMACData->xPTPConfigured != pdFALSE )
            {
                if( pxEMACData->xPTPTimeInitialized == pdFALSE )
                {
                    #if ipconfigIS_ENABLED( niEMAC_PTP_INIT_TIME_ENABLE )
                        ETH_TimeTypeDef xInitTime =
                        {
                            .Seconds = niEMAC_PTP_INIT_TIME_SECONDS,
                            .NanoSeconds = niEMAC_PTP_INIT_TIME_NANOSECONDS
                        };

                        if( HAL_ETH_PTP_SetTime( pxEthHandle, &xInitTime ) == HAL_OK )
                        {
                            pxEMACData->xPTPTimeInitialized = pdTRUE;
                        }
                    #endif

                    #if ipconfigIS_ENABLED( niEMAC_PTP_INIT_OFFSET_ENABLE )
                        ETH_TimeTypeDef xOffset =
                        {
                            .Seconds = niEMAC_PTP_INIT_OFFSET_SECONDS,
                            .NanoSeconds = niEMAC_PTP_INIT_OFFSET_NANOSECONDS
                        };

                        if( HAL_ETH_PTP_AddTimeOffset( pxEthHandle, niEMAC_PTP_INIT_OFFSET_SIGN, &xOffset ) == HAL_OK )
                        {
                            pxEMACData->xPTPTimeInitialized = pdTRUE;
                        }
                    #endif
                }

                prvCapturePTPTime( pxEthHandle, pxEMACData, prvGetInterfaceByEMACData( pxEMACData ) );
            }
        #else
            pxEMACData->xPTPConfigured = pdFALSE;
            pxEMACData->xPTPTimeInitialized = pdFALSE;
        #endif
    }

#endif /* if defined( HAL_ETH_USE_PTP ) */

/*---------------------------------------------------------------------------*/

static void prvConfigurePowerMode( ETH_HandleTypeDef * pxEthHandle,
                                   EMACData_t * pxEMACData,
                                   BaseType_t xLinkIsUp )
{
    if( ( pxEMACData == NULL ) || ( pxEthHandle == NULL ) )
    {
        return;
    }

    #if ipconfigIS_ENABLED( niEMAC_USE_POWER_DOWN_MODE )
        if( xLinkIsUp != pdFALSE )
        {
            if( pxEMACData->xPowerDownActive != pdFALSE )
            {
                HAL_ETH_ExitPowerDownMode( pxEthHandle );
                pxEMACData->xPowerDownActive = pdFALSE;
            }
        }
        else if( pxEMACData->xPowerDownActive == pdFALSE )
        {
            pxEMACData->ulLastWakeUpSource = 0U;

            #if ipconfigIS_ENABLED( niEMAC_USE_WAKEUP_FILTER )
                uint32_t ulWakeUpFilter[ 8U ] =
                {
                    niEMAC_WAKEUP_FILTER_WORD0,
                    niEMAC_WAKEUP_FILTER_WORD1,
                    niEMAC_WAKEUP_FILTER_WORD2,
                    niEMAC_WAKEUP_FILTER_WORD3,
                    niEMAC_WAKEUP_FILTER_WORD4,
                    niEMAC_WAKEUP_FILTER_WORD5,
                    niEMAC_WAKEUP_FILTER_WORD6,
                    niEMAC_WAKEUP_FILTER_WORD7
                };
                uint32_t ulFilterCount = niEMAC_WAKEUP_FILTER_COUNT;

                if( ulFilterCount > 8U )
                {
                    ulFilterCount = 8U;
                }

                if( ulFilterCount > 0U )
                {
                    ( void ) HAL_ETH_SetWakeUpFilter( pxEthHandle, ulWakeUpFilter, ulFilterCount );
                }
            #endif

            const ETH_PowerDownConfigTypeDef xPowerDownConfig =
            {
                .WakeUpPacket = ENABLE,
                .MagicPacket = ENABLE,
                .GlobalUnicast = DISABLE,
                .WakeUpForward = DISABLE
            };

            HAL_ETH_EnterPowerDownMode( pxEthHandle, &xPowerDownConfig );
            pxEMACData->xPowerDownActive = pdTRUE;
        }
    #else
        pxEMACData->xPowerDownActive = pdFALSE;
    #endif

    #if defined( niEMAC_STM32HX ) && ipconfigIS_ENABLED( niEMAC_USE_LPI_MODE )
        if( xLinkIsUp == pdFALSE )
        {
            if( pxEMACData->xLpiActive != pdFALSE )
            {
                HAL_ETHEx_ExitLPIMode( pxEthHandle );
                pxEMACData->xLpiActive = pdFALSE;
            }
        }
        else if( ( pxEMACData->xLpiActive == pdFALSE ) &&
                 ( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_STARTED ) )
        {
            HAL_ETHEx_EnterLPIMode( pxEthHandle, ENABLE, ENABLE );
            pxEMACData->xLpiActive = pdTRUE;
        }
    #else
        pxEMACData->xLpiActive = pdFALSE;
    #endif
}

/*---------------------------------------------------------------------------*/

#ifdef niEMAC_STM32HX

    static void prvInitPacketFilter( ETH_HandleTypeDef * pxEthHandle,
                                     const NetworkInterface_t * const pxInterface )
    {
        EMACData_t * const pxEMACData = prvGetEMACDataByEthHandle( pxEthHandle );

        if( pxEMACData == NULL )
        {
            return;
        }

        HAL_ETHEx_DisableL3L4Filtering( pxEthHandle );

        #if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM )
        {
            const uint8_t ucFilterCount = _FLD2VAL( ETH_MACHWF1R_L3L4FNUM, pxEthHandle->Instance->MACHWF1R );

            if( ucFilterCount > 0 )
            {
                ETH_MACConfigTypeDef xMACConfig;
                ( void ) HAL_ETH_GetMACConfig( pxEthHandle, &xMACConfig );

                if( xMACConfig.ChecksumOffload != ENABLE )
                {
                    /* "The Layer 3 and Layer 4 Packet Filter feature automatically selects the IPC Full Checksum
                     * Offload Engine on the Receive side. When this feature is enabled, you must set the IPC bit." */
                    xMACConfig.ChecksumOffload = ENABLE;
                    ( void ) HAL_ETH_SetMACConfig( pxEthHandle, &xMACConfig );
                }

                #if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES )
                {
                    ETH_L3FilterConfigTypeDef xL3FilterConfig;

                    ( void ) HAL_ETHEx_GetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_0, &xL3FilterConfig );
                    xL3FilterConfig.Protocol = ETH_L3_IPV4_MATCH;
                    xL3FilterConfig.SrcAddrFilterMatch = ETH_L3_SRC_ADDR_MATCH_DISABLE;
                    xL3FilterConfig.SrcAddrHigherBitsMatch = 0U;
                    xL3FilterConfig.Ip4SrcAddr = 0U;

                    #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
                    {
                        UBaseType_t uxIPv4EndPoints = 0U;
                        uint32_t ulIPv4Address = 0U;
                        NetworkEndPoint_t * pxEndPoint;

                        for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
                             pxEndPoint != NULL;
                             pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
                        {
                            if( ENDPOINT_IS_IPv4( pxEndPoint ) &&
                                ( pxEndPoint->ipv4_settings.ulIPAddress != 0U ) )
                            {
                                ulIPv4Address = pxEndPoint->ipv4_settings.ulIPAddress;
                                uxIPv4EndPoints++;

                                if( uxIPv4EndPoints > 1U )
                                {
                                    break;
                                }
                            }
                        }

                        if( uxIPv4EndPoints == 1U )
                        {
                            xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_PERFECT_MATCH_ENABLE;
                            xL3FilterConfig.DestAddrHigherBitsMatch = 0x1FU;
                            xL3FilterConfig.Ip4DestAddr = ulIPv4Address;
                        }
                        else
                        {
                            xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_MATCH_DISABLE;
                            xL3FilterConfig.DestAddrHigherBitsMatch = 0U;
                            xL3FilterConfig.Ip4DestAddr = 0U;
                        }
                    }
                    #else
                        xL3FilterConfig.SrcAddrFilterMatch = ETH_L3_SRC_ADDR_PERFECT_MATCH_ENABLE;
                        xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_PERFECT_MATCH_ENABLE;
                        xL3FilterConfig.SrcAddrHigherBitsMatch = 0x1FU;
                        xL3FilterConfig.DestAddrHigherBitsMatch = 0x1FU;
                        xL3FilterConfig.Ip4SrcAddr = FREERTOS_INADDR_BROADCAST;
                        xL3FilterConfig.Ip4DestAddr = FREERTOS_INADDR_BROADCAST;
                    #endif

                    ( void ) HAL_ETHEx_SetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_0, &xL3FilterConfig );

                    ( void ) HAL_ETHEx_GetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_1, &xL3FilterConfig );
                    xL3FilterConfig.Protocol = ETH_L3_IPV6_MATCH;
                    xL3FilterConfig.SrcAddrFilterMatch = ETH_L3_SRC_ADDR_MATCH_DISABLE;
                    xL3FilterConfig.SrcAddrHigherBitsMatch = 0U;

                    #if ipconfigIS_ENABLED( ipconfigUSE_IPv6 )
                    {
                        UBaseType_t uxIPv6EndPoints = 0U;
                        uint32_t ulIPv6Address[ 4 ] = { 0U };
                        NetworkEndPoint_t * pxEndPoint;

                        for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
                             pxEndPoint != NULL;
                             pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
                        {
                            if( ENDPOINT_IS_IPv6( pxEndPoint ) &&
                                ( memcmp( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00", ipSIZE_OF_IPv6_ADDRESS ) != 0 ) )
                            {
                                if( uxIPv6EndPoints == 0U )
                                {
                                    ( void ) memcpy( ulIPv6Address, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, sizeof( ulIPv6Address ) );
                                }

                                uxIPv6EndPoints++;

                                if( uxIPv6EndPoints > 1U )
                                {
                                    break;
                                }
                            }
                        }

                        if( uxIPv6EndPoints == 1U )
                        {
                            xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_PERFECT_MATCH_ENABLE;
                            xL3FilterConfig.DestAddrHigherBitsMatch = 0x1FU;
                            xL3FilterConfig.Ip6Addr[ 0 ] = ulIPv6Address[ 0 ];
                            xL3FilterConfig.Ip6Addr[ 1 ] = ulIPv6Address[ 1 ];
                            xL3FilterConfig.Ip6Addr[ 2 ] = ulIPv6Address[ 2 ];
                            xL3FilterConfig.Ip6Addr[ 3 ] = ulIPv6Address[ 3 ];
                        }
                        else
                        {
                            xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_MATCH_DISABLE;
                            xL3FilterConfig.DestAddrHigherBitsMatch = 0U;
                            xL3FilterConfig.Ip6Addr[ 0 ] = 0U;
                            xL3FilterConfig.Ip6Addr[ 1 ] = 0U;
                            xL3FilterConfig.Ip6Addr[ 2 ] = 0U;
                            xL3FilterConfig.Ip6Addr[ 3 ] = 0U;
                        }
                    }
                    #else
                        xL3FilterConfig.SrcAddrFilterMatch = ETH_L3_SRC_ADDR_PERFECT_MATCH_ENABLE;
                        xL3FilterConfig.DestAddrFilterMatch = ETH_L3_DEST_ADDR_PERFECT_MATCH_ENABLE;
                        xL3FilterConfig.SrcAddrHigherBitsMatch = 0x1FU;
                        xL3FilterConfig.DestAddrHigherBitsMatch = 0x1FU;
                        xL3FilterConfig.Ip6Addr[ 0 ] = 0xFFFFFFFFU;
                        xL3FilterConfig.Ip6Addr[ 1 ] = 0xFFFFFFFFU;
                        xL3FilterConfig.Ip6Addr[ 2 ] = 0xFFFFFFFFU;
                        xL3FilterConfig.Ip6Addr[ 3 ] = 0xFFFFFFFFU;
                    #endif

                    ( void ) HAL_ETHEx_SetL3FilterConfig( pxEthHandle, ETH_L3_FILTER_1, &xL3FilterConfig );
                }
                #endif /* if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES ) */

                #if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
                {
                    ETH_L4FilterConfigTypeDef xL4FilterConfig;
                    uint32_t ulDesiredL4Port = 0U;

                    #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
                    {
                        BaseType_t xHasIPv4Address = pdFALSE;
                        NetworkEndPoint_t * pxEndPoint;

                        for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
                             pxEndPoint != NULL;
                             pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
                        {
                            if( ENDPOINT_IS_IPv4( pxEndPoint ) &&
                                ( pxEndPoint->ipv4_settings.ulIPAddress != 0U ) )
                            {
                                xHasIPv4Address = pdTRUE;
                                break;
                            }
                        }

                        if( xHasIPv4Address == pdFALSE )
                        {
                            /* Narrow receive filter during DHCP discovery. */
                            ulDesiredL4Port = 68U;
                        }
                    }
                    #endif

                    ( void ) HAL_ETHEx_GetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_0, &xL4FilterConfig );
                    xL4FilterConfig.Protocol = ETH_L4_UDP_MATCH;
                    xL4FilterConfig.SrcPortFilterMatch = ETH_L4_SRC_PORT_MATCH_DISABLE;
                    xL4FilterConfig.DestPortFilterMatch = ( ulDesiredL4Port == 0U ) ? ETH_L4_DEST_PORT_MATCH_DISABLE : ETH_L4_DEST_PORT_PERFECT_MATCH_ENABLE;
                    xL4FilterConfig.SourcePort = 0U;
                    xL4FilterConfig.DestinationPort = ulDesiredL4Port;
                    ( void ) HAL_ETHEx_SetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_0, &xL4FilterConfig );
                    pxEMACData->ulCurrentL4FilterPort = ulDesiredL4Port;

                    ( void ) HAL_ETHEx_GetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_1, &xL4FilterConfig );
                    xL4FilterConfig.Protocol = ETH_L4_TCP_MATCH;
                    #if ipconfigIS_DISABLED( ipconfigUSE_TCP )
                        xL4FilterConfig.SrcPortFilterMatch = ETH_L4_SRC_PORT_PERFECT_MATCH_ENABLE;
                        xL4FilterConfig.DestPortFilterMatch = ETH_L4_DEST_PORT_PERFECT_MATCH_ENABLE;
                        xL4FilterConfig.SourcePort = 0xFFFFU;
                        xL4FilterConfig.DestinationPort = 0xFFFFU;
                    #else
                        xL4FilterConfig.SrcPortFilterMatch = ETH_L4_SRC_PORT_MATCH_DISABLE;
                        xL4FilterConfig.DestPortFilterMatch = ETH_L4_DEST_PORT_MATCH_DISABLE;
                        xL4FilterConfig.SourcePort = 0U;
                        xL4FilterConfig.DestinationPort = 0U;
                    #endif
                    ( void ) HAL_ETHEx_SetL4FilterConfig( pxEthHandle, ETH_L4_FILTER_1, &xL4FilterConfig );
                }
                #endif /* if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS ) */

                HAL_ETHEx_EnableL3L4Filtering( pxEthHandle );
            }
        }
        #endif /* if ipconfigIS_ENABLED( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM ) */
    }

#endif /* ifdef niEMAC_STM32HX */

/*---------------------------------------------------------------------------*/

#if defined( niEMAC_STM32HX ) && ipconfigIS_ENABLED( ipconfigUSE_IPv4 )

    static void prvConfigureARPOffload( ETH_HandleTypeDef * pxEthHandle,
                                        const NetworkInterface_t * pxInterface )
    {
        EMACData_t * const pxEMACData = prvGetEMACDataByEthHandle( pxEthHandle );
        uint32_t ulARPOffloadAddress = 0U;

        if( pxEMACData == NULL )
        {
            return;
        }

        #if ipconfigIS_ENABLED( niEMAC_USE_ARP_OFFLOAD )
            UBaseType_t uxIPv4EndpointCount = 0U;
            NetworkEndPoint_t * pxEndPoint;

            for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
                 pxEndPoint != NULL;
                 pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
            {
                if( ENDPOINT_IS_IPv4( pxEndPoint ) &&
                    ( pxEndPoint->ipv4_settings.ulIPAddress != 0U ) )
                {
                    ulARPOffloadAddress = pxEndPoint->ipv4_settings.ulIPAddress;
                    ++uxIPv4EndpointCount;

                    if( uxIPv4EndpointCount > 1U )
                    {
                        ulARPOffloadAddress = 0U;
                        break;
                    }
                }
            }
        #else
            ( void ) pxInterface;
        #endif

        if( pxEMACData->ulCurrentARPOffloadAddress != ulARPOffloadAddress )
        {
            HAL_ETHEx_DisableARPOffload( pxEthHandle );

            if( ulARPOffloadAddress != 0U )
            {
                HAL_ETHEx_SetARPAddressMatch( pxEthHandle, ulARPOffloadAddress );
                HAL_ETHEx_EnableARPOffload( pxEthHandle );
            }

            pxEMACData->ulCurrentARPOffloadAddress = ulARPOffloadAddress;
        }
    }

#endif /* if defined( niEMAC_STM32HX ) && ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) */

/*---------------------------------------------------------------------------*/

static BaseType_t prvPhyInit( EthernetPhy_t * pxPhyObject )
{
    BaseType_t xResult = pdFAIL;

    vPhyInitialise( pxPhyObject, ( xApplicationPhyReadHook_t ) prvPhyReadReg, ( xApplicationPhyWriteHook_t ) prvPhyWriteReg );

    if( xPhyDiscover( pxPhyObject ) != 0 )
    {
        xResult = pdPASS;
    }

    return xResult;
}

static BaseType_t prvPhyStart( ETH_HandleTypeDef * pxEthHandle,
                               NetworkInterface_t * pxInterface,
                               EthernetPhy_t * pxPhyObject )
{
    BaseType_t xResult = pdFALSE;

    if( prvGetPhyLinkStatus( pxInterface ) == pdFALSE )
    {
        const PhyProperties_t xPhyProperties =
        {
            #if ipconfigIS_ENABLED( niEMAC_AUTO_NEGOTIATION )
                .ucSpeed  = PHY_SPEED_AUTO,
                .ucDuplex = PHY_DUPLEX_AUTO,
            #else
                .ucSpeed  = ipconfigIS_ENABLED( niEMAC_USE_100MB ) ? PHY_SPEED_100 : PHY_SPEED_10,
                .ucDuplex = ipconfigIS_ENABLED( niEMAC_USE_FULL_DUPLEX ) ? PHY_DUPLEX_FULL : PHY_DUPLEX_HALF,
            #endif

            #if ipconfigIS_ENABLED( niEMAC_AUTO_CROSS )
                .ucMDI_X  = PHY_MDIX_AUTO,
            #elif ipconfigIS_ENABLED( niEMAC_CROSSED_LINK )
                .ucMDI_X  = PHY_MDIX_CROSSED,
            #else
                .ucMDI_X  = PHY_MDIX_DIRECT,
            #endif
        };

        #if ipconfigIS_DISABLED( niEMAC_AUTO_NEGOTIATION )
            pxPhyObject->xPhyPreferences.ucSpeed = xPhyProperties.ucSpeed;
            pxPhyObject->xPhyPreferences.ucDuplex = xPhyProperties.ucDuplex;
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
static void prvHAL_ETH_SetDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                            uint8_t ucIndex,
                                            const uint8_t * const pucMACAddr )
{
    configASSERT( ucIndex < niEMAC_MAC_SRC_MATCH_COUNT );
    const uint32_t ulMacAddrHigh = ( pucMACAddr[ 5 ] << 8 ) | ( pucMACAddr[ 4 ] );
    const uint32_t ulMacAddrLow = ( pucMACAddr[ 3 ] << 24 ) | ( pucMACAddr[ 2 ] << 16 ) | ( pucMACAddr[ 1 ] << 8 ) | ( pucMACAddr[ 0 ] );

    /* MACA0HR/MACA0LR reserved for the primary MAC-address. */
    const uint32_t ulMacRegHigh = ( ( uint32_t ) &( pxEthInstance->MACA1HR ) + ( 8 * ucIndex ) );
    const uint32_t ulMacRegLow = ( ( uint32_t ) &( pxEthInstance->MACA1LR ) + ( 8 * ucIndex ) );
    ( *( __IO uint32_t * ) ulMacRegHigh ) = ETH_MACA1HR_AE | ulMacAddrHigh;
    ( *( __IO uint32_t * ) ulMacRegLow ) = ulMacAddrLow;
}

/*---------------------------------------------------------------------------*/

static void prvHAL_ETH_ClearDestMACAddrMatch( ETH_TypeDef * const pxEthInstance,
                                              uint8_t ucIndex )
{
    configASSERT( ucIndex < niEMAC_MAC_SRC_MATCH_COUNT );
    const uint32_t ulMacRegHigh = ( ( uint32_t ) &( pxEthInstance->MACA1HR ) + ( 8 * ucIndex ) );
    const uint32_t ulMacRegLow = ( ( uint32_t ) &( pxEthInstance->MACA1LR ) + ( 8 * ucIndex ) );
    ( *( __IO uint32_t * ) ulMacRegHigh ) = 0U;
    ( *( __IO uint32_t * ) ulMacRegLow ) = 0U;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvAddDestMACAddrMatch( EMACData_t * pxEMACData,
                                          ETH_TypeDef * const pxEthInstance,
                                          const uint8_t * const pucMACAddr )
{
    BaseType_t xResult = pdFALSE;

    uint8_t ucIndex;

    for( ucIndex = 0; ucIndex < niEMAC_MAC_SRC_MATCH_COUNT; ++ucIndex )
    {
        if( pxEMACData->ucSrcMatchCounters[ ucIndex ] > 0U )
        {
            /* ETH_MACA1HR_MBC - Group Address Filtering */
            const uintptr_t uxMacRegHigh = ( ( uintptr_t ) &( pxEthInstance->MACA1HR ) + ( 8U * ucIndex ) );
            const uintptr_t uxMacRegLow = ( ( uintptr_t ) &( pxEthInstance->MACA1LR ) + ( 8U * ucIndex ) );

            const uint32_t ulMacAddrHigh = ( pucMACAddr[ 5 ] << 8 ) | ( pucMACAddr[ 4 ] );
            const uint32_t ulMacAddrLow = ( pucMACAddr[ 3 ] << 24 ) | ( pucMACAddr[ 2 ] << 16 ) | ( pucMACAddr[ 1 ] << 8 ) | ( pucMACAddr[ 0 ] );
            const uint32_t ulMacRegHigh = ( *( __IO uint32_t * ) uxMacRegHigh );
            const uint32_t ulMacRegLow = ( *( __IO uint32_t * ) uxMacRegLow );

            if( ( ( ulMacRegHigh & 0xFFFFU ) == ulMacAddrHigh ) && ( ulMacRegLow == ulMacAddrLow ) )
            {
                if( pxEMACData->ucSrcMatchCounters[ ucIndex ] < UINT8_MAX )
                {
                    ++( pxEMACData->ucSrcMatchCounters[ ucIndex ] );
                }

                xResult = pdTRUE;
                break;
            }
        }
        else if( pxEMACData->uxMACEntryIndex > niEMAC_MAC_SRC_MATCH_COUNT )
        {
            pxEMACData->uxMACEntryIndex = niEMAC_MAC_SRC_MATCH_COUNT;
        }
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvRemoveDestMACAddrMatch( EMACData_t * pxEMACData,
                                             ETH_TypeDef * const pxEthInstance,
                                             const uint8_t * const pucMACAddr )
{
    BaseType_t xResult = pdFALSE;

    uint8_t ucIndex;

    for( ucIndex = 0; ucIndex < niEMAC_MAC_SRC_MATCH_COUNT; ++ucIndex )
    {
        if( pxEMACData->ucSrcMatchCounters[ ucIndex ] > 0U )
        {
            /* ETH_MACA1HR_MBC - Group Address Filtering */
            const uintptr_t uxMacRegHigh = ( ( uintptr_t ) &( pxEthInstance->MACA1HR ) + ( 8U * ucIndex ) );
            const uintptr_t uxMacRegLow = ( ( uintptr_t ) &( pxEthInstance->MACA1LR ) + ( 8U * ucIndex ) );

            const uint32_t ulMacAddrHigh = ( pucMACAddr[ 5 ] << 8 ) | ( pucMACAddr[ 4 ] );
            const uint32_t ulMacAddrLow = ( pucMACAddr[ 3 ] << 24 ) | ( pucMACAddr[ 2 ] << 16 ) | ( pucMACAddr[ 1 ] << 8 ) | ( pucMACAddr[ 0 ] );
            const uint32_t ulMacRegHigh = ( *( __IO uint32_t * ) uxMacRegHigh );
            const uint32_t ulMacRegLow = ( *( __IO uint32_t * ) uxMacRegLow );

            if( ( ( ulMacRegHigh & 0xFFFFU ) == ulMacAddrHigh ) && ( ulMacRegLow == ulMacAddrLow ) )
            {
                if( --( pxEMACData->ucSrcMatchCounters[ ucIndex ] ) == 0U )
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

static BaseType_t prvSetNewDestMACAddrMatch( EMACData_t * pxEMACData,
                                             ETH_TypeDef * const pxEthInstance,
                                             uint8_t ucHashIndex,
                                             const uint8_t * const pucMACAddr )
{
    BaseType_t xResult = pdFALSE;

    if( pxEMACData->uxMACEntryIndex < niEMAC_MAC_SRC_MATCH_COUNT )
    {
        if( pxEMACData->ucAddrHashCounters[ ucHashIndex ] == 0U )
        {
            prvHAL_ETH_SetDestMACAddrMatch( pxEthInstance, pxEMACData->uxMACEntryIndex, pucMACAddr );
            pxEMACData->ucSrcMatchCounters[ pxEMACData->uxMACEntryIndex++ ] = 1U;
            xResult = pdTRUE;
        }
    }

    return xResult;
}

/*---------------------------------------------------------------------------*/

static void prvAddDestMACAddrHash( EMACData_t * pxEMACData,
                                   ETH_HandleTypeDef * pxEthHandle,
                                   uint8_t ucHashIndex )
{
    if( pxEMACData->ucAddrHashCounters[ ucHashIndex ] == 0 )
    {
        if( ucHashIndex & 0x20U )
        {
            pxEMACData->ulHashTable[ 1 ] |= ( 1U << ( ucHashIndex & 0x1FU ) );
        }
        else
        {
            pxEMACData->ulHashTable[ 0 ] |= ( 1U << ucHashIndex );
        }

        HAL_ETH_SetHashTable( pxEthHandle, pxEMACData->ulHashTable );
    }

    if( pxEMACData->ucAddrHashCounters[ ucHashIndex ] < UINT8_MAX )
    {
        ++( pxEMACData->ucAddrHashCounters[ ucHashIndex ] );
    }
}

/*---------------------------------------------------------------------------*/

static void prvRemoveDestMACAddrHash( EMACData_t * pxEMACData,
                                      ETH_HandleTypeDef * pxEthHandle,
                                      const uint8_t * const pucMACAddr )
{
    const uint8_t ucHashIndex = prvGetMacHashIndex( pucMACAddr );

    if( pxEMACData->ucAddrHashCounters[ ucHashIndex ] > 0U )
    {
        if( --( pxEMACData->ucAddrHashCounters[ ucHashIndex ] ) == 0U )
        {
            if( ucHashIndex & 0x20U )
            {
                pxEMACData->ulHashTable[ 1 ] &= ~( 1U << ( ucHashIndex & 0x1FU ) );
            }
            else
            {
                pxEMACData->ulHashTable[ 0 ] &= ~( 1U << ucHashIndex );
            }

            HAL_ETH_SetHashTable( pxEthHandle, pxEMACData->ulHashTable );
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
    EMACData_t * const pxEMACData = prvGetEMACDataByEthHandle( pxEthHandle );

    if( ( pxEMACData != NULL ) &&
        ( xSemaphoreTake( pxEMACData->xTxMutex, pdMS_TO_TICKS( niEMAC_TX_MAX_BLOCK_TIME_MS ) ) != pdFALSE ) )
    {
        pxActiveEMACData = pxEMACData;
        ( void ) HAL_ETH_ReleaseTxPacket( pxEthHandle );
        ( void ) xSemaphoreGive( pxEMACData->xTxMutex );
    }
    else
    {
        FreeRTOS_debug_printf( ( "prvReleaseTxPacket: Failed\n" ) );
    }

    if( pxEMACData != NULL )
    {
        BaseType_t xResyncTxDescSem = pdTRUE;

        #if defined( niEMAC_STM32HX )
            #if ipconfigIS_ENABLED( niEMAC_USE_TCP_SEGMENTATION )
                xResyncTxDescSem = pdFALSE;
            #endif
            #if ipconfigIS_ENABLED( niEMAC_USE_VLAN_OFFLOAD )
                if( pxEMACData->xVLANEnabled != pdFALSE )
                {
                    xResyncTxDescSem = pdFALSE;
                }
            #endif
            #if ipconfigIS_ENABLED( niEMAC_USE_INNER_VLAN_OFFLOAD )
                if( ( pxEMACData->xVLANEnabled != pdFALSE ) &&
                    ( ( niEMAC_INNER_VLAN_IDENTIFIER & 0x3FFFFU ) != 0U ) )
                {
                    xResyncTxDescSem = pdFALSE;
                }
            #endif
        #endif

        if( xResyncTxDescSem == pdFALSE )
        {
            return;
        }

        UBaseType_t uxTxDescUsed = ( UBaseType_t ) HAL_ETH_GetTxBuffersNumber( pxEthHandle );

        uxTxDescUsed = ( uxTxDescUsed + ( niEMAC_TX_BUFFERS_PER_DESC - 1U ) ) / niEMAC_TX_BUFFERS_PER_DESC;

        if( uxTxDescUsed > ( UBaseType_t ) ETH_TX_DESC_CNT )
        {
            uxTxDescUsed = ( UBaseType_t ) ETH_TX_DESC_CNT;
        }

        const UBaseType_t uxExpectedFree = ( UBaseType_t ) ETH_TX_DESC_CNT - uxTxDescUsed;
        UBaseType_t uxSemCount = uxSemaphoreGetCount( pxEMACData->xTxDescSem );

        while( uxSemCount < uxExpectedFree )
        {
            if( xSemaphoreGive( pxEMACData->xTxDescSem ) == pdFALSE )
            {
                break;
            }

            uxSemCount++;
        }

        while( uxSemCount > uxExpectedFree )
        {
            if( xSemaphoreTake( pxEMACData->xTxDescSem, 0U ) == pdFALSE )
            {
                break;
            }

            uxSemCount--;
        }
    }
}

/*---------------------------------------------------------------------------*/

static BaseType_t prvMacUpdateConfig( ETH_HandleTypeDef * pxEthHandle,
                                      EthernetPhy_t * pxPhyObject )
{
    BaseType_t xResult = pdFALSE;

    if( HAL_ETH_GetState( pxEthHandle ) == HAL_ETH_STATE_STARTED )
    {
        ( void ) HAL_ETH_Stop_IT( pxEthHandle );
    }

    #if ipconfigIS_ENABLED( niEMAC_AUTO_NEGOTIATION )
        ( void ) xPhyStartAutoNegotiation( pxPhyObject, xPhyGetMask( pxPhyObject ) );
    #else
        ( void ) xPhyFixedValue( pxPhyObject, xPhyGetMask( pxPhyObject ) );
    #endif

    if( prvApplyMACDMAConfig( pxEthHandle, pxPhyObject ) != pdFALSE )
    {
        xResult = pdTRUE;
    }

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
    }
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

static BaseType_t prvAcceptPacket( EMACData_t * pxEMACData,
                                   const NetworkBufferDescriptor_t * const pxDescriptor,
                                   uint16_t usLength )
{
    BaseType_t xResult = pdFALSE;
    ETH_HandleTypeDef * pxEthHandle = NULL;

    do
    {
        if( pxDescriptor == NULL )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Null Descriptor\n" ) );
            break;
        }

        if( usLength > pxDescriptor->xDataLength )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Packet size overflow\n" ) );
            break;
        }

        if( pxEMACData == NULL )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Invalid Interface\n" ) );
            break;
        }

        pxEthHandle = &( pxEMACData->xEthHandle );
        uint32_t ulErrorCode = 0;
        ( void ) HAL_ETH_GetRxDataErrorCode( pxEthHandle, &ulErrorCode );

        if( ulErrorCode != 0 )
        {
            iptraceETHERNET_RX_EVENT_LOST();
            FreeRTOS_debug_printf( ( "prvAcceptPacket: Rx Data Error\n" ) );
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

        #if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )
        {
            const uint32_t ulPrevIdx = ( pxEthHandle->RxDescList.RxDescIdx + ETH_RX_DESC_CNT - 1U ) % ETH_RX_DESC_CNT;
            const ETH_DMADescTypeDef * const pxRxDesc = ( const ETH_DMADescTypeDef * const ) pxEthHandle->RxDescList.RxDesc[ ulPrevIdx ];
            uint32_t ulRxDesc;
            #ifdef niEMAC_STM32HX
                ulRxDesc = pxRxDesc->DESC1;
            #elif defined( niEMAC_STM32FX )
                ulRxDesc = pxRxDesc->DESC4;
            #endif

            if( ( ulRxDesc & ETH_IP_HEADER_IPV4 ) != 0 )
            {
                /* Should be impossible if hardware filtering is implemented correctly */
                configASSERT( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) );
                #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
                    /* prvAllowIPPacketIPv4(); */
                #endif
            }
            else if( ( ulRxDesc & ETH_IP_HEADER_IPV6 ) != 0 )
            {
                /* Should be impossible if hardware filtering is implemented correctly */
                configASSERT( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) );
                #if ipconfigIS_ENABLED( ipconfigUSE_IPv6 )
                    /* prvAllowIPPacketIPv6(); */
                #endif
            }

            if( ( ulRxDesc & ETH_IP_PAYLOAD_MASK ) == ETH_IP_PAYLOAD_UNKNOWN )
            {
                /* Likely ARP */
            }
            else if( ( ulRxDesc & ETH_IP_PAYLOAD_MASK ) == ETH_IP_PAYLOAD_UDP )
            {
                /* prvProcessUDPPacket(); */
            }
            else if( ( ulRxDesc & ETH_IP_PAYLOAD_MASK ) == ETH_IP_PAYLOAD_TCP )
            {
                /* Should be impossible if hardware filtering is implemented correctly */
                configASSERT( ipconfigIS_ENABLED( ipconfigUSE_TCP ) );
                #if ipconfigIS_ENABLED( ipconfigUSE_TCP )
                    /* xProcessReceivedTCPPacket() */
                #endif
            }
            else if( ( ulRxDesc & ETH_IP_PAYLOAD_MASK ) == ETH_IP_PAYLOAD_ICMPN )
            {
                #if ipconfigIS_DISABLED( ipconfigREPLY_TO_INCOMING_PINGS ) && ipconfigIS_DISABLED( ipconfigSUPPORT_OUTGOING_PINGS )
                    iptraceETHERNET_RX_EVENT_LOST();
                    break;
                #else
                    /* ProcessICMPPacket(); */
                #endif
            }

            #ifdef niEMAC_STM32HX
                else if( ( ulRxDesc & ETH_IP_PAYLOAD_MASK ) == ETH_IP_PAYLOAD_IGMP )
                {
                }
            #endif

            if( eConsiderPacketForProcessing( pxDescriptor->pucEthernetBuffer ) != eProcessBuffer )
            {
                iptraceETHERNET_RX_EVENT_LOST();
                FreeRTOS_debug_printf( ( "prvAcceptPacket: Packet discarded\n" ) );
                break;
            }
        }
        #endif /* if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS ) */

        xResult = pdTRUE;
    } while( pdFALSE );

    return xResult;
}

/*---------------------------------------------------------------------------*/

#if ipconfigIS_ENABLED( ipconfigETHERNET_DRIVER_FILTERS_PACKETS )

    static eFrameProcessingResult_t eConsiderPacketForProcessing( const uint8_t * const pucEthernetBuffer )
    {
        if( pucEthernetBuffer == NULL )
        {
            return eReleaseBuffer;
        }

        const EthernetHeader_t * const pxEthernetHeader = ( const EthernetHeader_t * const ) pucEthernetBuffer;

        switch( pxEthernetHeader->usFrameType )
        {
            case ipARP_FRAME_TYPE:
                #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
                    return eProcessBuffer;
                #else
                    return eReleaseBuffer;
                #endif

            case ipIPv4_FRAME_TYPE:
                #if ipconfigIS_ENABLED( ipconfigUSE_IPv4 )
                {
                    const IPPacket_t * const pxIPPacket = ( const IPPacket_t * const ) pucEthernetBuffer;

                    switch( pxIPPacket->xIPHeader.ucProtocol )
                    {
                        case ipPROTOCOL_UDP:
                            return eProcessBuffer;

                        case ipPROTOCOL_TCP:
                            #if ipconfigIS_ENABLED( ipconfigUSE_TCP )
                                return eProcessBuffer;
                            #else
                                return eReleaseBuffer;
                            #endif

                        case ipPROTOCOL_ICMP:
                            #if ipconfigIS_ENABLED( ipconfigREPLY_TO_INCOMING_PINGS ) || ipconfigIS_ENABLED( ipconfigSUPPORT_OUTGOING_PINGS )
                                return eProcessBuffer;
                            #else
                                return eReleaseBuffer;
                            #endif

                        default:
                            return eReleaseBuffer;
                    }
                }
                #else
                    return eReleaseBuffer;
                #endif

            case ipIPv6_FRAME_TYPE:
                #if ipconfigIS_ENABLED( ipconfigUSE_IPv6 )
                {
                    const IPPacket_IPv6_t * const pxIPPacket_IPv6 = ( const IPPacket_IPv6_t * const ) pucEthernetBuffer;

                    switch( pxIPPacket_IPv6->xIPHeader.ucNextHeader )
                    {
                        case ipPROTOCOL_UDP:
                            return eProcessBuffer;

                        case ipPROTOCOL_TCP:
                            #if ipconfigIS_ENABLED( ipconfigUSE_TCP )
                                return eProcessBuffer;
                            #else
                                return eReleaseBuffer;
                            #endif

                        case ipPROTOCOL_ICMP_IPv6:
                            return eProcessBuffer;

                        default:
                            return eReleaseBuffer;
                    }
                }
                #else
                    return eReleaseBuffer;
                #endif

            default:
                return eReleaseBuffer;
        }
    }

#endif

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              IRQ Handlers                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

void ETH_IRQHandler( void )
{
    traceISR_ENTER();

    BaseType_t xSwitchRequired = pdFALSE;
    EMACData_t * pxEMACData = ( EMACData_t * ) pxActiveEMACData;

    if( ( pxEMACData == NULL ) || ( pxEMACData->xEthHandle.Instance == NULL ) )
    {
        for( UBaseType_t uxIndex = 0U; uxIndex < niEMAC_MAX_INTERFACE_NAMES; uxIndex++ )
        {
            if( ( pxInterfaces[ uxIndex ] != NULL ) &&
                ( xEMACData[ uxIndex ].xEthHandle.Instance != NULL ) )
            {
                pxEMACData = &( xEMACData[ uxIndex ] );
                break;
            }
        }
    }

    if( pxEMACData != NULL )
    {
        pxActiveEMACData = pxEMACData;
        pxEMACData->xSwitchRequired = pdFALSE;
        HAL_ETH_IRQHandler( &( pxEMACData->xEthHandle ) );
        xSwitchRequired = pxEMACData->xSwitchRequired;
    }

    portYIELD_FROM_ISR( xSwitchRequired );
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_ErrorCallback( ETH_HandleTypeDef * pxEthHandle )
{
    EMACData_t * const pxEMACData = prvGetEMACDataByEthHandle( pxEthHandle );
    eMAC_IF_EVENT eErrorEvents = eMacEventNone;
    const HAL_ETH_StateTypeDef xEthState = HAL_ETH_GetState( pxEthHandle );
    const uint32_t ulEthError = HAL_ETH_GetError( pxEthHandle );

    if( xEthState == HAL_ETH_STATE_ERROR )
    {
        /* Fatal bus error occurred */
        eErrorEvents |= eMacEventErrEth;
    }

    if( ( ulEthError & HAL_ETH_ERROR_DMA ) != 0 )
    {
        eErrorEvents |= eMacEventErrDma;
        const uint32_t ulDmaError = HAL_ETH_GetDMAError( pxEthHandle );

        if( ( ulDmaError & ETH_DMA_TX_BUFFER_UNAVAILABLE_FLAG ) != 0 )
        {
            eErrorEvents |= eMacEventErrTx;
        }

        if( ( ulDmaError & ETH_DMA_RX_BUFFER_UNAVAILABLE_FLAG ) != 0 )
        {
            eErrorEvents |= eMacEventErrRx;
        }
    }

    if( ( HAL_ETH_GetError( pxEthHandle ) & HAL_ETH_ERROR_MAC ) != 0 )
    {
        eErrorEvents |= eMacEventErrMac;
    }

    if( ( pxEMACData != NULL ) &&
        ( eErrorEvents != eMacEventNone ) )
    {
        prvWakeEMACTaskFromISR( pxEMACData, eErrorEvents );
    }
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_RxCpltCallback( ETH_HandleTypeDef * pxEthHandle )
{
    EMACData_t * const pxEMACData = prvGetEMACDataByEthHandle( pxEthHandle );
    static volatile size_t uxMostRXDescsUsed = 0U;

    const size_t uxRxUsed = pxEthHandle->RxDescList.RxDescCnt;

    if( uxMostRXDescsUsed < uxRxUsed )
    {
        uxMostRXDescsUsed = uxRxUsed;
    }

    iptraceNETWORK_INTERFACE_RECEIVE();

    if( ( pxEMACData != NULL ) && ( pxEMACData->xEMACTaskHandle != NULL ) )
    {
        prvWakeEMACTaskFromISR( pxEMACData, eMacEventRx );
    }
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_TxCpltCallback( ETH_HandleTypeDef * pxEthHandle )
{
    EMACData_t * const pxEMACData = prvGetEMACDataByEthHandle( pxEthHandle );
    static volatile size_t uxMostTXDescsUsed = 0U;

    const size_t uxTxUsed = HAL_ETH_GetTxBuffersNumber( pxEthHandle );

    if( uxMostTXDescsUsed < uxTxUsed )
    {
        uxMostTXDescsUsed = uxTxUsed;
    }

    iptraceNETWORK_INTERFACE_TRANSMIT();

    if( ( pxEMACData != NULL ) && ( pxEMACData->xEMACTaskHandle != NULL ) )
    {
        prvWakeEMACTaskFromISR( pxEMACData, eMacEventTx );
    }
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_PMTCallback( ETH_HandleTypeDef * pxEthHandle )
{
    EMACData_t * const pxEMACData = prvGetEMACDataByEthHandle( pxEthHandle );

    if( pxEMACData == NULL )
    {
        return;
    }

    pxEMACData->xPowerDownActive = pdFALSE;
    pxEMACData->ulLastWakeUpSource = HAL_ETH_GetMACWakeUpSource( pxEthHandle );

    NetworkInterface_t * const pxInterface = prvGetInterfaceByEMACData( pxEMACData );
    niEMAC_WAKE_EVENT_HOOK( pxInterface, pxEMACData->ulLastWakeUpSource );

    prvWakeEMACTaskFromISR( pxEMACData, eMacEventTxPending );
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_WakeUpCallback( ETH_HandleTypeDef * pxEthHandle )
{
    EMACData_t * const pxEMACData = prvGetEMACDataByEthHandle( pxEthHandle );

    if( pxEMACData == NULL )
    {
        return;
    }

    uint32_t ulWakeUpSource = HAL_ETH_GetMACWakeUpSource( pxEthHandle );

    if( ulWakeUpSource == 0U )
    {
        ulWakeUpSource = pxEMACData->ulLastWakeUpSource;
    }
    else
    {
        pxEMACData->ulLastWakeUpSource = ulWakeUpSource;
    }

    pxEMACData->xPowerDownActive = pdFALSE;

    NetworkInterface_t * const pxInterface = prvGetInterfaceByEMACData( pxEMACData );
    niEMAC_WAKE_EVENT_HOOK( pxInterface, ulWakeUpSource );

    prvWakeEMACTaskFromISR( pxEMACData, eMacEventTxPending );
}

/*---------------------------------------------------------------------------*/

#if defined( niEMAC_STM32HX )

    void HAL_ETH_EEECallback( ETH_HandleTypeDef * pxEthHandle )
    {
        EMACData_t * const pxEMACData = prvGetEMACDataByEthHandle( pxEthHandle );

        if( pxEMACData == NULL )
        {
            return;
        }

        pxEMACData->ulLastLPIEvent = HAL_ETHEx_GetMACLPIEvent( pxEthHandle );

        NetworkInterface_t * const pxInterface = prvGetInterfaceByEMACData( pxEMACData );
        niEMAC_LPI_EVENT_HOOK( pxInterface, pxEMACData->ulLastLPIEvent );

        prvWakeEMACTaskFromISR( pxEMACData, eMacEventTxPending );
    }

#endif /* if defined( niEMAC_STM32HX ) */

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
        #ifdef niEMAC_CACHEABLE
            if( niEMAC_CACHE_MAINTENANCE != 0 )
            {
                const uintptr_t uxDataStart = ( uintptr_t ) pxBufferDescriptor->pucEthernetBuffer;
                const uintptr_t uxLineStart = uxDataStart & ~niEMAC_DATA_ALIGNMENT_MASK;
                const size_t uxDataOffset = ( size_t ) ( uxDataStart - uxLineStart );
                const size_t uxLength = ( ( pxBufferDescriptor->xDataLength + uxDataOffset + niEMAC_DATA_ALIGNMENT_MASK ) & ~niEMAC_DATA_ALIGNMENT_MASK );
                SCB_InvalidateDCache_by_Addr( ( uint32_t * ) uxLineStart, uxLength );
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
    EMACData_t * const pxEMACData = ( EMACData_t * ) pxActiveEMACData;
    NetworkBufferDescriptor_t ** const ppxStartDescriptor = ( NetworkBufferDescriptor_t ** ) ppvStart;
    NetworkBufferDescriptor_t ** const ppxEndDescriptor = ( NetworkBufferDescriptor_t ** ) ppvEnd;
    NetworkBufferDescriptor_t * const pxCurDescriptor = pxPacketBuffer_to_NetworkBuffer( ( const void * ) pucBuff );

    if( pxEMACData == NULL )
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxLinkCallback: Invalid interface context\n" ) );
        if( pxCurDescriptor != NULL )
        {
            prvReleaseNetworkBufferDescriptor( pxCurDescriptor );
        }
        return;
    }

    if( pxCurDescriptor == NULL )
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxLinkCallback: Invalid buffer descriptor\n" ) );
        return;
    }

    #ifdef niEMAC_CACHEABLE
        if( niEMAC_CACHE_MAINTENANCE != 0 )
        {
            const uintptr_t uxDataStart = ( uintptr_t ) pucBuff;
            const uintptr_t uxLineStart = uxDataStart & ~niEMAC_DATA_ALIGNMENT_MASK;
            const size_t uxDataOffset = ( size_t ) ( uxDataStart - uxLineStart );
            const size_t uxLength = ( ( ( size_t ) usLength + uxDataOffset + niEMAC_DATA_ALIGNMENT_MASK ) & ~niEMAC_DATA_ALIGNMENT_MASK );
            SCB_InvalidateDCache_by_Addr( ( uint32_t * ) uxLineStart, uxLength );
        }
    #endif

    if( pxEMACData->xDropCurrentRxFrame != pdFALSE )
    {
        if( *ppxStartDescriptor != NULL )
        {
            prvReleaseNetworkBufferDescriptor( pxCurDescriptor );
            return;
        }

        pxEMACData->xDropCurrentRxFrame = pdFALSE;
    }

    if( *ppxStartDescriptor == NULL )
    {
        if( prvAcceptPacket( pxEMACData, pxCurDescriptor, usLength ) == pdTRUE )
        {
            pxCurDescriptor->xDataLength = usLength;
            #if ipconfigIS_ENABLED( ipconfigUSE_LINKED_RX_MESSAGES )
                pxCurDescriptor->pxNextBuffer = NULL;
            #endif

            *ppxStartDescriptor = pxCurDescriptor;
            *ppxEndDescriptor = pxCurDescriptor;
        }
        else
        {
            FreeRTOS_debug_printf( ( "HAL_ETH_RxLinkCallback: Buffer Dropped\n" ) );
            prvReleaseNetworkBufferDescriptor( pxCurDescriptor );
        }

        return;
    }

    if( usLength == 0U )
    {
        prvReleaseNetworkBufferDescriptor( pxCurDescriptor );
        return;
    }

    NetworkBufferDescriptor_t * const pxStartDescriptor = *ppxStartDescriptor;
    const size_t uxCurrentLength = pxStartDescriptor->xDataLength;
    const size_t uxNewLength = uxCurrentLength + ( size_t ) usLength;

    if( uxNewLength > niEMAC_DATA_BUFFER_SIZE )
    {
        FreeRTOS_debug_printf( ( "HAL_ETH_RxLinkCallback: Multi-buffer frame overflow\n" ) );
        pxEMACData->xDropCurrentRxFrame = pdTRUE;
        prvReleaseNetworkBufferDescriptor( pxCurDescriptor );
        return;
    }

    configASSERT( niEMAC_DATA_BUFFER_SIZE <= ( niEMAC_TOTAL_BUFFER_SIZE - ipBUFFER_PADDING ) );
    ( void ) memcpy( &( pxStartDescriptor->pucEthernetBuffer[ uxCurrentLength ] ), pucBuff, usLength );
    pxStartDescriptor->xDataLength = uxNewLength;
    *ppxEndDescriptor = pxStartDescriptor;
    prvReleaseNetworkBufferDescriptor( pxCurDescriptor );
}

/*---------------------------------------------------------------------------*/

void HAL_ETH_TxFreeCallback( uint32_t * pulBuff )
{
    TxPacketMeta_t * const pxTxMeta = ( TxPacketMeta_t * ) pulBuff;
    NetworkBufferDescriptor_t * pxNetworkBuffer = NULL;
    EMACData_t * pxEMACData = NULL;
    size_t uxDescCount = 0U;

    if( pxTxMeta == NULL )
    {
        return;
    }

    pxNetworkBuffer = pxTxMeta->pxDescriptor;
    pxEMACData = pxTxMeta->pxEMACData;
    uxDescCount = pxTxMeta->uxDescCount;
    pxTxMeta->xInUse = pdFALSE;
    pxTxMeta->pxDescriptor = NULL;
    pxTxMeta->pxEMACData = NULL;
    pxTxMeta->uxDescCount = 0U;

    prvReleaseNetworkBufferDescriptor( pxNetworkBuffer );

    if( pxEMACData != NULL )
    {
        for( size_t uxIndex = 0U; uxIndex < uxDescCount; uxIndex++ )
        {
            ( void ) xSemaphoreGive( pxEMACData->xTxDescSem );
        }

        if( pxEMACData->xEMACTaskHandle != NULL )
        {
            ( void ) xTaskNotify( pxEMACData->xEMACTaskHandle, eMacEventTxPending, eSetBits );
        }
    }
}

/*---------------------------------------------------------------------------*/

#if defined( HAL_ETH_USE_PTP )

    void HAL_ETH_TxPtpCallback( uint32_t * pulBuff,
                                ETH_TimeStampTypeDef * pxTimeStamp )
    {
        TxPacketMeta_t * const pxTxMeta = ( TxPacketMeta_t * ) pulBuff;

        if( ( pxTxMeta == NULL ) ||
            ( pxTxMeta->pxEMACData == NULL ) )
        {
            return;
        }

        EMACData_t * const pxEMACData = pxTxMeta->pxEMACData;

        if( pxEMACData->xPTPConfigured == pdFALSE )
        {
            return;
        }

        ETH_HandleTypeDef * const pxEthHandle = &( pxEMACData->xEthHandle );
        ETH_TimeStampTypeDef xTxTimeStamp;
        const ETH_TimeStampTypeDef * pxSelectedTimeStamp = pxTimeStamp;

        if( HAL_ETH_PTP_GetTxTimestamp( pxEthHandle, &xTxTimeStamp ) == HAL_OK )
        {
            pxSelectedTimeStamp = &xTxTimeStamp;
        }

        if( pxSelectedTimeStamp == NULL )
        {
            return;
        }

        pxEMACData->xLastTxTimeStamp = *pxSelectedTimeStamp;

        NetworkInterface_t * const pxInterface = prvGetInterfaceByEMACData( pxEMACData );
        prvCapturePTPTime( pxEthHandle, pxEMACData, pxInterface );
        niEMAC_PTP_TX_TIMESTAMP_HOOK( pxInterface, pxTxMeta->pxDescriptor, &( pxEMACData->xLastTxTimeStamp ) );
    }

#endif

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

    return (niEMAC_TOTAL_BUFFER_SIZE - ipBUFFER_PADDING);
}

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                      Network Interface Definition                         */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

NetworkInterface_t * pxSTM32_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                      NetworkInterface_t * pxInterface )
{
    static char pcName[ niEMAC_MAX_INTERFACE_NAMES ][ sizeof( "eth00" ) ];
    const UBaseType_t uxNameIndex = ( UBaseType_t ) xEMACIndex;
    EMACData_t * pxEMACData;

    if( uxNameIndex >= niEMAC_MAX_INTERFACE_NAMES )
    {
        FreeRTOS_debug_printf( ( "pxSTM32_FillInterfaceDescriptor: Invalid xEMACIndex\n" ) );
        return NULL;
    }

    pxEMACData = &( xEMACData[ uxNameIndex ] );

    ( void ) snprintf( pcName[ uxNameIndex ], sizeof( pcName[ uxNameIndex ] ), "eth%u", ( unsigned ) uxNameIndex );

    ( void ) memset( pxInterface, '\0', sizeof( *pxInterface ) );
    ( void ) memset( pxEMACData, '\0', sizeof( *pxEMACData ) );
    pxInterface->pcName = pcName[ uxNameIndex ];
    pxInterface->pvArgument = ( void * ) pxEMACData;
    pxInterface->pfInitialise = prvNetworkInterfaceInitialise;
    pxInterface->pfOutput = prvNetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = prvGetPhyLinkStatus;

    pxInterface->pfAddAllowedMAC = prvAddAllowedMACAddress;
    pxInterface->pfRemoveAllowedMAC = prvRemoveAllowedMACAddress;
    pxEMACData->xEMACIndex = xEMACIndex;
    pxEMACData->xMacInitStatus = eMacEthInit;
    pxInterfaces[ uxNameIndex ] = pxInterface;

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
        return pxSTM32_FillInterfaceDescriptor( xEMACIndex, pxInterface );
    }

#endif

/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                          Sample HAL User Functions                        */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/

#if 0

/**
 * @brief  Initializes the ETH MSP.
 * @param  heth: ETH handle
 * @retval None
 */
    void HAL_ETH_MspInit( ETH_HandleTypeDef * pxEthHandle )
    {
        if( pxEthHandle->Instance == ETH )
        {
            /* Enable ETHERNET clock */
            #ifdef niEMAC_STM32FX
                __HAL_RCC_ETH_CLK_ENABLE();
            #elif defined( STM32H5 )
                __HAL_RCC_ETH_CLK_ENABLE();
                __HAL_RCC_ETHTX_CLK_ENABLE();
                __HAL_RCC_ETHRX_CLK_ENABLE();
            #elif defined( STM32H7 )
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
             *  Common Pins
             *  ETH_MDC ----------------------> ETH_MDC_Port, ETH_MDC_Pin
             *  ETH_MDIO --------------------->
             *  ETH_RXD0 --------------------->
             *  ETH_RXD1 --------------------->
             *  ETH_TX_EN -------------------->
             *  ETH_TXD0 --------------------->
             *  ETH_TXD1 --------------------->
             *
             *  RMII Specific Pins
             *  ETH_REF_CLK ------------------>
             *  ETH_CRS_DV ------------------->
             *
             *  MII Specific Pins
             *  ETH_RX_CLK ------------------->
             *  ETH_RX_ER -------------------->
             *  ETH_RX_DV -------------------->
             *  ETH_RXD2 --------------------->
             *  ETH_RXD3 --------------------->
             *  ETH_TX_CLK ------------------->
             *  ETH_TXD2 --------------------->
             *  ETH_TXD3 --------------------->
             *  ETH_CRS ---------------------->
             *  ETH_COL ---------------------->
             */

            GPIO_InitTypeDef GPIO_InitStructure = { 0 };
            GPIO_InitStructure.Speed = GPIO_SPEED_HIGH;
            GPIO_InitStructure.Mode = GPIO_MODE_AF_PP;
            GPIO_InitStructure.Pull = GPIO_NOPULL;
            GPIO_InitStructure.Alternate = GPIO_AF11_ETH;

            GPIO_InitStructure.Pin = ETH_MDC_Pin;
            GPIO_InitStructure.Speed = GPIO_SPEED_MEDIUM;
            HAL_GPIO_Init( ETH_MDC_Port, &GPIO_InitStructure );
            GPIO_InitStructure.Speed = GPIO_SPEED_HIGH;

            GPIO_InitStructure.Pin = ETH_MDIO_Pin;
            HAL_GPIO_Init( ETH_MDIO_Port, &GPIO_InitStructure );

            GPIO_InitStructure.Pin = ETH_RXD0_Pin;
            HAL_GPIO_Init( ETH_RXD0_Port, &GPIO_InitStructure );

            GPIO_InitStructure.Pin = ETH_RXD1_Pin;
            HAL_GPIO_Init( ETH_RXD1_Port, &GPIO_InitStructure );

            GPIO_InitStructure.Pin = ETH_TX_EN_Pin;
            HAL_GPIO_Init( ETH_TX_EN_Port, &GPIO_InitStructure );

            GPIO_InitStructure.Pin = ETH_TXD0_Pin;
            HAL_GPIO_Init( ETH_TXD0_Port, &GPIO_InitStructure );

            GPIO_InitStructure.Pin = ETH_TXD1_Pin;
            HAL_GPIO_Init( ETH_TXD1_Port, &GPIO_InitStructure );

            if( pxEthHandle->Init.MediaInterface == HAL_ETH_RMII_MODE )
            {
                GPIO_InitStructure.Pin = ETH_REF_CLK_Pin;
                HAL_GPIO_Init( ETH_REF_CLK_Port, &GPIO_InitStructure );

                GPIO_InitStructure.Pin = ETH_CRS_DV_Pin;
                HAL_GPIO_Init( ETH_CRS_DV_Port, &GPIO_InitStructure );
            }
            else if( pxEthHandle->Init.MediaInterface == HAL_ETH_MII_MODE )
            {
                GPIO_InitStructure.Pin = ETH_RX_CLK_Pin;
                HAL_GPIO_Init( ETH_RX_CLK_Port, &GPIO_InitStructure );

                GPIO_InitStructure.Pin = ETH_RX_ER_Pin;
                HAL_GPIO_Init( ETH_RX_ER_Port, &GPIO_InitStructure );

                GPIO_InitStructure.Pin = ETH_RX_DV_Pin;
                HAL_GPIO_Init( ETH_RX_DV_Port, &GPIO_InitStructure );

                GPIO_InitStructure.Pin = ETH_RXD2_Pin;
                HAL_GPIO_Init( ETH_RXD2_Port, &GPIO_InitStructure );

                GPIO_InitStructure.Pin = ETH_RXD3_Pin;
                HAL_GPIO_Init( ETH_RXD3_Port, &GPIO_InitStructure );

                GPIO_InitStructure.Pin = ETH_TX_CLK_Pin;
                HAL_GPIO_Init( ETH_TX_CLK_Port, &GPIO_InitStructure );

                GPIO_InitStructure.Pin = ETH_TXD2_Pin;
                HAL_GPIO_Init( ETH_TXD2_Port, &GPIO_InitStructure );

                GPIO_InitStructure.Pin = ETH_TXD3_Pin;
                HAL_GPIO_Init( ETH_TXD3_Port, &GPIO_InitStructure );

                GPIO_InitStructure.Pin = ETH_COL_Pin;
                HAL_GPIO_Init( ETH_COL_Port, &GPIO_InitStructure );

                GPIO_InitStructure.Pin = ETH_CRS_Pin;
                HAL_GPIO_Init( ETH_CRS_Port, &GPIO_InitStructure );
            }

            /* Enable the Ethernet global Interrupt */
            HAL_NVIC_SetPriority( ETH_IRQn, ( uint32_t ) configMAX_SYSCALL_INTERRUPT_PRIORITY, 0 );
            HAL_NVIC_EnableIRQ( ETH_IRQn );
        }
    }

/*---------------------------------------------------------------------------*/

    void HAL_ETH_MspDeInit( ETH_HandleTypeDef * pxEthHandle )
    {
        if( pxEthHandle->Instance == ETH )
        {
            /* Peripheral clock disable */
            #ifdef niEMAC_STM32FX
                __HAL_RCC_ETH_CLK_DISABLE();
            #elif defined( STM32H5 )
                __HAL_RCC_ETH_CLK_DISABLE();
                __HAL_RCC_ETHTX_CLK_DISABLE();
                __HAL_RCC_ETHRX_CLK_DISABLE();
            #elif defined( STM32H7 )
                __HAL_RCC_ETH1MAC_CLK_DISABLE();
                __HAL_RCC_ETH1TX_CLK_DISABLE();
                __HAL_RCC_ETH1RX_CLK_DISABLE();
            #endif

            /**ETH GPIO Configuration
             * Common Pins
             * ETH_MDC ----------------------> ETH_MDC_Port, ETH_MDC_Pin
             * ETH_MDIO --------------------->
             * ETH_RXD0 --------------------->
             * ETH_RXD1 --------------------->
             * ETH_TX_EN -------------------->
             * ETH_TXD0 --------------------->
             * ETH_TXD1 --------------------->
             *
             * RMII Specific Pins
             * ETH_REF_CLK ------------------>
             * ETH_CRS_DV ------------------->
             *
             * MII Specific Pins
             * ETH_RX_CLK ------------------->
             * ETH_RX_ER -------------------->
             * ETH_RX_DV -------------------->
             * ETH_RXD2 --------------------->
             * ETH_RXD3 --------------------->
             * ETH_TX_CLK ------------------->
             * ETH_TXD2 --------------------->
             * ETH_TXD3 --------------------->
             * ETH_CRS ---------------------->
             * ETH_COL ---------------------->
             */

            HAL_GPIO_DeInit( ETH_MDC_Port, ETH_MDC_Pin );
            HAL_GPIO_DeInit( ETH_MDIO_Port, ETH_MDIO_Pin );
            HAL_GPIO_DeInit( ETH_RXD0_Port, ETH_RXD0_Pin );
            HAL_GPIO_DeInit( ETH_RXD1_Port, ETH_RXD1_Pin );
            HAL_GPIO_DeInit( ETH_TX_EN_Port, ETH_TX_EN_Pin );
            HAL_GPIO_DeInit( ETH_TXD0_Port, ETH_TXD0_Pin );
            HAL_GPIO_DeInit( ETH_TXD1_Port, ETH_TXD1_Pin );

            if( pxEthHandle->Init.MediaInterface == HAL_ETH_RMII_MODE )
            {
                HAL_GPIO_DeInit( ETH_REF_CLK_Port, ETH_REF_CLK_Pin );
                HAL_GPIO_DeInit( ETH_CRS_DV_Port, ETH_CRS_DV_Pin );
            }
            else if( pxEthHandle->Init.MediaInterface == HAL_ETH_MII_MODE )
            {
                HAL_GPIO_DeInit( ETH_RX_CLK_Port, ETH_RX_CLK_Pin );
                HAL_GPIO_DeInit( ETH_RX_ER_Port, ETH_RX_ER_Pin );
                HAL_GPIO_DeInit( ETH_RX_DV_Port, ETH_RX_DV_Pin );
                HAL_GPIO_DeInit( ETH_RXD2_Port, ETH_RXD2_Pin );
                HAL_GPIO_DeInit( ETH_RXD3_Port, ETH_RXD3_Pin );
                HAL_GPIO_DeInit( ETH_TX_CLK_Port, ETH_TX_CLK_Pin );
                HAL_GPIO_DeInit( ETH_TXD2_Port, ETH_TXD2_Pin );
                HAL_GPIO_DeInit( ETH_TXD3_Port, ETH_TXD3_Pin );
                HAL_GPIO_DeInit( ETH_COL_Port, ETH_COL_Pin );
                HAL_GPIO_DeInit( ETH_CRS_Port, ETH_CRS_Pin );
            }

            /* ETH interrupt Deinit */
            HAL_NVIC_DisableIRQ( ETH_IRQn );
        }
    }

/*---------------------------------------------------------------------------*/

    #if defined( __MPU_PRESENT ) && ( __MPU_PRESENT == 1U )

        void MPU_Config( void )
        {
            MPU_Region_InitTypeDef MPU_InitStruct = { 0 };

            HAL_MPU_Disable();

            extern uint8_t __ETH_BUFFERS_START;

            MPU_InitStruct.Enable = ipconfigIS_ENABLED( niEMAC_USE_MPU ) ? ENABLE : DISABLE;
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

            HAL_MPU_ConfigRegion( &MPU_InitStruct );


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

            HAL_MPU_ConfigRegion( &MPU_InitStruct );

            HAL_MPU_Enable( MPU_PRIVILEGED_DEFAULT );
        }

    #endif /* if defined( __MPU_PRESENT ) && ( __MPU_PRESENT == 1U ) */

#endif /* if 0 */

/*---------------------------------------------------------------------------*/
