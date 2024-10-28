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
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"
#include "FreeRTOS_Routing.h"

/* Xilinx library files. */
#include <xemacps.h>
#include "x_topology.h"
#include "x_emacpsif.h"
#include "x_emacpsif_hw.h"
#include "x_emac_map.h"

/* Provided memory configured as uncached. */
#include "uncached_memory.h"

#ifndef niEMAC_HANDLER_TASK_PRIORITY
    /* Define the priority of the task prvEMACHandlerTask(). */
    #define niEMAC_HANDLER_TASK_PRIORITY    configMAX_PRIORITIES - 1
#endif

#define niBMSR_LINK_STATUS                  0x0004uL

#if ( ipconfigNETWORK_MTU > 1526 )
    #if ( ipconfigPORT_SUPPRESS_WARNING == 0 )
        #warning the use of Jumbo Frames has not been tested sufficiently yet.
    #endif
    #define USE_JUMBO_FRAMES    1
#endif

/* The size of each buffer when BufferAllocation_1 is used:
 * https://freertos.org/Documentation/03-Libraries/02-FreeRTOS-plus/02-FreeRTOS-plus-TCP/05-Buffer-management */
#if ( USE_JUMBO_FRAMES == 1 )
    #define niBUFFER_1_PACKET_SIZE    10240
#else
    #define niBUFFER_1_PACKET_SIZE    1536
#endif

/* Naming and numbering of PHY registers. */
#define PHY_REG_01_BMSR    0x01         /* Basic mode status register */

#ifndef iptraceEMAC_TASK_STARTING
    #define iptraceEMAC_TASK_STARTING()    do {} while( 0 )
#endif

/* Default the size of the stack used by the EMAC deferred handler task to twice
 * the size of the stack used by the idle task - but allow this to be overridden in
 * FreeRTOSConfig.h as configMINIMAL_STACK_SIZE is a user definable constant. */
#ifndef configEMAC_TASK_STACK_SIZE
    #define configEMAC_TASK_STACK_SIZE    ( 8 * configMINIMAL_STACK_SIZE )
#endif

#if ( ipconfigZERO_COPY_RX_DRIVER == 0 || ipconfigZERO_COPY_TX_DRIVER == 0 )
    #error Please define both 'ipconfigZERO_COPY_RX_DRIVER' and 'ipconfigZERO_COPY_TX_DRIVER' as 1
#endif

#if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 || ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
    #if ( ipconfigPORT_SUPPRESS_WARNING == 0 )
        #warning Please define both 'ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM' and 'ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM' as 1
    #endif
#endif

#ifndef nicUSE_UNCACHED_MEMORY

/*
 * Don't use cached memory for network buffer, which is more efficient than
 * using cached memory.
 */
    #define nicUSE_UNCACHED_MEMORY    0
#endif

/*-----------------------------------------------------------*/

/*
 * Look for the link to be up every few milliseconds until
 * xMaxTimeTicks has passed or a link is found.
 */
static BaseType_t prvGMACWaitLS( BaseType_t xEMACIndex,
                                 TickType_t xMaxTimeTicks );

/*
 * A deferred interrupt handler for all MAC/DMA interrupt sources.
 */
static void prvEMACHandlerTask( void * pvParameters );

/*-----------------------------------------------------------*/

/* FreeRTOS+TCP/multi :
 * Each network device has 3 access functions:
 * - initialise the device
 * - output a network packet
 * - return the PHY link-status (LS)
 * They can be defined as static because their addresses will be
 * stored in struct NetworkInterface_t. */

static NetworkInterface_t * pxMyInterfaces[ XPAR_XEMACPS_NUM_INSTANCES ];

static BaseType_t xUltrascaleNetworkInterfaceInitialise( NetworkInterface_t * pxInterface );

static BaseType_t xUltrascaleNetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                     NetworkBufferDescriptor_t * const pxBuffer,
                                                     BaseType_t bReleaseAfterSend );

static BaseType_t xUltrascaleGetPhyLinkStatus( NetworkInterface_t * pxInterface );

NetworkInterface_t * pxUltrascale_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                           NetworkInterface_t * pxInterface );

/*-----------------------------------------------------------*/

/* EMAC data/descriptions. */
static xemacpsif_s xEMACpsifs[ XPAR_XEMACPS_NUM_INSTANCES ];

struct xtopology_t xXTopologies[ XPAR_XEMACPS_NUM_INSTANCES ] =
{
    [ 0 ] =
        {
        .emac_baseaddr    = XPAR_XEMACPS_0_BASEADDR,
        .emac_type        = xemac_type_emacps,
        .intc_baseaddr    = 0x0,
        .intc_emac_intr   = 0x0,
        .scugic_baseaddr  = XPAR_SCUGIC_0_CPU_BASEADDR,
        .scugic_emac_intr = ZYNQMP_EMACPS_0_IRQ_ID,
        },
    #if ( XPAR_XEMACPS_NUM_INSTANCES > 1 )
        [ 1 ] =
        {
        .emac_baseaddr    = XPAR_XEMACPS_1_BASEADDR,
        .emac_type        = xemac_type_emacps,
        .intc_baseaddr    = 0x0,
        .intc_emac_intr   = 0x0,
        .scugic_baseaddr  = XPAR_SCUGIC_0_CPU_BASEADDR,
        .scugic_emac_intr = ZYNQMP_EMACPS_1_IRQ_ID,
        },
    #elif ( XPAR_XEMACPS_NUM_INSTANCES > 2 )
        [ 2 ] =
        {
        .emac_baseaddr    = XPAR_XEMACPS_2_BASEADDR,
        .emac_type        = xemac_type_emacps,
        .intc_baseaddr    = 0x0,
        .intc_emac_intr   = 0x0,
        .scugic_baseaddr  = XPAR_SCUGIC_0_CPU_BASEADDR,
        .scugic_emac_intr = ZYNQMP_EMACPS_2_IRQ_ID,
        },
    #elif ( XPAR_XEMACPS_NUM_INSTANCES > 3 )
        [ 3 ] =
        {
        .emac_baseaddr    = XPAR_XEMACPS_3_BASEADDR,
        .emac_type        = xemac_type_emacps,
        .intc_baseaddr    = 0x0,
        .intc_emac_intr   = 0x0,
        .scugic_baseaddr  = XPAR_SCUGIC_0_CPU_BASEADDR,
        .scugic_emac_intr = ZYNQMP_EMACPS_3_IRQ_ID,
        },
    #endif /* if ( XPAR_XEMACPS_NUM_INSTANCES > 1 ) */
};

XEmacPs_Config mac_configs[ XPAR_XEMACPS_NUM_INSTANCES ] =
{
    [ 0 ] =
        {
        .DeviceId        = XPAR_XEMACPS_0_DEVICE_ID,     /**< Unique ID  of device */
        .BaseAddress     = XPAR_XEMACPS_0_BASEADDR,      /**< Physical base address of IPIF registers */
        .IsCacheCoherent = XPAR_XEMACPS_0_IS_CACHE_COHERENT
        },
    #if ( XPAR_XEMACPS_NUM_INSTANCES > 1 )
        [ 1 ] =
        {
        .DeviceId        = XPAR_XEMACPS_1_DEVICE_ID,     /**< Unique ID  of device */
        .BaseAddress     = XPAR_XEMACPS_1_BASEADDR,      /**< Physical base address of IPIF registers */
        .IsCacheCoherent = XPAR_XEMACPS_1_IS_CACHE_COHERENT
        },
    #elif ( XPAR_XEMACPS_NUM_INSTANCES > 2 )
        [ 2 ] =
        {
        .DeviceId        = XPAR_XEMACPS_2_DEVICE_ID,     /**< Unique ID  of device */
        .BaseAddress     = XPAR_XEMACPS_2_BASEADDR,      /**< Physical base address of IPIF registers */
        .IsCacheCoherent = XPAR_XEMACPS_2_IS_CACHE_COHERENT
        },
    #elif ( XPAR_XEMACPS_NUM_INSTANCES > 3 )
        [ 3 ] =
        {
        .DeviceId        = XPAR_XEMACPS_3_DEVICE_ID,     /**< Unique ID  of device */
        .BaseAddress     = XPAR_XEMACPS_3_BASEADDR,      /**< Physical base address of IPIF registers */
        .IsCacheCoherent = XPAR_XEMACPS_3_IS_CACHE_COHERENT
        },
    #endif /* if ( XPAR_XEMACPS_NUM_INSTANCES > 1 ) */
};

extern uint32_t phy_detected[ 4 ];

/* A copy of PHY register 1: 'PHY_REG_01_BMSR' */
static uint32_t ulPHYLinkStates[ XPAR_XEMACPS_NUM_INSTANCES ];

/* Holds the handle of the task used as a deferred interrupt processor.  The
 * handle is used so direct notifications can be sent to the task for all EMAC/DMA
 * related interrupts. */
TaskHandle_t xEMACTaskHandles[ XPAR_XEMACPS_NUM_INSTANCES ];

/*-----------------------------------------------------------*/

/**
 * @brief Initialise the interface number 'xIndex'
 * @param xIndex: the index of the interface, between 0
 *                zero and (XPAR_XEMACPS_NUM_INSTANCES-1)
 * @note Although the function is declared public, it should
 *       not be called directly by an application.
 */
void vInitialiseOnIndex( BaseType_t xIndex )
{
    if( ( xIndex >= 0 ) && ( xIndex < XPAR_XEMACPS_NUM_INSTANCES ) )
    {
        NetworkInterface_t * pxInterface = pxMyInterfaces[ xIndex ];

        if( pxInterface != NULL )
        {
            xUltrascaleNetworkInterfaceInitialise( pxInterface );
        }
    }
}
/*-----------------------------------------------------------*/

/* The function xNetworkInterfaceInitialise() will be called as
 * long as it returns the value pdFAIL.
 * It will go through several stages as described in 'eEMACStates'.
 */
typedef enum xEMAC_STATE
{
    xEMAC_Init = 0,
    xEMAC_SetupPHY,
    xEMAC_WaitPHY,
    xEMAC_Ready,
    xEMAC_Fatal,
} EMACState_t;

static EMACState_t eEMACStates[ XPAR_XEMACPS_NUM_INSTANCES ] = { xEMAC_Init };

static BaseType_t xUltrascaleNetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    uint32_t ulLinkSpeed, ulDMAReg;
    BaseType_t xStatus, xReturn = pdFAIL;
    XEmacPs * pxEMAC_PS;
    const TickType_t xWaitLinkDelay = pdMS_TO_TICKS( 1000U );
    NetworkEndPoint_t * pxEndPoint;
    BaseType_t xEMACIndex = ( BaseType_t ) pxInterface->pvArgument;

    configASSERT( xEMACIndex >= 0 );
    configASSERT( xEMACIndex < XPAR_XEMACPS_NUM_INSTANCES );

    pxEMAC_PS = &( xEMACpsifs[ xEMACIndex ].emacps );

    switch( eEMACStates[ xEMACIndex ] )
    {
        case xEMAC_Init:

            pxMyInterfaces[ xEMACIndex ] = pxInterface;

            ulPHYLinkStates[ xEMACIndex ] = 0U;
            memset( &xEMACpsifs[ xEMACIndex ], '\0', sizeof( xEMACpsifs[ xEMACIndex ] ) );

            xStatus = XEmacPs_CfgInitialize( pxEMAC_PS, &( mac_configs[ xEMACIndex ] ), mac_configs[ xEMACIndex ].BaseAddress );

            if( xStatus != XST_SUCCESS )
            {
                FreeRTOS_printf( ( "xEMACInit: EmacPs Configuration Failed....\n" ) );
                eEMACStates[ xEMACIndex ] = xEMAC_Fatal;
                break;
            }

            pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
            configASSERT( pxEndPoint != NULL );

            #if ( USE_JUMBO_FRAMES == 1 )
                /* Enable jumbo frames for zynqmp */
                XEmacPs_SetOptions( pxEMAC_PS, XEMACPS_JUMBO_ENABLE_OPTION );
            #endif

            /* Initialize the mac and set the MAC address at position 1. */
            XEmacPs_SetMacAddress( pxEMAC_PS, ( void * ) pxEndPoint->xMACAddress.ucBytes, 1 );

            #if ( ipconfigIS_ENABLED( ipconfigUSE_LLMNR ) )
            {
                #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )
                {
                    XEmacPs_SetHash( pxEMAC_PS, ( void * ) xLLMNR_MacAddress.ucBytes );
                }
                #endif /* ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) */

                #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
                {
                    XEmacPs_SetHash( pxEMAC_PS, ( void * ) xLLMNR_MacAddressIPv6.ucBytes );
                }
                #endif /* ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) ) */
            }
            #endif /* ( ipconfigIS_ENABLED( ipconfigUSE_LLMNR ) ) */

            #if ( ipconfigIS_ENABLED( ipconfigUSE_MDNS ) )
            {
                #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )
                {
                    XEmacPs_SetHash( pxEMAC_PS, ( void * ) xMDNS_MacAddress.ucBytes );
                }
                #endif /* ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) */

                #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
                {
                    XEmacPs_SetHash( pxEMAC_PS, ( void * ) xMDNS_MacAddressIPv6.ucBytes );
                }
                #endif /* ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) ) */
            }
            #endif /* ( ipconfigIS_ENABLED( ipconfigUSE_MDNS) ) */

            #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
            {
                /* set the solicited-node multicast address */
                for( NetworkEndPoint_t * pxEndPointIter = FreeRTOS_FirstEndPoint( pxInterface );
                     pxEndPointIter != NULL;
                     pxEndPointIter = FreeRTOS_NextEndPoint( pxInterface, pxEndPointIter ) )
                {
                    if( pxEndPointIter->bits.bIPv6 != pdFALSE_UNSIGNED )
                    {
                        unsigned char ucSsolicitedNodeMAC[ 6 ] = { 0x33, 0x33, 0xff, 0, 0, 0 };
                        ucSsolicitedNodeMAC[ 3 ] = pxEndPointIter->ipv6_settings.xIPAddress.ucBytes[ 13 ];
                        ucSsolicitedNodeMAC[ 4 ] = pxEndPointIter->ipv6_settings.xIPAddress.ucBytes[ 14 ];
                        ucSsolicitedNodeMAC[ 5 ] = pxEndPointIter->ipv6_settings.xIPAddress.ucBytes[ 15 ];
                        XEmacPs_SetHash( pxEMAC_PS, ( void * ) ucSsolicitedNodeMAC );
                    }
                }
            }
            #endif /* ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) ) */

            /* allow reception of multicast addresses programmed into hash (LLMNR or mDNS) */
            XEmacPs_SetOptions( pxEMAC_PS, XEMACPS_MULTICAST_OPTION );

            /* TODO: is it needed to add the MAC of the second endpoint? */
            pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint );

            if( pxEndPoint != NULL )
            {
                /* If there is a second end-point, store the MAC
                 * address at position 4.*/
                XEmacPs_SetMacAddress( pxEMAC_PS, ( void * ) pxEndPoint->xMACAddress.ucBytes, 4 );
            }

            XEmacPs_SetMdioDivisor( pxEMAC_PS, MDC_DIV_224 );
            phy_detected[ xEMACIndex ] = ulDetectPHY( pxEMAC_PS );

            if( phy_detected[ xEMACIndex ] == ~0U )
            {
                FreeRTOS_printf( ( "xEMACInit: No valid PHY was found\n" ) );
                eEMACStates[ xEMACIndex ] = xEMAC_Fatal;
                break;
            }

            eEMACStates[ xEMACIndex ] = xEMAC_SetupPHY;

        /* Fall through. */

        case xEMAC_SetupPHY:
            ulLinkSpeed = Phy_Setup_US( pxEMAC_PS, phy_detected[ xEMACIndex ] );

            if( ulLinkSpeed == XST_FAILURE )
            {
                /* The speed could not be determined yet.
                 * This is not a fatal error.
                 * xNetworkInterfaceInitialise() will be called again
                 * by the IP-task.
                 */
                break;
            }

            XEmacPs_SetOperatingSpeed( pxEMAC_PS, ulLinkSpeed );

            /* Setting the operating speed of the MAC needs a delay. */
            vTaskDelay( pdMS_TO_TICKS( 25UL ) );

            /* Enable 16-bytes AHB bursts */
            XEmacPs_DMABLengthUpdate( pxEMAC_PS, XEMACPS_16BYTE_BURST );

            setup_isr( &( xEMACpsifs[ xEMACIndex ] ) );
            init_dma( &( xEMACpsifs[ xEMACIndex ] ) );
            start_emacps( &( xEMACpsifs[ xEMACIndex ] ) );
            eEMACStates[ xEMACIndex ] = xEMAC_WaitPHY;

        /* Fall through. */

        case xEMAC_WaitPHY:
            prvGMACWaitLS( xEMACIndex, xWaitLinkDelay );

            if( xGetPhyLinkStatus( pxInterface ) == pdFALSE )
            {
                /* The Link Status is not yet high, Stay in 'xEMAC_WaitPHY'. */
                break;
            }

            if( xEMACTaskHandles[ xEMACIndex ] == NULL )
            {
                /* The deferred interrupt handler task is created at the highest
                 * possible priority to ensure the interrupt handler can return directly
                 * to it.  The task's handle is stored in xEMACTaskHandles[] so interrupts can
                 * notify the task when there is something to process. */
                const char * pcTaskName;

                switch( xEMACIndex )
                {
                    case 1:
                        pcTaskName = "EMAC1";
                        break;

                    case 2:
                        pcTaskName = "EMAC2";
                        break;

                    case 3:
                        pcTaskName = "EMAC3";
                        break;

                    case 0:
                    default:
                        pcTaskName = "EMAC0";
                        break;
                }

                xTaskCreate( prvEMACHandlerTask, pcTaskName, configEMAC_TASK_STACK_SIZE, ( void * ) xEMACIndex, niEMAC_HANDLER_TASK_PRIORITY, &( xEMACTaskHandles[ xEMACIndex ] ) );

                if( xEMACTaskHandles[ xEMACIndex ] == NULL )
                {
                    eEMACStates[ xEMACIndex ] = xEMAC_Fatal;
                    break;
                }
            }

            eEMACStates[ xEMACIndex ] = xEMAC_Ready;

        /* Fall through. */

        case xEMAC_Ready:
            /* The network driver is operational. */
            xReturn = pdPASS;
            break;

        case xEMAC_Fatal:

            /* A fatal error has occurred, and the driver
             * can not start. */
            break;
    } /* switch( eEMACState ) */

    return xReturn;
}

/*-----------------------------------------------------------*/
static BaseType_t xUltrascaleNetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                     NetworkBufferDescriptor_t * const pxBuffer,
                                                     BaseType_t bReleaseAfterSend )
{
    BaseType_t xEMACIndex = ( BaseType_t ) pxInterface->pvArgument;

    configASSERT( xEMACIndex >= 0 );
    configASSERT( xEMACIndex < XPAR_XEMACPS_NUM_INSTANCES );

    #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM != 0 )
    {
        ProtocolPacket_t * pxPacket;

        /* If the peripheral must calculate the checksum, it wants
         * the protocol checksum to have a value of zero. */
        pxPacket = ( ProtocolPacket_t * ) ( pxBuffer->pucEthernetBuffer );

        #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
            ICMPPacket_IPv6_t * pxICMPPacket = ( ICMPPacket_IPv6_t * ) pxBuffer->pucEthernetBuffer;

            if( ( pxPacket->xICMPPacket.xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE ) &&
                ( pxICMPPacket->xIPHeader.ucNextHeader == ipPROTOCOL_ICMP_IPv6 ) )
            {
                /* The EMAC will calculate the checksum of the IP-header.
                 * It can only calculate protocol checksums of UDP and TCP,
                 * so for ICMP and other protocols it must be done manually. */
                usGenerateProtocolChecksum( pxBuffer->pucEthernetBuffer, pxBuffer->xDataLength, pdTRUE );
            }
        #endif /* ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) ) */

        #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )
        {
            if( ( pxPacket->xICMPPacket.xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE ) &&
                ( pxPacket->xICMPPacket.xIPHeader.ucProtocol == ipPROTOCOL_ICMP ) )
            {
                /* The EMAC will calculate the checksum of the IP-header.
                 * It can only calculate protocol checksums of UDP and TCP,
                 * so for ICMP and other protocols it must be done manually. */
                usGenerateProtocolChecksum( pxBuffer->pucEthernetBuffer, pxBuffer->xDataLength, pdTRUE );
            }
        }
        #endif /* ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) */
    }
    #endif /* ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM */

    if( ( ulPHYLinkStates[ xEMACIndex ] & niBMSR_LINK_STATUS ) != 0UL )
    {
        iptraceNETWORK_INTERFACE_TRANSMIT();

        /* emacps_send_message() will take ownership of pxBuffer, and
         * make sure it will get release when bReleaseAfterSend is pdTRUE. */
        emacps_send_message( &( xEMACpsifs[ xEMACIndex ] ), pxBuffer, bReleaseAfterSend );
    }
    else if( bReleaseAfterSend != pdFALSE )
    {
        /* No link. */
        vReleaseNetworkBufferAndDescriptor( pxBuffer );
    }

    return pdTRUE;
}
/*-----------------------------------------------------------*/

static inline unsigned long ulReadMDIO( BaseType_t xEMACIndex,
                                        unsigned ulRegister )
{
    uint16_t usValue;

    XEmacPs_PhyRead( &( xEMACpsifs[ xEMACIndex ].emacps ), phy_detected[ xEMACIndex ], ulRegister, &usValue );
    return usValue;
}
/*-----------------------------------------------------------*/

static BaseType_t prvGMACWaitLS( BaseType_t xEMACIndex,
                                 TickType_t xMaxTimeTicks )
{
    TickType_t xStartTime, xEndTime;
    const TickType_t xShortDelay = pdMS_TO_TICKS( 20UL );
    BaseType_t xReturn;

    xStartTime = xTaskGetTickCount();

    for( ; ; )
    {
        xEndTime = xTaskGetTickCount();

        if( xEndTime - xStartTime > xMaxTimeTicks )
        {
            xReturn = pdFALSE;
            break;
        }

        ulPHYLinkStates[ xEMACIndex ] = ulReadMDIO( xEMACIndex, PHY_REG_01_BMSR );

        if( ( ulPHYLinkStates[ xEMACIndex ] & niBMSR_LINK_STATUS ) != 0uL )
        {
            xReturn = pdTRUE;
            break;
        }

        vTaskDelay( xShortDelay );
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

#if ( nicUSE_UNCACHED_MEMORY == 0 )
    void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
    {
        static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * niBUFFER_1_PACKET_SIZE ] __attribute__( ( aligned( 32 ) ) );
        uint8_t * ucRAMBuffer = ucNetworkPackets;
        uint32_t ul;

        for( ul = 0; ul < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ul++ )
        {
            pxNetworkBuffers[ ul ].pucEthernetBuffer = ucRAMBuffer + ipBUFFER_PADDING;
            *( ( uintptr_t * ) ucRAMBuffer ) = ( uintptr_t ) &( pxNetworkBuffers[ ul ] );
            ucRAMBuffer += niBUFFER_1_PACKET_SIZE;
        }
    }
#else /* if ( nicUSE_UNCACHED_MEMORY == 0 ) */
    void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
    {
        static uint8_t * pucNetworkPackets = NULL;

        if( pucNetworkPackets == NULL )
        {
            pucNetworkPackets = pucGetUncachedMemory( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * niBUFFER_1_PACKET_SIZE );

            if( pucNetworkPackets != NULL )
            {
                uint8_t * ucRAMBuffer = pucNetworkPackets;
                uint32_t ul;

                for( ul = 0; ul < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ul++ )
                {
                    pxNetworkBuffers[ ul ].pucEthernetBuffer = ucRAMBuffer + ipBUFFER_PADDING;
                    *( ( unsigned * ) ucRAMBuffer ) = ( unsigned ) ( &( pxNetworkBuffers[ ul ] ) );
                    ucRAMBuffer += niBUFFER_1_PACKET_SIZE;
                }
            }
        }
    }
#endif /* ( nicUSE_UNCACHED_MEMORY == 0 ) */
/*-----------------------------------------------------------*/

static BaseType_t xUltrascaleGetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    BaseType_t xReturn;
    BaseType_t xEMACIndex = ( BaseType_t ) pxInterface->pvArgument;

    if( ( ulPHYLinkStates[ xEMACIndex ] & niBMSR_LINK_STATUS ) == 0uL )
    {
        xReturn = pdFALSE;
    }
    else
    {
        xReturn = pdTRUE;
    }

    return xReturn;
}

/*-----------------------------------------------------------*/
#if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 1 )

/* Do not call the following function directly. It is there for downward compatibility.
 * The function FreeRTOS_IPInit() will call it to initialise the interface and end-point
 * objects.  See the description in FreeRTOS_Routing.h. */
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface )
    {
        return pxUltrascale_FillInterfaceDescriptor( xEMACIndex, pxInterface );
    }
#endif

NetworkInterface_t * pxUltrascale_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                           NetworkInterface_t * pxInterface )
{
    static char pcNames[ XPAR_XEMACPS_NUM_INSTANCES ][ 8 ];

    configASSERT( xEMACIndex >= 0 );
    configASSERT( xEMACIndex < XPAR_XEMACPS_NUM_INSTANCES );

/* This function pxZynq_FillInterfaceDescriptor() adds a network-interface.
 * Make sure that the object pointed to by 'pxInterface'
 * is declared static or global, and that it will remain to exist. */

    strcpy( pcNames[ xEMACIndex ], "ETH" );
    uint8_t temp = strlen( pcNames[ xEMACIndex ] );
    pcNames[ xEMACIndex ][ temp ] = ( char ) xEMACIndex + '0';
    pcNames[ xEMACIndex ][ temp + 1 ] = '\0';

    memset( pxInterface, '\0', sizeof( *pxInterface ) );
    pxInterface->pcName = pcNames[ xEMACIndex ];     /* Just for logging, debugging. */
    pxInterface->pvArgument = ( void * ) xEMACIndex; /* Has meaning only for the driver functions. */
    pxInterface->pfInitialise = xUltrascaleNetworkInterfaceInitialise;
    pxInterface->pfOutput = xUltrascaleNetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = xUltrascaleGetPhyLinkStatus;

    FreeRTOS_AddNetworkInterface( pxInterface );

    return pxInterface;
}

/*-----------------------------------------------------------*/

BaseType_t xGetPhyLinkStatus( struct xNetworkInterface * pxInterface )
{
    return xUltrascaleGetPhyLinkStatus( pxInterface );
}

/*-----------------------------------------------------------*/

static void prvEMACHandlerTask( void * pvParameters )
{
    TimeOut_t xPhyTime;
    TickType_t xPhyRemTime;
    BaseType_t xResult = 0;
    uint32_t xStatus;
    const TickType_t ulMaxBlockTime = pdMS_TO_TICKS( 100UL );

    BaseType_t xEMACIndex = ( BaseType_t ) pvParameters;
    xemacpsif_s * pxEMAC_PS;

    configASSERT( xEMACIndex >= 0 );
    configASSERT( xEMACIndex < XPAR_XEMACPS_NUM_INSTANCES );

    pxEMAC_PS = &( xEMACpsifs[ xEMACIndex ] );

    /* A possibility to set some additional task properties like calling
     * portTASK_USES_FLOATING_POINT() */
    iptraceEMAC_TASK_STARTING();

    vTaskSetTimeOutState( &xPhyTime );
    xPhyRemTime = pdMS_TO_TICKS( ipconfigPHY_LS_LOW_CHECK_TIME_MS );
    FreeRTOS_printf( ( "prvEMACHandlerTask[ %ld ] started running\n", xEMACIndex ) );

    for( ; ; )
    {
        #if ( ipconfigHAS_PRINTF != 0 )
        {
            /* Call a function that monitors resources: the amount of free network
             * buffers and the amount of free space on the heap.  See FreeRTOS_IP.c
             * for more detailed comments. */
            vPrintResourceStats();
        }
        #endif /* ( ipconfigHAS_PRINTF != 0 ) */

        if( ( pxEMAC_PS->isr_events & EMAC_IF_ALL_EVENT ) == 0 )
        {
            /* No events to process now, wait for the next. */
            ulTaskNotifyTake( pdFALSE, ulMaxBlockTime );
        }

        if( ( pxEMAC_PS->isr_events & EMAC_IF_RX_EVENT ) != 0 )
        {
            pxEMAC_PS->isr_events &= ~EMAC_IF_RX_EVENT;
            xResult = emacps_check_rx( pxEMAC_PS, pxMyInterfaces[ xEMACIndex ] );
        }

        if( ( pxEMAC_PS->isr_events & EMAC_IF_TX_EVENT ) != 0 )
        {
            pxEMAC_PS->isr_events &= ~EMAC_IF_TX_EVENT;
            emacps_check_tx( pxEMAC_PS );
        }

        if( ( pxEMAC_PS->isr_events & EMAC_IF_ERR_EVENT ) != 0 )
        {
            pxEMAC_PS->isr_events &= ~EMAC_IF_ERR_EVENT;
            emacps_check_errors( pxEMAC_PS );
        }

        if( xResult > 0 )
        {
            /* A packet was received. No need to check for the PHY status now,
             * but set a timer to check it later on. */
            vTaskSetTimeOutState( &xPhyTime );
            xPhyRemTime = pdMS_TO_TICKS( ipconfigPHY_LS_HIGH_CHECK_TIME_MS );
            xResult = 0;

            if( ( ulPHYLinkStates[ xEMACIndex ] & niBMSR_LINK_STATUS ) == 0uL )
            {
                /* Indicate that the Link Status is high, so that
                 * xNetworkInterfaceOutput() can send packets. */
                ulPHYLinkStates[ xEMACIndex ] |= niBMSR_LINK_STATUS;
                FreeRTOS_printf( ( "prvEMACHandlerTask: PHY LS assume 1\n" ) );
            }
        }
        else if( xTaskCheckForTimeOut( &xPhyTime, &xPhyRemTime ) != pdFALSE )
        {
            xStatus = ulReadMDIO( xEMACIndex, PHY_REG_01_BMSR );

            if( ( ulPHYLinkStates[ xEMACIndex ] & niBMSR_LINK_STATUS ) != ( xStatus & niBMSR_LINK_STATUS ) )
            {
                ulPHYLinkStates[ xEMACIndex ] = xStatus;
                FreeRTOS_printf( ( "prvEMACHandlerTask: PHY LS now %d\n", ( ulPHYLinkStates[ xEMACIndex ] & niBMSR_LINK_STATUS ) != 0uL ) );
            }

            vTaskSetTimeOutState( &xPhyTime );

            if( ( ulPHYLinkStates[ xEMACIndex ] & niBMSR_LINK_STATUS ) != 0uL )
            {
                xPhyRemTime = pdMS_TO_TICKS( ipconfigPHY_LS_HIGH_CHECK_TIME_MS );
            }
            else
            {
                xPhyRemTime = pdMS_TO_TICKS( ipconfigPHY_LS_LOW_CHECK_TIME_MS );
            }
        }
    }
}
/*-----------------------------------------------------------*/
