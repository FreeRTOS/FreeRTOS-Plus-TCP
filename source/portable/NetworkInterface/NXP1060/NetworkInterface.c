/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
 * Copyright (C) 2023 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/**
 * @file NetworkInterface.c
 * @brief Implements the Network Interface driver for the NXP MIMXRT1060 board.
 */
/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

#include "fsl_device_registers.h"
#include "fsl_debug_console.h"
#include "board.h"

#include "fsl_phy.h"

#include "fsl_phyksz8081.h"
#include "fsl_enet_mdio.h"
#include "fsl_enet.h"

#include "NetworkInterface.h"

#if ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES != 1
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/* MDIO operations. */
#define EXAMPLE_MDIO_OPS      enet_ops

/* PHY operations. */
#define EXAMPLE_PHY_OPS       phyksz8081_ops

/* ENET clock frequency. */
#define EXAMPLE_CLOCK_FREQ    CLOCK_GetFreq( kCLOCK_IpgClk )

/*
 * Padding of ethernet frames has to be disabled for zero-copy functionality
 * since ENET driver requires the starting buffer addresses to be aligned.
 */
#if ETH_PAD_SIZE != 0
    #error "ETH_PAD_SIZE != 0"
#endif /* ETH_PAD_SIZE != 0 */

/*******************************************************************************
 * Definitions
 ******************************************************************************/
#define ENET_RING_NUM    ( 1 )

/* The length or RX buffer. */
#ifndef ENET_RXBUFF_SIZE
    #define ENET_RXBUFF_SIZE    ( ENET_FRAME_MAX_FRAMELEN )
#endif

/* ENET IRQ priority. Used in FreeRTOS. */
/* Interrupt priorities. */
#ifdef __CA7_REV
    #ifndef ENET_PRIORITY
        #define ENET_PRIORITY         ( 21U )
    #endif
    #ifndef ENET_1588_PRIORITY
        #define ENET_1588_PRIORITY    ( 20U )
    #endif
#else
    #ifndef ENET_PRIORITY
        #define ENET_PRIORITY         ( 6U )
    #endif
    #ifndef ENET_1588_PRIORITY
        #define ENET_1588_PRIORITY    ( 5U )
    #endif
#endif /* ifdef __CA7_REV */

/* The number of ENET buffers needed to receive frame of maximum length. */
#define MAX_BUFFERS_PER_FRAME \
    ( ( ENET_FRAME_MAX_FRAMELEN / ENET_RXBUFF_SIZE ) + ( ( ENET_FRAME_MAX_FRAMELEN % ENET_RXBUFF_SIZE == 0 ) ? 0 : 1 ) )

/* The length or TX buffer. */
#ifndef ENET_TXBUFF_SIZE
    #define ENET_TXBUFF_SIZE    ( ENET_FRAME_MAX_FRAMELEN )
#endif

/* The number of buffer descriptors in ENET RX ring. */
#ifndef ENET_RXBD_NUM
    #define ENET_RXBD_NUM    ( 5 )
#endif

/* Ring should be able to receive at least 1 frame with maximum length. */
#if ENET_RXBD_NUM < MAX_BUFFERS_PER_FRAME
    #error "ENET_RXBD_NUM < MAX_BUFFERS_PER_FRAME"
#endif

/* The number of RX buffers. ENET_RXBD_NUM is always held by ENET driver,
 * so a couple more are needed to pass zero-copy data into lwIP. */
#ifndef ENET_RXBUFF_NUM
    #define ENET_RXBUFF_NUM    ( ENET_RXBD_NUM * 2 )
#endif

/* At least ENET_RXBD_NUM number of buffers is always held by ENET driver for RX.
 * Some additional buffers are needed to pass at least one frame zero-copy data to lwIP. */
#if ENET_RXBUFF_NUM < ( ENET_RXBD_NUM + MAX_BUFFERS_PER_FRAME )
    #error "ENET_RXBUFF_NUM < (ENET_RXBD_NUM + MAX_BUFFERS_PER_FRAME)"
#endif

/* The number of buffer descriptors in ENET TX ring. */
#ifndef ENET_TXBD_NUM
    #define ENET_TXBD_NUM            ( 3 )
#endif

#define MAX_AUTONEG_FAILURE_COUNT    ( 5 )

#if defined( FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL ) && FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL
    #if defined( FSL_FEATURE_L2CACHE_LINESIZE_BYTE ) && \
    ( ( !defined( FSL_SDK_DISBLE_L2CACHE_PRESENT ) ) || ( FSL_SDK_DISBLE_L2CACHE_PRESENT == 0 ) )
        #if defined( FSL_FEATURE_L1DCACHE_LINESIZE_BYTE )
            #define FSL_CACHE_LINESIZE_MAX     MAX( FSL_FEATURE_L1DCACHE_LINESIZE_BYTE, FSL_FEATURE_L2CACHE_LINESIZE_BYTE )
            #define FSL_ENET_BUFF_ALIGNMENT    MAX( ENET_BUFF_ALIGNMENT, FSL_CACHE_LINESIZE_MAX )
        #else
            #define FSL_ENET_BUFF_ALIGNMENT    MAX( ENET_BUFF_ALIGNMENT, FSL_FEATURE_L2CACHE_LINESIZE_BYTE )
        #endif
    #elif defined( FSL_FEATURE_L1DCACHE_LINESIZE_BYTE )
        #define FSL_ENET_BUFF_ALIGNMENT        MAX( ENET_BUFF_ALIGNMENT, FSL_FEATURE_L1DCACHE_LINESIZE_BYTE )
    #else
        #define FSL_ENET_BUFF_ALIGNMENT        ENET_BUFF_ALIGNMENT
    #endif /* if defined( FSL_FEATURE_L2CACHE_LINESIZE_BYTE ) && ( ( !defined( FSL_SDK_DISBLE_L2CACHE_PRESENT ) ) || ( FSL_SDK_DISBLE_L2CACHE_PRESENT == 0 ) ) */
#else /* if defined( FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL ) && FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL */
    #define FSL_ENET_BUFF_ALIGNMENT            ENET_BUFF_ALIGNMENT
#endif /* if defined( FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL ) && FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL */

typedef uint8_t   rx_buffer_t[ SDK_SIZEALIGN( ENET_RXBUFF_SIZE, FSL_ENET_BUFF_ALIGNMENT ) ];
typedef uint8_t   tx_buffer_t[ SDK_SIZEALIGN( ENET_TXBUFF_SIZE, FSL_ENET_BUFF_ALIGNMENT ) ];

/*!
 * @brief Used to wrap received data in a pbuf to be passed into lwIP
 *        without copying.
 * Once last reference is released, buffer can be used by ENET RX DMA again.
 */
typedef struct rx_pbuf_wrapper
{
    void * buffer;             /*!< Original buffer wrapped. */
    volatile bool buffer_used; /*!< Wrapped buffer is used by ENET or FreeRTOS+TCP. */
} rx_pbuf_wrapper_t;

/**
 * Helper structure to hold private data used to operate your Ethernet interface.
 */
struct ethernetif
{
    ENET_Type * base;
    enet_handle_t handle;
    enet_rx_bd_struct_t * RxBuffDescrip;
    enet_tx_bd_struct_t * TxBuffDescrip;
    rx_buffer_t * RxDataBuff;
    tx_buffer_t * TxDataBuff;
    rx_pbuf_wrapper_t RxPbufs[ ENET_RXBUFF_NUM ];
};

typedef enum xEMAC_STATE
{
    xEMAC_SetupPHY,
    xEMAC_WaitPHY,
    xEMAC_Init,
    xEMAC_Ready,
    xEMAC_Fatal,
} EMACState_t;

static EMACState_t eEMACState = xEMAC_SetupPHY;

static mdio_handle_t mdioHandle = { .ops = &EXAMPLE_MDIO_OPS };

static phy_handle_t phyHandle = { .phyAddr = 0x00, .mdioHandle = &mdioHandle, .ops = &EXAMPLE_PHY_OPS };

/*-----------------------------------------------------------*/

/*
 * A deferred interrupt handler task that processes
 */

static TaskHandle_t receiveTaskHandle = NULL;

static struct ethernetif EthernetInterface1;
struct ethernetif * ethernetifLocal = &EthernetInterface1;

/*-----------------------------------------------------------*/

/* The queue used to communicate Ethernet events with the IP task. */
extern QueueHandle_t xNetworkEventQueue;

/*-----------------------------------------------------------*/

AT_NONCACHEABLE_SECTION_ALIGN( static enet_rx_bd_struct_t rxBuffDescrip_0[ ENET_RXBD_NUM ], FSL_ENET_BUFF_ALIGNMENT );
AT_NONCACHEABLE_SECTION_ALIGN( static enet_tx_bd_struct_t txBuffDescrip_0[ ENET_TXBD_NUM ], FSL_ENET_BUFF_ALIGNMENT );
SDK_ALIGN( static rx_buffer_t rxDataBuff_0[ ENET_RXBUFF_NUM ], FSL_ENET_BUFF_ALIGNMENT );
SDK_ALIGN( static tx_buffer_t txDataBuff_0[ ENET_TXBD_NUM ], FSL_ENET_BUFF_ALIGNMENT );

static void prvEMACHandlerTask( void * pvParameters );

static void ethernet_callback( ENET_Type * base,
                               enet_handle_t * handle,
                               enet_event_t event,
                               enet_frame_info_t * frameInfo,
                               void * userData );

static void prvProcessFrame( int length );

BaseType_t xNetworkInterfaceInitialise( void )
{
    status_t xStatus;
    phy_config_t xConfig = { 0 };
    BaseType_t xResult = pdFAIL;
    phy_speed_t speed;
    phy_duplex_t duplex;
    status_t readStatus;
    enet_config_t config;
    uint32_t sysClock;
    enet_buffer_config_t buffCfg[ ENET_RING_NUM ];
    int i;
    uint8_t ucCounter = 0;
    bool autoNegotiationComplete = false;
    bool LinkUp = false;

    configASSERT( FSL_FEATURE_ENET_QUEUE == 1 );

    #if defined( ENET_ENHANCEDBUFFERDESCRIPTOR_MODE )
        configASSERT( pdFALSE );
    #endif

    switch( eEMACState )
    {
        case xEMAC_SetupPHY:
            ethernetifLocal->RxBuffDescrip = &( rxBuffDescrip_0[ 0 ] );
            ethernetifLocal->TxBuffDescrip = &( txBuffDescrip_0[ 0 ] );
            ethernetifLocal->RxDataBuff = &( rxDataBuff_0[ 0 ] );
            ethernetifLocal->TxDataBuff = &( txDataBuff_0[ 0 ] );
            ethernetifLocal->base = ( void * ) ENET_BASE;

            /* Set the clock frequency. */
            mdioHandle.resource.csrClock_Hz = EXAMPLE_CLOCK_FREQ;
            mdioHandle.resource.base = ( void * ) ENET_BASE;

            /* Set the configuration to auto-negotiate; set the phy to full duplex mode; the phy's address; and the speed. */
            xConfig.autoNeg = pdTRUE;
            xConfig.duplex = kPHY_FullDuplex;
            xConfig.phyAddr = BOARD_ENET0_PHY_ADDRESS;
            xConfig.speed = kPHY_Speed100M;

            FreeRTOS_printf( ( "Starting PHY initialization.\r\n" ) );

            xStatus = PHY_Init( &phyHandle, &xConfig );

            if( xStatus != kStatus_Success )
            {
                FreeRTOS_printf( ( "Failed to initialize the PHY..." ) );
                break;
            }

            eEMACState = xEMAC_WaitPHY;
        /* Fall through. */

        case xEMAC_WaitPHY:
            FreeRTOS_printf( ( "Configuration successful. Waiting for auto-negotiation to complete...\r\n" ) );

            do
            {
                readStatus = PHY_GetAutoNegotiationStatus( &phyHandle, &autoNegotiationComplete );

                if( autoNegotiationComplete == true )
                {
                    break;
                }

                /* Try for only a limited number of times. */
                if( ucCounter++ > MAX_AUTONEG_FAILURE_COUNT )
                {
                    break;
                }

                vTaskDelay( pdMS_TO_TICKS( 10 ) );
            }
            while( readStatus == kStatus_Success );

            if( autoNegotiationComplete == false )
            {
                FreeRTOS_printf( ( "Failed to complete auto-negotiation. Using default values." ) );

                xConfig.autoNeg = pdFALSE;
                xConfig.duplex = kPHY_FullDuplex;
                xConfig.phyAddr = BOARD_ENET0_PHY_ADDRESS;
                xConfig.speed = kPHY_Speed100M;

                xStatus = PHY_Init( &phyHandle, &xConfig );

                if( xStatus != kStatus_Success )
                {
                    FreeRTOS_printf( ( "Failed to re-initialize the PHY with default configs too..." ) );
                    eEMACState = xEMAC_Fatal;
                    break;
                }
                else
                {
                    FreeRTOS_printf( ( "PHY re-initialization successful." ) );
                }
            }
            else
            {
                FreeRTOS_printf( ( "Auto-negotiation complete.\r\n" ) );
            }

            ucCounter = 0;

            do
            {
                readStatus = PHY_GetLinkStatus( &phyHandle, &LinkUp );

                if( LinkUp == true )
                {
                    break;
                }

                vTaskDelay( pdMS_TO_TICKS( 1000 ) );

                /* Try for only a limited number of times. */
                if( ucCounter++ > MAX_AUTONEG_FAILURE_COUNT )
                {
                    break;
                    xResult = pdFAIL;
                }
            }
            while( readStatus == kStatus_Success );

            if( LinkUp == false )
            {
                FreeRTOS_printf( ( "Failed to get the link up." ) );
                break;
            }
            else
            {
                /* Success in auto-negotiation and the link is up. */
                FreeRTOS_printf( ( "Link up." ) );
            }

            readStatus = PHY_GetLinkSpeedDuplex( &phyHandle, &speed, &duplex );

            if( readStatus != kStatus_Success )
            {
                break;
            }

            eEMACState = xEMAC_Init;
        /* Fall through. */

        case xEMAC_Init:

            /* prepare the buffer configuration. */
            buffCfg[ 0 ].rxBdNumber = ENET_RXBD_NUM;                  /* Receive buffer descriptor number. */
            buffCfg[ 0 ].txBdNumber = ENET_TXBD_NUM;                  /* Transmit buffer descriptor number. */
            buffCfg[ 0 ].rxBuffSizeAlign = sizeof( rx_buffer_t );     /* Aligned receive data buffer size. */
            buffCfg[ 0 ].txBuffSizeAlign = sizeof( tx_buffer_t );     /* Aligned transmit data buffer size. */
            buffCfg[ 0 ].rxBdStartAddrAlign =
                &( rxBuffDescrip_0[ 0 ] );                            /* Aligned receive buffer descriptor start address. */
            buffCfg[ 0 ].txBdStartAddrAlign =
                &( txBuffDescrip_0[ 0 ] );                            /* Aligned transmit buffer descriptor start address. */
            buffCfg[ 0 ].rxBufferAlign =
                &( rxDataBuff_0[ 0 ][ 0 ] );                          /* Receive data buffer start address. */
            buffCfg[ 0 ].txBufferAlign = &( txDataBuff_0[ 0 ][ 0 ] ); /* Transmit data buffer start address. */
            buffCfg[ 0 ].txFrameInfo = NULL;                          /* Transmit frame information start address. Set only if using zero-copy transmit. */
            buffCfg[ 0 ].rxMaintainEnable = true;                     /* Receive buffer cache maintain. */
            buffCfg[ 0 ].txMaintainEnable = true;                     /* Transmit buffer cache maintain. */

            sysClock = phyHandle.mdioHandle->resource.csrClock_Hz;

            ENET_GetDefaultConfig( &config );

            config.ringNum = ENET_RING_NUM;
            config.rxBuffAlloc = NULL;
            config.rxBuffFree = NULL;
            config.userData = ethernetifLocal;
            config.miiSpeed = ( enet_mii_speed_t ) speed;
            config.miiDuplex = ( enet_mii_duplex_t ) duplex;

            uint32_t instance;
            static ENET_Type * const enetBases[] = ENET_BASE_PTRS;
            static const IRQn_Type enetTxIrqId[] = ENET_Transmit_IRQS;
            /*! @brief Pointers to enet receive IRQ number for each instance. */
            static const IRQn_Type enetRxIrqId[] = ENET_Receive_IRQS;

            /* Only get interrupt for incoming messages. */
            config.interrupt = kENET_RxFrameInterrupt;
            config.callback = ethernet_callback;

            for( instance = 0; instance < ARRAY_SIZE( enetBases ); instance++ )
            {
                if( enetBases[ instance ] == ethernetifLocal->base )
                {
                    NVIC_SetPriority( enetRxIrqId[ instance ], ENET_PRIORITY );
                    NVIC_SetPriority( enetTxIrqId[ instance ], ENET_PRIORITY );
                    break;
                }
            }

            configASSERT( instance != ARRAY_SIZE( enetBases ) );

            if( instance == ARRAY_SIZE( enetBases ) )
            {
                eEMACState = xEMAC_Fatal;
                break;
            }

            for( i = 0; i < ENET_RXBUFF_NUM; i++ )
            {
                ethernetifLocal->RxPbufs[ i ].buffer = &( ethernetifLocal->RxDataBuff[ i ][ 0 ] );
                ethernetifLocal->RxPbufs[ i ].buffer_used = false;
            }

            /* Initialize the ENET module. */
            readStatus = ENET_Init( ethernetifLocal->base,
                                    &ethernetifLocal->handle,
                                    &config,
                                    &buffCfg[ 0 ],
                                    ipLOCAL_MAC_ADDRESS,
                                    sysClock );

            if( readStatus == kStatus_Success )
            {
                FreeRTOS_printf( ( "ENET initialized." ) );
                ENET_ActiveRead( ethernetifLocal->base );
                eEMACState = xEMAC_WaitPHY;
            }
            else
            {
                FreeRTOS_printf( ( "Failed to initialize ENET." ) );
                break;
            }

            /* The handler task is created at the highest possible priority to
             * ensure the interrupt handler can return directly to it. */
            xResult = xTaskCreate( prvEMACHandlerTask,
                                   "EMAC-Handler",
                                   configMINIMAL_STACK_SIZE * 3,
                                   NULL,
                                   configMAX_PRIORITIES - 1,
                                   &receiveTaskHandle );

            if( receiveTaskHandle == NULL )
            {
                FreeRTOS_printf( ( "Failed to create the handler task." ) );
                eEMACState = xEMAC_Fatal;
                break;
            }

            /* Enable the interrupt and set its priority to the minimum
             * interrupt priority.  */
            NVIC_SetPriority( ENET_IRQn, ENET_PRIORITY );
            NVIC_EnableIRQ( ENET_IRQn );

            FreeRTOS_printf( ( "Driver ready for use." ) );
            eEMACState = xEMAC_Ready;
        /* Fall through. */

        case xEMAC_Ready:
            xResult = pdPASS;
            break;

        case xEMAC_Fatal:
            xResult = pdFAIL;
            break;
    }

    return xResult;
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t xReleaseAfterSend )
{
    status_t result;
    BaseType_t xReturn = pdFAIL;
    bool LinkUp = false;
    status_t readStatus;

    readStatus = PHY_GetLinkStatus( &phyHandle, &LinkUp );

    if( ( readStatus == kStatus_Success ) &&
        ( LinkUp == true ) )
    {
        result = ENET_SendFrame( ethernetifLocal->base,
                                 &ethernetifLocal->handle,
                                 pxNetworkBuffer->pucEthernetBuffer,
                                 pxNetworkBuffer->xDataLength,
                                 0,
                                 false,
                                 NULL );

        switch( result )
        {
            case kStatus_ENET_TxFrameBusy:
                FreeRTOS_printf( ( "Failed to send the frame - driver busy!\r\n" ) );
                break;

            case kStatus_Success:
                iptraceNETWORK_INTERFACE_TRANSMIT();
                xReturn = pdPASS;
                break;
        }
    }

    if( xReleaseAfterSend == pdTRUE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

    return xReturn;
}

static void prvEMACHandlerTask( void * parameter )
{
    bool LinkUp = false;
    status_t readStatus;

    while( pdTRUE )
    {
        if( ulTaskNotifyTake( pdTRUE, pdMS_TO_TICKS( 500 ) ) == pdFALSE ) /* no RX packets for a bit so check for a link */
        {
            const IPStackEvent_t xNetworkEventDown = { .eEventType = eNetworkDownEvent, .pvData = NULL };

            readStatus = PHY_GetLinkStatus( &phyHandle, &LinkUp );

            if( ( readStatus == kStatus_Success ) &&
                ( LinkUp == pdFALSE ) )
            {
                xSendEventStructToIPTask( &xNetworkEventDown, 0U );
            }
        }
        else
        {
            BaseType_t receiving = pdTRUE;

            while( receiving == pdTRUE )
            {
                uint32_t length;
                const status_t status = ENET_GetRxFrameSize( &( ethernetifLocal->handle ), &length, 0 );

                switch( status )
                {
                    case kStatus_Success: /* there is a frame.  process it */

                        if( length )
                        {
                            if( length > 1100 )
                            {
                                static int a = 0;
                                a++;
                            }

                            prvProcessFrame( length );
                        }

                        break;

                    case kStatus_ENET_RxFrameEmpty: /* Received an empty frame.  Ignore it */
                        receiving = pdFALSE;
                        break;

                    case kStatus_ENET_RxFrameError: /* Received an error frame.  Read & drop it */
                        PRINTF( "RX Receive Error\n" );
                        ENET_ReadFrame( ethernetifLocal->base, &( ethernetifLocal->handle ), NULL, 0, 0, NULL );
                        /* Not sure if a trace is required.  The MAC had an error and needed to dump bytes */
                        break;

                    default:
                        PRINTF( "RX Receive default\n" );
                        break;
                }
            }
        }
    }
}

/*
 * @brief Callback for ENET interrupts. We have only enabled the Ethernet receive interrupts
 * in the case of this driver.
 */
static void ethernet_callback( ENET_Type * base,
                               enet_handle_t * handle,
                               enet_event_t event,
                               enet_frame_info_t * frameInfo,
                               void * userData )
{
    BaseType_t needsToYield = pdFALSE;

    switch( event )
    {
        case kENET_RxEvent:
            vTaskNotifyGiveFromISR( receiveTaskHandle, &needsToYield );
            portEND_SWITCHING_ISR( needsToYield );
            break;

        default:
            FreeRTOS_printf( ( "Unknown interrupt callback %u!", event ) );
            break;
    }
}

static void prvProcessFrame( int length )
{
    NetworkBufferDescriptor_t * pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( length, 0 );

    if( pxBufferDescriptor != NULL )
    {
        ENET_ReadFrame( ethernetifLocal->base, &( ethernetifLocal->handle ), pxBufferDescriptor->pucEthernetBuffer, length, 0, NULL );
        pxBufferDescriptor->xDataLength = length;

        if( ipCONSIDER_FRAME_FOR_PROCESSING( pxBufferDescriptor->pucEthernetBuffer ) == eProcessBuffer )
        {
            IPStackEvent_t xRxEvent;
            xRxEvent.eEventType = eNetworkRxEvent;
            xRxEvent.pvData = ( void * ) pxBufferDescriptor;

            if( xSendEventStructToIPTask( &xRxEvent, 0 ) == pdFALSE )
            {
                vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
                iptraceETHERNET_RX_EVENT_LOST();
                FreeRTOS_printf( ( "RX Event Lost\n" ) );
            }
        }
        else
        {
            FreeRTOS_printf( ( "RX Event not to be considered\n" ) );
            vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
            /* Not sure if a trace is required.  The stack did not want this message */
        }
    }
    else
    {
        FreeRTOS_printf( ( "RX No Buffer Available\n" ) );
        ENET_ReadFrame( ENET, &( ethernetifLocal->handle ), NULL, length, 0, NULL );
        /* No buffer available to receive this message */
        iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER();
    }
}
