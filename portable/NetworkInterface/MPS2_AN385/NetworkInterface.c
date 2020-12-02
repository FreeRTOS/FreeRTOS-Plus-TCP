/*
 * FreeRTOS+TCP V2.3.2
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://github.com/FreeRTOS
 * https://www.FreeRTOS.org
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "task.h"
#include "semphr.h"

/* standard library definitions */
#include <string.h>
#include <limits.h>

/* FreeRTOS+TCP includes. */
#include <FreeRTOS_IP.h>
#include <FreeRTOS_IP_Private.h>

#include "NetworkBufferManagement.h"

#include "CMSIS/SMM_MPS2.h"
#include "ether_lan9118/smsc9220_eth_drv.h"
#include "ether_lan9118/smsc9220_emac_config.h"

#include <FreeRTOSIPConfig.h>
#include "NetworkInterface.h"

/* =============================== Function Macros ========================== */

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
 * driver will filter incoming packets and only pass the stack those packets it
 * considers need processing. */
#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif


/* ============================= Variable Definitions ======================= */
#ifndef configNUM_TX_DESCRIPTORS
    #error please define configNUM_TX_DESCRIPTORS in your FreeRTOSIPConfig.h
#endif

#ifndef PHY_LS_LOW_CHECK_TIME_MS
    /* Check if the LinkSStatus in the PHY is still low every second. */
    #define PHY_LS_LOW_CHECK_TIME_MS    1000
#endif

#define nwRX_TASK_STACK_SIZE            140

#define niMAX_TX_ATTEMPTS               ( 5 )


/* =============================  Static Prototypes ========================= */
static void rx_task( void * pvParameters );

static void packet_rx();

static uint32_t low_level_input( NetworkBufferDescriptor_t ** pxNetworkBuffer );

static const struct smsc9220_eth_dev_cfg_t SMSC9220_ETH_DEV_CFG =
{
    .base = SMSC9220_BASE
};

static struct smsc9220_eth_dev_data_t SMSC9220_ETH_DEV_DATA = { .state = 0 };

static struct smsc9220_eth_dev_t SMSC9220_ETH_DEV =
{
    &( SMSC9220_ETH_DEV_CFG ),
    &( SMSC9220_ETH_DEV_DATA )
};

static void print_hex( unsigned const char * const bin_data,
                       size_t len );


/* =============================  Extern Variables ========================== */
/* defined in main_networking.c */
extern uint8_t ucMACAddress[ SMSC9220_HWADDR_SIZE ]; /* 6 bytes */


/* =============================  Static Variables ========================== */
static TaskHandle_t xRxHanderTask = NULL;


/* =============================  Static Functions ========================== */

/*!
 * @brief print binary packet in hex
 * @param [in] bin_daa data to print
 * @param [in] len length of the data
 */
#if ( ipconfigHAS_DEBUG_PRINTF == 1 )
    static void print_hex( unsigned const char * const bin_data,
                           size_t len )
    {
        size_t i;

        for( i = 0; i < len; ++i )
        {
            printf( "%.2X ", bin_data[ i ] );

            if( ( ( i + 1 ) % 16 ) == 0 )
            {
                printf( "\n" );
            }
        }

        printf( "\n" );
    }
#else /* if ( ipconfigHAS_DEBUG_PRINTF == 1 ) */
    #define print_hex    ( void * ) 0;
#endif /* if ( ipconfigHAS_DEBUG_PRINTF == 1 ) */

static void wait_ms_function( uint32_t sleep_ms )
{
    vTaskDelay( pdMS_TO_TICKS( sleep_ms ) );
}

static void set_mac( const uint8_t * addr )
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    uint8_t _hwaddr[ SMSC9220_HWADDR_SIZE ];

    if( !addr )
    {
        return;
    }

    memcpy( _hwaddr, addr, sizeof _hwaddr );
    uint32_t mac_low = 0;
    uint32_t mac_high = 0;
    /* Using local variables to make sure the right alignment is used */
    memcpy( ( void * ) &mac_low, ( void * ) addr, 4 );
    memcpy( ( void * ) &mac_high, ( void * ) ( addr + 4 ), 2 );

    if( smsc9220_mac_regwrite( dev, SMSC9220_MAC_REG_OFFSET_ADDRL, mac_low ) )
    {
        return;
    }

    if( smsc9220_mac_regwrite( dev, SMSC9220_MAC_REG_OFFSET_ADDRH, mac_high ) )
    {
        return;
    }
}

/**
 * @brief function to poll the netwrok card(qemu emulation) as we faced some
 *        problems with the network interrupt being fired for no reason at
 *        a very high rate which made the program not progress
 */
static void rx_task( void * pvParameters )
{
    BaseType_t xResult = 0;
    uint32_t ulNotifiedValue;
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    const TickType_t xBlockTime = pdMS_TO_TICKS( 50ul );

    FreeRTOS_debug_printf( ( "Enter\n" ) );

    for( ; ; )
    {
        if( ( smsc9220_get_interrupt( dev,
                                      SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL ) ) )
        {   /* data received */
            smsc9220_clear_interrupt( dev,
                                      SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL );
            xResult = pdPASS;
        }
        else
        {
            vTaskDelay( xBlockTime );
            continue;
        }

        packet_rx();
        smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL );
    }
}

static void packet_rx()
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
    NetworkBufferDescriptor_t * pxNetworkBuffer = NULL;
    uint32_t data_read;

    FreeRTOS_debug_printf( ( "Enter\n" ) );
    data_read = low_level_input( &pxNetworkBuffer );

    if( data_read > 0 )
    {
        xRxEvent.pvData = ( void * ) pxNetworkBuffer;

        if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0 ) == pdFAIL )
        {
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
        }
    }

    FreeRTOS_debug_printf( ( "Exit\n" ) );
}

static uint32_t low_level_input( NetworkBufferDescriptor_t ** pxNetworkBuffer )
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    const TickType_t xDescriptorWaitTime = pdMS_TO_TICKS( 250 );
    uint32_t message_length = 0;
    uint32_t received_bytes = 0;

    FreeRTOS_debug_printf( ( "Enter\n" ) );

    message_length = smsc9220_peek_next_packet_size( dev );

    if( message_length != 0 )
    {
        *pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( message_length,
                                                             xDescriptorWaitTime );

        if( *pxNetworkBuffer != NULL )
        {
            ( *pxNetworkBuffer )->xDataLength = message_length;

            received_bytes = smsc9220_receive_by_chunks( dev,
                                                         ( *pxNetworkBuffer )->pucEthernetBuffer,
                                                         message_length ); /* not used */
            ( *pxNetworkBuffer )->xDataLength = received_bytes;
            FreeRTOS_debug_printf( ( "incoming data < < < < < < < < < < read: %d length: %d\n",
                                     received_bytes,
                                     message_length ) );
            print_hex( ( *pxNetworkBuffer )->pucEthernetBuffer,
                       received_bytes );
        }
        else
        {
            FreeRTOS_printf( ( "pxNetworkBuffer = NULL\n" ) );
        }
    }

    FreeRTOS_debug_printf( ( "Exit\n" ) );
    return received_bytes;
}

/* =============================== API Functions ============================ */
BaseType_t xNetworkInterfaceInitialise( void )
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    BaseType_t xReturn = pdPASS;
    enum smsc9220_error_t err;

    FreeRTOS_debug_printf( ( "Enter\n" ) );

    if( xRxHanderTask == NULL )
    {
        xReturn = xTaskCreate( rx_task,
                               "EMAC",
                               nwRX_TASK_STACK_SIZE,
                               NULL,
                               configMAX_PRIORITIES - 4,
                               &xRxHanderTask );
        configASSERT( xReturn != 0 );
    }

    err = smsc9220_init( dev, wait_ms_function );

    if( err != SMSC9220_ERROR_NONE )
    {
        FreeRTOS_debug_printf( ( "%s: %d\n", "smsc9220_init failed", err ) );
        xReturn = pdFAIL;
    }
    else
    {
        NVIC_DisableIRQ( ETHERNET_IRQn );
        smsc9220_disable_all_interrupts( dev );
        smsc9220_clear_all_interrupts( dev );

        smsc9220_set_fifo_level_irq( dev, SMSC9220_FIFO_LEVEL_IRQ_RX_STATUS_POS,
                                     SMSC9220_FIFO_LEVEL_IRQ_LEVEL_MIN );
        smsc9220_set_fifo_level_irq( dev, SMSC9220_FIFO_LEVEL_IRQ_TX_STATUS_POS,
                                     SMSC9220_FIFO_LEVEL_IRQ_LEVEL_MIN );
        smsc9220_set_fifo_level_irq( dev, SMSC9220_FIFO_LEVEL_IRQ_TX_DATA_POS,
                                     SMSC9220_FIFO_LEVEL_IRQ_LEVEL_MAX );
        set_mac( ucMACAddress );
        NVIC_SetPriority( ETHERNET_IRQn, configMAC_INTERRUPT_PRIORITY );
        smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL );
    }

    FreeRTOS_debug_printf( ( "Exit\n" ) );
    return xReturn;
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t xReleaseAfterSend )
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    const TickType_t xBlockTimeTicks = pdMS_TO_TICKS( 50 );
    enum smsc9220_error_t error = SMSC9220_ERROR_NONE;
    BaseType_t xReturn = pdFAIL;
    int x;

    FreeRTOS_debug_printf( ( "Enter\n" ) );

    for( x = 0; x < niMAX_TX_ATTEMPTS; x++ )
    {
        if( pxNetworkBuffer->xDataLength < SMSC9220_ETH_MAX_FRAME_SIZE )
        {   /*_RB_ The size needs to come from FreeRTOSIPConfig.h. */
            FreeRTOS_debug_printf( ( "outgoing data > > > > > > > > > > > > length: %d\n",
                                     pxNetworkBuffer->xDataLength ) );
            print_hex( pxNetworkBuffer->pucEthernetBuffer,
                       pxNetworkBuffer->xDataLength );
            error = smsc9220_send_by_chunks( dev,
                                             pxNetworkBuffer->xDataLength,
                                             true,
                                             pxNetworkBuffer->pucEthernetBuffer,
                                             pxNetworkBuffer->xDataLength );

            if( error == SMSC9220_ERROR_NONE )
            {
                xReturn = pdPASS;
                break;
            }
            else
            {
                xReturn = pdFAIL;
                FreeRTOS_debug_printf( ( "Error send by chuncks: %d\n",
                                         error ) );
            }
        }
        else
        {
            xReturn = pdFAIL;
            FreeRTOS_debug_printf( ( "Packet size too large:%d\n",
                                     pxNetworkBuffer->xDataLength ) );
            break;
        }
    }

    if( xReleaseAfterSend == pdTRUE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

    FreeRTOS_debug_printf( ( "Exit\n" ) );
    return xReturn;
}

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    /* FIX ME. */
}

BaseType_t xGetPhyLinkStatus( void )
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    uint32_t phy_basic_status_reg_value = 0;
    bool current_link_status_up = pdFALSE;

    /* Get current status */
    smsc9220_phy_regread( dev, SMSC9220_PHY_REG_OFFSET_BSTATUS,
                          &phy_basic_status_reg_value );
    current_link_status_up = ( bool ) ( phy_basic_status_reg_value &
                                        ( 1ul << ( PHY_REG_BSTATUS_LINK_STATUS_INDEX ) ) );
    return current_link_status_up;
}
