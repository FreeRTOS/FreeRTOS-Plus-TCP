/*
 * FreeRTOS+TCP V2.3.1
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "task.h"
#include "semphr.h"

/* standard library definitions */
#include <string.h>
#include <limits.h>
#include <stdio.h>

/* FreeRTOS+TCP includes. */
#include <FreeRTOS_IP.h>
#include <FreeRTOS_IP_Private.h>

#include "NetworkBufferManagement.h"


#include "CMSIS/SMM_MPS2.h"
/* #include "CMSIS/ARMCM3.h" */
/* #include "CMSIS/Driver_ETH.h" */
#include "ether_lan9118/smsc9220_eth_drv.h"
#include "ether_lan9118/smsc9220_emac_config.h"

#include <FreeRTOSIPConfig.h>
#include "NetworkInterface.h"

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
 * driver will filter incoming packets and only pass the stack those packets it
* considers need processing. */
#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

#ifndef configNUM_TX_DESCRIPTORS
    #error please define configNUM_TX_DESCRIPTORS in your FreeRTOSIPConfig.h
#endif

#ifndef PHY_LS_LOW_CHECK_TIME_MS
    /* Check if the LinkSStatus in the PHY is still low every second. */
    #define PHY_LS_LOW_CHECK_TIME_MS    1000
#endif

#define nwRX_TASK_STACK_SIZE    140

#define niMAX_TX_ATTEMPTS           ( 5 )

#define TX_BIT    0x01
#define RX_BIT    0x02

static void rx_task( void * pvParameters );

static void packet_rx();

static uint32_t low_level_input(NetworkBufferDescriptor_t ** pxNetworkBuffer);

static const struct smsc9220_eth_dev_cfg_t SMSC9220_ETH_DEV_CFG = {
                            .base = SMSC9220_BASE};

static struct smsc9220_eth_dev_data_t SMSC9220_ETH_DEV_DATA = {
                            .state = 0};

static struct smsc9220_eth_dev_t SMSC9220_ETH_DEV = {&(SMSC9220_ETH_DEV_CFG),
                            &(SMSC9220_ETH_DEV_DATA)};

static void print_hex( unsigned const char * const bin_data, size_t len);
// defined in main_networking.c
extern uint8_t ucMACAddress[ SMSC9220_HWADDR_SIZE ]; // 6 bytes

static TaskHandle_t xRxHanderTask = NULL;

/* xTXDescriptorSemaphore is a counting semaphore with
 * a maximum count of ETH_TXBUFNB, which is the number of
 * DMA TX descriptors. */
static SemaphoreHandle_t xTXDescriptorSemaphore = NULL;

/*!
 * @brief print binary packet in hex
 * @param [in] bin_daa data to print
 * @param [in] len length of the data
 */
//#if ( ipconfigHAS_DEBUG_PRINTF == 1 )
static void print_hex( unsigned const char * const bin_data,
                       size_t len )
{
    size_t i;

    for( i = 0; i < len; ++i )
    {
        printf(  "%.2X ", bin_data[ i ]  );
        if (((i + 1) % 16) == 0)
            printf("\n");
    }

    printf(  "\n"  );
}
//#else
//#define print_hex (void*)0;
//#endif


static void wait_ms_function(uint32_t sleep_ms)
{
    vTaskDelay(pdMS_TO_TICKS(sleep_ms));
    return;
}

static void set_mac(const uint8_t *addr)
{
    const struct smsc9220_eth_dev_t* dev = &SMSC9220_ETH_DEV;
    uint8_t _hwaddr[SMSC9220_HWADDR_SIZE];
    if (!addr) {
        return;
    }
    memcpy (_hwaddr, addr, sizeof _hwaddr);
    uint32_t mac_low = 0;
    uint32_t mac_high = 0;
    /* Using local variables to make sure the right alignment is used */
    memcpy ((void*)&mac_low, (void*)addr, 4);
    memcpy ((void*)&mac_high, (void*)(addr+4), 2);
    if (smsc9220_mac_regwrite (dev, SMSC9220_MAC_REG_OFFSET_ADDRL, mac_low)) {
        return;
    }
    if (smsc9220_mac_regwrite (dev, SMSC9220_MAC_REG_OFFSET_ADDRH, mac_high)) {
        return;
    }
}

bool get_mac(uint8_t *addr)
{
    const struct smsc9220_eth_dev_t* dev = &SMSC9220_ETH_DEV;
    if (smsc9220_read_mac_address ( dev, ( char * ) addr ) == SMSC9220_ERROR_NONE ) {
        return pdTRUE;
    } else {
        return pdFALSE;
    }
}

BaseType_t xNetworkInterfaceInitialise( void )
{
    const struct smsc9220_eth_dev_t* dev = &SMSC9220_ETH_DEV;
    BaseType_t xReturn = pdPASS;
    //struct smsc9220_eth_dev_t* dev;
    enum smsc9220_error_t err;

    FreeRTOS_debug_printf( ("Enter\n") );

    if ( xRxHanderTask == NULL )
    {
        xReturn = xTaskCreate( rx_task,
                               "EMAC",
                               nwRX_TASK_STACK_SIZE,
                               NULL,
                               configMAX_PRIORITIES - 4,
                               &xRxHanderTask );
        configASSERT( xReturn != 0 );
    }

    err = smsc9220_init (dev, wait_ms_function);
    if (err != SMSC9220_ERROR_NONE)
    {
        FreeRTOS_debug_printf(("%s: %d\n", "smsc9220_init failed", err));
        xReturn = pdFAIL;
    }
    else
    {
        NVIC_DisableIRQ (ETHERNET_IRQn);
        //smsc9220_disable_interrupt(dev, SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL);
        smsc9220_disable_all_interrupts(dev);
        smsc9220_clear_all_interrupts(dev);

        smsc9220_set_fifo_level_irq (dev, SMSC9220_FIFO_LEVEL_IRQ_RX_STATUS_POS,
                                    SMSC9220_FIFO_LEVEL_IRQ_LEVEL_MIN);
        smsc9220_set_fifo_level_irq (dev, SMSC9220_FIFO_LEVEL_IRQ_TX_STATUS_POS,
                                    SMSC9220_FIFO_LEVEL_IRQ_LEVEL_MIN);
        smsc9220_set_fifo_level_irq (dev, SMSC9220_FIFO_LEVEL_IRQ_TX_DATA_POS,
                                    SMSC9220_FIFO_LEVEL_IRQ_LEVEL_MAX);

        set_mac(ucMACAddress);

        /*
        if ( xTXDescriptorSemaphore == NULL )
        {
            xTXDescriptorSemaphore = xSemaphoreCreateCounting( ( UBaseType_t ) configNUM_TX_DESCRIPTORS,
                                                            ( UBaseType_t ) configNUM_TX_DESCRIPTORS );
            configASSERT( xTXDescriptorSemaphore != NULL );
        }
        */
        label:
        NVIC_SetPriority( ETHERNET_IRQn, configMAC_INTERRUPT_PRIORITY );
        //NVIC_EnableIRQ (ETHERNET_IRQn);

    // NVIC_ClearPendingIRQ(ETHERNET_IRQn);
        /* Enable Ethernet interrupts in NVIC */
        smsc9220_enable_interrupt(dev, SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL);
    }
    FreeRTOS_debug_printf( ("Exit\n") );
    return xReturn;
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t xReleaseAfterSend )
{
    const struct smsc9220_eth_dev_t* dev = &SMSC9220_ETH_DEV;
    const TickType_t xBlockTimeTicks = pdMS_TO_TICKS( 50 );
    enum smsc9220_error_t error = SMSC9220_ERROR_NONE;
    BaseType_t xReturn = pdFAIL;
    int x;

    FreeRTOS_debug_printf( ("Enter\n") );

    for ( x = 0; x < niMAX_TX_ATTEMPTS; x++ )
    {
        if ( pxNetworkBuffer->xDataLength < SMSC9220_ETH_MAX_FRAME_SIZE )
        {   /*_RB_ The size needs to come from FreeRTOSIPConfig.h. */
            FreeRTOS_debug_printf(("outgoing data > > > > > > > > > > > > length: %d\n",
                    pxNetworkBuffer->xDataLength));
            printf("outgoing data\n");
            print_hex(pxNetworkBuffer->pucEthernetBuffer,
                      pxNetworkBuffer->xDataLength);
            error = smsc9220_send_by_chunks(dev,
                                            pxNetworkBuffer->xDataLength,
                                            true,
                                            pxNetworkBuffer->pucEthernetBuffer,
                                            pxNetworkBuffer->xDataLength);
             if (error == SMSC9220_ERROR_NONE)
             {
                 xReturn = pdPASS;
                 break;
             }
             else
             {
                xReturn = pdFAIL;
                FreeRTOS_debug_printf( ("Error send by chuncks: %d\n",
                                        error) );
             }
        }
        else
        {
            xReturn = pdFAIL;
            FreeRTOS_debug_printf( ("Packet size too large:%d\n",
                                    pxNetworkBuffer->xDataLength) );
            break;
        }
    }
    printf("releasing in output\n");
    if ( xReleaseAfterSend  == pdTRUE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }
    FreeRTOS_debug_printf( ("Exit\n") );
    return xReturn;
}

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    /* FIX ME. */
}

BaseType_t xGetPhyLinkStatus( void )
{
    const struct smsc9220_eth_dev_t* dev = &SMSC9220_ETH_DEV;
    uint32_t phy_basic_status_reg_value = 0;
    bool current_link_status_up = false;
    /* Get current status */
    smsc9220_phy_regread(dev, SMSC9220_PHY_REG_OFFSET_BSTATUS,
                         &phy_basic_status_reg_value);
    current_link_status_up = (bool)(phy_basic_status_reg_value &
                          (1ul << (PHY_REG_BSTATUS_LINK_STATUS_INDEX)));
    /* Compare with the previous state */
    return current_link_status_up;
/*
    if (current_link_status_up != _prev_link_status_up) {
        _emac_link_state_cb(current_link_status_up);
        _prev_link_status_up = current_link_status_up;
    }
*/

    /* FIX ME. */
    return pdFALSE;
}

void EthernetISR(void)
{
    const struct smsc9220_eth_dev_t* dev = &SMSC9220_ETH_DEV;
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    int ret;
    FreeRTOS_debug_printf( ("Enter\n") );


    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_GPIO0)))
        printf("1\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_GPIO1)))
        printf("2\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_GPIO2)))
        printf("3\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL)))
        printf("4\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_RX_STATUS_FIFO_FULL)))
        printf("5\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_RX_DROPPED_FRAME)))
        printf("6\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_TX_STATUS_FIFO_LEVEL)))
        printf("7\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_TX_STATUS_FIFO_FULL)))
        printf("8\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_TX_DATA_FIFO_AVAILABLE)))
        printf("9\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_TX_DATA_FIFO_OVERRUN)))
        printf("9\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_TX_ERROR)))
        printf("10\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_RX_ERROR)))
        printf("11\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_RX_WATCHDOG_TIMEOUT)))
        printf("12\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_TX_STATUS_OVERFLOW)))
        printf("13\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_TX_POWER_MANAGEMENT)))
        printf("14\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_PHY)))
        printf("15\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_GP_TIMER)))
        printf("16\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_RX_DMA)))
        printf("17\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_TX_IOC)))
        printf("18\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_RX_DROPPED_FRAME_HALF)))
        printf("19\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_RX_STOPPED)))
        printf("20\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_TX_STOPPED)))
        printf("30\n");
    if ((ret = smsc9220_get_interrupt(dev,SMSC9220_INTERRUPT_SW)))
        printf("40\n");

    if ((ret = smsc9220_get_interrupt(dev,
                               SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL)))
    {
        smsc9220_clear_interrupt(dev,
                                 SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL);
        smsc9220_disable_interrupt(dev,
                                   SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL);
        NVIC_ClearPendingIRQ(ETHERNET_IRQn);
        NVIC_DisableIRQ(ETHERNET_IRQn);
        xTaskNotifyFromISR( xRxHanderTask,
                            RX_BIT,
                            eSetBits,
                            &xHigherPriorityTaskWoken );

    }
    //NVIC_DisableIRQ(ETHERNET_IRQn);
    NVIC_ClearPendingIRQ(ETHERNET_IRQn);
    smsc9220_clear_all_interrupts(dev);
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
    FreeRTOS_debug_printf( ("Exit\n") );
}

static void rx_task( void * pvParameters )
{

    BaseType_t xResult = 0;
    uint32_t ulNotifiedValue;
    const struct smsc9220_eth_dev_t* dev = &SMSC9220_ETH_DEV;
    const TickType_t xBlockTime = pdMS_TO_TICKS( 50ul );
    FreeRTOS_debug_printf( ("Enter\n") );

    for (; ;)
    {
        if ((smsc9220_get_interrupt(dev,
                                    SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL)))
        { // data received
            smsc9220_clear_interrupt(dev,
                                     SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL);
        //    smsc9220_disable_interrupt(dev,
         //                              SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL);
            xResult = pdPASS;

        }
        else{
            vTaskDelay(xBlockTime );
            continue;
        }
        /*
        xResult = xTaskNotifyWait ( pdFALSE,
                                    ULONG_MAX,
                                    &ulNotifiedValue,
                                    portMAX_DELAY );
        */
        printf("received notification from isr\n");
        //if ( xResult == pdPASS )
        {
         //   if ( ( ulNotifiedValue & RX_BIT ) != 0 )
            {   /* packets received */
                packet_rx();
         //       NVIC_EnableIRQ (ETHERNET_IRQn);
                smsc9220_enable_interrupt(dev, SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL);
            }
        }
        //else
        {
        }
    }
}

static void packet_rx()
{
    const struct smsc9220_eth_dev_t* dev = &SMSC9220_ETH_DEV;
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
    NetworkBufferDescriptor_t * pxNetworkBuffer = NULL;
    uint32_t data_read;

    FreeRTOS_debug_printf( ("Enter\n") );
    //pxNetworkBuffer = pxGetNetworkBufferWithDescriptor(0, (TickType_t) 0);
   // if (pxNetworkBuffer != NULL)
   // {
        data_read = low_level_input(&pxNetworkBuffer);
        if (data_read > 0)
        {
            xRxEvent.pvData = ( void * ) pxNetworkBuffer;

            if (xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0 ) == pdFAIL)
            {
        printf("after send to ip task check\n");
        print_hex((pxNetworkBuffer)->hedge, 50);
        print_hex((pxNetworkBuffer)->hedge2, 50);
                vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
            }
        }
    //}
    FreeRTOS_debug_printf( ("Exit\n") );
}

static uint32_t low_level_input(NetworkBufferDescriptor_t ** pxNetworkBuffer)
{
    const struct smsc9220_eth_dev_t* dev = &SMSC9220_ETH_DEV;
    const TickType_t xDescriptorWaitTime = pdMS_TO_TICKS( 250 );
    uint32_t message_length = 0;
    uint32_t received_bytes = 0;

    FreeRTOS_debug_printf( ("Enter\n") );

    message_length = smsc9220_peek_next_packet_size(dev);
    if (message_length != 0)
    {
        /* The Ethernet controller cannot remove CRC from the end of the
        * incoming packet, thus it should be taken into account when
        * calculating the actual message length.*/
        //message_length -= CRC_LENGTH_BYTES;
        *pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( message_length,
                                                             xDescriptorWaitTime );
        printf("after receive check\n");
        print_hex((*pxNetworkBuffer)->hedge, 50);
        print_hex((*pxNetworkBuffer)->hedge2, 50);
        if (*pxNetworkBuffer != NULL)
        {
            (*pxNetworkBuffer)->xDataLength = message_length;

            received_bytes = smsc9220_receive_by_chunks(dev,
                                    (*pxNetworkBuffer)->pucEthernetBuffer,
                                    message_length);
                                    //(*pxNetworkBuffer)->xDataLength);
            (*pxNetworkBuffer)->xDataLength = received_bytes;
            FreeRTOS_debug_printf(("incoming data < < < < < < < < < < read: %d length: %d\n",
                    received_bytes, message_length
                    ));
            print_hex((*pxNetworkBuffer)->pucEthernetBuffer,
                    received_bytes);
        }
        else{
            FreeRTOS_debug_printf( ("pxNetworkBuffer = NULL\n") );
            printf ("pxNetworkBuffer = NULL\n" );
        }
    }
    printf("after send check\n");
    print_hex((*pxNetworkBuffer)->hedge, 50);
    print_hex((*pxNetworkBuffer)->hedge2, 50);
    FreeRTOS_debug_printf( ("Exit\n") );
    return received_bytes;
}
