/**
 *       @file: NetworkInterface.c
 *	   @author: jscott <jscott@hotstart.com>
 *       @date: Feb 1, 2022
 *  @copyright: Hotstart 2022 Hotstart Thermal Management. All Rights Reserved.
 *
 *      Permission is hereby granted, free of charge, to any person obtaining a copy of
 *      this software and associated documentation files (the "Software"), to deal in
 *      the Software without restriction, including without limitation the rights to
 *      use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 *      the Software, and to permit persons to whom the Software is furnished to do so,
 *      subject to the following conditions:
 *
 *      The above copyright notice and this permission notice shall be included in all
 *      copies or substantial portions of the Software.
 *
 *      THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 *      IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 *      FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 *      COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 *      IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 *      CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *      @brief:Network Interface driver for the Texas Instruments TM4C line of microcontrollers.
 *
 *      This driver was written and tested with the TM4C1294NCPDT, which includes a built-in MAC and
 *      PHY. The expectation is that this driver should function correctly across all the MAC/PHY
 *      integrated parts of the TM4C129X parts.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>

#include "inc/hw_ints.h"
#include "inc/hw_emac.h"
#include "inc/hw_memmap.h"
#include "inc/hw_nvic.h"

#include "driverlib/flash.h"
#include "driverlib/interrupt.h"
#include "driverlib/gpio.h"
#include "driverlib/rom_map.h"
#include "driverlib/sysctl.h"
#include "driverlib/systick.h"
#include "driverlib/emac.h"

#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#define BUFFER_SIZE                             (ipTOTAL_ETHERNET_FRAME_SIZE + ipBUFFER_PADDING)
#define BUFFER_SIZE_ROUNDED_UP                  ((BUFFER_SIZE + 7) & ~0x7UL)
#define PHY_PHYS_ADDR                           0
#define ETH_DEFERRED_INT_TASK_STACK_SIZE        512

#define SYSCONFIG_SYSFREQ_HZ                            120000000
#define SYSCONFIG_FREERTOS_TCP_TX_DESC_COUNT            8
#define SYSCONFIG_FREERTOS_TCP_RX_DESC_COUNT            8
#define SYSCONFIG_FREERTOS_TCP_MAX_PENDING_RX_PACKETS   SYSCONFIG_FREERTOS_TCP_RX_DESC_COUNT

typedef struct {
    uint32_t number_descriptors;
    uint32_t write;
    uint32_t read;
} tDescriptorList;

typedef enum
{
    eMACInitQueue = 0, /* Queue must be initialized. */
    eMACInitTask,      /* Task must be initialized. */
    eMACInitHw,        /* Must initialize MAC. */
    eMACInitComplete,  /* Initialization was successful. */
} eMAC_INIT_STATUS_TYPE;
static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMACInitQueue;

static tEMACDMADescriptor _tx_descriptors[SYSCONFIG_FREERTOS_TCP_TX_DESC_COUNT];
static tEMACDMADescriptor _rx_descriptors[SYSCONFIG_FREERTOS_TCP_RX_DESC_COUNT];

static tDescriptorList _tx_descriptor_list = { .number_descriptors = SYSCONFIG_FREERTOS_TCP_TX_DESC_COUNT, 0 };
static tDescriptorList _rx_descriptor_list = { .number_descriptors = SYSCONFIG_FREERTOS_TCP_RX_DESC_COUNT, 0 };

static uint8_t _network_buffers[ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS][BUFFER_SIZE_ROUNDED_UP];
#pragma DATA_ALIGN(_network_buffers, 4)

static QueueHandle_t _received_packets_queue = NULL;

/* Default the size of the stack used by the EMAC deferred handler task to twice
 * the size of the stack used by the idle task - but allow this to be overridden in
 * FreeRTOSConfig.h as configMINIMAL_STACK_SIZE is a user definable constant. */
#ifndef configEMAC_TASK_STACK_SIZE
    #define configEMAC_TASK_STACK_SIZE    ( 2 * configMINIMAL_STACK_SIZE )
#endif

#ifndef niEMAC_HANDLER_TASK_PRIORITY
    #define niEMAC_HANDLER_TASK_PRIORITY    configMAX_PRIORITIES - 1
#endif

/**
 * Reads the Ethernet MAC from user Flash.
 * @param mac_address_bytes[out] The byte array which will hold the MAC address
 * @return pdPASS on success, pdFAIL if the MAC is invalid from user Flash
 */
static BaseType_t _ethernet_mac_get(uint8_t *mac_address_bytes);

/**
 * Initialize DMA descriptors
 */
static void _dma_descriptors_init(void);

/**
 * Frees previously sent network buffers
 */
static void _process_transmit_complete(void);

/**
 * Processes received packets and forwards those acceptable to the network stack
 */
static void _process_received_packet(void);

/**
 * Processes PHY interrupts.
 */
static void _process_phy_interrupt(void);

/**
 * Thread to forward received packets from the ISR to the network stack
 * @param parameters Not used
 */
static void _packet_received_thread(void *parameters);

BaseType_t xNetworkInterfaceInitialise(void)
{
    uint8_t mac_address_bytes[6];
    uint16_t ui16Val;
    BaseType_t xResult = pdPASS;

    switch (xMacInitStatus)
    {
    case eMACInitQueue:
        // Create the RX packet forwarding queue
        _received_packets_queue = xQueueCreate(SYSCONFIG_FREERTOS_TCP_MAX_PENDING_RX_PACKETS, sizeof(NetworkBufferDescriptor_t*));

        if (NULL == _received_packets_queue)
        {
            break;
        }

        xMacInitStatus = eMACInitTask;

    case eMACInitTask:
        // Create the RX packet forwarding task
        if (pdFAIL == xTaskCreate(_packet_received_thread, "tcprx", configEMAC_TASK_STACK_SIZE, NULL, niEMAC_HANDLER_TASK_PRIORITY, NULL))
        {
            break;
        }

        xMacInitStatus = eMACInitHw;

    case eMACInitHw:
        // Read the MAC from user Flash
        if (pdPASS != _ethernet_mac_get(&mac_address_bytes[0]))
        {
            break;
        }

        MAP_SysCtlPeripheralReset(SYSCTL_PERIPH_EMAC0);
        MAP_SysCtlPeripheralReset(SYSCTL_PERIPH_EPHY0);

        while (!MAP_SysCtlPeripheralReady(SYSCTL_PERIPH_EMAC0))
        {
        }

        MAP_EMACPHYConfigSet(
                EMAC0_BASE,
                EMAC_PHY_TYPE_INTERNAL | EMAC_PHY_INT_MDIX_EN
                        | EMAC_PHY_AN_100B_T_FULL_DUPLEX);

        MAP_EMACInit(EMAC0_BASE, SYSCONFIG_SYSFREQ_HZ,
                     EMAC_BCONFIG_MIXED_BURST | EMAC_BCONFIG_PRIORITY_FIXED, 4,
                     4, 0);

        MAP_EMACConfigSet(
                EMAC0_BASE,
                (
                    EMAC_CONFIG_100MBPS |
                    EMAC_CONFIG_FULL_DUPLEX |
                    EMAC_CONFIG_CHECKSUM_OFFLOAD |
                    EMAC_CONFIG_7BYTE_PREAMBLE |
                    EMAC_CONFIG_IF_GAP_96BITS |
                    EMAC_CONFIG_USE_MACADDR0 |
                    EMAC_CONFIG_SA_FROM_DESCRIPTOR |
                    EMAC_CONFIG_BO_LIMIT_1024
                ),
                (
                    EMAC_MODE_RX_STORE_FORWARD |
                    EMAC_MODE_TX_STORE_FORWARD |
                    EMAC_MODE_RX_THRESHOLD_64_BYTES |
                    EMAC_MODE_TX_THRESHOLD_64_BYTES),
                0);


        // Clear any stray PHY interrupts that may be set.
        ui16Val = MAP_EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1);
        ui16Val = MAP_EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR2);

        // Configure and enable the link status change interrupt in the PHY.
        ui16Val = MAP_EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_SCR);
        ui16Val |= (EPHY_SCR_INTEN_EXT | EPHY_SCR_INTOE_EXT);
        MAP_EMACPHYWrite(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_SCR, ui16Val);
        MAP_EMACPHYWrite(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1, (EPHY_MISR1_LINKSTATEN |
                     EPHY_MISR1_SPEEDEN | EPHY_MISR1_DUPLEXMEN | EPHY_MISR1_ANCEN));

        // Read the PHY interrupt status to clear any stray events.
        ui16Val = MAP_EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1);

        // Set MAC filtering options.  We receive all broadcast and mui32ticast
        // packets along with those addressed specifically for us.
        MAP_EMACFrameFilterSet(EMAC0_BASE, (EMAC_FRMFILTER_HASH_AND_PERFECT |
                           EMAC_FRMFILTER_PASS_MULTICAST));

        // Set the MAC address
        MAP_EMACAddrSet(EMAC0_BASE, 0, &mac_address_bytes[0]);

        // Clears any previously asserted interrupts
        MAP_EMACIntClear(EMAC0_BASE, EMACIntStatus(EMAC0_BASE, false));

        // Initialize the DMA descriptors
        _dma_descriptors_init();

        // Enable TX/RX
        MAP_EMACTxEnable(EMAC0_BASE);
        MAP_EMACRxEnable(EMAC0_BASE);

        // Set the interrupt to a lower priority than the OS scheduler interrupts
        MAP_IntPrioritySet(INT_EMAC0,  (6 << (8 - configPRIO_BITS)));

        // Enable the Ethernet RX and TX interrupt source.
        MAP_EMACIntEnable(EMAC0_BASE, (EMAC_INT_RECEIVE | EMAC_INT_TRANSMIT |
                      EMAC_INT_TX_STOPPED | EMAC_INT_RX_NO_BUFFER |
                      EMAC_INT_RX_STOPPED | EMAC_INT_PHY));

        // Enable EMAC interrupts
        MAP_IntEnable(INT_EMAC0);

        // Enable all processor interrupts.
        MAP_IntMasterEnable();

        // Tell the PHY to start an auto-negotiation cycle.
        MAP_EMACPHYWrite(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_BMCR, (EPHY_BMCR_ANEN |
                EPHY_BMCR_RESTARTAN));

        xMacInitStatus = eMACInitComplete;
    }

    if (eMACInitComplete != xMacInitStatus)
    {
        xResult = pdFAIL;
    }

    return xResult;
}

BaseType_t xNetworkInterfaceOutput(NetworkBufferDescriptor_t * const pxNetworkBuffer, BaseType_t xReleaseAfterSend)
{
    BaseType_t success = pdTRUE;
    tEMACDMADescriptor *dma_descriptor;

    dma_descriptor = &_tx_descriptors[_tx_descriptor_list.write];

    // If the DMA controller still owns the descriptor, all DMA descriptors are in use, bail out
    if (0 == (dma_descriptor->ui32CtrlStatus & DES0_RX_CTRL_OWN))
    {
        // Assign the buffer to the DMA descriptor
        dma_descriptor->pvBuffer1 = pxNetworkBuffer->pucEthernetBuffer;

        // Inform the DMA of the size of the packet
        dma_descriptor->ui32Count = (pxNetworkBuffer->xDataLength & DES1_TX_CTRL_BUFF1_SIZE_M) << DES1_TX_CTRL_BUFF1_SIZE_S;

        // Inform the DMA that this is the first and last segment of the packet, calculate the checksums, the descriptors are
        // chained, and to use interrupts
        dma_descriptor->ui32CtrlStatus = DES0_TX_CTRL_FIRST_SEG | /*DES0_TX_CTRL_IP_ALL_CKHSUMS |*/ DES0_TX_CTRL_CHAINED
                | DES0_TX_CTRL_LAST_SEG | DES0_TX_CTRL_INTERRUPT;// | DES0_TX_CTRL_REPLACE_CRC;

        // Advance the index in the list
        _tx_descriptor_list.write++;

        // Wrap around if required
        if (_tx_descriptor_list.write == SYSCONFIG_FREERTOS_TCP_TX_DESC_COUNT)
        {
            _tx_descriptor_list.write = 0;
        }

        // Give the DMA descriptor to the DMA controller
        dma_descriptor->ui32CtrlStatus |= DES0_TX_CTRL_OWN;

        // Inform the DMA it has a new descriptor
        MAP_EMACTxDMAPollDemand(EMAC0_BASE);

        iptraceNETWORK_INTERFACE_TRANSMIT();
    }
    else
    {
        success = pdFALSE;
    }

    return success;
}

void vNetworkInterfaceAllocateRAMToBuffers(NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ])
{
    BaseType_t i;

    for (i = 0; i < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; i++)
    {
        // Assign buffers to each descriptor
        pxNetworkBuffers[i].pucEthernetBuffer = &_network_buffers[i][ipBUFFER_PADDING];

        // Set the 'hidden' reference to the descriptor for use in DMA interrupts
        *((uint32_t *) &_network_buffers[i][0]) = (uint32_t) &((pxNetworkBuffers[i]));
    }
}

static BaseType_t _ethernet_mac_get(uint8_t *mac_address_bytes)
{
    BaseType_t success = pdPASS;
    uint32_t mac_address_words[2] = { 0 };

    // Attempt to read the MAC address
    MAP_FlashUserGet(&mac_address_words[0], &mac_address_words[1]);

    // If the MAC is not set, fail
    if (0xFFFFFFFF == mac_address_words[0] || 0xFFFFFFFF == mac_address_words[1])
    {
        terminal_printf("MAC Address not set\r\n");

        success = pdFAIL;
    }
    else
    {
        // Otherwise return the MAC address in a usable format for the driver
        *(mac_address_bytes + 0) = (mac_address_words[0] >> 0)  & 0xFF;
        *(mac_address_bytes + 1) = (mac_address_words[0] >> 8)  & 0xFF;
        *(mac_address_bytes + 2) = (mac_address_words[0] >> 16) & 0xFF;
        *(mac_address_bytes + 3) = (mac_address_words[1] >> 0)  & 0xFF;
        *(mac_address_bytes + 4) = (mac_address_words[1] >> 8)  & 0xFF;
        *(mac_address_bytes + 5) = (mac_address_words[1] >> 16) & 0xFF;
    }

    return success;
}

static void _dma_descriptors_init(void)
{
    uint32_t i;
    size_t buffer_size_requested;
    NetworkBufferDescriptor_t *stack_descriptor;

    // Initialize the TX DMA descriptors
    for (i = 0; i < SYSCONFIG_FREERTOS_TCP_TX_DESC_COUNT; i++)
    {
        // Clear the length of the packet
        _tx_descriptors[i].ui32Count = 0;

        // Clear the reference to the buffer
        _tx_descriptors[i].pvBuffer1 = NULL;

        // Set the next link in the DMA descriptor chain, either the next in the chain or the first descriptor in the event
        // that this is the last descriptor
        _tx_descriptors[i].DES3.pLink = (
                (i == (SYSCONFIG_FREERTOS_TCP_TX_DESC_COUNT - 1)) ?
                        &_tx_descriptors[0] : &_tx_descriptors[i + 1]);
        _tx_descriptors[i].ui32CtrlStatus = DES0_TX_CTRL_INTERRUPT | DES0_TX_CTRL_CHAINED
                | DES0_TX_CTRL_IP_ALL_CKHSUMS;
    }

    // Set the TX descriptor index
    _tx_descriptor_list.write = 0;
    _tx_descriptor_list.read = 0;

    for (i = 0; i < SYSCONFIG_FREERTOS_TCP_RX_DESC_COUNT; i++)
    {
        stack_descriptor = pxGetNetworkBufferWithDescriptor(ipTOTAL_ETHERNET_FRAME_SIZE, 0);

        configASSERT(NULL != stack_descriptor);

        // Get a buffer from the stack and assign it to the DMA Descriptor
        _rx_descriptors[i].pvBuffer1 = stack_descriptor->pucEthernetBuffer;

        // Inform the DMA controller that the descriptors are chained and the size of the buffer
        _rx_descriptors[i].ui32Count = DES1_RX_CTRL_CHAINED | ((buffer_size_requested << DES1_TX_CTRL_BUFF1_SIZE_S) & DES1_TX_CTRL_BUFF1_SIZE_M);

        // Give the DMA descriptor to the DMA controller
        _rx_descriptors[i].ui32CtrlStatus = DES0_RX_CTRL_OWN;

        // Set the next link the DMA descriptor chain
        _rx_descriptors[i].DES3.pLink = ((i == (SYSCONFIG_FREERTOS_TCP_RX_DESC_COUNT - 1)) ? &_rx_descriptors[0] : &_rx_descriptors[i + 1]);
    }

    // Set the RX descriptor index
    _rx_descriptor_list.write = 0;

    // Set the head of the DMA descriptor list in the EMAC peripheral
    MAP_EMACTxDMADescriptorListSet(EMAC0_BASE, &_tx_descriptors[0]);
    MAP_EMACRxDMADescriptorListSet(EMAC0_BASE, &_rx_descriptors[0]);
}

void freertos_tcp_ethernet_int(void)
{
    uint32_t status;

    // Read the interrupt status
    status = EMACIntStatus(EMAC0_BASE, true);

    // Handle power management interrupts
    if(status & EMAC_INT_POWER_MGMNT)
    {
        MAP_EMACTxEnable(EMAC0_BASE);
        MAP_EMACRxEnable(EMAC0_BASE);

        MAP_EMACPowerManagementStatusGet(EMAC0_BASE);

        status &= ~(EMAC_INT_POWER_MGMNT);
    }

    if (status)
    {
        MAP_EMACIntClear(EMAC0_BASE, status);
    }

    // Handle PHY interrupts
    if (EMAC_INT_PHY & status)
    {
        _process_phy_interrupt();
    }

    // Handle Transmit Complete interrupts
    if (EMAC_INT_TRANSMIT & status)
    {
        _process_transmit_complete();
    }

    // Handle Receive interrupts
    if ((EMAC_INT_RECEIVE | EMAC_INT_RX_NO_BUFFER | EMAC_INT_RX_STOPPED) & status)
    {
        _process_received_packet();
    }
}

static void _process_transmit_complete(void)
{
    uint32_t i;
    tEMACDMADescriptor *dma_descriptor;
    NetworkBufferDescriptor_t *stack_descriptor;

    for (i = 0; ((i < _tx_descriptor_list.number_descriptors) && (_tx_descriptor_list.read != _tx_descriptor_list.write)); i++)
    {
        // Get a reference to the current DMA descriptor
        dma_descriptor = &_tx_descriptors[_tx_descriptor_list.read];

        // If the descriptor is still owned by the DMA controller, exit
        if (dma_descriptor->ui32CtrlStatus & DES0_TX_CTRL_OWN)
        {
            break;
        }

        // Get the 'hidden' reference to the stack descriptor from the buffer
        stack_descriptor = *((NetworkBufferDescriptor_t **) (((uint8_t *) dma_descriptor->pvBuffer1) - ipBUFFER_PADDING));

        // Release the stack descriptor
        vNetworkBufferReleaseFromISR(stack_descriptor);

        _tx_descriptor_list.read++;

        if (_tx_descriptor_list.read == _tx_descriptor_list.number_descriptors)
        {
            _tx_descriptor_list.read = 0;
        }
    }
}

static void _process_received_packet(void)
{
    NetworkBufferDescriptor_t *new_stack_descriptor;
    NetworkBufferDescriptor_t *cur_stack_descriptor;
    tEMACDMADescriptor *dma_descriptor;
    BaseType_t higher_priority_task_woken = pdFALSE;
    uint32_t i;

    // Go through the list of RX DMA descriptors
    for (i = 0; i < SYSCONFIG_FREERTOS_TCP_RX_DESC_COUNT; i++)
    {
        // Get a reference to the descriptor
        dma_descriptor = &_rx_descriptors[_rx_descriptor_list.write];

        // Make sure the buffer is non-null
        configASSERT(NULL != dma_descriptor->pvBuffer1);

        // If the descriptor is still in use by DMA, stop processing here
        if (DES0_RX_CTRL_OWN == (dma_descriptor->ui32CtrlStatus & DES0_RX_CTRL_OWN))
        {
            break;
        }

        // If there is NOT an error in the frame
        if (0 == (dma_descriptor->ui32CtrlStatus & DES0_RX_STAT_ERR))
        {
            // Get a new empty descriptor
            new_stack_descriptor = pxNetworkBufferGetFromISR(ipTOTAL_ETHERNET_FRAME_SIZE);

            // If a descriptor was provided
            if (NULL != new_stack_descriptor)
            {
                // Get a reference to the current stack descriptor held by the DMA descriptor
                cur_stack_descriptor = *((NetworkBufferDescriptor_t **) (((uint8_t*) dma_descriptor->pvBuffer1) - ipBUFFER_PADDING));

                // Set the length of the buffer on the current descriptor
                cur_stack_descriptor->xDataLength = (dma_descriptor->ui32CtrlStatus & DES0_RX_STAT_FRAME_LENGTH_M) >> DES0_RX_STAT_FRAME_LENGTH_S;

                // Assign the new stack descriptor to the DMA descriptor
                dma_descriptor->pvBuffer1 = new_stack_descriptor->pucEthernetBuffer;

                // Ask the stack if it wants to process the frame.
                if (eProcessBuffer == eConsiderFrameForProcessing(cur_stack_descriptor->pucEthernetBuffer))
                {
                    // Send the stack descriptor to the forwarding thread
                    xQueueSendFromISR(_received_packets_queue, &cur_stack_descriptor, &higher_priority_task_woken);
                }
                else
                {
                    // Free the descriptor
                    vNetworkBufferReleaseFromISR(cur_stack_descriptor);
                }
            } // end if descriptor is available
        } // end if frame had error

        // Set up the DMA descriptor for the next receive transaction
        dma_descriptor->ui32Count = DES1_RX_CTRL_CHAINED | ipTOTAL_ETHERNET_FRAME_SIZE;
        dma_descriptor->ui32CtrlStatus = DES0_RX_CTRL_OWN;

        _rx_descriptor_list.write++;

        if (_rx_descriptor_list.write == _rx_descriptor_list.number_descriptors)
        {
            _rx_descriptor_list.write = 0;
        }
    }

    portEND_SWITCHING_ISR(higher_priority_task_woken);
}

static void _process_phy_interrupt(void)
{
    uint16_t value;
    uint16_t status;
    uint32_t configuration;
    uint32_t mode;
    uint32_t max_frame_size;

    // Read the PHY interrupts status
    value = MAP_EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1);
    status = MAP_EMACPHYRead(EMAC0_BASE, PHY_PHYS_ADDR, EPHY_STS);

    // If status has changed
    if (value & EPHY_MISR1_LINKSTAT)
    {
        // If the link is down
        if (0 == (status & EPHY_STS_LINK))
        {
            // We could inform the stack that the Ethernet link is down, but we'd need to do so
            // from a thread, not an interrupt.
        }
    }

    // If the speed or duplex has changed
    if (value & (EPHY_MISR1_SPEED | EPHY_MISR1_SPEED | EPHY_MISR1_ANC))
    {
        MAP_EMACConfigGet(EMAC0_BASE, &configuration, &mode, &max_frame_size);

        if (status & EPHY_STS_SPEED)
        {
            configuration &= ~EMAC_CONFIG_100MBPS;
        }
        else
        {
            configuration |= EMAC_CONFIG_100MBPS;
        }

        if (status & EPHY_STS_DUPLEX)
        {
            configuration |= EMAC_CONFIG_FULL_DUPLEX;
        }
        else
        {
            configuration &= ~EMAC_CONFIG_FULL_DUPLEX;
        }

        MAP_EMACConfigSet(EMAC0_BASE, configuration, mode, max_frame_size);
    }
}

static void _packet_received_thread(void *parameters)
{
    NetworkBufferDescriptor_t* stack_descriptor;
    IPStackEvent_t event;

    for (;;)
    {
        // Wait for a recevied stack descriptor
        if (pdTRUE == xQueueReceive(_received_packets_queue, &stack_descriptor, portMAX_DELAY))
        {
            // Setup the event
            event.eEventType = eNetworkRxEvent;
            event.pvData = stack_descriptor;

            // Forward the event
            if (pdFALSE == xSendEventStructToIPTask(&event, 0))
            {
                // Release the buffer if an error was encountered
                vReleaseNetworkBufferAndDescriptor(stack_descriptor);

                iptraceETHERNET_RX_EVENT_LOST();
            }
            else
            {
                iptraceNETWORK_INTERFACE_RECEIVE();
            }
        }
    }
}
