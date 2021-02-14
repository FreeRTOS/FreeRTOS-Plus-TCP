/*
 * FreeRTOS+TCP V2.3.2
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Driver code:
 * Copyright (C) Nicholas J. Kinar <n.kinar@usask.ca>, Centre for Hydrology, University of Saskatchewan
 *
 * MSP432 Driverlib (C) 2017-2019 Texas Instruments Incorporated <https://www.ti.com/>
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

#include <ti/devices/msp432e4/driverlib/driverlib.h>
#include <ti/devices/msp432e4/driverlib/emac.h>
#include <string.h>
#include "ti_drivers_config.h"
#include "FreeRTOS.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_private.h"
#include "FreeRTOSIPConfigDefaults.h"
#include "NetworkBufferManagement.h"
#include "task.h"
#include "constants.h"
#include "NetworkInterface.h"

/*
NOTES:
This is a driver for the internal MAC of the MSP432E401Y microcontroller from Texas Instruments.

(1) See below for defines that configure and override FreeRTOS defines so that the driver can be used.
(2) The driver provides link up and down detection that also takes into consideration remote faults
and Ethernet cable plug/unplug events during data transmission.
(3) The EMAC hardware is automatically re-started if there is an internal error.
(4) The MAC address can be set from outside of the driver or read from internal flash.
(5) The EMAC hardware can be turned on or off from external tasks.
(6) The EMAC hardware is set to 10BASE-T Half Duplex to ensure that the FreeRTOS+TCP stack does not receive
data too quickly. This is because the 120 MHz processor cannot respond fast enough to ping floods or
other events.  The hardware is thereby set up so that it can respond in a robust fashion.
(7) Supports tickless interrupts.
(8) To turn on and off the EMAC, it is best to do a hard microcontroller reset.

Recommended settings in FreeRTOSIPConfig.h:
#define ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES 1
#define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM  1
#define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM  1
#define ipconfigIP_TASK_STACK_SIZE_WORDS    ( configMINIMAL_STACK_SIZE * 100 )
#define ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS      60
#define configTASK_NOTIFICATION_ARRAY_ENTRIES 2                 // >= 2 so that task notifications can be used in this driver
 // Turn off debug printf features since this might interfere with the network stack processing
#define ipconfigHAS_DEBUG_PRINTF    0
#define ipconfigHAS_PRINTF          0

Recommended settings in FreeRTOSConfig.h:
#define configTICK_RATE_HZ              ( ( TickType_t ) 1000 )
#define configUSE_PREEMPTION            1
#define configUSE_TIME_SLICING          0
#define configCPU_CLOCK_HZ              ( ( unsigned long ) 120000000 )
#define configMINIMAL_STACK_SIZE        ( ( unsigned short ) 256 )
#define configTOTAL_HEAP_SIZE           ( ( size_t ) ( 0x28000 ) )  // IMPORTANT: adjust per project requirements
#define ipconfigTCP_WIN_SEG_COUNT       240

REFERENCES:
[1] FreeRTOS Forum
[2] Texas Instruments Driverlib code examples
*/

//--------------------------------------------------------------------
// Defines
#define RTOS_NET_UP_DOWN_TASK_NAME "NetUpDown"
#define RTOS_NET_RX_TASK_NAME "NetRX"
#define RTOS_NET_TX_TASK_NAME "NetTX"
#define RTOS_NET_CHECK_TASK_NAME "NetChk"
#define RTOS_NET_UP_DOWN_TASK_SIZE  configMINIMAL_STACK_SIZE
#define RTOS_NET_CHECK_TASK_SIZE    configMINIMAL_STACK_SIZE
#define RTOS_RX_POLL_MAC_TASK_SIZE 3*configMINIMAL_STACK_SIZE
#define RTOS_TX_POLL_MAC_TASK_SIZE 3*configMINIMAL_STACK_SIZE
#define NUM_TX_DESCRIPTORS 8
#define NUM_RX_DESCRIPTORS 8

#define ETH_UP_DELAY_MS             1000
#define ETH_DOWN_DELAY_MS           1000
#define ETH_MAX_TIMEOUT_CYCLES      12000000
#define ETH_STARTUP_TIMEOUT         ETH_MAX_TIMEOUT_CYCLES

#define ETH_RX_QUEUE_LEN  NUM_TX_DESCRIPTORS
#define ETH_TX_QUEUE_LEN  NUM_RX_DESCRIPTORS

// DMA descriptors
tEMACDMADescriptor g_psRxDescriptor[NUM_TX_DESCRIPTORS];
tEMACDMADescriptor g_psTxDescriptor[NUM_RX_DESCRIPTORS];
uint32_t g_ui32RxDescIndex;
uint32_t g_ui32TxDescIndex;

#define ETH_MAX_BUFFER_SIZE 1526
#define ETH_RX_BUFFER_SIZE  ETH_MAX_BUFFER_SIZE
#define ETH_TX_BUFFER_SIZE  ETH_MAX_BUFFER_SIZE
uint8_t g_ppui8RxBuffer[NUM_RX_DESCRIPTORS][ETH_RX_BUFFER_SIZE];

// Task handles
TaskHandle_t xTaskToNotifyEthernetRX = NULL;
TaskHandle_t xTaskToNotifyEthernetTX = NULL;
TaskHandle_t xHandleCheckLinkUpOrDown = NULL;
TaskHandle_t xHandleCheckNet = NULL;
BaseType_t xHigherPriorityTaskWokenRX = pdFALSE;
BaseType_t xHigherPriorityTaskWokenTX = pdFALSE;
BaseType_t xHigherPriorityTaskWokenCheck = pdFALSE;

// Queue handles
QueueHandle_t xQueueRX;
QueueHandle_t xQueueTX;

// TX Queue positions
#define TX_QUEPOS_FIRST_EVENT   0
#define TX_QUEPOS_SECOND_EVENT  1

// MAC address
uint8_t pui8MACAddr[ipMAC_ADDRESS_LENGTH_BYTES ];

// State variable that indicates whether the network is up or down
bool networkUP = false;

// Minimum packet length is required to ensure that all of the bytes are transmitted
// even when there are issues with the network (i.e. a network cable pulled out during TX or RX)
#define ETHERNET_MIN_PACKET_BYTES  60

// Ensure that the RTOS settings work well for this driver
#if configTASK_NOTIFICATION_ARRAY_ENTRIES < 2
    #undef configTASK_NOTIFICATION_ARRAY_ENTRIES
    #define configTASK_NOTIFICATION_ARRAY_ENTRIES 2
#endif
#ifndef ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM  1
#endif
#ifndef ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM  1
#endif
#ifdef ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
    #undef ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM 1
#endif
#ifdef ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
    #undef ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM 1
#endif
#ifndef ipconfigETHERNET_MINIMUM_PACKET_BYTES
    #define ipconfigETHERNET_MINIMUM_PACKET_BYTES   ETHERNET_MIN_PACKET_BYTES
#endif
#ifdef ipconfigETHERNET_MINIMUM_PACKET_BYTES
    #undef ipconfigETHERNET_MINIMUM_PACKET_BYTES
    #define ipconfigETHERNET_MINIMUM_PACKET_BYTES   ETHERNET_MIN_PACKET_BYTES
#endif
#if ipconfigHAS_DEBUG_PRINTF == 1
    #warning The network interface may not work properly if ipconfigHAS_DEBUG_PRINTF 1.  Please set ipconfigHAS_DEBUG_PRINTF 0 for production use.
#endif
#ifndef __MSP432E401Y__
    #define __MSP432E401Y__  // required to use driverlib
#endif

static bool loadMACInternal();
static bool setupEMAC();
static void offEMAC();
static void initDescriptors(uint32_t ui32Base);
static uint32_t packetTransmit(uint8_t *pui8Buf, uint32_t i32BufLen);
static void ethernetIntHandler(void);
static uint32_t processReceivedPacket(void);
static void applicationProcessFrameRX(uint32_t i32FrameLen, uint8_t *pui8Buf, uint32_t index );
static void checkLinkUpOrDownTask( void *pvParameters );
static void prvEMACDeferredInterruptHandlerTask( void *pvParameters );
static bool isEMACLinkUp();
static void DMAFreeDescriptorRX(uint32_t indx);
static void prvEMACDeferredInterfaceOutput( void *pvParameters );
static void prvChkNetworkState( void *pvParameters );
static void vSetNetworkInterfaceConfig(const struct InternalNetworkInterfaceMSP432EConfig config);

// EMAC interrupts
#define EMAC_INTERRUPTS EMAC_INT_RECEIVE | EMAC_INT_TRANSMIT | EMAC_INT_BUS_ERROR | EMAC_INT_TX_STOPPED | EMAC_INT_RX_STOPPED

// RX data input buffer
struct NetworkInterfaceDataIn
{
    uint8_t *buff;          // buffer to the data
    uint32_t buff_siz;      // buffer size
    uint32_t indx;          // index of buffer in DMA descriptor (if required)
}; // end

// TX data output buffer
struct NetworkInterfaceDataOut
{
    NetworkBufferDescriptor_t *pxDescriptor;
    BaseType_t xReleaseAfterSend;
}; // end

static struct InternalNetworkInterfaceMSP432EConfig configLocal;
static bool hasBeenSetup = false;


//--------------------------------------------------------------------
bool loadMACInternal()
{
    uint32_t ui32User0, ui32User1;
    // Read the MAC address from internal flash. Bit[23:0] are stored in user register0, and Bit[47:24] are stored in user register1.
    // The MAC address can be loaded from an external IC or can be loaded from the internal registers if the registers are not zero.
    // The evaluation kit hardware uses reading from internal flash variables but this can also be used for production as well
    // if the internal flash is programmed on the assembly line.
    FlashUserGet(&ui32User0, &ui32User1);
    if((ui32User0 == 0xffffffff) || (ui32User1 == 0xffffffff))
    {
        return false;
    }
    configLocal.MACAddr[0] = ((ui32User0 >> 0) & 0xff);
    configLocal.MACAddr[1] = ((ui32User0 >> 8) & 0xff);
    configLocal.MACAddr[2] = ((ui32User0 >> 16) & 0xff);
    configLocal.MACAddr[3] = ((ui32User1 >> 0) & 0xff);
    configLocal.MACAddr[4] = ((ui32User1 >> 8) & 0xff);
    configLocal.MACAddr[5] = ((ui32User1 >> 16) & 0xff);
    return true;
} // end


// This function sets up the EMAC. Not to be called directly from outside of this file.
bool setupEMAC()
{
    uint32_t ui32Loop;
    bool rv;

    if (xTaskGetSchedulerState() == taskSCHEDULER_RUNNING)
    {
        taskENTER_CRITICAL();
    }

    if(configLocal.setMACAddrInternal == true)
    {
        rv = loadMACInternal();
        if (rv==false) return false;
    }

    // enable and reset the internal MAC
    SysCtlPeripheralPowerOn(SYSCTL_PERIPH_EMAC0);
    SysCtlPeripheralPowerOn(SYSCTL_PERIPH_EPHY0);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_EMAC0);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_EPHY0);
    SysCtlPeripheralReset(SYSCTL_PERIPH_EMAC0);
    SysCtlPeripheralReset(SYSCTL_PERIPH_EPHY0);

    while(!SysCtlPeripheralReady(SYSCTL_PERIPH_EMAC0))
    {
    }

    // configure the internal PHY
    EMACPHYConfigSet(EMAC0_BASE,
                     (EMAC_PHY_TYPE_INTERNAL |
                      EMAC_PHY_INT_MDIX_EN |
                      EMAC_PHY_AN_10B_T_HALF_DUPLEX));

    // reset the MAC to latch the configuration
    EMACReset(EMAC0_BASE);

    // wait
    SysCtlDelay(ETH_STARTUP_TIMEOUT);

    // init the EMAC
    EMACInit(EMAC0_BASE, configCPU_CLOCK_HZ,
             EMAC_BCONFIG_MIXED_BURST | EMAC_BCONFIG_PRIORITY_FIXED, 4, 4,
               0);

    /*
        Since the checksum is computed in the hardware using EMAC_CONFIG_CHECKSUM_OFFLOAD,
        there is also a need to turn on defines in FreeRTOS+TCP as well.

        #define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM  1
        #define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM  1
     */
    EMACConfigSet(EMAC0_BASE,
                  (EMAC_CONFIG_FULL_DUPLEX |
                   EMAC_CONFIG_CHECKSUM_OFFLOAD |
                   EMAC_CONFIG_IF_GAP_96BITS |
                   EMAC_CONFIG_USE_MACADDR0 |
                   EMAC_CONFIG_BO_LIMIT_1024),
                  (EMAC_MODE_RX_STORE_FORWARD |  EMAC_MODE_TX_STORE_FORWARD
                          ), ETH_MAX_BUFFER_SIZE);

    // DMA descriptors init
    initDescriptors(EMAC0_BASE);

    // program MAC address from the cached address
    EMACAddrSet(EMAC0_BASE, 0, configLocal.MACAddr);

    // Set address filtering
    EMACAddrFilterSet(EMAC0_BASE, 0, EMAC_FILTER_ADDR_ENABLE | EMAC_FILTER_SOURCE_ADDR);

    // Set MAC filtering options
    EMACFrameFilterSet(EMAC0_BASE, EMAC_FRMFILTER_SADDR | EMAC_FRMFILTER_PASS_NO_CTRL);

    // indicate that the receive descriptors are available to the DMA to start the receive processing
    for(ui32Loop = 0; ui32Loop < NUM_RX_DESCRIPTORS; ui32Loop++)
    {
          g_psRxDescriptor[ui32Loop].ui32CtrlStatus |= DES0_RX_CTRL_OWN;
    }

    // Enable the Ethernet MAC transmitter and receiver
    EMACTxEnable(EMAC0_BASE);
    EMACRxEnable(EMAC0_BASE);

    // Enable the Ethernet interrupt
    IntPrioritySet(INT_EMAC0, 0x20);  // (0x01 << 5) to set the priority into the last three bits for Cortex M4F

    // register the interrupt handler for the Ethernet MAC
    EMACIntRegister(EMAC0_BASE, ethernetIntHandler);

    // enable the interrupts for the EMAC
    EMACIntClear(EMAC0_BASE, EMACIntStatus(EMAC0_BASE, false));
    IntEnable(INT_EMAC0);
    EMACIntEnable(EMAC0_BASE, EMAC_INTERRUPTS);

    // inject a delay here to ensure that the EMAC is functional by the time that the other code is run
    SysCtlDelay(ETH_STARTUP_TIMEOUT);

    // check to see if the link is up and indicate if the link is up
    if(isEMACLinkUp())
    {
        networkUP = true;
    }

    if (xTaskGetSchedulerState() == taskSCHEDULER_RUNNING)
    {
        taskEXIT_CRITICAL();
    }

    return true;
} // end


// This function only turns off the Ethernet EMAC.  This function does not turn off any
// of the processing tasks and therefore should not be called directly from external tasks.
void offEMAC()
{
    uint32_t status, cnt;
    if (xTaskGetSchedulerState() == taskSCHEDULER_RUNNING)
    {
        taskENTER_CRITICAL();
    }
    networkUP = false;

    cnt = 0;
    status = EMACStatusGet(EMAC0_BASE);
    while(status)
    {
        status = EMACStatusGet(EMAC0_BASE);
        cnt++;
        if(cnt == ETH_STARTUP_TIMEOUT)
        {
            if (xTaskGetSchedulerState() == taskSCHEDULER_RUNNING)
            {
                   taskEXIT_CRITICAL();
            }
            return;
        }
    }
    IntDisable(INT_EMAC0);
    SysCtlPeripheralDisable(SYSCTL_PERIPH_EMAC0);
    SysCtlPeripheralDisable(SYSCTL_PERIPH_EPHY0);
    SysCtlPeripheralPowerOff(SYSCTL_PERIPH_EMAC0);
    SysCtlPeripheralPowerOff(SYSCTL_PERIPH_EPHY0);
    if (xTaskGetSchedulerState() == taskSCHEDULER_RUNNING)
    {
        taskEXIT_CRITICAL();
    }
} // end


// Interrupt handler
void ethernetIntHandler(void)
{
    uint32_t ui32Temp;
    ui32Temp = EMACIntStatus(EMAC0_BASE, true);

    if(ui32Temp & EMAC_INT_RECEIVE)
    {
        // RX
        processReceivedPacket();
    }
    else if (ui32Temp & EMAC_INT_TRANSMIT)
    {
        // TX
        vTaskNotifyGiveIndexedFromISR( xTaskToNotifyEthernetTX,  TX_QUEPOS_SECOND_EVENT, &xHigherPriorityTaskWokenTX);
        portYIELD_FROM_ISR( xHigherPriorityTaskWokenTX );
    }
    else
    {
        // Anything else other than receive or transmit is treated as an error
        // and a task is therefore used to reset the entire EMAC to ensure that the system remains functional.
        vTaskNotifyGiveFromISR( xHandleCheckNet, &xHigherPriorityTaskWokenCheck);
        portYIELD_FROM_ISR(xHigherPriorityTaskWokenCheck );
     }

    // clear the interrupt
    EMACIntClear(EMAC0_BASE, ui32Temp);
    // as per Application Note SLAA739–June 2017
#if configUSE_TICKLESS_IDLE   == 1
    SCB->SCR &= ~SCB_SCR_SLEEPONEXIT_Msk;   // Disable SLEEPONEXIT
    __DSB();                                // Ensures SLEEPONEXIT is set
#endif

} // end


// Init the DMA descriptors
void initDescriptors(uint32_t ui32Base)
{
    uint32_t ui32Loop;

    for(ui32Loop = 0; ui32Loop < NUM_TX_DESCRIPTORS; ui32Loop++)
    {
        g_psTxDescriptor[ui32Loop].ui32Count = DES1_TX_CTRL_SADDR_INSERT;
        g_psTxDescriptor[ui32Loop].DES3.pLink =
            (ui32Loop == (NUM_TX_DESCRIPTORS - 1)) ?
            g_psTxDescriptor : &g_psTxDescriptor[ui32Loop + 1];
        g_psTxDescriptor[ui32Loop].ui32CtrlStatus =
            (DES0_TX_CTRL_LAST_SEG | DES0_TX_CTRL_FIRST_SEG |
             DES0_TX_CTRL_INTERRUPT | DES0_TX_CTRL_CHAINED |
             DES0_TX_CTRL_IP_ALL_CKHSUMS);
    }

    for(ui32Loop = 0; ui32Loop < NUM_RX_DESCRIPTORS; ui32Loop++)
    {
        g_psRxDescriptor[ui32Loop].ui32CtrlStatus = 0;
        g_psRxDescriptor[ui32Loop].ui32Count =
            (DES1_RX_CTRL_CHAINED |
             (ETH_RX_BUFFER_SIZE << DES1_RX_CTRL_BUFF1_SIZE_S));
        g_psRxDescriptor[ui32Loop].pvBuffer1 = g_ppui8RxBuffer[ui32Loop];
        g_psRxDescriptor[ui32Loop].DES3.pLink =
            (ui32Loop == (NUM_RX_DESCRIPTORS - 1)) ?
            g_psRxDescriptor : &g_psRxDescriptor[ui32Loop + 1];
    }

    EMACRxDMADescriptorListSet(ui32Base, g_psRxDescriptor);
    EMACTxDMADescriptorListSet(ui32Base, g_psTxDescriptor);

    g_ui32RxDescIndex = 0;
    g_ui32TxDescIndex = NUM_TX_DESCRIPTORS - 1;

} // end


// Transmit a packet - call this function from the network stack
// pui8Buf = the buffer
// i32BufLen = length of the buffer
uint32_t packetTransmit(uint8_t *pui8Buf, uint32_t i32BufLen)
{
    uint8_t bufferTX[ETH_TX_BUFFER_SIZE];

    g_ui32TxDescIndex++;
    if(g_ui32TxDescIndex == NUM_TX_DESCRIPTORS)
    {
        g_ui32TxDescIndex = 0;
    }

    // The copy needs to be done here since directly assigning a pointer does not seem to work
    // and causes the transmitter to stop.  Some testing indicates that that this can be quicker than
    // simply assigning the pointer for smaller packets.
    memcpy(bufferTX, pui8Buf, i32BufLen);

    g_psTxDescriptor[g_ui32TxDescIndex].ui32Count = i32BufLen;
    g_psTxDescriptor[g_ui32TxDescIndex].pvBuffer1 = bufferTX;
    g_psTxDescriptor[g_ui32TxDescIndex].ui32CtrlStatus =
        (DES0_TX_CTRL_LAST_SEG | DES0_TX_CTRL_FIRST_SEG |
         DES0_TX_CTRL_INTERRUPT | DES0_TX_CTRL_IP_ALL_CKHSUMS |
         DES0_TX_CTRL_CHAINED | DES0_TX_CTRL_OWN);

    EMACTxDMAPollDemand(EMAC0_BASE);
    return(i32BufLen);
} // end


// Function to process the received packet
uint32_t processReceivedPacket(void)
{
    uint32_t i32FrameLen;
    i32FrameLen = 0;

    if(!(g_psRxDescriptor[g_ui32RxDescIndex].ui32CtrlStatus & DES0_RX_CTRL_OWN))
    {
        // Does it have a valid frame?
        if(!(g_psRxDescriptor[g_ui32RxDescIndex].ui32CtrlStatus &
             DES0_RX_STAT_ERR))
        {
            if(g_psRxDescriptor[g_ui32RxDescIndex].ui32CtrlStatus &
               DES0_RX_STAT_LAST_DESC)
            {
                // get the frame length
                i32FrameLen =
                    ((g_psRxDescriptor[g_ui32RxDescIndex].ui32CtrlStatus &
                      DES0_RX_STAT_FRAME_LENGTH_M) >>
                     DES0_RX_STAT_FRAME_LENGTH_S);

                // call the function that sends the data to the task
                applicationProcessFrameRX(i32FrameLen,
                               g_psRxDescriptor[g_ui32RxDescIndex].pvBuffer1, g_ui32RxDescIndex);
            }
        }

        // Move on to the next RX packet
        g_ui32RxDescIndex++;
        if(g_ui32RxDescIndex == NUM_RX_DESCRIPTORS)
        {
            g_ui32RxDescIndex = 0;
        }
    } // end if

    // return the frame length
    return i32FrameLen;
} // end


// This function passes the framelength and the RX buffer into the FreeRTOS task.
// The function is called from the ISR and therefore must use portYIELD_FROM_ISR()
void applicationProcessFrameRX(uint32_t i32FrameLen, uint8_t *pui8Buf, uint32_t index )
{
    BaseType_t rv;
    struct NetworkInterfaceDataIn NIDataIn;

    NIDataIn.buff = pui8Buf;
    NIDataIn.buff_siz = i32FrameLen;
    NIDataIn.indx = index;

    // send the data into the queue
    rv = xQueueSendFromISR(xQueueRX, &NIDataIn, &xHigherPriorityTaskWokenRX);
    if (rv == pdTRUE)
    {
        vTaskNotifyGiveFromISR( xTaskToNotifyEthernetRX, &xHigherPriorityTaskWokenRX);
        portYIELD_FROM_ISR( xHigherPriorityTaskWokenRX );
    } // end
    else
    {
        DMAFreeDescriptorRX(index);
    }
} // end


// Function to free the RX descriptor
void DMAFreeDescriptorRX(uint32_t indx)
{
    g_psRxDescriptor[indx].ui32CtrlStatus = DES0_RX_CTRL_OWN;
} // end


//-------------------------------------------------------------
// FREERTOS+TCP FUNCTIONS
//-------------------------------------------------------------

// Call this function to populate the driver defaults struct with defaults
void vGetInternalNetworkInterfaceMSP432EConfigDefaults(struct InternalNetworkInterfaceMSP432EConfig *config)
{
    uint32_t k;
    config->turnOnEMAC = true;
    config->setMACAddrInternal = false;
    for(k = 0; k < ipMAC_ADDRESS_LENGTH_BYTES; k++)
    {
        config->MACAddr[k] = 0xFF;
    }
} // end


void vSetNetworkInterfaceConfig(const struct InternalNetworkInterfaceMSP432EConfig config)
{
    configLocal = config;
} // end


// Call this function to setup the network
bool vPublicSetupEMACNetwork(const struct InternalNetworkInterfaceMSP432EConfig config)
{
    bool rv;
    rv = false;
    BaseType_t tv;

    // setup the MAC address and turn on the EMAC if required
    vSetNetworkInterfaceConfig(config);
    if( config.turnOnEMAC){ rv = setupEMAC(); }
    if(rv == false) return false;

    // ensure that the code can only be run once to create the tasks
    if(hasBeenSetup == true)
    {
        return true;
    }

    // create the queues
    xQueueRX = xQueueCreate(ETH_RX_QUEUE_LEN, sizeof(struct NetworkInterfaceDataIn));
    if(xQueueRX == NULL) return false;
    xQueueTX = xQueueCreate(ETH_TX_QUEUE_LEN, sizeof(struct NetworkInterfaceDataOut));
    if (xQueueTX == NULL) return false;

    // RX task
    tv = xTaskCreate( prvEMACDeferredInterruptHandlerTask,
                 RTOS_NET_RX_TASK_NAME,
                 RTOS_RX_POLL_MAC_TASK_SIZE,
                 NULL,
                 configMAX_PRIORITIES-1,
                 &xTaskToNotifyEthernetRX );
    if (tv != pdPASS) return false;

    // TX task
    tv = xTaskCreate( prvEMACDeferredInterfaceOutput,
                 RTOS_NET_TX_TASK_NAME,
                 RTOS_TX_POLL_MAC_TASK_SIZE,
                 NULL,
                 configMAX_PRIORITIES-1,
                 &xTaskToNotifyEthernetTX );
    if (tv != pdPASS) return false;

    // Link Up/Down task
    tv = xTaskCreate( checkLinkUpOrDownTask,
                 RTOS_NET_UP_DOWN_TASK_NAME,
                 RTOS_NET_CHECK_TASK_SIZE,
                 NULL,
                 tskIDLE_PRIORITY,
                 &xHandleCheckLinkUpOrDown );
    if (tv != pdPASS) return false;

    // Task to check the network state and reset things if something went wrong
    tv = xTaskCreate (prvChkNetworkState,
                 RTOS_NET_CHECK_TASK_NAME,
                 RTOS_NET_CHECK_TASK_SIZE,
                 NULL,
                 tskIDLE_PRIORITY,
                 &xHandleCheckNet);
    if (tv != pdPASS) return false;

    // latch the setup state
    hasBeenSetup = true;

    // the setup has succeeded
    return true;
} // end


// Function to check the network state and then reset things accordingly if an interrupt has occurred
// and this indicates that something is wrong with the network.
void prvChkNetworkState( void *pvParameters )
{
    for(;;)
    {
        ulTaskNotifyTake( pdTRUE, portMAX_DELAY );
        vPublicTurnOnEMAC();
        vTaskDelay(pdMS_TO_TICKS(ETH_DOWN_DELAY_MS));
    }
} // end


// FreeRTOS task that handles the RX interrupt using task handle xTaskToNotifyEthernetRX
void prvEMACDeferredInterruptHandlerTask( void *pvParameters )
{
    NetworkBufferDescriptor_t *pxDescriptor = NULL;
    IPStackEvent_t xRxEvent;
    struct NetworkInterfaceDataIn NIDataReceived;
    uint32_t xBytesReceived;

    for(;;)
    {
        ulTaskNotifyTake( pdTRUE, portMAX_DELAY );
        xQueueReceive (xQueueRX, &NIDataReceived, 0);
        if( eConsiderFrameForProcessing( NIDataReceived.buff ) == eProcessBuffer )
        {
            xBytesReceived = NIDataReceived.buff_siz - ipSIZE_OF_ETH_CRC_BYTES;  // do not include the CRC bytes in the received size
            pxDescriptor = pxGetNetworkBufferWithDescriptor(xBytesReceived, 0);
            if (pxDescriptor != NULL)
            {
                memcpy(pxDescriptor->pucEthernetBuffer, NIDataReceived.buff, NIDataReceived.buff_siz);
                pxDescriptor->xDataLength = xBytesReceived;
                xRxEvent.eEventType = eNetworkRxEvent;
                xRxEvent.pvData = ( void * ) pxDescriptor;
                if( xSendEventStructToIPTask( &xRxEvent, 0 ) == pdTRUE )
                {
                    // The buffer does not need to be released here since this will be done internally by the network stack
                    iptraceNETWORK_INTERFACE_RECEIVE();
                }
                else
                {
                    // The buffer needs to be released since we cannot send to the network stack
                    vReleaseNetworkBufferAndDescriptor( pxDescriptor );
                    iptraceETHERNET_RX_EVENT_LOST();
                }
            }
        }
        // Release the DMA descriptor at a specific index
        taskENTER_CRITICAL();
        DMAFreeDescriptorRX(NIDataReceived.indx);
        taskEXIT_CRITICAL();
    } // end for
} // end


// Network initialization is already done outside of this function, so this function will only
// report if the network is initialized by returning a flag. Called directly by FreeRTOS.
BaseType_t xNetworkInterfaceInitialise( void )
{
   if(networkUP == true)
   {
       vTaskDelay(pdMS_TO_TICKS(ETH_UP_DELAY_MS ));
       return pdTRUE;
   }
   return pdFALSE;
} // end


// Task to output the data to the network interface. This allows the network stack to continue
// processing while the data is able to be sent.
void prvEMACDeferredInterfaceOutput( void *pvParameters )
{
    struct NetworkInterfaceDataOut NIDataOutput;
    for (;;)
    {
        ulTaskNotifyTakeIndexed(TX_QUEPOS_FIRST_EVENT, pdTRUE, portMAX_DELAY );
        xQueueReceive (xQueueTX, &NIDataOutput, 0);

        // For ICMP packets, the checksum must be zero if the network hardware computes the checksum or the buffer will not be properly sent
        // For this driver it is required that ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 1
        ProtocolPacket_t * pxPacket;
        pxPacket = ( ProtocolPacket_t * ) ( NIDataOutput.pxDescriptor->pucEthernetBuffer );
        if( pxPacket->xICMPPacket.xIPHeader.ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP )
        {
            pxPacket->xICMPPacket.xICMPHeader.usChecksum = ( uint16_t ) 0u;
        }
        taskENTER_CRITICAL();
        packetTransmit(NIDataOutput.pxDescriptor->pucEthernetBuffer, (uint32_t)NIDataOutput.pxDescriptor->xDataLength);
        taskEXIT_CRITICAL();

        // wait until transmit
        ulTaskNotifyTakeIndexed(TX_QUEPOS_SECOND_EVENT, pdTRUE, portMAX_DELAY );
        iptraceNETWORK_INTERFACE_TRANSMIT();

         if(NIDataOutput.xReleaseAfterSend)
        {
            vReleaseNetworkBufferAndDescriptor(NIDataOutput.pxDescriptor);
        }
    } // end
} // end


// Function to output packets to the network.
// Called directly by FreeRTOS. This function should not block and therefore passes
// all output data to a queue.  If the function blocks the network stack can become unresponsive
// so all of the output work is thereby done by another task.
BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor,
                                    BaseType_t xReleaseAfterSend )
{
    struct NetworkInterfaceDataOut NIDataOutput;
    BaseType_t txResp;

    NIDataOutput.pxDescriptor = pxDescriptor;
    NIDataOutput.xReleaseAfterSend  = xReleaseAfterSend;
    txResp = xQueueSend(xQueueTX, &NIDataOutput, 0);
    if (txResp == pdTRUE)
    {
        xTaskNotifyGiveIndexed( xTaskToNotifyEthernetTX, 0);
        return pdTRUE;
    }
    return pdFALSE;
} // end


//-----------------------------------------------------------------------------------------------------
// Network interface UP or DOWN tasks and associated functions
//-----------------------------------------------------------------------------------------------------

// Function to check and see if the network is up or down by polling a register in the Ethernet driver.
// Apparently there is no other way to do this other than polling.  The register is checked for link status,
// but also for remote faults and this takes into consideration a pulled Ethernet cable during RX and TX.
bool isEMACLinkUp()
{
    uint8_t ui8PHYAddr = 0;  // refers to the internal PHY
    uint16_t check;
    check = EMACPHYRead(EMAC0_BASE, ui8PHYAddr, EPHY_BMSR);
    if( ((check & EPHY_BMSR_LINKSTAT) == 0) || (check & EPHY_BMSR_RFAULT) )
    {
        return false;   // link is not up
    }
    return true;        // link is up
} // end


// A task to check and see if the link is up or down by polling an EMAC register.
void checkLinkUpOrDownTask( void *pvParameters )
{
   bool check;
   check = false;

   for(;;)
   {
       check = isEMACLinkUp();
       if(check==true && networkUP==false)
       {
           networkUP = true;
       }
       else if (networkUP==true && check==false)
       {
           // FreeRTOS will poll xNetworkInterfaceInitialise() to check if the network is up.
           // After FreeRTOS_NetworkDown() is called, so there is no corresponding FreeRTOS_NetworkUp() function...
           networkUP = false;
           FreeRTOS_NetworkDown();
       } // end
   } // end for
} // end


// Call this network function to physically turn on the EMAC from an internal task.
bool vPublicTurnOnEMAC()
{
    if(hasBeenSetup == false) return false;
    setupEMAC();   // turn on the physical hardware
    if (xTaskGetSchedulerState() == taskSCHEDULER_RUNNING)  // required check
    {
        FreeRTOS_NetworkDown();
        vTaskResume( xHandleCheckLinkUpOrDown );
        vTaskResume( xHandleCheckNet );
        vTaskResume( xTaskToNotifyEthernetRX);
        vTaskResume( xTaskToNotifyEthernetTX);
    }
    return true;
} // end


// Call this function to physically turn off the EMAC from an external task.
// It is recommended to check the network stack for open sockets before calling this task,
// and only call the task after all sockets are closed and there are no connected clients.
// In an operational sense, the best way to turn off the EMAC is to do a hard reset.
bool vPublicTurnOffEMAC()
{
    if(hasBeenSetup == false) return false;  // make sure that the MAC has been setup
     if (xTaskGetSchedulerState() == taskSCHEDULER_RUNNING)
     {
         vTaskSuspend( xHandleCheckLinkUpOrDown );
         vTaskSuspend( xHandleCheckNet );
         vTaskSuspend (xTaskToNotifyEthernetRX);
         vTaskSuspend (xTaskToNotifyEthernetTX);
     }
     networkUP = false;
     if (xTaskGetSchedulerState() == taskSCHEDULER_RUNNING)
     {
         FreeRTOS_NetworkDown();                        // Signal to FreeRTOS that the network is down
         vTaskDelay(pdMS_TO_TICKS(ETH_DOWN_DELAY_MS));  // Wait until FreeRTOS has finished processing
     }
     offEMAC();  // Turn off the physical hardware
     return true;
} // end


// Call this function to obtain the MAC address used by the driver
void vPublicGetMACAddr(uint8_t pui8MACAddrGet[ ipMAC_ADDRESS_LENGTH_BYTES])
{
    memcpy(pui8MACAddrGet, configLocal.MACAddr, ipMAC_ADDRESS_LENGTH_BYTES);
} // end


//-----------------------------------------------------------------------------------------------------
// For BufferAllocation_1.c (see the FreeRTOS documentation for further details and examples)
//-----------------------------------------------------------------------------------------------------
#define BUFFER_SIZE_ALLOC1 ( ipTOTAL_ETHERNET_FRAME_SIZE + ipBUFFER_PADDING )
#define BUFFER_SIZE_ALLOC1_ROUNDED_UP ( ( BUFFER_SIZE_ALLOC1 + 7 ) & ~0x07UL )
static uint8_t ucBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ BUFFER_SIZE_ALLOC1_ROUNDED_UP ];
void vNetworkInterfaceAllocateRAMToBuffers(
    NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
BaseType_t x;

    for( x = 0; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++ )
    {
        /* pucEthernetBuffer is set to point ipBUFFER_PADDING bytes in from the
        beginning of the allocated buffer. */
        pxNetworkBuffers[ x ].pucEthernetBuffer = &( ucBuffers[ x ][ ipBUFFER_PADDING ] );

        /* The following line is also required, but will not be required in
        future versions. */
        *( ( uint32_t * ) &ucBuffers[ x ][ 0 ] ) = ( uint32_t ) &( pxNetworkBuffers[ x ] );
    }
} // end
//-----------------------------------------------------------------------------------------------------





