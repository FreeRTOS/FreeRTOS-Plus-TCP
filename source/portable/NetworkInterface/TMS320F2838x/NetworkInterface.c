/**
 *       @file: NetworkInterface.c
 *	   @author: Adrien Cardinale <adrien.cardinale@heig-vd.ch>
 *       @date: Dec 01, 2023
 *  @copyright: 
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
 *      @brief:Network Interface driver for the Texas Instruments f28388d.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>

#include "inc/hw_ints.h"
#include "inc/hw_emac.h"
#include "inc/hw_memmap.h"
#include "inc/hw_nvic.h"

#include "driverlib_cm.h"

#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_Routing.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"


#define ETHERNET_NO_OF_RX_PACKETS   2U
#define ETHERNET_MAX_PACKET_LENGTH 1536U
#define NUM_PACKET_DESC_RX_APPLICATION 8

#define EMAC_IF_RX_EVENT     1UL
#define EMAC_IF_TX_EVENT     2UL
#define EMAC_IF_ERR_EVENT    4UL
#define EMAC_IF_ALL_EVENT    ( EMAC_IF_RX_EVENT | EMAC_IF_TX_EVENT | EMAC_IF_ERR_EVENT )

TaskHandle_t xEMACTaskHandle = NULL;

Ethernet_Pkt_Desc *pPktDescGlobal = NULL;

Ethernet_Handle emac_handle;
Ethernet_InitConfig *pInitCfg;

static NetworkInterface_t* pxMyInterface = NULL;

NetworkBufferDescriptor_t* pxGlobalDescriptor = NULL;

uint32_t genericISRCustomcount = 0;
uint32_t genericISRCustomRBUcount = 0;
uint32_t genericISRCustomROVcount = 0;
uint32_t genericISRCustomRIcount = 0;
extern Ethernet_Device Ethernet_device_struct;
__attribute__( ( aligned( 32 ) ) ) uint8_t Ethernet_rxBuffer[ETHERNET_NO_OF_RX_PACKETS *
                          ETHERNET_MAX_PACKET_LENGTH];

extern uint32_t Ethernet_rxInterruptCount;

static void prvEMACDeferredInterruptHandlerTask( void *pvParameters );
static BaseType_t prvf28388d_NetworkInterfaceInitialise(NetworkInterface_t* pxInterface);
static BaseType_t prvf28388d_NetworkInterfaceOutput(NetworkInterface_t* pxInterface, NetworkBufferDescriptor_t* const pxDescriptor, BaseType_t xReleaseAfterSend);
NetworkInterface_t* pxf28388d_FillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t* pxInterface);


#if (ipconfigIPv4_BACKWARD_COMPATIBLE == 1)
    NetworkInterface_t* pxFillInterfaceDescriptor(BaseType_t xEMACIndex, NetworkInterface_t* pxInterface){
        return pxf28388d_FillInterfaceDescriptor(xEMACIndex, pxInterface);
    }
#endif

NetworkInterface_t* pxf28388d_FillInterfaceDescriptor( BaseType_t xEMACIndex, NetworkInterface_t* pxInterface){
    pxInterface->pcName ="f28388d";
    pxInterface->pvArgument = (void*)xEMACIndex;
    pxInterface->pfInitialise = prvf28388d_NetworkInterfaceInitialise;
    pxInterface->pfOutput = prvf28388d_NetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = NULL;

    FreeRTOS_AddNetworkInterface(pxInterface);

    return pxInterface;
}


Ethernet_Pkt_Desc *Ethernet_receivePacketCallbackCustom(Ethernet_Handle handleApplication, Ethernet_Pkt_Desc *pPktDesc){
    BaseType_t higher_priority_task_woken = pdFALSE;
    xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_RX_EVENT, eSetBits, &( higher_priority_task_woken ) );
    portYIELD_FROM_ISR( higher_priority_task_woken );    
    pPktDescGlobal = pPktDesc;
    return Ethernet_getPacketBuffer();
}

void Ethernet_releaseTxPacketBufferCallbackCustom(Ethernet_Handle handleApplication, Ethernet_Pkt_Desc *pPacket){
    BaseType_t higher_priority_task_woken = pdFALSE;
    xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_TX_EVENT, eSetBits, &( higher_priority_task_woken ) );
    portYIELD_FROM_ISR( higher_priority_task_woken );
}


static BaseType_t prvf28388d_NetworkInterfaceInitialise(NetworkInterface_t* pxInterface){
    BaseType_t xReturn;


    Ethernet_InitInterfaceConfig initInterfaceConfig;

    initInterfaceConfig.ssbase = EMAC_SS_BASE;
    initInterfaceConfig.enet_base = EMAC_BASE;
    initInterfaceConfig.phyMode = ETHERNET_SS_PHY_INTF_SEL_MII;

    //
    // Assign SoC specific functions for Enabling,Disabling interrupts
    // and for enabling the Peripheral at system level
    //
    initInterfaceConfig.ptrPlatformInterruptDisable =
                                                    &Platform_disableInterrupt;
    initInterfaceConfig.ptrPlatformInterruptEnable =
                                                     &Platform_enableInterrupt;
    initInterfaceConfig.ptrPlatformPeripheralEnable =
                                                    &Platform_enablePeripheral;
    initInterfaceConfig.ptrPlatformPeripheralReset =
                                                     &Platform_resetPeripheral;

    //
    // Assign the peripheral number at the SoC
    //
    initInterfaceConfig.peripheralNum = SYSCTL_PERIPH_CLK_ENET;

    //
    // Assign the default SoC specific interrupt numbers of Ethernet interrupts
    //
    initInterfaceConfig.interruptNum[0] = INT_EMAC;
    initInterfaceConfig.interruptNum[1] = INT_EMAC_TX0;
    initInterfaceConfig.interruptNum[2] = INT_EMAC_TX1;
    initInterfaceConfig.interruptNum[3] = INT_EMAC_RX0;
    initInterfaceConfig.interruptNum[4] = INT_EMAC_RX1;

    pInitCfg = Ethernet_initInterface(initInterfaceConfig);

    Ethernet_getInitConfig(pInitCfg);

    pInitCfg->dmaMode.InterruptMode = ETHERNET_DMA_MODE_INTM_MODE2;

    //
    // Assign the callbacks for Getting packet buffer when needed
    // Releasing the TxPacketBuffer on Transmit interrupt callbacks
    // Receive packet callback on Receive packet completion interrupt
    //
    pInitCfg->pfcbRxPacket = &Ethernet_receivePacketCallbackCustom;
    pInitCfg->pfcbGetPacket = &Ethernet_getPacketBuffer;
    pInitCfg->pfcbFreePacket = &Ethernet_releaseTxPacketBuffer;

    //
    //Assign the Buffer to be used by the Low level driver for receiving
    //Packets. This should be accessible by the Ethernet DMA
    //
    pInitCfg->rxBuffer = Ethernet_rxBuffer;

    //
    // The Application handle is not used by this application
    // Hence using a dummy value of 1
    //
    Ethernet_getHandle((Ethernet_Handle)1, pInitCfg , &emac_handle);

    //
    //Do global Interrupt Enable
    //
    (void)Interrupt_enableInProcessor();

    //
    //Assign default ISRs
    //
    Interrupt_registerHandler(INT_EMAC_TX0, Ethernet_transmitISR);
    Interrupt_registerHandler(INT_EMAC_RX0, Ethernet_receiveISR);
//    Interrupt_registerHandler(INT_EMAC, Ethernet_genericISR);

    //
    //Change the priority of the interrupt handlers
    //

    Interrupt_setPriority(INT_EMAC_TX0, 15);
    Interrupt_setPriority(INT_EMAC_RX0, 15);
//    Interrupt_setPriority(INT_EMAC, 15);

    //
    //Enable the default interrupt handlers
    //
    Interrupt_enable(INT_EMAC_TX0);
    Interrupt_enable(INT_EMAC_RX0);
//    Interrupt_enable(INT_EMAC);

    if(pInitCfg == NULL){
        xReturn = pdFAIL;
    }else{
        NetworkEndPoint_t* pxEndPoint = FreeRTOS_FirstEndPoint(pxInterface);
        uint8_t MACAddress[ipMAC_ADDRESS_LENGTH_BYTES] = pxEndPoint->xMACAddress.ucBytes;
        uint32_t MACAddressLow = (pxEndPoint->xMACAddress.ucBytes[0]) | (pxEndPoint->xMACAddress.ucBytes[1] << 8) | (pxEndPoint->xMACAddress.ucBytes[2] << 16) | (pxEndPoint->xMACAddress.ucBytes[3]<<24);
        uint32_t MACAddressHigh = (pxEndPoint->xMACAddress.ucBytes[4]) | (pxEndPoint->xMACAddress.ucBytes[5] << 8);
        Ethernet_setMACAddr(EMAC_BASE, 0, MACAddressHigh, MACAddressLow, ETHERNET_CHANNEL_0);
        xReturn = pdPASS;
    }

    if(xEMACTaskHandle == NULL){
        xTaskCreate(prvEMACDeferredInterruptHandlerTask, "EMACInt", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xEMACTaskHandle);
        configASSERT(xEMACTaskHandle);
        pxMyInterface = pxInterface;
    }

    return xReturn;
}

static BaseType_t prvf28388d_NetworkInterfaceOutput(NetworkInterface_t* pxInterface, NetworkBufferDescriptor_t* const pxDescriptor, BaseType_t xReleaseAfterSend){
    pxGlobalDescriptor = pxDescriptor;
    
    Ethernet_Pkt_Desc pktDesc;
    
    pktDesc.bufferLength = pxDescriptor->xDataLength;
    pktDesc.dataOffset = 0;
    pktDesc.dataBuffer = pxDescriptor->pucEthernetBuffer;
    pktDesc.nextPacketDesc = 0;
    pktDesc.flags = ETHERNET_PKT_FLAG_SOP | ETHERNET_PKT_FLAG_EOP | ETHERNET_PKT_FLAG_SA_INS | ETHERNET_PKT_FLAG_SAIC;
    pktDesc.pktChannel = ETHERNET_DMA_CHANNEL_NUM_0;
    pktDesc.pktLength = pxDescriptor->xDataLength;
    pktDesc.validLength = pxDescriptor->xDataLength;
    pktDesc.numPktFrags = 1;

    uint32_t ret = Ethernet_sendPacket(emac_handle, &pktDesc);

    if(ret == 0){
        vReleaseNetworkBufferAndDescriptor(pxDescriptor);
    }

    if(xReleaseAfterSend != pdFALSE){
        pxDescriptor->pucEthernetBuffer = NULL;
        vReleaseNetworkBufferAndDescriptor(pxDescriptor);
    }
}

static void prvEMACDeferredInterruptHandlerTask( void *pvParameters )
{
    NetworkBufferDescriptor_t *pxBufferDescriptor;
    IPStackEvent_t xRxEvent;
    uint32_t ulISREvents = 0U;
    for( ;; )
    {
        xTaskNotifyWait( 0U,
                         EMAC_IF_ALL_EVENT,
                         &( ulISREvents ),
                         portMAX_DELAY );
        if((ulISREvents & EMAC_IF_RX_EVENT) != 0){
            pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( ETHERNET_MAX_PACKET_LENGTH, 0 );

            if(pxBufferDescriptor != NULL){
                memcpy(pxBufferDescriptor->pucEthernetBuffer, pPktDescGlobal->dataBuffer, ETHERNET_MAX_PACKET_LENGTH);
                pxBufferDescriptor->xDataLength = pPktDescGlobal->validLength;

                if(eConsiderFrameForProcessing(pxBufferDescriptor->pucEthernetBuffer) == eProcessBuffer){
                    pxBufferDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint(pxMyInterface, pxBufferDescriptor->pucEthernetBuffer);
                    if(pxBufferDescriptor->pxEndPoint != NULL){
                        xRxEvent.eEventType = eNetworkRxEvent;
                        xRxEvent.pvData = (void*)pxBufferDescriptor;
                        if(xSendEventStructToIPTask(&xRxEvent, 0) == pdFALSE){
                            vReleaseNetworkBufferAndDescriptor(pxBufferDescriptor);
                            iptraceETHERNET_RX_EVENT_LOST();
                        }else{
                            iptraceNETWORK_INTERFACE_RECEIVE();
                        }
                    }else{
                        vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
                    }
                }else{
                    vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
                }
            }else{
                iptraceETHERNET_RX_EVENT_LOST();
            }
        } else if((ulISREvents & EMAC_IF_TX_EVENT) != 0){
            vReleaseNetworkBufferAndDescriptor(pxGlobalDescriptor);
        } else if((ulISREvents & EMAC_IF_ERR_EVENT) != 0){
        }
    }
}
