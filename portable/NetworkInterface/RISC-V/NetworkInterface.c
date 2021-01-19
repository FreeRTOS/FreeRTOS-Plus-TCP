/*
FreeRTOS+TCP V2.0.11
Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

 http://aws.amazon.com/freertos
 http://www.FreeRTOS.org
*/

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

#include "FreeRTOS_IP.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Sockets.h"
#include "NetworkBufferManagement.h"

/* FreeRTOS+TCP includes. */
#include "NetworkInterface.h"

/* Board specific includes */
#include "riscv_hal_eth.h"

// Netboot needs this
BaseType_t xNetworkInterfaceDestroy( void );

BaseType_t xNetworkInterfaceInitialise( void )
{
	FreeRTOS_debug_printf( ("xNetworkInterfaceInitialise\r\n") );

	// Init DMA
	configASSERT(DmaSetup(&AxiDmaInstance, XPAR_AXIDMA_0_DEVICE_ID) == 0);

	// Init Ethernet
	configASSERT(PhySetup(&AxiEthernetInstance, XPAR_AXIETHERNET_0_DEVICE_ID) == 0);

	// Connect to PLIC
	configASSERT(AxiEthernetSetupIntrSystem(&Plic, &AxiEthernetInstance, &AxiDmaInstance, PLIC_SOURCE_ETH, XPAR_AXIETHERNET_0_DMA_RX_INTR,
						XPAR_AXIETHERNET_0_DMA_TX_INTR) == 0);
	
	uint16_t Speed;
	configASSERT( XAxiEthernet_GetSgmiiStatus(&AxiEthernetInstance, &Speed) == 0);

	/*
	 * Start the Axi Ethernet and enable its ERROR interrupts
	 */
	XAxiEthernet_Start(&AxiEthernetInstance);
	XAxiEthernet_IntEnable(&AxiEthernetInstance, XAE_INT_RECV_ERROR_MASK);

	vTaskDelay(pdMS_TO_TICKS(AXIETHERNET_PHY_DELAY_SEC*1000));
	return pdPASS;
}
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceDestroy( void )
{
	FreeRTOS_debug_printf( ("xNetworkInterfaceDestroy\r\n") );
	XAxiEthernet_IntDisable(&AxiEthernetInstance, XAE_INT_RECV_ERROR_MASK);
	AxiEthernetDisableIntrSystem(&Plic, PLIC_SOURCE_ETH, XPAR_AXIETHERNET_0_DMA_RX_INTR, XPAR_AXIETHERNET_0_DMA_TX_INTR);
	XAxiDma_Reset(&AxiDmaInstance);
	XAxiEthernet_Reset(&AxiEthernetInstance);
	PhyReset(&AxiEthernetInstance);
	return pdPASS;
}

/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer, BaseType_t xReleaseAfterSend )
{
	/* get BD ring descriptor */
	XAxiDma_BdRing *TxRingPtr = XAxiDma_GetTxRing(&AxiDmaInstance);
	XAxiDma_Bd * BdPtr;

	FreeRTOS_debug_printf( ("xNetworkInterfaceOutput\r\n") );

	/* allocate next BD from the BD ring */
	taskENTER_CRITICAL();
	configASSERT( XAxiDma_BdRingAlloc(TxRingPtr, 1, &BdPtr) == 0);
	taskEXIT_CRITICAL();

	/* configure BD */
	uint8_t* xTxBuffer = AxiEthernetGetTxBuffer();
	memcpy(xTxBuffer, pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength);
#if defined(__clang__)
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpointer-to-int-cast"
#endif
	XAxiDma_BdSetBufAddr(BdPtr,(u32)xTxBuffer);
	XAxiDma_BdSetLength(BdPtr, pxNetworkBuffer->xDataLength, TxRingPtr->MaxTransferLen);
	XAxiDma_BdSetCtrl(BdPtr, XAXIDMA_BD_CTRL_TXSOF_MASK |
			     XAXIDMA_BD_CTRL_TXEOF_MASK);
#if defined(__clang__)
#else
#pragma GCC diagnostic pop
#endif	
	/* pass BD to HW */
	taskENTER_CRITICAL();
	configASSERT( XAxiDma_BdRingToHw(TxRingPtr, 1, BdPtr) == 0 );

	/* start transaction */
	configASSERT( XAxiDma_BdRingStart(TxRingPtr) == 0);
	taskEXIT_CRITICAL();

	/* Call the standard trace macro to log the send event. */
    iptraceNETWORK_INTERFACE_TRANSMIT();

	// simple driver
	if( xReleaseAfterSend != pdFALSE )
    {
        /* It is assumed SendData() copies the data out of the FreeRTOS+TCP Ethernet
        buffer.  The Ethernet buffer is therefore no longer needed, and must be
        freed for re-use. */
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

	return pdPASS;
}
/*-----------------------------------------------------------*/

BaseType_t xGetPhyLinkStatus( void )
{
	if (PhyLinkStatus(&AxiEthernetInstance)) {
		return pdPASS;
	} else {
		return pdFAIL;
	}
}
/*-----------------------------------------------------------*/
