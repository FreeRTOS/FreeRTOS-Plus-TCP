/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef RISCV_HAL_ETH_H
#define RISCV_HAL_ETH_H

#include "xaxiethernet.h"
#include "xaxidma.h"
#include "plic_driver.h"
#include "bsp.h"

/* Driver instances*/
extern XAxiEthernet AxiEthernetInstance;
extern XAxiDma AxiDmaInstance;
extern volatile int FramesTx;
extern volatile int FramesRx;

#define RXBD_CNT		64	/* Number of RxBDs to use */
#define TXBD_CNT		64	/* Number of TxBDs to use */
#define BD_ALIGNMENT		XAXIDMA_BD_MINIMUM_ALIGNMENT/* Byte alignment of
							     * BDs
							     */
#define PAYLOAD_SIZE		1000	/* Payload size used in examples */
#define BD_RX_STATUS_OFFSET	2


#define AXIETHERNET_PHY_DELAY_SEC	4	/*
						 * Amount of time to delay waiting on
						 * PHY to reset.
						 */

uint8_t* AxiEthernetGetTxBuffer(void);

/* Interrupt handlers */
void TxIntrHandler(XAxiDma_BdRing *TxRingPtr);
void TxCallBack(XAxiDma_BdRing *TxRingPtr);
void RxIntrHandler(XAxiDma_BdRing *RxRingPtr);
void RxCallBack(XAxiDma_BdRing *RxRingPtr);
void AxiEthernetErrorHandler(XAxiEthernet *AxiEthernet);

int AxiEthernetSetupIntrSystem(plic_instance_t *IntcInstancePtr,
				XAxiEthernet *AxiEthernetInstancePtr,
				XAxiDma *DmaInstancePtr,
				u16 AxiEthernetIntrId,
				u16 DmaRxIntrId, u16 DmaTxIntrId);

void AxiEthernetDisableIntrSystem(plic_instance_t *IntcInstancePtr,
				   u16 AxiEthernetIntrId,
				   u16 DmaRxIntrId, u16 DmaTxIntrId);

int PhySetup(XAxiEthernet *AxiEthernetInstancePtr, u16 AxiEthernetDeviceId);
void PhyReset(XAxiEthernet *AxiEthernetInstancePtr);
int DmaSetup(XAxiDma *DmaInstancePtr, u16 AxiDmaDeviceId);

int PhyLinkStatus(XAxiEthernet *AxiEthernetInstancePtr);

/* Assert helper function*/
void AxiEthernetUtilErrorTrap(char *Message);

int AxiEtherentConfigureTIPhy(XAxiEthernet *AxiEthernetInstancePtr, u32 PhyAddr);


/**
 * This task is notified from DMA Tx irq and clears up a BD from BD ring
 */
void DmaFreeBDTask( void *pvParameters );

void prvEMACDeferredInterruptHandlerTask( void *pvParameters );
#endif /* RISCV_HAL_ETH_H */ 