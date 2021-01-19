#include "riscv_hal_eth.h"

#include "xil_assert.h"
#include <stdio.h> // for printf
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"

/* FreeRTOS+TCP includes. */
#include "NetworkInterface.h"

// TODO: a bunch of these is not used, clean it
#define AXIETHERNET_LOOPBACK_SPEED	100	/* 100Mb/s for Mii */
#define AXIETHERNET_LOOPBACK_SPEED_1G 	1000	/* 1000Mb/s for GMii */
#define AXIETHERNET_LOOPBACK_SPEED_2p5G 2500	/* 2p5G for 2.5G MAC */
#define NUM_PACKETS  1 /* Number of ethernet frames to hold */

/* IEEE PHY Specific definitions */
#define PHY_R0_CTRL_REG			0
#define PHY_R1_STATUS_REG		1
#define PHY_R3_PHY_IDENT_REG	3

#define PHY_R5_PART_ABIL_1_REG	5
#define PHY_R10_PART_ABIL_3_REG	10

#define PHY_R0_RESET         0x8000
#define PHY_R0_LOOPBACK      0x4000
#define PHY_R0_ANEG_ENABLE   0x1000
#define PHY_R0_DFT_SPD_MASK  0x2040
#define PHY_R0_DFT_SPD_10    0x0000
#define PHY_R0_DFT_SPD_100   0x2000
#define PHY_R0_DFT_SPD_1000  0x0040
#define PHY_R0_DFT_SPD_2500  0x0040
#define PHY_R0_ISOLATE       0x0400

#define PHY_R1_LINK_STATUS	0x0004
#define PHY_R1_ANEG_COMP	0x0020
#define PHY_R1_1GBPS_EXT	0x0100

#define PHY_R5_ACK			0x4000
#define PHY_R5_100MBPS		0x0380
#define PHY_R5_10MBPS		0x0060

#define PHY_R10_1GBPS		0x0C00

/* Marvel PHY 88E1111 Specific definitions */
#define PHY_R20_EXTND_CTRL_REG	20
#define PHY_R27_EXTND_STS_REG	27

#define PHY_R20_DFT_SPD_10    	0x20
#define PHY_R20_DFT_SPD_100   	0x50
#define PHY_R20_DFT_SPD_1000  	0x60
#define PHY_R20_RX_DLY		0x80

#define PHY_R27_MAC_CONFIG_GMII      0x000F
#define PHY_R27_MAC_CONFIG_MII       0x000F
#define PHY_R27_MAC_CONFIG_RGMII     0x000B
#define PHY_R27_MAC_CONFIG_SGMII     0x0004

/* Marvel PHY 88E1116R Specific definitions */
#define PHY_R22_PAGE_ADDR_REG	22
#define PHY_PG2_R21_CTRL_REG	21

#define PHY_REG21_10      0x0030
#define PHY_REG21_100     0x2030
#define PHY_REG21_1000    0x0070
#define PHY_R32_RGMIICTL1 0x32

/* Marvel PHY flags */
#define MARVEL_PHY_88E1111_MODEL	0xC0
#define MARVEL_PHY_88E1116R_MODEL	0x240
#define PHY_MODEL_NUM_MASK		0x3F0

/* TI PHY flags */
#define TI_PHY_IDENTIFIER		0x2000
#define TI_PHY_MODEL			0x230
#define TI_PHY_CR			0xD
#define TI_PHY_PHYCTRL			0x10
#define TI_PHY_CR_SGMII_EN		0x0800
#define TI_PHY_ADDDR			0xE
#define TI_PHY_CFGR2			0x14
#define TI_PHY_SGMIITYPE		0xD3
#define TI_PHY_CFGR2_SGMII_AUTONEG_EN	0x0080
#define TI_PHY_SGMIICLK_EN		0x4000
#define TI_PHY_CR_DEVAD_EN		0x001F
#define TI_PHY_CR_DEVAD_DATAEN		0x4000

#define TI_PHY_CFGR4			0x31
#define TI_PHY_CFGR4_RES_BIT8		0x100
#define TI_PHY_CFGR4_RES_BIT7		0x080
#define TI_PHY_CFGR4_ANEG_TIMER		0x060

/* Driver instances*/
XAxiEthernet AxiEthernetInstance;
XAxiDma AxiDmaInstance;

static TaskHandle_t DmaFreeBDTaskHandle = NULL;
static TaskHandle_t prvEMACDeferredInterruptHandlerTaskHandle = NULL;

/*
 * Number of bytes to reserve for BD space for the number of BDs desired
 */
#define RXBD_SPACE_BYTES XAxiDma_BdRingMemCalc(BD_ALIGNMENT, RXBD_CNT)
#define TXBD_SPACE_BYTES XAxiDma_BdRingMemCalc(BD_ALIGNMENT, TXBD_CNT)

/*
 * Define an aligned data type for an ethernet frame. This declaration is
 * specific to the GNU compiler
 */
typedef uint8_t EthernetFrame[NUM_PACKETS * XAE_MAX_JUMBO_FRAME_SIZE] __attribute__ ((aligned(BD_ALIGNMENT)));
// 0x80000000
static uint8_t * const TxFrameBufRef = (uint8_t *)0x80000000;
//static EthernetFrame TxFrameBuf[TXBD_CNT] __attribute__ ((section(".uncached")));	/* Transmit buffers */
// 0x80015fc0
static uint8_t * const RxFrameBufRef =(uint8_t *)(TxFrameBufRef + TXBD_CNT * sizeof(EthernetFrame));
//static EthernetFrame RxFrameBuf[RXBD_CNT] __attribute__ ((section(".uncached")));	/* Receive buffers */

/*
 * Aligned memory segments to be used for buffer descriptors
 */
// 8002bf80
//char RxBdSpace[RXBD_SPACE_BYTES] __attribute__ ((aligned(BD_ALIGNMENT))) __attribute__ ((section(".uncached")));
char * const RxBdSpaceRef = (char *) (RxFrameBufRef + RXBD_CNT * sizeof(EthernetFrame));
// 8002c200
//char TxBdSpace[TXBD_SPACE_BYTES] __attribute__ ((aligned(BD_ALIGNMENT))) __attribute__ ((section(".uncached")));
char * const TxBdSpaceRef = (char *) (RxBdSpaceRef + RXBD_SPACE_BYTES);


/*
 * Counters to be incremented by callbacks
 */
volatile int FramesRx;	  /* Num of frames that have been received */
volatile int FramesTx;	  /* Num of frames that have been sent */
volatile int DeviceErrors; /* Num of errors detected in the device */


// @mpodhradsky: "Declaring AxiEthernetMAC as weak, so it can be overriden in the user app"
char AxiEthernetMAC[6]  __attribute__((weak)) = { configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5 };


uint8_t* AxiEthernetGetTxBuffer(void) {
	static uint8_t idx = 0;
	//return (uint8_t*)&TxFrameBuf[idx++ % TXBD_CNT];
	return (uint8_t *)(TxFrameBufRef + (idx++ % TXBD_CNT)*sizeof(EthernetFrame));
}

void AxiEthernetUtilErrorTrap(char *Message)
{
	printf("%s\r\n", Message);
    Xil_AssertVoidAlways();
}

int PhyLinkStatus(XAxiEthernet *AxiEthernetInstancePtr) {
    static uint16_t val = 0xff;
    XAxiEthernet_PhyRead(AxiEthernetInstancePtr, XPAR_AXIETHERNET_0_PHYADDR,
				PHY_R1_STATUS_REG, &val);
    return (val & PHY_R1_LINK_STATUS);
}

int AxiEtherentConfigureTIPhy(XAxiEthernet *AxiEthernetInstancePtr, u32 PhyAddr)
{
	printf("AxiEthernetMAC[0] = %#X\r\n", AxiEthernetMAC[0]);
	printf("AxiEthernetMAC[1] = %#X\r\n", AxiEthernetMAC[1]);
	printf("AxiEthernetMAC[2] = %#X\r\n", AxiEthernetMAC[2]);
	printf("AxiEthernetMAC[3] = %#X\r\n", AxiEthernetMAC[3]);
	printf("AxiEthernetMAC[4] = %#X\r\n", AxiEthernetMAC[4]);
	printf("AxiEthernetMAC[5] = %#X\r\n", AxiEthernetMAC[5]);
	u16 PhyReg5;
	u16 PhyRegCfg4;
	u16 Speed;
	u16 Status;

	/* Enable autonegotiation */
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, PHY_R0_CTRL_REG,
			    PHY_R0_ANEG_ENABLE | PHY_R0_DFT_SPD_1000);

	/* Enable SGMII Clock */
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_CR,
			      TI_PHY_CR_DEVAD_EN);
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_ADDDR,
			      TI_PHY_SGMIITYPE);
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_CR,
			      TI_PHY_CR_DEVAD_EN | TI_PHY_CR_DEVAD_DATAEN);
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_ADDDR,
			      TI_PHY_SGMIICLK_EN);

	/* Disable RGMII */
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_CR,
			      TI_PHY_CR_DEVAD_EN);
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_ADDDR,
			      PHY_R32_RGMIICTL1);
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_CR,
			      TI_PHY_CR_DEVAD_EN | TI_PHY_CR_DEVAD_DATAEN);
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_ADDDR, 0);

	/* Enable SGMII */
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_PHYCTRL,
	                      TI_PHY_CR_SGMII_EN);

	/* Wait for autonegotiation */
	XAxiEthernet_PhyRead(AxiEthernetInstancePtr, PhyAddr,
		  			     PHY_R5_PART_ABIL_1_REG, &PhyReg5);
	while (!(PhyReg5 & PHY_R5_ACK)) {
		msleep(100);
		XAxiEthernet_PhyRead(AxiEthernetInstancePtr, PhyAddr,
				     PHY_R5_PART_ABIL_1_REG, &PhyReg5);
	}

	/* Magic VCU-118 workaround */
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_CR,
				  TI_PHY_CR_DEVAD_EN);
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_ADDDR,
				  TI_PHY_CFGR4);
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_CR,
				  TI_PHY_CR_DEVAD_EN | TI_PHY_CR_DEVAD_DATAEN);
	XAxiEthernet_PhyRead(AxiEthernetInstancePtr, PhyAddr, TI_PHY_ADDDR,
				  &PhyRegCfg4);
	PhyRegCfg4 &= ~TI_PHY_CFGR4_RES_BIT7;
	PhyRegCfg4 |= TI_PHY_CFGR4_RES_BIT8;
	PhyRegCfg4 |= TI_PHY_CFGR4_ANEG_TIMER;
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_CR,
				  TI_PHY_CR_DEVAD_EN);
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_ADDDR,
				  TI_PHY_CFGR4);
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_CR,
				  TI_PHY_CR_DEVAD_EN | TI_PHY_CR_DEVAD_DATAEN);
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, PhyAddr, TI_PHY_ADDDR,
				  PhyRegCfg4);

	XAxiEthernet_PhyRead(AxiEthernetInstancePtr, PhyAddr, PHY_R1_STATUS_REG,
			     &Status);
	while (!(Status & PHY_R1_ANEG_COMP)) {
		msleep(100);
		XAxiEthernet_PhyRead(AxiEthernetInstancePtr, PhyAddr,
				     PHY_R1_STATUS_REG, &Status);
	}

	/* Pass result of autonegotiation to AxiEthernet */
	Speed = 0;
	if (Status & PHY_R1_1GBPS_EXT) {
		u16 PhyReg10;
		XAxiEthernet_PhyRead(AxiEthernetInstancePtr, PhyAddr,
			PHY_R10_PART_ABIL_3_REG, &PhyReg10);
		if (PhyReg10 & PHY_R10_1GBPS) {
			Speed = XAE_SPEED_1000_MBPS;
		}
	}
	if (!Speed) {
		XAxiEthernet_PhyRead(AxiEthernetInstancePtr, PhyAddr,
			PHY_R5_PART_ABIL_1_REG, &PhyReg5);
		if (PhyReg5 & PHY_R5_100MBPS) {
			Speed = XAE_SPEED_100_MBPS;
		} else if (PhyReg5 & PHY_R5_10MBPS) {
			Speed = XAE_SPEED_10_MBPS;
		} else {
			return XST_FAILURE;
		}
	}

	configASSERT(XAxiEthernet_SetOperatingSpeed(AxiEthernetInstancePtr, Speed) == 0);

	return XST_SUCCESS;
}

/**
 *  Handles TX interrupts and frees BDs
 **/
void DmaFreeBDTask( void *pvParameters ) {
	(void) pvParameters;
	XAxiDma_BdRing *TxRingPtr = XAxiDma_GetTxRing(&AxiDmaInstance);
	XAxiDma_Bd * BdPtr;
	int BdLimit = 1;

	for (;;) {
		taskENTER_CRITICAL();
		int BdReturned = XAxiDma_BdRingFromHw(TxRingPtr, BdLimit, &BdPtr);
		taskEXIT_CRITICAL();

		if (BdReturned == 0) {
			/* wait for notification */
			ulTaskNotifyTake( pdFALSE, portMAX_DELAY );
			continue;
		}

		configASSERT(BdReturned == BdLimit);

		taskENTER_CRITICAL();
		configASSERT( XAxiDma_BdRingFree(TxRingPtr, BdLimit, BdPtr) == 0 );
		taskEXIT_CRITICAL();
	}
}


/**
 * Handle RX data
 */
// Simple driver
void prvEMACDeferredInterruptHandlerTask( void *pvParameters ) {
	(void) pvParameters;
	NetworkBufferDescriptor_t *pxBufferDescriptor;
	size_t xBytesReceived = 0;
	uint8_t* xRxBuffer;
	/* Used to indicate that xSendEventStructToIPTask() is being called because
	of an Ethernet receive event. */
	IPStackEvent_t xRxEvent;
	XAxiDma_BdRing *RxRingPtr = XAxiDma_GetRxRing(&AxiDmaInstance);
 	XAxiDma_Bd * BdPtr;
 	int BdLimit = 1;
	 uint32_t BdSts;

	for(;;) {
		taskENTER_CRITICAL();
		int BdReturned = XAxiDma_BdRingFromHw(RxRingPtr, BdLimit, &BdPtr);
		taskEXIT_CRITICAL();

		/* Wait for the Ethernet MAC interrupt to indicate that another packet
        has been received.  The task notification is used in a similar way to a
        counting semaphore to count Rx events, but is a lot more efficient than
        a semaphore. */
		if (BdReturned == 0) {
			ulTaskNotifyTake( pdFALSE, portMAX_DELAY );
			continue;
		}

		configASSERT(BdReturned == BdLimit);

		/* Examine the BD */
		BdSts = XAxiDma_BdGetSts(BdPtr);
		if (BdSts & XAXIDMA_BD_STS_ALL_ERR_MASK) {
			AxiEthernetUtilErrorTrap("Rx Error");
		}
		else {
			xBytesReceived =
			(size_t) (XAxiDma_BdRead(BdPtr,XAXIDMA_BD_USR4_OFFSET)) & 0x0000FFFF;
		}

		if (xBytesReceived > 0) {
			/* Allocate a network buffer descriptor that points to a buffer
            large enough to hold the received frame.  As this is the simple
            rather than efficient example the received data will just be copied
            into this buffer. */
            pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( xBytesReceived, 0 );

			configASSERT( pxBufferDescriptor != NULL);

			// Buf address
#if defined(__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wint-to-pointer-cast"
/* this cast is OK */
			xRxBuffer = (uint8_t*)XAxiDma_BdGetBufAddr(BdPtr);
#pragma clang diagnostic pop
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wint-to-pointer-cast"
/* this cast is OK */
			xRxBuffer = (uint8_t*)XAxiDma_BdGetBufAddr(BdPtr);
#pragma GCC diagnostic pop
#endif

			/* pxBufferDescriptor->pucEthernetBuffer now points to an Ethernet
                buffer large enough to hold the received data.  Copy the
                received data into pcNetworkBuffer->pucEthernetBuffer.  Here it
                is assumed ReceiveData() is a peripheral driver function that
                copies the received data into a buffer passed in as the function's
                parameter.  Remember! While is is a simple robust technique -
               it is not efficient.  An example that uses a zero copy technique
            is provided further down this page. */
            memcpy(pxBufferDescriptor->pucEthernetBuffer,  xRxBuffer, xBytesReceived);
            pxBufferDescriptor->xDataLength = xBytesReceived;

			/* See if the data contained in the received Ethernet frame needs
            to be processed.  NOTE! It is preferable to do this in
            the interrupt service routine itself, which would remove the need
            to unblock this task for packets that don't need processing. */
            if( eConsiderFrameForProcessing( pxBufferDescriptor->pucEthernetBuffer )
                                                                  == eProcessBuffer )
            {
				/* The event about to be sent to the TCP/IP is an Rx event. */
                xRxEvent.eEventType = eNetworkRxEvent;

                /* pvData is used to point to the network buffer descriptor that
                now references the received data. */
                xRxEvent.pvData = ( void * ) pxBufferDescriptor;

                /* Send the data to the TCP/IP stack. */
                if( xSendEventStructToIPTask( &xRxEvent, 0 ) == pdFALSE )
                {
                    /* The buffer could not be sent to the IP task so the buffer
                    must be released. */
                    vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );

                    /* Make a call to the standard trace macro to log the
                    occurrence. */
                    iptraceETHERNET_RX_EVENT_LOST();
                }
                else
                {
                    /* The message was successfully sent to the TCP/IP stack.
                    Call the standard trace macro to log the occurrence. */
                    iptraceNETWORK_INTERFACE_RECEIVE();
                }
			}
			else
            {
                /* The Ethernet frame can be dropped, but the Ethernet buffer
                must be released. */
                vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
            }
		}
	}
}

/**
 * Initialize DMA
 */
int DmaSetup(XAxiDma *DmaInstancePtr, u16 AxiDmaDeviceId)
{
	XAxiDma_Config *DmaConfig;
	XAxiDma_BdRing *RxRingPtr = XAxiDma_GetRxRing(DmaInstancePtr);
	XAxiDma_BdRing *TxRingPtr = XAxiDma_GetTxRing(DmaInstancePtr);
	XAxiDma_Bd BdTemplate;
	XAxiDma_Bd *BdPtr;
	XAxiDma_Bd *BdCurPtr;

	int Status;

	DmaConfig = XAxiDma_LookupConfig(AxiDmaDeviceId);
	/*
	 * Initialize AXIDMA engine. AXIDMA engine must be initialized before
	 * AxiEthernet. During AXIDMA engine initialization, AXIDMA hardware is
	 * reset, and since AXIDMA reset line is connected to AxiEthernet, this
	 * would ensure a reset of AxiEthernet.
	 */
	configASSERT( XAxiDma_CfgInitialize(DmaInstancePtr, DmaConfig) == 0);

	/*
	 * Setup RxBD space.
	 *
	 * We have already defined a properly aligned area of memory to store
	 * RxBDs at the beginning of this source code file so just pass its
	 * address into the function. No MMU is being used so the physical and
	 * virtual addresses are the same.
	 *
	 * Setup a BD template for the Rx channel. This template will be copied
	 * to every RxBD. We will not have to explicitly set these again.
	 */

	/* Disable all RX interrupts before RxBD space setup */
	XAxiDma_BdRingIntDisable(RxRingPtr, XAXIDMA_IRQ_ALL_MASK);

#if defined(__clang__)
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpointer-to-int-cast"
#endif
	/*
	 * Create the RxBD ring
	 */
	//Status = XAxiDma_BdRingCreate(RxRingPtr, (u32) &RxBdSpace,
	//			     (u32) &RxBdSpace, BD_ALIGNMENT, RXBD_CNT);
	Status = XAxiDma_BdRingCreate(RxRingPtr, (u32) RxBdSpaceRef,
				     (u32) RxBdSpaceRef, BD_ALIGNMENT, RXBD_CNT);
	
	configASSERT( Status == 0);

	XAxiDma_BdClear(&BdTemplate);
	configASSERT( XAxiDma_BdRingClone(RxRingPtr, &BdTemplate) == 0);

	/*
	 * Setup TxBD space.
	 *
	 * Like RxBD space, we have already defined a properly aligned area of
	 * memory to use.
	 */
	/* Disable all RX interrupts before RxBD space setup */
	XAxiDma_BdRingIntDisable(TxRingPtr, XAXIDMA_IRQ_ALL_MASK);

	/*
	 * Create the TxBD ring
	 */
	//Status = XAxiDma_BdRingCreate(TxRingPtr, (u32) &TxBdSpace,
	//			     (u32) &TxBdSpace, BD_ALIGNMENT, TXBD_CNT);
	Status = XAxiDma_BdRingCreate(TxRingPtr, (u32) TxBdSpaceRef,
				     (u32) TxBdSpaceRef, BD_ALIGNMENT, TXBD_CNT);
	configASSERT( Status == 0);

	/*
	 * We reuse the bd template, as the same one will work for both rx and
	 * tx.
	 */
	configASSERT( XAxiDma_BdRingClone(TxRingPtr, &BdTemplate) == 0);

	/*
	 * Interrupt coalescing parameters are set to their default settings
	 * which is to interrupt the processor after every frame has been
	 * processed by the DMA engine.
	 */
	configASSERT( XAxiDma_BdRingSetCoalesce(TxRingPtr, 1, 1) == 0);
	configASSERT( XAxiDma_BdRingSetCoalesce(RxRingPtr, 1, 1) == 0);

	/* Check status */
	int FreeBdCount = XAxiDma_BdRingGetFreeCnt(RxRingPtr);
	configASSERT( FreeBdCount == RXBD_CNT);

	/*
	 * Allocate RXBD_CNT RxBD.
	 */
	Status = XAxiDma_BdRingAlloc(RxRingPtr, FreeBdCount, &BdPtr);
	configASSERT( Status == 0);

	BdCurPtr = BdPtr;
	for (int Index = 0; Index < FreeBdCount; Index++) {
		//Status = XAxiDma_BdSetBufAddr(BdCurPtr, (u32)&RxFrameBuf[Index]);
		Status = XAxiDma_BdSetBufAddr(BdCurPtr, (u32)(RxFrameBufRef +(Index*sizeof(EthernetFrame))));

		if (Status != XST_SUCCESS) {
			printf("Rx set buffer addr %x on BD %x failed %d\r\n",
			//(unsigned int)&RxFrameBuf[Index],
			(unsigned int)(RxFrameBufRef +(Index*sizeof(EthernetFrame))),
			(unsigned int)(UINTPTR)BdCurPtr, Status);

			return XST_FAILURE;
		}

		//Status = XAxiDma_BdSetLength(BdCurPtr, sizeof(RxFrameBuf[Index]),
		Status = XAxiDma_BdSetLength(BdCurPtr, sizeof(EthernetFrame),
					RxRingPtr->MaxTransferLen);
		if (Status != XST_SUCCESS) {
			printf("Rx set length %u on BD %x failed %d\r\n",
				(unsigned int)sizeof(EthernetFrame), (unsigned int)(UINTPTR)BdCurPtr, Status);
			    //sizeof(RxFrameBuf[Index]), (UINTPTR)BdCurPtr, Status);

			return XST_FAILURE;
		}

		/* Receive BDs do not need to set anything for the control
		 * The hardware will set the SOF/EOF bits per stream status
		 */
		XAxiDma_BdSetCtrl(BdCurPtr, 0);
		XAxiDma_BdSetId(BdCurPtr, Index);
		BdCurPtr = (XAxiDma_Bd *)XAxiDma_BdRingNext(RxRingPtr, BdCurPtr);
	}
#if defined(__clang__)
#else
#pragma GCC diagnostic pop
#endif
	/*
	 * Enqueue to HW
	 */
	configASSERT( XAxiDma_BdRingToHw(RxRingPtr, FreeBdCount, BdPtr) == 0);

	/*
	 * Start DMA RX channel. Now it's ready to receive data.
	 */
	configASSERT( XAxiDma_BdRingStart(RxRingPtr) == 0);

	/* Enable all RX interrupts */
	XAxiDma_BdRingIntEnable(RxRingPtr, XAXIDMA_IRQ_ALL_MASK);
	/* Enable Cyclic DMA mode */
	XAxiDma_BdRingEnableCyclicDMA(RxRingPtr);
	XAxiDma_SelectCyclicMode(DmaInstancePtr, XAXIDMA_DEVICE_TO_DMA, 1);

	/*
	 * Enable DMA transmit related interrupts
	 */
	XAxiDma_BdRingIntEnable(TxRingPtr, XAXIDMA_IRQ_ALL_MASK);

	/* Start RX DMA channel */
	configASSERT( XAxiDma_BdRingStart(RxRingPtr) == 0);

	// create DmaFreeTask
	xTaskCreate( DmaFreeBDTask, "DmaFreeBDTask", configMINIMAL_STACK_SIZE*5, NULL, ipconfigIP_TASK_PRIORITY - 1, &DmaFreeBDTaskHandle);
	xTaskCreate( prvEMACDeferredInterruptHandlerTask, "prvEMACDeferredInterruptHandlerTask", configMINIMAL_STACK_SIZE*5, NULL,
		ipconfigIP_TASK_PRIORITY - 1, &prvEMACDeferredInterruptHandlerTaskHandle);

	return XST_SUCCESS;
}


/**
 * Initialize Ethernet
 */
int PhySetup(XAxiEthernet *AxiEthernetInstancePtr, u16 AxiEthernetDeviceId)
{
	XAxiEthernet_Config *MacCfgPtr;

	/*
	 *  Get the configuration of AxiEthernet hardware.
	 */
	MacCfgPtr = XAxiEthernet_LookupConfig(AxiEthernetDeviceId);

	/*
	 * Check if DMA is present or not.
	 */
	configASSERT( MacCfgPtr->AxiDevType == XPAR_AXI_DMA);

	/*
	 * Initialize AxiEthernet hardware.
	 */
	configASSERT( XAxiEthernet_CfgInitialize(AxiEthernetInstancePtr, MacCfgPtr,
						MacCfgPtr->BaseAddress) == 0);

	/*
	 * Make sure Tx, Rx and extended multicast are enabled.
	 */
	configASSERT( XAxiEthernet_SetOptions(AxiEthernetInstancePtr,
						XAE_RECEIVER_ENABLE_OPTION | XAE_DEFAULT_OPTIONS |
						XAE_TRANSMITTER_ENABLE_OPTION) == 0);


	/*
	 * Set the MAC address
	 */
	configASSERT( XAxiEthernet_SetMacAddress(AxiEthernetInstancePtr,
							AxiEthernetMAC) == 0);

	AxiEtherentConfigureTIPhy(AxiEthernetInstancePtr, XPAR_AXIETHERNET_0_PHYADDR);

	return XST_SUCCESS;
}


/**
 * Uninitialize Ethernet
 */
void PhyReset(XAxiEthernet *AxiEthernetInstancePtr)
{
	XAxiEthernet_PhyWrite(AxiEthernetInstancePtr, XPAR_AXIETHERNET_0_PHYADDR,
			      PHY_R0_CTRL_REG, PHY_R0_RESET);
}


void TxCallBack(XAxiDma_BdRing *TxRingPtr)
{
	(void) TxRingPtr;
	configASSERT( DmaFreeBDTaskHandle != NULL);

	static BaseType_t askForContextSwitch = pdFALSE;
	vTaskNotifyGiveFromISR( DmaFreeBDTaskHandle, &askForContextSwitch);

	FramesTx++;
}

/*****************************************************************************/
/**
*
* This is the DMA TX Interrupt handler function.
*
* @param	TxRingPtr is a pointer to TX channel of the DMA engine.
*
* @return	None.
*
* @note		This Interrupt handler MUST clear pending interrupts before
*		handling them by calling the call back. Otherwise the following
*		corner case could raise some issue:
*
*		A packet got transmitted and a TX interrupt got asserted. If
*		the interrupt handler calls the callback before clearing the
*		interrupt, a new packet may get transmitted in the callback.
*		This new packet then can assert one more TX interrupt before
*		the control comes out of the callback function. Now when
*		eventually control comes out of the callback function, it will
*		never know about the second new interrupt and hence while
*		clearing the interrupts, would clear the new interrupt as well
*		and will never process it.
*		To avoid such cases, interrupts must be cleared before calling
*		the callback.
*
******************************************************************************/
void TxIntrHandler(XAxiDma_BdRing *TxRingPtr)
{
	u32 IrqStatus;

	/* Read pending interrupts */
	IrqStatus = XAxiDma_BdRingGetIrq(TxRingPtr);

	/* Acknowledge pending interrupts */
	XAxiDma_BdRingAckIrq(TxRingPtr, IrqStatus);

	/*
	 * If no interrupt is asserted, raise error flag, reset the
	 * hardware to recover from the error, and return with no further
	 * processing.
	 */
	if (!(IrqStatus & XAXIDMA_IRQ_ALL_MASK)) {
		DeviceErrors++;
		printf("AXIDma: No interrupts asserted in TX status register");
		XAxiDma_Reset(&AxiDmaInstance);
		configASSERT( XAxiDma_ResetIsDone(&AxiDmaInstance) == 1);
		return;
	}

	/* If error interrupt is asserted, raise error flag, reset the
	 * hardware to recover from the error, and return with no further
	 * processing.
	 */
	if ((IrqStatus & XAXIDMA_IRQ_ERROR_MASK)) {
		printf("AXIDMA: TX Error interrupts\n");
		/*
		 * Reset should never fail for transmit channel
		 */
		XAxiDma_Reset(&AxiDmaInstance);

		configASSERT( XAxiDma_ResetIsDone(&AxiDmaInstance) == 1);
		return;
	}

	/*
	 * If Transmit done interrupt is asserted, call TX call back function
	 * to handle the processed BDs and raise the according flag
	 */
	if ((IrqStatus & (XAXIDMA_IRQ_DELAY_MASK | XAXIDMA_IRQ_IOC_MASK))) {
		TxCallBack(TxRingPtr);
	}
}


void RxCallBack(XAxiDma_BdRing *RxRingPtr)
{
	(void) RxRingPtr;
	configASSERT( prvEMACDeferredInterruptHandlerTaskHandle != NULL);

	static BaseType_t askForContextSwitch = pdFALSE;
	vTaskNotifyGiveFromISR( prvEMACDeferredInterruptHandlerTaskHandle, &askForContextSwitch);

	FramesRx++;
}

void RxIntrHandler(XAxiDma_BdRing *RxRingPtr)
{
	u32 IrqStatus;

	/* Read pending interrupts */
	IrqStatus = XAxiDma_BdRingGetIrq(RxRingPtr);

	/* Acknowledge pending interrupts */
	XAxiDma_BdRingAckIrq(RxRingPtr, IrqStatus);

	/*
	 * If no interrupt is asserted, raise error flag, reset the
	 * hardware to recover from the error, and return with no further
	 * processing.
	 */
	if (!(IrqStatus & XAXIDMA_IRQ_ALL_MASK)) {
		DeviceErrors++;
		printf("AXIDma: No interrupts asserted in RX status register");
		XAxiDma_Reset(&AxiDmaInstance);
		configASSERT( XAxiDma_ResetIsDone(&AxiDmaInstance) == 1);
		return;
	}

	/* If error interrupt is asserted, raise error flag, reset the
	 * hardware to recover from the error, and return with no further
	 * processing.
	 */
	if ((IrqStatus & XAXIDMA_IRQ_ERROR_MASK)) {
		printf("AXIDMA: RX Error interrupts\n");

		/* Reset could fail and hang
		 * NEED a way to handle this or do not call it??
		 */
		XAxiDma_Reset(&AxiDmaInstance);
		configASSERT( XAxiDma_ResetIsDone(&AxiDmaInstance) == 1);

		return;
	}

	/*
	 * If Reception done interrupt is asserted, call RX call back function
	 * to handle the processed BDs and then raise the according flag.
	 */
	if ((IrqStatus & (XAXIDMA_IRQ_DELAY_MASK | XAXIDMA_IRQ_IOC_MASK))) {
		RxCallBack(RxRingPtr);
	}
}

void AxiEthernetErrorHandler(XAxiEthernet *AxiEthernet)
{
	u32 Pending = XAxiEthernet_IntPending(AxiEthernet);

	if (Pending & XAE_INT_RXRJECT_MASK) {
		printf("AxiEthernet: Rx packet rejected");
		configASSERT( 0); // TODO: always fail for now
	}

	if (Pending & XAE_INT_RXFIFOOVR_MASK) {
		printf("AxiEthernet: Rx fifo over run");
		configASSERT( 0); // TODO: always fail for now
	}

	XAxiEthernet_IntClear(AxiEthernet, Pending);

	DeviceErrors++;
}


int AxiEthernetSetupIntrSystem(plic_instance_t *IntcInstancePtr,
				XAxiEthernet *AxiEthernetInstancePtr,
				XAxiDma *DmaInstancePtr,
				u16 AxiEthernetIntrId,
				u16 DmaRxIntrId,
				u16 DmaTxIntrId)
{
    xaxi_debug_printf("AxiEthernetSetupIntrSystem\r\n");
	XAxiDma_BdRing * TxRingPtr = XAxiDma_GetTxRing(DmaInstancePtr);
	XAxiDma_BdRing * RxRingPtr = XAxiDma_GetRxRing(DmaInstancePtr);
	int Status;

	/*
	 * Initialize the interrupt controller and connect the ISR
	 */
	Status = PLIC_register_interrupt_handler(IntcInstancePtr, AxiEthernetIntrId,
							(XInterruptHandler)
							AxiEthernetErrorHandler,
							AxiEthernetInstancePtr);
    if (Status == 0) {
        printf("Unable to connect ISR to interrupt controller: AxiEthernetIntrId %u\r\n",AxiEthernetIntrId);
        return XST_FAILURE;
    }
	Status = PLIC_register_interrupt_handler(IntcInstancePtr, DmaTxIntrId,
						(XInterruptHandler) TxIntrHandler,
									TxRingPtr);
    if (Status == 0) {
        printf("Unable to connect ISR to interrupt controller: DmaTxIntrId %u\r\n",DmaTxIntrId);
        return XST_FAILURE;
    }
	Status = PLIC_register_interrupt_handler(IntcInstancePtr, DmaRxIntrId,
						(XInterruptHandler) RxIntrHandler,
								RxRingPtr);
    if (Status == 0) {
        printf("Unable to connect ISR to interrupt controller: DmaRxIntrId %u\r\n",DmaRxIntrId);
        return XST_FAILURE;
    }

	return XST_SUCCESS;
}

void AxiEthernetDisableIntrSystem(plic_instance_t *IntcInstancePtr,
					u16 AxiEthernetIntrId,
					u16 DmaRxIntrId,
					u16 DmaTxIntrId)
{
	/* Stop the tasks */
	vTaskSuspend(DmaFreeBDTaskHandle);
	vTaskSuspend(prvEMACDeferredInterruptHandlerTaskHandle);

	/*
	 * Disconnect the interrupts for the DMA TX and RX channels
	 */
    PLIC_unregister_interrupt_handler(IntcInstancePtr, DmaTxIntrId);
	PLIC_unregister_interrupt_handler(IntcInstancePtr, DmaRxIntrId);

	/*
	 * Disconnect and disable the interrupt for the Axi Ethernet device
	 */
    PLIC_unregister_interrupt_handler(IntcInstancePtr, AxiEthernetIntrId);

	/* Now the callbacks won't be called we can delete the tasks */
	vTaskDelete(DmaFreeBDTaskHandle);
	vTaskDelete(prvEMACDeferredInterruptHandlerTaskHandle);
}
