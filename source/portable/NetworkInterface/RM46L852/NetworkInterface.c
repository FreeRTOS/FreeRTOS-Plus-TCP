/*
 * RM46L852.c
 *
 *  Created on: Jul 10, 2023
 *      Author: chmalho
 */

#include "FreeRTOS.h"
#include "list.h"
#include "queue.h"
#include "semphr.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "emac.h"
#include "mdio.h"
#include "phy_dp83640.h"
#include "sci.h"

struct emac_tx_bdp {
  volatile struct emac_tx_bdp *next;
  volatile uint32 bufptr;
  volatile uint32 bufoff_len;
  volatile uint32 flags_pktlen;

  /* helper to know which pbuf this tx bd corresponds to */
  volatile struct NetworkBufferDescriptor_t *pbuf;
}emac_tx_bdp;

/* EMAC RX Buffer descriptor data structure */
struct emac_rx_bdp {
  volatile struct emac_rx_bdp *next;
  volatile uint32 bufptr;
  volatile uint32 bufoff_len;
  volatile uint32 flags_pktlen;

  /* helper to know which pbuf this rx bd corresponds to */
  volatile struct NetworkBufferDescriptor_t *pbuf;
}emac_rx_bdp;

/**
 * Helper struct to hold the data used to operate on a particular
 * receive channel
 */
struct rxch {
  volatile struct emac_rx_bdp *free_head;
  volatile struct emac_rx_bdp *active_head;
  volatile struct emac_rx_bdp *active_tail;
  uint32 freed_pbuf_len;
}rxch;

/**
 * Helper struct to hold the data used to operate on a particular
 * transmit channel
 */
struct txch {
  volatile struct emac_tx_bdp *free_head;
  volatile struct emac_tx_bdp *active_tail;
  volatile struct emac_tx_bdp *next_bd_to_process;
  volatile uint32 free_num;
}txch;

/**
 * Helper struct to hold private data used to operate the ethernet interface.
 */
struct hdkif {
  /* emac instance number */
  uint32 inst_num;

  uint8 mac_addr[6];

  /* emac base address */
  uint32 emac_base;

  /* emac controller base address */
  volatile uint32 emac_ctrl_base;
  volatile uint32 emac_ctrl_ram;

  /* mdio base address */
  volatile uint32 mdio_base;

  /* phy parameters for this instance - for future use */
  uint32 phy_addr;
  boolean (*phy_autoneg)(uint32, uint32, uint16);
  boolean (*phy_partnerability)(uint32, uint32, uint16*);

  /* The tx/rx channels for the interface */
  struct txch txchptr;
  struct rxch rxchptr;
}hdkif;

struct hdkif xHdkif;

/* Defining interface for all the emac instances */
static struct hdkif hdkif_data[MAX_EMAC_INSTANCE];

static struct hdkif * pHdkif = &xHdkif;

uint32 hdkif_swizzle_data(uint32 word) {

#if defined(_TMS570LC43x_)
    return
        (((word << 24) & 0xFF000000) |
        ((word <<  8) & 0x00FF0000)  |
        ((word >>  8) & 0x0000FF00)  |
        ((word >> 24) & 0x000000FF));
#else
    return word;
#endif
}

struct emac_tx_bdp *hdkif_swizzle_txp(volatile struct emac_tx_bdp *p) {
    return (struct emac_tx_bdp *)hdkif_swizzle_data((uint32)p);
}

struct emac_rx_bdp *hdkif_swizzle_rxp(volatile struct emac_rx_bdp *p) {
    return (struct emac_rx_bdp *)hdkif_swizzle_data((uint32)p);
}
static void
hdkif_inst_config() {
  if(xHdkif.inst_num == 0) {
    xHdkif.emac_base = EMAC_0_BASE;
    xHdkif.emac_ctrl_base = EMAC_CTRL_0_BASE;
    xHdkif.emac_ctrl_ram = EMAC_CTRL_RAM_0_BASE;
    xHdkif.mdio_base = MDIO_0_BASE;
    xHdkif.phy_addr = 1;
    xHdkif.phy_autoneg = Dp83640AutoNegotiate;
    xHdkif.phy_partnerability = Dp83640PartnerAbilityGet;
    xHdkif.mac_addr[0] = 0x00U;
    xHdkif.mac_addr[1] = 0x08U;
    xHdkif.mac_addr[2]= 0xEEU;
    xHdkif.mac_addr[3]= 0x03U;
    xHdkif.mac_addr[4]= 0xA6U;
    xHdkif.mac_addr[5]= 0x6CU;
  }
}

uint8   emacAddress[6U] =   {0x00U, 0x08U, 0xEEU, 0x03U, 0xA6U, 0x6CU};
BaseType_t xNetworkInterfaceInitialise( void )
{
    xHdkif.inst_num = 0;
    hdkif_inst_config();
    if (EMACHWInit(emacAddress) == EMAC_ERR_OK)
    {    sci_print("\n network initialise successful\n");
        return pdPASS;}
    else
        sci_print("\n network initialise unsuccessful\n");
        return pdFAIL;
}
BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t xReleaseAfterSend )
{
    txch_t * txch;
    NetworkBufferDescriptor_t * q;
    uint16 totLen;
    uint16 qLen;
    volatile emac_tx_bd_t * curr_bd, * active_head, * bd_end;

    txch = &( xHdkif.txchptr );
    sci_print("\n Entering Network Output\n");
    /* Get the buffer descriptor which is free to transmit */
    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
    curr_bd = txch->free_head;
    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
    bd_end = curr_bd;
    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
    active_head = curr_bd;

    /* Update the total packet length */
    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
    curr_bd->flags_pktlen &= ( ~( ( uint32 ) 0xFFFFU ) );
    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */

    curr_bd->flags_pktlen |=  pxNetworkBuffer->xDataLength;

    /* Indicate the start of the packet */
    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
    curr_bd->flags_pktlen |= ( EMAC_BUF_DESC_SOP | EMAC_BUF_DESC_OWNER );


    /* Copy pbuf information into TX buffer descriptors */
    q = pxNetworkBuffer;

//    while( q != NULL )
//    {
        /* Initialize the buffer pointer and length */
        /*SAFETYMCUSW 439 S MR:11.3 <APPROVED> "RHS is a pointer value required to be stored. - Advisory as per MISRA" */
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
         curr_bd->bufptr = ( uint32 ) ( pxNetworkBuffer->pucEthernetBuffer );
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
       // qLen = q->xDataLength;
        curr_bd->bufoff_len = ( ( uint32 ) ( pxNetworkBuffer->xDataLength ) & 0xFFFFU );
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
        bd_end = curr_bd;
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
        //curr_bd = curr_bd->next;
//        q = q->xBufferListItem.pxNext;
//    }

    /* Indicate the start and end of the packet */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
    bd_end->next = NULL;
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
    bd_end->flags_pktlen |= EMAC_BUF_DESC_EOP;

    /*SAFETYMCUSW 71 S MR:17.6 <APPROVED> "Assigned pointer value has required scope." */
    txch->free_head = curr_bd;

    /* For the first time, write the HDP with the filled bd */
    if( txch->active_tail == NULL )
    {
        /*SAFETYMCUSW 439 S MR:11.3 <APPROVED> "Address stored in pointer is passed as as an int parameter. - Advisory as per MISRA" */
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
        EMACTxHdrDescPtrWrite( xHdkif.emac_base, ( uint32 ) ( active_head ), ( uint32 ) EMAC_CHANNELNUMBER );
    }

    /*
     * Chain the bd's. If the DMA engine, already reached the end of the chain,
     * the EOQ will be set. In that case, the HDP shall be written again.
     */
    else
    {
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
        curr_bd = txch->active_tail;

        /* Wait for the EOQ bit is set */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
        while( EMAC_BUF_DESC_EOQ != ( curr_bd->flags_pktlen & EMAC_BUF_DESC_EOQ ) )
        {
        }

        /* Don't write to TXHDP0 until it turns to zero */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        while( ( ( uint32 ) 0U != *( ( uint32 * ) 0xFCF78600U ) ) )
        {
        }

        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
        curr_bd->next = active_head;

        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
        if( EMAC_BUF_DESC_EOQ == ( curr_bd->flags_pktlen & EMAC_BUF_DESC_EOQ ) )
        {
            /* Write the Header Descriptor Pointer and start DMA */
            /*SAFETYMCUSW 439 S MR:11.3 <APPROVED> "Address stored in pointer is passed as as an int parameter. - Advisory as per MISRA" */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            EMACTxHdrDescPtrWrite( xHdkif.emac_base, ( uint32 ) ( active_head ), ( uint32 ) EMAC_CHANNELNUMBER );
        }
    }

    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
    txch->active_tail = bd_end;

    return pdPASS;
}

#define BUFFER_SIZE_ALLOC1               ( ipTOTAL_ETHERNET_FRAME_SIZE + ipBUFFER_PADDING )
#define BUFFER_SIZE_ALLOC1_ROUNDED_UP    ( ( BUFFER_SIZE_ALLOC1 + 7 ) & ~0x07UL )
static uint8_t ucBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ BUFFER_SIZE_ALLOC1_ROUNDED_UP ];

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    BaseType_t x;

    for( x = 0; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++ )
    {
        /* pucEthernetBuffer is set to point ipBUFFER_PADDING bytes in from the
         * beginning of the allocated buffer. */
        pxNetworkBuffers[ x ].pucEthernetBuffer = &( ucBuffers[ x ][ ipBUFFER_PADDING ] );

        /* The following line is also required, but will not be required in
         * future versions. */
        *( ( uint32_t * ) &ucBuffers[ x ][ 0 ] ) = ( uint32_t ) &( pxNetworkBuffers[ x ] );
    }
}


