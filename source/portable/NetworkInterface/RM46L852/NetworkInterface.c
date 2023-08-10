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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 */

/**
 * @file NetworkInterface.c
 * @brief Implements the Network Interface driver for the TI Hercules RM46 board.
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


#if ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#endif


TaskHandle_t receiveTaskHandle = NULL;

void prvEMACHandlerTask( void * pvParameters  );
void prvProcessFrame( NetworkBufferDescriptor_t * pxBufferDescriptor );
uint8   emacAddress[6U] =   {0x00U, 0x08U, 0xEEU, 0x03U, 0xA6U, 0x6CU};

/*
 * This function is used to call EMAC API to perform low level hardware
 * initializations.
 * Also, creates prvEMACHandlerTask for handling received packets.
 */

BaseType_t xNetworkInterfaceInitialise( void )
{
    BaseType_t xFirstCall = pdTRUE;
    BaseType_t xTaskCreated;

    if (EMACHWInit(emacAddress) == EMAC_ERR_OK)
    {
        if( ( xFirstCall == pdTRUE ) || ( receiveTaskHandle == NULL ) )
        {
            /* The handler task is created at the highest possible priority to
             * ensure the interrupt handler can return directly to it. */
            xTaskCreated = xTaskCreate( prvEMACHandlerTask,
                                        "EMAC-Handler",
                                        configMINIMAL_STACK_SIZE,
                                        NULL,
                                        configMAX_PRIORITIES - 1,
                                        &receiveTaskHandle );

            if( ( receiveTaskHandle == NULL ) || ( xTaskCreated != pdPASS ) )
            {
                FreeRTOS_printf( ( "Failed to create the handler task." ) );

            }
            /* After this, the task should not be created. */
            else
                xFirstCall = pdFALSE;
        }

        return pdPASS;
    }
    else
    {
        return pdFAIL;
    }
}

/*
 *  This function is used to call EMAC API to transmit packets.
 *  And freeing the network buffers.
 */

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t xReleaseAfterSend )
{
      struct pbuf_struct xpbuf;
      xpbuf.payload = pxNetworkBuffer->pucEthernetBuffer;
      xpbuf.len = pxNetworkBuffer->xDataLength;
      xpbuf.tot_len = pxNetworkBuffer->xDataLength;
      xpbuf.next = NULL;
      if(xpbuf.tot_len < MIN_PKT_LEN)
      {
          xpbuf.tot_len = MIN_PKT_LEN;
          xpbuf.len = MIN_PKT_LEN;
      }

      taskENTER_CRITICAL();
      {
          EMACTransmit(&hdkif_data[0U],&xpbuf);
      }
      taskEXIT_CRITICAL();

      if( xReleaseAfterSend == pdTRUE )
      {
          vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
      }
      return pdPASS;
}

/*
 *  This Task is notified everytime a packet is received.
 *  It calls EMACReceive for actual packet processing.
 */

void prvEMACHandlerTask( void * pvParameters  )
{

    while( pdTRUE )
    {
        ulTaskNotifyTake( pdTRUE, pdMS_TO_TICKS( 500 ) );

        taskENTER_CRITICAL();
        {
            EMACReceive(&hdkif_data[0U]);
        }
        taskEXIT_CRITICAL();
    }
}

/*
 *  This function sends RX event to IP task for further processing the data packet.
 */

void prvProcessFrame( NetworkBufferDescriptor_t * pxBufferDescriptor)
{

    if( pxBufferDescriptor != NULL )
    {

        if( ipCONSIDER_FRAME_FOR_PROCESSING( pxBufferDescriptor->pucEthernetBuffer ) == eProcessBuffer )
        {

            /* send packet to IP task for further processing */
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
            #if ( ( ipconfigHAS_DEBUG_PRINTF == 1 ) && defined( FreeRTOS_debug_printf ) )
                const EthernetHeader_t * pxEthernetHeader;
                char ucSource[ 18 ];
                char ucDestination[ 18 ];

                pxEthernetHeader = ( ( const EthernetHeader_t * ) pxBufferDescriptor->pucEthernetBuffer );


                FreeRTOS_EUI48_ntop( pxEthernetHeader->xSourceAddress.ucBytes, ucSource, 'A', ':' );
                FreeRTOS_EUI48_ntop( pxEthernetHeader->xDestinationAddress.ucBytes, ucDestination, 'A', ':' );

                FreeRTOS_debug_printf( ( "Invalid target MAC: dropping frame from: %s to: %s", ucSource, ucDestination ) );
            #endif /* if ( ( ipconfigHAS_DEBUG_PRINTF == 1 ) && defined( FreeRTOS_debug_printf ) ) */
            vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
            /* Not sure if a trace is required.  The stack did not want this message */
        }
    }
    else
    {
        #if ( ( ipconfigHAS_DEBUG_PRINTF == 1 ) && defined( FreeRTOS_debug_printf ) )
            FreeRTOS_debug_printf( ( "No Buffer Available: dropping incoming frame!!" ) );
        #endif


        /* No buffer available to receive this message */
        iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER();
    }
}

/*
 *  This function is called from prvEMACHandlerTask.
 *  It iterates over the packet (packet may be spread across multiple buffers),
 *  copies it into a single buffer descriptor for IP task to process.
 */
void EMACReceive(hdkif_t *hdkif)
{

    rxch_t *rxch_int;
    volatile emac_rx_bd_t *curr_bd, *curr_tail, *last_bd;
    volatile uint32 curr_len;

    /* The receive structure that holds data about a particular receive channel */
    rxch_int = &(hdkif->rxchptr);

    /* Get the buffer descriptors which contain the earliest filled data */
    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
    curr_bd = rxch_int->active_head;
    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
    last_bd = rxch_int->active_tail;

    /**
    * Process the descriptors as long as data is available
    * when the DMA is receiving data, SOP flag will be set
    */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
    while((curr_bd->flags_pktlen & EMAC_BUF_DESC_SOP) == EMAC_BUF_DESC_SOP)
    {

        /* Start processing once the packet is loaded */
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
        if((curr_bd->flags_pktlen & EMAC_BUF_DESC_OWNER) != EMAC_BUF_DESC_OWNER)
        {

            /* this bd chain will be freed after processing */
            /*SAFETYMCUSW 71 S MR:17.6 <APPROVED> "Assigned pointer value has required scope." */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            rxch_int->free_head = curr_bd;

            /* Get the total length of the packet. curr_bd points to the start
            * of the packet.
            */

            /*
            * The loop runs till it reaches the end of the packet.
            */
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */

            /* this handles the case of one packet being spread across multiple buffers*/

            /* allocate a buffer of size equal to packet size */
            NetworkBufferDescriptor_t * pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( (curr_bd->flags_pktlen & 0x0000FFFF) , 0 );
            pxBufferDescriptor->xDataLength = (curr_bd->flags_pktlen & 0x0000FFFF);
            curr_len=0;
            while((curr_bd->flags_pktlen & EMAC_BUF_DESC_EOP)!= EMAC_BUF_DESC_EOP)
            {

                ( void ) memcpy ( curr_len + pxBufferDescriptor->pucEthernetBuffer,
                                 (uint8_t *)curr_bd->bufptr,
                                 (curr_bd->bufoff_len & 0x0000FFFF) );
                curr_len+=(curr_bd->bufoff_len & 0x0000FFFF);
                /*Update the flags for the descriptor again and the length of the buffer*/
                /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
                curr_bd->flags_pktlen = (uint32)EMAC_BUF_DESC_OWNER;
                /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
                curr_bd->bufoff_len = (uint32)MAX_TRANSFER_UNIT;
                /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
                last_bd = curr_bd;
                /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
                curr_bd = curr_bd->next;


            }

            /* Updating the last descriptor (which contained the EOP flag) */
            ( void ) memcpy ( curr_len + pxBufferDescriptor->pucEthernetBuffer,
                             (uint8_t *)curr_bd->bufptr,
                             (curr_bd->bufoff_len & 0x0000FFFF) );

            prvProcessFrame(pxBufferDescriptor);

            /* Updating the last descriptor (which contained the EOP flag) */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */

            curr_bd->flags_pktlen = (uint32)EMAC_BUF_DESC_OWNER;

            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            curr_bd->bufoff_len = (uint32)MAX_TRANSFER_UNIT;
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            last_bd = curr_bd;
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            curr_bd = curr_bd->next;

            /* Acknowledge that this packet is processed */
            /*SAFETYMCUSW 439 S MR:11.3 <APPROVED> "Address stored in pointer is passed as as an int parameter. - Advisory as per MISRA" */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            EMACRxCPWrite(hdkif->emac_base, (uint32)EMAC_CHANNELNUMBER, (uint32)last_bd);

            /* The next buffer descriptor is the new head of the linked list. */
            /*SAFETYMCUSW 71 S MR:17.6 <APPROVED> "Assigned pointer value has required scope." */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            rxch_int->active_head = curr_bd;

            /* The processed descriptor is now the tail of the linked list. */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            curr_tail = rxch_int->active_tail;
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            curr_tail->next = rxch_int->free_head;

            /* The last element in the already processed Rx descriptor chain is now the end of list. */
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            last_bd->next = NULL;

            /**
            * Check if the reception has ended. If the EOQ flag is set, the NULL
            * Pointer is taken by the DMA engine. So we need to write the RX HDP
            * with the next descriptor.
            */
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            if((curr_tail->flags_pktlen & EMAC_BUF_DESC_EOQ) == EMAC_BUF_DESC_EOQ)
            {
                /*SAFETYMCUSW 439 S MR:11.3 <APPROVED> "Address stored in pointer is passed as as an int parameter. - Advisory as per MISRA" */
                /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
                EMACRxHdrDescPtrWrite(hdkif->emac_base, (uint32)(rxch_int->free_head), (uint32)EMAC_CHANNELNUMBER);
            }

            /*SAFETYMCUSW 71 S MR:17.6 <APPROVED> "Assigned pointer value has required scope." */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are assigned in this driver" */
            rxch_int->free_head  = curr_bd;
            rxch_int->active_tail = last_bd;
        }
    }
}

/*
 * This function is called from the EMAC RX Interrupt Handler.
 * it is responsible to notify the prvEMACHandlerTask whenever
 * a packet is received.
 */
void RXTaskNotify()
{
    BaseType_t needsToYield = FALSE;
    configASSERT(receiveTaskHandle != NULL);
    vTaskNotifyGiveFromISR( receiveTaskHandle, &needsToYield );
    portYIELD_FROM_ISR( needsToYield );
}

