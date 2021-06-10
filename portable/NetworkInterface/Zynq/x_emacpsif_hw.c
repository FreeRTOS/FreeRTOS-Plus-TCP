/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* XILINX CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/


/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Routing.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "Zynq/x_emacpsif.h"

extern TaskHandle_t xEMACTaskHandles[ XPAR_XEMACPS_NUM_INSTANCES ];

/*** IMPORTANT: Define PEEP in xemacpsif.h and sys_arch_raw.c
 *** to run it on a PEEP board
 ***/

void setup_isr( xemacpsif_s * xemacpsif )
{
    /*
     * Setup callbacks
     */
    XEmacPs_SetHandler( &xemacpsif->emacps, XEMACPS_HANDLER_DMASEND,
                        ( void * ) emacps_send_handler,
                        ( void * ) xemacpsif );

    XEmacPs_SetHandler( &xemacpsif->emacps, XEMACPS_HANDLER_DMARECV,
                        ( void * ) emacps_recv_handler,
                        ( void * ) xemacpsif );

    XEmacPs_SetHandler( &xemacpsif->emacps, XEMACPS_HANDLER_ERROR,
                        ( void * ) emacps_error_handler,
                        ( void * ) xemacpsif );
}

void start_emacps( xemacpsif_s * xemacps )
{
    /* start the temac */
    XEmacPs_Start( &xemacps->emacps );
}


volatile int error_msg_count = 0;
volatile const char * last_err_msg = "";

struct xERROR_MSG
{
    void * arg;
    u8 Direction;
    u32 ErrorWord;
};

static struct xERROR_MSG xErrorList[ 8 ];
static BaseType_t xErrorHead, xErrorTail;

void emacps_error_handler( void * arg,
                           u8 Direction,
                           u32 ErrorWord )
{
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    xemacpsif_s * xemacpsif;
    BaseType_t xNextHead = xErrorHead;
    BaseType_t xEMACIndex;

    xemacpsif = ( xemacpsif_s * ) ( arg );
    xEMACIndex = xemacpsif->emacps.Config.DeviceId;

    if( ( Direction != XEMACPS_SEND ) || ( ErrorWord != XEMACPS_TXSR_USEDREAD_MASK ) )
    {
        if( ++xNextHead == ( sizeof( xErrorList ) / sizeof( xErrorList[ 0 ] ) ) )
        {
            xNextHead = 0;
        }

        if( xNextHead != xErrorTail )
        {
            xErrorList[ xErrorHead ].arg = arg;
            xErrorList[ xErrorHead ].Direction = Direction;
            xErrorList[ xErrorHead ].ErrorWord = ErrorWord;

            xErrorHead = xNextHead;

            xemacpsif = ( xemacpsif_s * ) ( arg );
            xemacpsif->isr_events |= EMAC_IF_ERR_EVENT;
        }

        if( xEMACTaskHandles[ xEMACIndex ] != NULL )
        {
            vTaskNotifyGiveFromISR( xEMACTaskHandles[ xEMACIndex ], &xHigherPriorityTaskWoken );
        }
    }

    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}

static void emacps_handle_error( void * arg,
                                 u8 Direction,
                                 u32 ErrorWord );

int emacps_check_errors( xemacpsif_s * xemacps )
{
    int xResult;

    ( void ) xemacps;

    if( xErrorHead == xErrorTail )
    {
        xResult = 0;
    }
    else
    {
        xResult = 1;
        emacps_handle_error(
            xErrorList[ xErrorTail ].arg,
            xErrorList[ xErrorTail ].Direction,
            xErrorList[ xErrorTail ].ErrorWord );
    }

    return xResult;
}

static void emacps_handle_error( void * arg,
                                 u8 Direction,
                                 u32 ErrorWord )
{
    xemacpsif_s * xemacpsif;
    XEmacPs * xemacps;
    BaseType_t xEMACIndex;

    xemacpsif = ( xemacpsif_s * ) ( arg );

    xemacps = &xemacpsif->emacps;
    xEMACIndex = xemacps->Config.DeviceId;

    last_err_msg = NULL;

    if( ErrorWord != 0 )
    {
        switch( Direction )
        {
            case XEMACPS_RECV:

                if( ( ErrorWord & XEMACPS_RXSR_HRESPNOK_MASK ) != 0 )
                {
                    last_err_msg = "Receive DMA error";
                    vInitialiseOnIndex( xEMACIndex );
                }

                if( ( ErrorWord & XEMACPS_RXSR_RXOVR_MASK ) != 0 )
                {
                    last_err_msg = "Receive over run";
                    emacps_recv_handler( arg );
                }

                if( ( ErrorWord & XEMACPS_RXSR_BUFFNA_MASK ) != 0 )
                {
                    last_err_msg = "Receive buffer not available";
                    emacps_recv_handler( arg );
                }

                break;

            case XEMACPS_SEND:

                if( ( ErrorWord & XEMACPS_TXSR_HRESPNOK_MASK ) != 0 )
                {
                    last_err_msg = "Transmit DMA error";
                    vInitialiseOnIndex( xEMACIndex );
                }

                if( ( ErrorWord & XEMACPS_TXSR_URUN_MASK ) != 0 )
                {
                    last_err_msg = "Transmit under run";
                    HandleTxErrors( xemacpsif );
                }

                if( ( ErrorWord & XEMACPS_TXSR_BUFEXH_MASK ) != 0 )
                {
                    last_err_msg = "Transmit buffer exhausted";
                    HandleTxErrors( xemacpsif );
                }

                if( ( ErrorWord & XEMACPS_TXSR_RXOVR_MASK ) != 0 )
                {
                    last_err_msg = "Transmit retry excessed limits";
                    HandleTxErrors( xemacpsif );
                }

                if( ( ErrorWord & XEMACPS_TXSR_FRAMERX_MASK ) != 0 )
                {
                    last_err_msg = "Transmit collision";
                    emacps_check_tx( xemacpsif );
                }

                break;
        }
    }

    /* Break on this statement and inspect error_msg if you like */
    if( last_err_msg != NULL )
    {
        error_msg_count++;
        FreeRTOS_printf( ( "emacps_handle_error: %s\n", last_err_msg ) );
    }
}

void HandleTxErrors( xemacpsif_s * xemacpsif )
{
    u32 netctrlreg;

    /*taskENTER_CRITICAL() */
    {
        netctrlreg = XEmacPs_ReadReg( xemacpsif->emacps.Config.BaseAddress,
                                      XEMACPS_NWCTRL_OFFSET );
        netctrlreg = netctrlreg & ( ~XEMACPS_NWCTRL_TXEN_MASK );
        XEmacPs_WriteReg( xemacpsif->emacps.Config.BaseAddress,
                          XEMACPS_NWCTRL_OFFSET, netctrlreg );

        clean_dma_txdescs( xemacpsif );
        netctrlreg = XEmacPs_ReadReg( xemacpsif->emacps.Config.BaseAddress,
                                      XEMACPS_NWCTRL_OFFSET );
        netctrlreg = netctrlreg | ( XEMACPS_NWCTRL_TXEN_MASK );
        XEmacPs_WriteReg( xemacpsif->emacps.Config.BaseAddress,
                          XEMACPS_NWCTRL_OFFSET, netctrlreg );
    }
    /*taskEXIT_CRITICAL( ); */
}
