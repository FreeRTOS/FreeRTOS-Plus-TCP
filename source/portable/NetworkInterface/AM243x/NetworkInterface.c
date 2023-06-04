/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_DNS.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include <drivers/udma/udma_priv.h>
#include <drivers/udma.h>
#include <enet.h>
#include <networking/enet/core/include/per/cpsw.h>
#include <networking/enet/utils/include/enet_appmemutils_cfg.h>
#include <networking/enet/utils/include/enet_apputils.h>
#include <networking/enet/utils/include/enet_appmemutils.h>
#include <networking/enet/utils/include/enet_appboardutils.h>
#include <networking/enet/utils/include/enet_appsoc.h>
#include <networking/enet/utils/include/enet_apprm.h>

#include "Enet_NetIF.h"

/*-----------------------------------------------------------*/

BaseType_t xAM243x_Eth_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface );

static BaseType_t xAM243x_Eth_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                     NetworkBufferDescriptor_t * const pxDescriptor,
                                                     BaseType_t xReleaseAfterSend );

static BaseType_t xAM243x_Eth_GetPhyLinkStatus( NetworkInterface_t * pxInterface );

NetworkInterface_t * pxAM243x_Eth_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                          NetworkInterface_t * pxInterface );

/*-----------------------------------------------------------*/

/* ENET config macros */

#define ENET_SYSCFG_NETIF_COUNT                     (1U)
#define ETH_MAX_PACKET_SIZE        ( ( uint32_t ) 1536U ) 

/*-----------------------------------------------------------*/

BaseType_t xEnetDriver_Opened = pdFALSE;

/*-----------------------------------------------------------*/

#if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 1 )

/* Do not call the following function directly. It is there for downward compatibility.
 * The function FreeRTOS_IPInit() will call it to initialice the interface and end-point
 * objects.  See the description in FreeRTOS_Routing.h. */
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface )
    {
        NULL
    }

#endif
/*-----------------------------------------------------------*/

/* Uncomment this in case BufferAllocation_1.c is used. */

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    // TODO: check alignment and section where this memory block should be placed. Also,
    // check if ETH_MAX_PACKET_SIZE appropriate.
    static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * ETH_MAX_PACKET_SIZE ] __attribute__( ( aligned( 32 ) ) );
    uint8_t * ucRAMBuffer = ucNetworkPackets;
    uint32_t ul;

    for( ul = 0; ul < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ul++ )
    {
        pxNetworkBuffers[ ul ].pucEthernetBuffer = ucRAMBuffer + ipBUFFER_PADDING;
        *( ( unsigned * ) ucRAMBuffer ) = ( unsigned ) ( &( pxNetworkBuffers[ ul ] ) );
        ucRAMBuffer += ETH_MAX_PACKET_SIZE;
    }
}

NetworkInterface_t * pxAM243x_Eth_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                          NetworkInterface_t * pxInterface )
{

    NetworkInterface_t * pxRetInterface = NULL;
    static char pcName[ENET_SYSCFG_NETIF_COUNT][ 8 ];
    static xNetIFArgs uxNetIFArgs[ENET_SYSCFG_NETIF_COUNT];

    if(xEMACIndex < ENET_SYSCFG_NETIF_COUNT)
    {
// TODO: Handle ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
// #if ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
//         const uint32_t checksum_offload_flags = (NETIF_CHECKSUM_GEN_UDP | NETIF_CHECKSUM_GEN_TCP | NETIF_CHECKSUM_CHECK_TCP | NETIF_CHECKSUM_CHECK_UDP);
//         const uint32_t checksum_flags = (NETIF_CHECKSUM_ENABLE_ALL & ~checksum_offload_flags);
// #endif     

        snprintf( pcName[xEMACIndex], sizeof( pcName[xEMACIndex] ), "eth%ld", xEMACIndex );
        uxNetIFArgs[xEMACIndex].xNetIFID = xEMACIndex;

        memset( pxInterface, '\0', sizeof( *pxInterface ) );
        pxInterface->pcName = pcName[xEMACIndex];                    /* Interface name */
        pxInterface->pvArgument = ( void * ) &uxNetIFArgs[xEMACIndex]; 
        pxInterface->pfInitialise = xAM243x_Eth_NetworkInterfaceInitialise;
        pxInterface->pfOutput = xAM243x_Eth_NetworkInterfaceOutput;
        pxInterface->pfGetPhyLinkStatus = xAM243x_Eth_GetPhyLinkStatus;

        FreeRTOS_AddNetworkInterface( pxInterface );

        pxRetInterface = pxInterface;

        // TODO: Check if its required to set a default netif wrt. +TCP stack
        // if(xEMACIndex == ENET_SYSCFG_DEFAULT_NETIF_IDX)
        // {
        //     netif_set_default(&gNetif[xEMACIndex]);
        // }

// TODO: Handle ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
// #if ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
//        NETIF_SET_CHECKSUM_CTRL(&gNetif[xEMACIndex], checksum_flags);
// #endif

    }
    else
    {
        FreeRTOS_printf(("ERROR: xEMACIndex is out of valid range!\r\n"));
        configASSERT(FALSE);
    }

    return pxRetInterface;
}
/*-----------------------------------------------------------*/

BaseType_t xAM243x_Eth_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    BaseType_t xRetVal = pdFALSE;

    if(xEnetDriver_Opened == pdFALSE)
    {
        xEnetDriverHandle xIFHandle;
        xIFHandle = FreeRTOSTCPEnet_open(pxInterface);

        if(xIFHandle != NULL)
        {
            xEnetDriver_Opened = pdTRUE;
            xRetVal = pdTRUE;
        }
    }

    return xRetVal;

}

static void prvPassEthMessages( NetworkBufferDescriptor_t * pxDescriptor )
{
    IPStackEvent_t xRxEvent;

    xRxEvent.eEventType = eNetworkRxEvent;
    xRxEvent.pvData = ( void * ) pxDescriptor;

    if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 1000 ) != pdPASS )
    {
        /* The buffer could not be sent to the stack so must be released again.
         * This is a deferred handler task, not a real interrupt, so it is ok to
         * use the task level function here. */
        #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
            {
                do
                {
                    NetworkBufferDescriptor_t * pxNext = pxDescriptor->pxNextBuffer;
                    vReleaseNetworkBufferAndDescriptor( pxDescriptor );
                    pxDescriptor = pxNext;
                } while( pxDescriptor != NULL );
            }
        #else
            {
                vReleaseNetworkBufferAndDescriptor( pxDescriptor );
            }
        #endif /* ipconfigUSE_LINKED_RX_MESSAGES */
        iptraceETHERNET_RX_EVENT_LOST();
        FreeRTOS_printf( ( "prvPassEthMessages: Can not queue return packet!\n" ) );
    }
    else
    {
        iptraceNETWORK_INTERFACE_RECEIVE();
    }
}

void AM243x_Eth_NetworkInterfaceInput(EnetNetIF_RxObj *rx,
                       Enet_MacPort rxPortNum,
                       NetworkBufferDescriptor_t * pxDescriptor)
{
    xEnetDriverHandle hLwip2Enet = rx->hEnetNetIF;
    NetworkInterface_t * pxInterface;

#if (ENET_ENABLE_PER_CPSW == 1)
    pxInterface = hLwip2Enet->mapRxPort2Netif[ENET_MACPORT_NORM(rxPortNum)];
#else
    /* ToDo: ICSSG doesnot fill rxPortNum correctly, so using the rx->flowIdx to map to netif*/
    pxInterface = hLwip2Enet->mapRxPort2Netif[ENETNETIF_RXFLOW_2_PORTIDX(rx->flowIdx)];
#endif
    configASSERT(pxInterface != NULL);
    pxDescriptor->pxInterface = pxInterface;
    pxDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint( pxInterface, pxDescriptor->pucEthernetBuffer );
    prvPassEthMessages(pxDescriptor);
}

static BaseType_t xAM243x_Eth_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                     NetworkBufferDescriptor_t * const pxDescriptor,
                                                     BaseType_t xReleaseAfterSend )
{
    return pdFALSE;
}

static BaseType_t xAM243x_Eth_GetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    return pdFALSE;
}