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

/**
 * Enet device specific header files
 */

#include <kernel/nortos/dpl/common/printf.h>

#include "ti_enet_config.h"

#include <enet_appmemutils.h>
#include <enet_cfg.h>
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
#include <networking/enet/core/include/core/enet_utils.h>

#include "Enet_NetIF.h"
#include "Enet_NetIFQueue.h"

#include "NetworkBufferManagement.h"

/* ========================================================================== */
/*                           Macros & Typedefs                                */
/* ========================================================================== */
#define ENETLWIP_PACKET_POLL_PERIOD_US (1000U)

#define ENETLWIP_APP_POLL_PERIOD       (500U)
/*! \brief RX packet task stack size */
#define LWIPIF_RX_PACKET_TASK_STACK    (1024U)

/*! \brief TX packet task stack size */
#define LWIPIF_TX_PACKET_TASK_STACK    (1024U)

/*! \brief Links status poll task stack size */
#if (_DEBUG_ == 1)
#define LWIPIF_POLL_TASK_STACK         (3072U)
#else
#define LWIPIF_POLL_TASK_STACK         (1024U)
#endif

#define OS_TASKPRIHIGH              8U

#define LWIPIF_RX_PACKET_TASK_PRI      (OS_TASKPRIHIGH)

#define LWIPIF_TX_PACKET_TASK_PRI      (OS_TASKPRIHIGH)

#define LWIP_POLL_TASK_PRI             (OS_TASKPRIHIGH - 1U)

#define ENET_SYSCFG_NETIF_COUNT                     (1U)

#define ENET_SYSCFG_DEFAULT_NETIF_IDX              (0U)

#define NETIF_INST_ID0           (0U)

NetBufNode gFreeTxNetBufArr[ENET_SYSCFG_TOTAL_NUM_TX_PKT];

static void EnetNetIF_notifyTxPackets(void *cbArg);

static xEnetDriverObj gEnetDriverObj = { {{0}} };

static xEnetDriverHandle EnetNetif_getObj(void)
{
    uintptr_t key = EnetOsal_disableAllIntr();

    xEnetDriverHandle hEnet = &gEnetDriverObj;

	EnetOsal_restoreAllIntr(key);

    return hEnet;
}

static void EnetNetIF_notifyTxPackets(void *cbArg)
{
    Enet_Netif_TxHandle hTxEnet = (Enet_Netif_TxHandle)cbArg;
    xEnetDriverHandle hEnet = hTxEnet->hEnet_Netif;

    /* do not post events if init not done or shutdown in progress */
    if ((hEnet->initDone) && (hEnet->txPktNotify.cbFxn != NULL))
    {
        /* Notify Callbacks to post event/semephore */
        hEnet->txPktNotify.cbFxn(hEnet->txPktNotify.cbArg);
    }
}

static void EnetNetIF_notifyRxPackets(void *cbArg)
{
    Enet_Netif_RxHandle hRxEnet = (Enet_Netif_RxHandle)cbArg;
    xEnetDriverHandle hEnet = hRxEnet->hEnet_Netif;

    /* do not post events if init not done or shutdown in progress */
    if (hEnet->initDone)
    {
        for(uint32_t i = 0U; i < hEnet->numRxChannels; i++)
        {
            if (hEnet->rx[i].enabled)
            {
                EnetDma_disableRxEvent(hEnet->rx[i].hFlow);
            }
            if (hEnet->rxPktNotify.cbFxn != NULL)
            {
                hEnet->rxPktNotify.cbFxn(hEnet->rxPktNotify.cbArg);
            }
        }
    }
}

static void EnetNetIFAppCb_getNetifInfo(NetworkInterface_t * pxInterface,
                                  Enet_Netif_AppIf_GetHandleNetifInfo *outArgs)
{
    (void) pxInterface;

    outArgs->numRxChannels = ENET_SYSCFG_RX_FLOWS_NUM;
    outArgs->numTxChannels = ENET_SYSCFG_TX_CHANNELS_NUM;
    outArgs->isDirected = false;
}

static void EnetNetIFAppCb_getEnetIFInstInfo(Enet_Netif_AppIf_GetEnetIFInstInfo *outArgs)
{
    EnetPer_AttachCoreOutArgs attachInfo;
    EnetApp_HandleInfo handleInfo;
    Enet_Type enetType;
    uint32_t instId;

    uint32_t coreId = EnetSoc_getCoreId();


    EnetApp_getEnetInstInfo(&enetType,
                            &instId);

    EnetApp_acquireHandleInfo(enetType, instId, &handleInfo);
    EnetApp_coreAttach(enetType,instId, coreId, &attachInfo);

    outArgs->hEnet         = handleInfo.hEnet;
    outArgs->hostPortRxMtu = attachInfo.rxMtu;
    ENET_UTILS_ARRAY_COPY(outArgs->txMtu, attachInfo.txMtu);
    outArgs->isPortLinkedFxn = &EnetApp_isPortLinked;
	outArgs->timerPeriodUs   = ENETLWIP_PACKET_POLL_PERIOD_US;

    outArgs->maxNumNetif = ENET_SYSCFG_NETIF_COUNT;
    outArgs->numRxChannels = ENET_SYSCFG_RX_FLOWS_NUM;
    outArgs->numTxChannels = ENET_SYSCFG_TX_CHANNELS_NUM;

    outArgs->pFreeTx = gFreeTxNetBufArr;
    outArgs->pFreeTxSize = ENET_SYSCFG_TOTAL_NUM_TX_PKT;
    // LWIP_MEMPOOL_INIT(RX_POOL); // TODO: Replace custom buffer (cbuf) based RX packet allocation with
    // custom pxGetNetworkBufferWithDescriptor which has a separate owner that can be checked
    // to release the packet back to the HW when vReleaseNetworkBufferAndDescriptor is called.


#if ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
    int32_t status;
    /* Confirm HW checksum offload is enabled when LWIP chksum offload is enabled */
        Enet_IoctlPrms prms;
        bool csumOffloadFlg;
        ENET_IOCTL_SET_OUT_ARGS(&prms, &csumOffloadFlg);
        ENET_IOCTL(handleInfo.hEnet,
                   coreId,
                   ENET_HOSTPORT_IS_CSUM_OFFLOAD_ENABLED,
                   &prms,
                   status);
        if (status != ENET_SOK)
        {
            EnetAppUtils_print("() Failed to get checksum offload info: %d\r\n", status);
        }

        configASSERT(true == csumOffloadFlg);
#endif
}

static void EnetNetIF_saveAppIfCfg(xEnetDriverHandle hEnet,
                                    Enet_Netif_AppIf_GetEnetIFInstInfo *appInfo)
{
    hEnet->numRxChannels = appInfo->numRxChannels;
    hEnet->numTxChannels = appInfo->numTxChannels;
}

static void  EnetNetIF_initGetTxHandleInArgs(xEnetDriverHandle hEnet,
                                             uint32_t chNum,
                                             EnetNetIFAppIf_GetTxHandleInArgs *inArgs)
{
    inArgs->cbArg      = &hEnet->tx[chNum];
    inArgs->notifyCb   = &EnetNetIF_notifyTxPackets;
    inArgs->chId       = chNum;
    inArgs->pktInfoQ   = &hEnet->tx[chNum].freePktInfoQ;
}

static void EnetNetIF_initGetRxHandleInArgs(xEnetDriverHandle hEnet,
                                            uint32_t chNum,
                                            EnetNetIFAppIf_GetRxHandleInArgs *inArgs)
{
    inArgs->cbArg      = &hEnet->rx[chNum];
    inArgs->notifyCb   = &EnetNetIF_notifyRxPackets;
    inArgs->chId       = chNum;
    inArgs->pktInfoQ   = &hEnet->rx[chNum].freePktInfoQ;
}

static void EnetNetIFAppCb_getTxHandleInfo(EnetNetIFAppIf_GetTxHandleInArgs *inArgs,
                                    EnetNetIFAppIf_TxHandleInfo *outArgs)
{
    Enet_Type enetType;
    uint32_t instId, i;
    EnetDma_Pkt *pPktInfo;
    EnetApp_HandleInfo handleInfo;
    EnetApp_GetTxDmaHandleOutArgs  txChInfo;
    EnetApp_GetDmaHandleInArgs     txInArgs;

    EnetApp_getEnetInstInfo(&enetType,
                            &instId);
    EnetApp_acquireHandleInfo(enetType, instId, &handleInfo);

    /* Open TX channel */
    txInArgs.cbArg     = inArgs->cbArg;
    txInArgs.notifyCb  = inArgs->notifyCb;

    EnetApp_getTxDmaHandle(inArgs->chId,
                          &txInArgs,
                          &txChInfo);

    outArgs->hTxChannel = txChInfo.hTxCh;
    outArgs->txChNum = txChInfo.txChNum;
    outArgs->numPackets = txChInfo.maxNumTxPkts;
    outArgs->disableEvent = true;

    /* Initialize the DMA free queue */
    EnetQueue_initQ(inArgs->pktInfoQ);

    for (i = 0U; i < txChInfo.maxNumTxPkts; i++)
    {
        /* Initialize Pkt info Q from allocated memory */
        pPktInfo = EnetMem_allocEthPktInfoMem(&inArgs->cbArg,
                                              ENETDMA_CACHELINE_ALIGNMENT);

        configASSERT(pPktInfo != NULL);
        ENET_UTILS_SET_PKT_APP_STATE(&pPktInfo->pktState, ENET_PKTSTATE_APP_WITH_FREEQ);
        EnetQueue_enq(inArgs->pktInfoQ, &pPktInfo->node);

    }

}

static Enet_Netif_TxHandle EnetNetIF_initTxObj(uint32_t txCh,
                                              xEnetDriverHandle hEnet)
{
    Enet_Netif_TxHandle hTxHandle;
    EnetNetIFAppIf_GetTxHandleInArgs inArgs;
    EnetNetIFAppIf_TxHandleInfo outArgs;

    if(hEnet->tx[txCh].enabled == true)
    {
        hEnet->tx[txCh].refCount++;
        hTxHandle = &hEnet->tx[txCh];
    }
    else{

        EnetNetIF_initGetTxHandleInArgs(hEnet, txCh, &inArgs);
        EnetNetIFAppCb_getTxHandleInfo(&inArgs, &outArgs);

        hEnet->tx[txCh].numPackets = outArgs.numPackets;
        hEnet->tx[txCh].hCh = outArgs.hTxChannel;
        hEnet->tx[txCh].chNum = outArgs.txChNum;
        configASSERT(hEnet->tx[txCh].hCh != NULL);

        hEnet->tx[txCh].disableEvent = outArgs.disableEvent;

        hEnet->tx[txCh].stats.freeAppPktEnq = outArgs.numPackets;
        hEnet->allocPktInfo += outArgs.numPackets;

        /* Initialize the TX pbuf queues */
        NetBufQueue_init(&hEnet->tx[txCh].readyPbufQ);
        NetBufQueue_init(&hEnet->tx[txCh].unusedPbufQ);

        hEnet->tx[txCh].refCount = 1U;
        hEnet->tx[txCh].enabled = true;
        hEnet->tx[txCh].hEnet_Netif = hEnet;

        hTxHandle = &hEnet->tx[txCh];
    }
    return hTxHandle;
}

static void Enet_Netif_mapNetif2Tx(NetworkInterface_t * pxInterface,
                        bool isDirected,
                        Enet_Netif_TxHandle hTxEnet,
                        xEnetDriverHandle hEnet)
{
    BaseType_t xNetIFNum = *( (uint32_t *) pxInterface->pvArgument);

    configASSERT(xNetIFNum < ENET_SYSCFG_NETIF_COUNT);

    hEnet->mapNetif2Tx[xNetIFNum] = hTxEnet;
    if(isDirected)
    {
        hEnet->mapNetif2TxPortNum[xNetIFNum] = ENET_MACPORT_DENORM(xNetIFNum);
    }
}

void EnetNetIFAppCb_getRxHandleInfo(EnetNetIFAppIf_GetRxHandleInArgs *inArgs,
                                     EnetNetIFAppIf_RxHandleInfo *outArgs)
{
    Enet_Type enetType;
    uint32_t instId, i;
    EnetDma_Pkt *pPktInfo;
    // TODO: remove
    // LwipifEnetAppIf_custom_rx_pbuf* cPbuf;
    struct pbuf* hPbufPacket;
    int32_t status;
    bool useRingMon = false;
    EnetApp_HandleInfo handleInfo;
    EnetPer_AttachCoreOutArgs attachInfo;
    uint32_t coreId          = EnetSoc_getCoreId();
    EnetApp_GetRxDmaHandleOutArgs  rxChInfo;
    EnetApp_GetDmaHandleInArgs     rxInArgs;

    EnetApp_getEnetInstInfo(&enetType,
                            &instId);
    EnetApp_acquireHandleInfo(enetType, instId, &handleInfo);
    EnetApp_coreAttach(enetType,instId, coreId, &attachInfo);

    /* Open RX channel */
    rxInArgs.cbArg     = inArgs->cbArg;
    rxInArgs.notifyCb  = inArgs->notifyCb;

    EnetApp_getRxDmaHandle(inArgs->chId,
                          &rxInArgs,
                          &rxChInfo);

    outArgs->rxFlowStartIdx = rxChInfo.rxFlowStartIdx;
    outArgs->rxFlowIdx = rxChInfo.rxFlowIdx;
    outArgs->hRxFlow  = rxChInfo.hRxCh;
    outArgs->numPackets  = rxChInfo.maxNumRxPkts;
    outArgs->disableEvent = !useRingMon;
    if(rxChInfo.macAddressValid)
    {
        EnetUtils_copyMacAddr(&outArgs->macAddr[inArgs->chId][0U], rxChInfo.macAddr);
        EnetAppUtils_print("Host MAC address-%d : ",inArgs->chId);
        EnetAppUtils_printMacAddr(&outArgs->macAddr[inArgs->chId][0U]);
    }

    /* Initialize the DMA free queue */
    EnetQueue_initQ(inArgs->pktInfoQ);

    for (i = 0U; i < rxChInfo.maxNumRxPkts; i++)
    {
        // TODO: Enqueue network buffers to the free queue

        // pPktInfo = EnetMem_allocEthPkt(&inArgs->cbArg,
        //                    ENET_MEM_LARGE_POOL_PKT_SIZE,
        //                    ENETDMA_CACHELINE_ALIGNMENT);
        // EnetAppUtils_assert(pPktInfo != NULL);

        // ENET_UTILS_SET_PKT_APP_STATE(&pPktInfo->pktState, ENET_PKTSTATE_APP_WITH_FREEQ);

        // cPbuf = (LwipifEnetAppIf_custom_rx_pbuf*)LWIP_MEMPOOL_ALLOC(RX_POOL);

        // cPbuf->p.custom_free_function = LwipifEnetAppCb_pbuf_free_custom;
        // cPbuf->pktInfoMem         = pPktInfo;
        // cPbuf->freePktInfoQ         = inArgs->pktInfoQ;
        // cPbuf->p.pbuf.flags |= PBUF_FLAG_IS_CUSTOM;

        // hPbufPacket = pbuf_alloced_custom(PBUF_RAW, ENET_MEM_LARGE_POOL_PKT_SIZE, PBUF_POOL, &cPbuf->p, pPktInfo->sgList.list[0].bufPtr, pPktInfo->sgList.list[0].segmentAllocLen);

        // pPktInfo->appPriv = (void *)hPbufPacket;

        // if (hPbufPacket != NULL)
        // {
        //     EnetAppUtils_assert(hPbufPacket->payload != NULL);
        //     EnetAppUtils_assert(ENET_UTILS_IS_ALIGNED(hPbufPacket->payload, ENETDMA_CACHELINE_ALIGNMENT));

        //     /* Enqueue to the free queue */
		// 	EnetQueue_enq(inArgs->pktInfoQ, &pPktInfo->node);
        // }
        // else
        // {
        //     DebugP_log("ERROR: Pbuf_alloc() failure...exiting!\r\n");
        //     EnetAppUtils_assert(FALSE);
        // }
    }

    if(ENET_SYSCFG_NETIF_COUNT > 1U)
    {
        for(uint32_t i =1U; i<ENET_SYSCFG_NETIF_COUNT; i++)
        {
            /* Allocating another mac addresses for number of netifs supported*/
            status = EnetAppUtils_allocMac(handleInfo.hEnet,
                                        attachInfo.coreKey,
                                        coreId,
                                        &outArgs->macAddr[i][0U]);
            EnetAppUtils_assert(ENET_SOK == status);
            EnetAppUtils_addHostPortEntry(handleInfo.hEnet, coreId,  &outArgs->macAddr[i][0U]);
            EnetAppUtils_print("Host MAC address-%d : ",i);
            EnetAppUtils_printMacAddr(&outArgs->macAddr[i][0U]);
        }
    }
}

static Enet_Netif_RxHandle EnetNetIF_initRxObj(uint32_t rxCh,
                                              xEnetDriverHandle hEnet)
{
    Enet_Netif_RxHandle hRxHandle;
    EnetNetIFAppIf_GetRxHandleInArgs inArgs;
    EnetNetIFAppIf_RxHandleInfo outArgs;

    if(hEnet->rx[rxCh].enabled == true)
    {
        hEnet->rx[rxCh].refCount++;
        hRxHandle = &hEnet->rx[rxCh];
    }
    else{

        EnetNetIF_initGetRxHandleInArgs(hEnet, rxCh, &inArgs);
        EnetNetIFAppCb_getRxHandleInfo(&inArgs, &outArgs);

        hEnet->rx[rxCh].numPackets = outArgs.numPackets;

        hEnet->rx[rxCh].flowIdx     = outArgs.rxFlowIdx;
        hEnet->rx[rxCh].flowStartIdx = outArgs.rxFlowStartIdx;
        hEnet->rx[rxCh].hFlow       = outArgs.hRxFlow;
        configASSERT(hEnet->rx[rxCh].hFlow != NULL);
        hEnet->rx[rxCh].disableEvent = outArgs.disableEvent;

        for (uint32_t i = 0U; i < hEnet->appInfo.maxNumNetif; i++)
        {
            EnetUtils_copyMacAddr(&hEnet->macAddr[i][0U], &outArgs.macAddr[i][0U]);
        }

        hEnet->rx[rxCh].stats.freeAppPktEnq = outArgs.numPackets;
        hEnet->allocPktInfo += outArgs.numPackets;

        hEnet->rx[rxCh].refCount = 1U;
        hEnet->rx[rxCh].enabled = true;
        hEnet->rx[rxCh].hEnet_Netif = hEnet;

        hRxHandle = &hEnet->rx[rxCh];
    }

    return hRxHandle;
}

static void Enet_Netif_mapNetif2Rx(NetworkInterface_t * pxInterface,
                        bool isDirected,
                        Enet_Netif_RxHandle hRxEnet,
                        xEnetDriverHandle hEnet)
{
    BaseType_t xNetIFNum = *( (uint32_t *) pxInterface->pvArgument);

    hEnet->mapNetif2Rx[xNetIFNum] = hRxEnet;
    hEnet->mapRxPort2Netif[xNetIFNum] = pxInterface;
#if (ENET_ENABLE_PER_ICSSG == 1)
    /* ToDo: ICSSG doesnot fill rxPortNum correctly, so using the hRxEnet->flowIdx to map to pxInterface*/
    hEnet->mapRxPort2Netif[LWIP_RXFLOW_2_PORTIDX(hRxEnet->flowIdx)] = pxInterface;
#endif
    /* For non-directed packets, we map both ports to the first pxInterface*/
    if(!isDirected)
    {
        for(uint32_t portIdx = 0U; portIdx < CPSW_STATS_MACPORT_MAX; portIdx++)
        {
            if(portIdx < ENET_CFG_NETIF_MAX)
            {
            hEnet->mapRxPort2Netif[portIdx] = pxInterface;
            }
        }
    }
}


xEnetDriverHandle FreeRTOSTCPEnet_open(NetworkInterface_t * pxInterface)
{
 
    xEnetDriverHandle hEnet;
    Enet_Netif_TxHandle hTxEnet;
    Enet_Netif_RxHandle hRxEnet;
    Enet_Netif_AppIf_GetHandleNetifInfo netifInfo;
    int32_t status;
    uint32_t i;

    hEnet = EnetNetif_getObj();
    if (hEnet->initDone == false)
    {

        /* MCast List is EMPTY */
        hEnet->MCastCnt = 0U;

        /* Init internal bookkeeping fields */
        hEnet->oldMCastCnt = 0U;

        for (i = 0U; i < ENET_CFG_NETIF_MAX; i++)
        {
            hEnet->mapNetif2Rx[i] = NULL;
            hEnet->mapNetif2Tx[i] = NULL;
            hEnet->mapNetif2TxPortNum[i] = ENET_MAC_PORT_INV;
        }

        for (i = 0U; i < CPSW_STATS_MACPORT_MAX; i++)
        {
            hEnet->mapRxPort2Netif[i] = NULL;
        }


        /* First init tasks, semaphores and clocks. This is required because
         * EnetDma event cb ISR can happen immediately after opening rx flow
         * in LwipifEnetAppCb_getHandle and all semaphores, clocks and tasks should
         * be valid at that point
         */

        EnetNetIFAppCb_getEnetIFInstInfo(&hEnet->appInfo);

        /* Save params received from application interface */
        EnetNetIF_saveAppIfCfg(hEnet, &hEnet->appInfo);

        configASSERT(hEnet->appInfo.hEnet != NULL);
        configASSERT(hEnet->appInfo.isPortLinkedFxn != NULL);
        configASSERT(hEnet->appInfo.pFreeTx != NULL);

        NetBufQueue_init_freeQ(hEnet->appInfo.pFreeTx, hEnet->appInfo.pFreeTxSize);


        /* set the print function callback if not null */
        hEnet->print = (Enet_Print) &EnetUtils_printf;
	}

    /* Process netif related parameters*/
    EnetNetIFAppCb_getNetifInfo(pxInterface, &netifInfo);

    for(i=0U; i < netifInfo.numTxChannels; i++)
    {
        hTxEnet = EnetNetIF_initTxObj(i, hEnet);
        Enet_Netif_mapNetif2Tx(pxInterface, netifInfo.isDirected, hTxEnet, hEnet);
    }

    for(i=0U; i < netifInfo.numRxChannels; i++)
    {
        hRxEnet = EnetNetIF_initRxObj(i, hEnet);
        Enet_Netif_mapNetif2Rx(pxInterface, netifInfo.isDirected, hRxEnet, hEnet);
    }
    // /* Updating the netif params */
    // EnetUtils_copyMacAddr(netif->hwaddr ,&hEnet->macAddr[netif->num][0U]);
    // netif->hwaddr_len = ENET_MAC_ADDR_LEN;
    // netif->state = (void *)hEnet;
    // hEnet->netif[netif->num] = netif;

    // /* DMA handles are availablw now, so starting the tasks and completing the initialization of lwipif*/
    // if(hEnet->initDone == false)
    // {
    //     status = Lwip2Enet_startRxTx(hEnet);
    //     if (status != ENET_SOK)
    //     {
    //         Lwip2Enet_print(hEnet,"Failed to start the tasks: %d\n", status);
    //     }

    //     /* Get initial link/interface status from the driver */
    //     hEnet->linkIsUp = hEnet->appInfo.isPortLinkedFxn(hEnet->appInfo.hEnet);

    //     for (i = 0U; i < hEnet->numTxChannels; i++)
    //     {
    //         if (hEnet->tx[i].disableEvent)
    //         {
    //             EnetDma_disableTxEvent(hEnet->tx[i].hCh);
    //         }
    //     }

    //     for (i = 0U; i < hEnet->numRxChannels; i++)
    //     {
    //         if ((hEnet->rx[i].enabled) &&  (hEnet->rx[i].disableEvent))
    //         {
    //             EnetDma_disableRxEvent(hEnet->rx[i].hFlow);
    //         }
    //     }
    //     /* assert if clk period is not valid  */
    //     configASSERT(0U != hEnet->appInfo.timerPeriodUs);
    //     Lwip2Enet_createTimer(hEnet);
    //     // ClockP_start(&hEnet->pacingClkObj);

    //     hEnet->initDone = TRUE;
    // }


    // TODO: Wait till link is up before returing, because if the open() returns,
    // the IP-task will start and send packets immediately
    return hEnet;

}
