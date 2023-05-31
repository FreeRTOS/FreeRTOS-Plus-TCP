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

static void EnetNetIF_submitRxPktQ(EnetNetIF_RxObj *rx);

static void EnetNetIF_processRxUnusedQ(EnetNetIF_RxObj *rx,
                                       EnetDma_PktQ *unUsedQ);

static void EnetNetIF_submitRxPackets(EnetNetIF_RxObj *rx,
                                      EnetDma_PktQ *pSubmitQ);

static xEnetDriverHandle EnetNetif_getObj(void)
{
    uintptr_t key = EnetOsal_disableAllIntr();

    xEnetDriverHandle hEnet = &gEnetDriverObj;

	EnetOsal_restoreAllIntr(key);

    return hEnet;
}

static void EnetNetIF_notifyTxPackets(void *cbArg)
{
    EnetNetIF_TxHandle hTxEnet = (EnetNetIF_TxHandle)cbArg;
    xEnetDriverHandle hEnet = hTxEnet->hEnetNetIF;

    /* do not post events if init not done or shutdown in progress */
    if ((hEnet->initDone) && (hEnet->txPktNotify.cbFxn != NULL))
    {
        /* Notify Callbacks to post event/semephore */
        hEnet->txPktNotify.cbFxn(hEnet->txPktNotify.cbArg);
    }
}

static void EnetNetIF_notifyRxPackets(void *cbArg)
{
    EnetNetIF_RxHandle hRxEnet = (EnetNetIF_RxHandle)cbArg;
    xEnetDriverHandle hEnet = hRxEnet->hEnetNetIF;

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
                                  EnetNetIF_AppIf_GetHandleNetifInfo *outArgs)
{
    (void) pxInterface;

    outArgs->numRxChannels = ENET_SYSCFG_RX_FLOWS_NUM;
    outArgs->numTxChannels = ENET_SYSCFG_TX_CHANNELS_NUM;
    outArgs->isDirected = false;
}

static void EnetNetIFAppCb_getEnetIFInstInfo(EnetNetIF_AppIf_GetEnetIFInstInfo *outArgs)
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
                                    EnetNetIF_AppIf_GetEnetIFInstInfo *appInfo)
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

static EnetNetIF_TxHandle EnetNetIF_initTxObj(uint32_t txCh,
                                              xEnetDriverHandle hEnet)
{
    EnetNetIF_TxHandle hTxHandle;
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
        hEnet->tx[txCh].hEnetNetIF = hEnet;

        hTxHandle = &hEnet->tx[txCh];
    }
    return hTxHandle;
}

static void EnetNetIF_mapNetif2Tx(NetworkInterface_t * pxInterface,
                        bool isDirected,
                        EnetNetIF_TxHandle hTxEnet,
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

static EnetNetIF_RxHandle EnetNetIF_initRxObj(uint32_t rxCh,
                                              xEnetDriverHandle hEnet)
{
    EnetNetIF_RxHandle hRxHandle;
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
        hEnet->rx[rxCh].hEnetNetIF = hEnet;

        hRxHandle = &hEnet->rx[rxCh];
    }

    return hRxHandle;
}

static void EnetNetIF_mapNetif2Rx(NetworkInterface_t * pxInterface,
                        bool isDirected,
                        EnetNetIF_RxHandle hRxEnet,
                        xEnetDriverHandle hEnet)
{
    BaseType_t xNetIFNum = *( (uint32_t *) pxInterface->pvArgument);

    configASSERT(xNetIFNum < ENET_SYSCFG_NETIF_COUNT);

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

static void EnetNetIF_processRxUnusedQ(EnetNetIF_RxObj *rx,
                                       EnetDma_PktQ *unUsedQ)
{
    EnetDma_Pkt *pDmaPacket;

    pDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(unUsedQ);
    while (pDmaPacket != NULL)
    {
        /* Get the full PBUF packet that needs to be returned to the rx.freePktInfoQ */
        struct pbuf* hPbufPacket = (struct pbuf *)pDmaPacket->appPriv;
        if (hPbufPacket)
        {
            /* Put packet info into free Q as we have removed the Pbuf buffers
             * from the it */
            EnetQueue_enq(&rx->freePktInfoQ, &pDmaPacket->node);
            // TODO update stats macro LWIP2ENETSTATS_ADDONE(&rx->stats.freeAppPktEnq);

            pDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(unUsedQ);
        }
        else
        {
            /* should never happen as this is received from HW */
            configASSERT(FALSE);
        }
    }
}

static void EnetNetIF_submitRxPackets(EnetNetIF_RxObj *rx,
                                      EnetDma_PktQ *pSubmitQ)
{
    int32_t retVal;

    retVal = EnetDma_submitRxPktQ(rx->hFlow, pSubmitQ);
    if (ENET_SOK != retVal)
    {
		FreeRTOS_printf(("EnetDma_submitRxPktQ: failed to submit pkts: %d\n",
                        retVal));
    }

    if (EnetQueue_getQCount(pSubmitQ))
    {
        /* Copy unused packets to back to readyQ */
        EnetNetIF_processRxUnusedQ(rx, pSubmitQ);
    }
}

/*
 * Enqueue a new packet and make sure that buffer descriptors are properly linked.
 * NOTE: Not thread safe
 */
static void EnetNetIF_submitRxPktQ(EnetNetIF_RxObj *rx)
{
    EnetDma_PktQ resubmitPktQ;
    struct pbuf* hPbufPacket;
    EnetDma_Pkt *pCurrDmaPacket;
    uint32_t bufSize;
    xEnetDriverHandle hEnet = rx->hEnetNetIF;

    EnetQueue_initQ(&resubmitPktQ);

    /*
     * Fill in as many packets as we can with new PBUF buffers so they can be
     * returned to the stack to be filled in.
     */
    pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&rx->freePktInfoQ);

    while (NULL != pCurrDmaPacket)
    {
        hPbufPacket = (struct pbuf*)pCurrDmaPacket->appPriv;
        if (hPbufPacket)
        {
            // TODO: deal with planned RX buffer allocation scheme for FR+TCP
            // LwipifEnetAppIf_custom_rx_pbuf* my_pbuf  = (LwipifEnetAppIf_custom_rx_pbuf*)hPbufPacket;

            // my_pbuf->p.custom_free_function = LwipifEnetAppCb_pbuf_free_custom;
            // my_pbuf->pktInfoMem         = pCurrDmaPacket;
            // my_pbuf->freePktInfoQ         = &rx->freePktInfoQ;
            // my_pbuf->p.pbuf.flags |= PBUF_FLAG_IS_CUSTOM;

            // bufSize = ENET_UTILS_ALIGN(hEnet->appInfo.hostPortRxMtu, ENETDMA_CACHELINE_ALIGNMENT);
            // hPbufPacket = pbuf_alloced_custom(PBUF_RAW, bufSize, PBUF_POOL, &my_pbuf->p, pCurrDmaPacket->sgList.list[0].bufPtr, pCurrDmaPacket->sgList.list[0].segmentAllocLen);

            // LWIP2ENETSTATS_ADDONE(&rx->stats.freePbufPktDeq);
            // LWIP2ENETSTATS_ADDONE(&rx->stats.freeAppPktDeq);

            EnetQueue_enq(&resubmitPktQ, &pCurrDmaPacket->node);

            pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&rx->freePktInfoQ);
        }
        else
        {
            EnetQueue_enq(&rx->freePktInfoQ, &pCurrDmaPacket->node);
            break;
        }
    }

    /*
     * Return the same DMA packets back to the DMA channel (but now
     * associated with a new PBM Packet and buffer)
     */
    if (EnetQueue_getQCount(&resubmitPktQ))
    {
        EnetNetIF_submitRxPackets(rx, &resubmitPktQ);
    }
}

static int32_t EnetNetIF_startRxTx(xEnetDriverHandle hEnet)
{
    int32_t status = ENET_SOK;
    uint32_t i;

    for(i = 0U; i< hEnet->numRxChannels; i++)
    {
        configASSERT(NULL != hEnet->rx[i].hFlow);
    }

    for(i = 0U; i< hEnet->numTxChannels; i++)
    {
        configASSERT(NULL != hEnet->tx[i].hCh);
        status = EnetDma_enableTxEvent(hEnet->tx[i].hCh);
    }

    for(i = 0U; i< hEnet->numRxChannels; i++)
    {
        /* Submit all allocated packets to DMA so it can use for packet RX */
        EnetNetIF_submitRxPktQ(&hEnet->rx[i]);
    }

    return status;
}


xEnetDriverHandle FreeRTOSTCPEnet_open(NetworkInterface_t * pxInterface)
{
 
    xEnetDriverHandle hEnet;
    EnetNetIF_TxHandle hTxEnet;
    EnetNetIF_RxHandle hRxEnet;
    EnetNetIF_AppIf_GetHandleNetifInfo netifInfo;
    int32_t status;
    uint32_t i;
    BaseType_t xNetIFNum;
    NetworkEndPoint_t * pxEndPoint;

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
        EnetNetIF_mapNetif2Tx(pxInterface, netifInfo.isDirected, hTxEnet, hEnet);
    }

    for(i=0U; i < netifInfo.numRxChannels; i++)
    {
        hRxEnet = EnetNetIF_initRxObj(i, hEnet);
        EnetNetIF_mapNetif2Rx(pxInterface, netifInfo.isDirected, hRxEnet, hEnet);
    }
    // /* Updating the netif params */
    // EnetUtils_copyMacAddr(netif->hwaddr ,&hEnet->macAddr[netif->num][0U]);
    // netif->hwaddr_len = ENET_MAC_ADDR_LEN;
    // netif->state = (void *)hEnet;

    xNetIFNum = *( (uint32_t *) pxInterface->pvArgument);
    configASSERT(xNetIFNum < ENET_SYSCFG_NETIF_COUNT);
    
    pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );

    if( pxEndPoint != NULL && xNetIFNum < ENET_SYSCFG_NETIF_COUNT )
    {
        EnetUtils_copyMacAddr( pxEndPoint->xMACAddress.ucBytes, &hEnet->macAddr[xNetIFNum][0U]);
    }
    else
    {
        configASSERT(pdFALSE);
    }
    hEnet->pxInterface[xNetIFNum] = pxInterface;

    /* DMA handles are availablw now, so starting the tasks and completing the initialization of lwipif*/
    if(hEnet->initDone == false)
    {
        status = EnetNetIF_startRxTx(hEnet);
        if (status != ENET_SOK)
        {
            FreeRTOS_printf(("Failed to start the tasks: %d\n", status));
        }

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

        hEnet->initDone = TRUE;
    }


    // TODO: Wait till link is up before returing, because if the open() returns,
    // the IP-task will start and send packets immediately
    return hEnet;

}
