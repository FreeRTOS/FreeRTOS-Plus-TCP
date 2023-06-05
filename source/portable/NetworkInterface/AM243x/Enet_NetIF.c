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
#include <kernel/dpl/DebugP.h>
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

#include "FreeRTOS.h"

#include "Enet_NetIF.h"
#include "Enet_NetIFQueue.h"

#include "FreeRTOS_Routing.h"
#include "NetworkBufferManagement.h"

/* ========================================================================== */
/*                           Macros & Typedefs                                */
/* ========================================================================== */
#define ENETLWIP_PACKET_POLL_PERIOD_US (1000U)

#define ENETNETIF_APP_POLL_PERIOD       (500U)
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

#define ENETNETIF_RX_PACKET_TASK_PRI      (OS_TASKPRIHIGH)

#define ENETNETIF_TX_PACKET_TASK_PRI      (OS_TASKPRIHIGH)

#define ENETNETIF_POLL_TASK_PRI           (OS_TASKPRIHIGH - 1U)

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

static uint32_t EnetNetIF_prepTxPktQ(EnetNetIF_TxObj *tx,
                                     EnetDma_PktQ *pPktQ);

void AM243x_Eth_NetworkInterfaceInput(EnetNetIF_RxObj *rx,
                       Enet_MacPort rxPortNum,
                       NetworkBufferDescriptor_t * pxDescriptor);

uint8_t gPktRxTaskStack[LWIPIF_RX_PACKET_TASK_STACK] __attribute__ ((aligned(sizeof(long long))));
uint8_t gPktTxTaskStack[LWIPIF_TX_PACKET_TASK_STACK] __attribute__ ((aligned(sizeof(long long))));
uint8_t gPollTaskStack[LWIPIF_POLL_TASK_STACK] __attribute__ ((aligned(sizeof(long long))));

/*!* Handle to Rx semaphore, on which the rxTask awaits for notification
* of used packets available.
*/
SemaphoreP_Object rxPktSem;
/*!* Handle to Tx semaphore, on which the txTask awaits for notification
* of used packets available.
*/
SemaphoreP_Object txPktSem;

/*!* Handle to Polling task semaphore, on which the pollTask awaits for notification
* of used packets available.
*/
SemaphoreP_Object pollSem;

/*! Handle to polling task whose job is to retrieve packets consumed by the hardware and
*  give them to the stack */
TaskP_Object pollTask;
/*
 * Clock handle for triggering the packet Rx notify
 */
ClockP_Object pollLinkClkObj;

/*
 * Handle to counting shutdown semaphore, which all subtasks created in the
 * open function must post before the close operation can complete.
 */
SemaphoreP_Object shutDownSemObj;
/** Boolean to indicate shutDownFlag status of translation layer.*/
volatile bool shutDownFlag;

/*!
* Handle to Rx task, whose job it is to receive packets used by the hardware
* and give them to the stack, and return freed packets back to the hardware.
*/
    TaskP_Object rxTask;
/*! Handle to Tx task whose job is to retrieve packets consumed by the hardware and
*  give them to the stack */
    TaskP_Object txTask;
/*! Handle to polling task whose job is to retrieve packets consumed by the hardware and
*  give them to the stack */
    TaskP_Object pollTask;

uint8_t * getEnetAppBuffMem(uint32_t req_Size)
{
    (void) req_Size;

    NetworkBufferDescriptor_t * pxReturn = pxGetNetworkBufferWithDescriptor_RX(1536U); 
    return pxReturn->pucEthernetBuffer;

}

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
    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
    BaseType_t xNetIFNum;

    configASSERT(pxNetIFArgs != NULL);
    xNetIFNum = pxNetIFArgs->xNetIFID;

    configASSERT(xNetIFNum < ENET_SYSCFG_NETIF_COUNT);

    hEnet->mapNetif2Tx[xNetIFNum] = hTxEnet;
    if(isDirected)
    {
        hEnet->mapNetif2TxPortNum[xNetIFNum] = ENET_MACPORT_DENORM(xNetIFNum);
    }
}

void EnetNetIF_AppCb_ReleaseNetDescriptor(NetworkBufferDescriptor_t * const pxNetworkBuffer)
{
    EnetNetIF_AppIf_CustomNetBuf * xCNetBuf = (EnetNetIF_AppIf_CustomNetBuf *) pxNetworkBuffer;
    uint32_t key = HwiP_disable();

    EnetQueue_enq(xCNetBuf->freePktInfoQ, &xCNetBuf->pktInfoMem->node);

    HwiP_restore(key);
}

void EnetNetIFAppCb_getRxHandleInfo(EnetNetIFAppIf_GetRxHandleInArgs *inArgs,
                                     EnetNetIFAppIf_RxHandleInfo *outArgs)
{
    Enet_Type enetType;
    uint32_t instId, i;
    EnetDma_Pkt *pPktInfo;
    // TODO: remove
    // LwipifEnetAppIf_custom_rx_pbuf* cPbuf;
    NetworkBufferDescriptor_t * pxNetDesc;
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

        pPktInfo = EnetMem_allocEthPkt(&inArgs->cbArg,
                           ENET_MEM_LARGE_POOL_PKT_SIZE,
                           ENETDMA_CACHELINE_ALIGNMENT);
        EnetAppUtils_assert(pPktInfo != NULL);

        ENET_UTILS_SET_PKT_APP_STATE(&pPktInfo->pktState, ENET_PKTSTATE_APP_WITH_FREEQ);

        pxNetDesc = (NetworkBufferDescriptor_t *) (pPktInfo->sgList.list[0].bufPtr - ipBUFFER_PADDING);
        EnetNetIF_AppIf_CustomNetBuf * pxCustomNetDesc = (EnetNetIF_AppIf_CustomNetBuf *) pxNetDesc;

        pxCustomNetDesc->pktInfoMem = pPktInfo;
        pxCustomNetDesc->freePktInfoQ = inArgs->pktInfoQ;
        pxNetDesc->xDataLength = ENET_MEM_LARGE_POOL_PKT_SIZE; //FIXME: less than ENET_MEM_LARGE_POOL_PKT_SIZE because of padding

        // cPbuf = (LwipifEnetAppIf_custom_rx_pbuf*)LWIP_MEMPOOL_ALLOC(RX_POOL);

        // cPbuf->p.custom_free_function = LwipifEnetAppCb_pbuf_free_custom;
        // cPbuf->pktInfoMem         = pPktInfo;
        // cPbuf->freePktInfoQ         = inArgs->pktInfoQ;
        // cPbuf->p.pbuf.flags |= PBUF_FLAG_IS_CUSTOM;

        // pxNetDesc = pbuf_alloced_custom(PBUF_RAW, ENET_MEM_LARGE_POOL_PKT_SIZE, PBUF_POOL, &cPbuf->p, pPktInfo->sgList.list[0].bufPtr, pPktInfo->sgList.list[0].segmentAllocLen);

        pPktInfo->appPriv = (void *)pxNetDesc;

        if (pxNetDesc != NULL)
        {
            EnetAppUtils_assert(pxNetDesc->pucEthernetBuffer != NULL);
            EnetAppUtils_assert(ENET_UTILS_IS_ALIGNED(pxNetDesc->pucEthernetBuffer, ENETDMA_CACHELINE_ALIGNMENT));

            /* Enqueue to the free queue */
			EnetQueue_enq(inArgs->pktInfoQ, &pPktInfo->node);
        }
        else
        {
            DebugP_log("ERROR: Pbuf_alloc() failure...exiting!\r\n");
            EnetAppUtils_assert(FALSE);
        }
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

    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
    BaseType_t xNetIFNum;

    configASSERT(pxNetIFArgs != NULL);
    xNetIFNum = pxNetIFArgs->xNetIFID;

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
        NetworkBufferDescriptor_t * pxNetworkBuffer = (NetworkBufferDescriptor_t *)pDmaPacket->appPriv;
        if (pxNetworkBuffer)
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
    NetworkBufferDescriptor_t * pxNetDesc;
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
        pxNetDesc = (NetworkBufferDescriptor_t *)pCurrDmaPacket->appPriv;
        if (pxNetDesc)
        {
            // TODO: deal with planned RX buffer allocation scheme for FR+TCP

            EnetNetIF_AppIf_CustomNetBuf * pxCustomNetDesc = (EnetNetIF_AppIf_CustomNetBuf *) pxNetDesc;
            
            pxCustomNetDesc->pktInfoMem = pCurrDmaPacket;
            pxCustomNetDesc->freePktInfoQ = &rx->freePktInfoQ;
            pxNetDesc->xDataLength = ENET_MEM_LARGE_POOL_PKT_SIZE; //FIXME: less than ENET_MEM_LARGE_POOL_PKT_SIZE because of padding
            configASSERT(ENET_UTILS_ALIGN(hEnet->appInfo.hostPortRxMtu, ENETDMA_CACHELINE_ALIGNMENT) == ENET_MEM_LARGE_POOL_PKT_SIZE); //TODO check!

            // LwipifEnetAppIf_custom_rx_pbuf* my_pbuf  = (LwipifEnetAppIf_custom_rx_pbuf*)pxNetDesc;

            // my_pbuf->p.custom_free_function = LwipifEnetAppCb_pbuf_free_custom;
            // my_pbuf->pktInfoMem         = pCurrDmaPacket;
            // my_pbuf->freePktInfoQ         = &rx->freePktInfoQ;
            // my_pbuf->p.pbuf.flags |= PBUF_FLAG_IS_CUSTOM;

            // bufSize = ENET_UTILS_ALIGN(hEnet->appInfo.hostPortRxMtu, ENETDMA_CACHELINE_ALIGNMENT);
            // pxNetDesc = pbuf_alloced_custom(PBUF_RAW, bufSize, PBUF_POOL, &my_pbuf->p, pCurrDmaPacket->sgList.list[0].bufPtr, pCurrDmaPacket->sgList.list[0].segmentAllocLen);

            // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&rx->stats.freePbufPktDeq);
            // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&rx->stats.freeAppPktDeq);

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

void EnetNetIF_retrieveTxPkts(EnetNetIF_TxObj *tx)
{
    EnetDma_PktQ tempQueue;
    uint32_t packetCount = 0U;
    int32_t retVal;

    // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&tx->stats.pktStats.rawNotifyCnt);
    packetCount = 0U;

    /* Retrieve the used (sent/empty) packets from the channel */
    {
        EnetQueue_initQ(&tempQueue);
        /* Retrieve all TX packets and keep them locally */
        retVal = EnetDma_retrieveTxPktQ(tx->hCh, &tempQueue);
        if (ENET_SOK != retVal)
        {
            FreeRTOS_printf(("EnetNetIF_retrieveTxPkts: Failed to retrieve TX pkts: %d\n",
                            retVal));
        }
    }

    if (tempQueue.count != 0U)
    {
        /*
         * Get all used Tx DMA packets from the hardware, then return those
         * buffers to the txFreePktQ so they can be used later to send with.
         */
        packetCount = EnetNetIF_prepTxPktQ(tx, &tempQueue);
    }
    else
    {
        // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&tx->stats.pktStats.zeroNotifyCnt);
    }

    if (packetCount != 0U)
    {
        // TODO: take care of stats Lwip2Enet_updateTxNotifyStats(&tx->stats.pktStats, packetCount, 0U);
    }
}

static void EnetNetIF_timerCb(ClockP_Object *hClk, void * arg)
{
#if defined (ENET_SOC_HOSTPORT_DMA_TYPE_UDMA)
    /* Post semaphore to rx handling task */
    xEnetDriverHandle hEnet = (xEnetDriverHandle)arg;

    if (hEnet->initDone)
    {
        for (uint32_t i = 0U; i < hEnet->numTxChannels; i++)
        {
            if (hEnet->tx[i].enabled)
            {
                EnetNetIF_retrieveTxPkts(&hEnet->tx[i]);
            }
        }

        if (hEnet->rxPktNotify.cbFxn != NULL)
        {
            hEnet->rxPktNotify.cbFxn(hEnet->rxPktNotify.cbArg);
        }
    }
#endif
}

static void EnetNetIF_createTimer(xEnetDriverHandle hEnet)
{
    ClockP_Params clkPrms;
    int32_t status;

    ClockP_Params_init(&clkPrms);
    clkPrms.start  = true;
    clkPrms.timeout = ClockP_usecToTicks(hEnet->appInfo.timerPeriodUs);
    clkPrms.period = ClockP_usecToTicks(hEnet->appInfo.timerPeriodUs);
    clkPrms.callback = &EnetNetIF_timerCb;
    clkPrms.args = hEnet;

    status =  ClockP_construct(&hEnet->pacingClkObj, &clkPrms);
    configASSERT(status == SystemP_SUCCESS);
}

void EnetNetIF_setRxNotifyCallback(xEnetDriverHandle hEnet, Enet_notify_t *pRxPktNotify)
{
    hEnet->rxPktNotify = *pRxPktNotify;
}

void EnetNetIF_setTxNotifyCallback(xEnetDriverHandle hEnet, Enet_notify_t *pTxPktNotify)
{
    hEnet->txPktNotify = *pTxPktNotify;
}

void EnetNetIF_setNotifyCallbacks(NetworkInterface_t * pxInterface, Enet_notify_t *pRxNotify, Enet_notify_t *pTxNotify)
{

    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
    xEnetDriverHandle hEnet = pxNetIFArgs->hEnet;
    EnetNetIF_setRxNotifyCallback(hEnet, pRxNotify);
    EnetNetIF_setRxNotifyCallback(hEnet, pTxNotify);
}

/*
* create a function called postEvent[i]. each event, each postfxn.
*/
static void EnetNetIFApp_postSemaphore(void *pArg)
{
    SemaphoreP_Object *pSem = (SemaphoreP_Object *) pArg;
    SemaphoreP_post(pSem);
}

// static void Lwip2Enet_updateTxNotifyStats(Lwip2Enet_PktTaskStats *pktStats,
//                                           uint32_t packetCount,
//                                           uint32_t timeDiff)
// {
// #if defined(LWIPIF_INSTRUMENTATION_ENABLED)
//     uint32_t notificationCount;
//     uint32_t timePerPacket = timeDiff / packetCount;

//     notificationCount = pktStats->dataNotifyCnt & (HISTORY_CNT - 1U);
//     pktStats->dataNotifyCnt++;

//     pktStats->totalPktCnt   += packetCount;
//     pktStats->totalCycleCnt += timeDiff;

//     pktStats->cycleCntPerNotify[notificationCount] = timeDiff;
//     if (timeDiff > pktStats->cycleCntPerNotifyMax)
//     {
//         pktStats->cycleCntPerNotifyMax = timeDiff;
//     }

//     pktStats->pktsPerNotify[notificationCount] = packetCount;
//     if (packetCount > pktStats->pktsPerNotifyMax)
//     {
//         pktStats->pktsPerNotifyMax = packetCount;
//     }

//     pktStats->cycleCntPerPkt[notificationCount] = timePerPacket;
//     if (timePerPacket > pktStats->cycleCntPerPktMax)
//     {
//         pktStats->cycleCntPerPktMax = timePerPacket;
//     }
// #endif
// }

static uint32_t EnetNetIF_prepTxPktQ(EnetNetIF_TxObj *tx,
                                     EnetDma_PktQ *pPktQ)
{
    uint32_t packetCount;
    EnetDma_Pkt *pCurrDmaPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer;

    packetCount = EnetQueue_getQCount(pPktQ);

    pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(pPktQ);
    while (pCurrDmaPacket)
    {
        pxNetworkBuffer = (NetworkBufferDescriptor_t *)pCurrDmaPacket->appPriv;

        configASSERT(pxNetworkBuffer != NULL);
        /* Free PBUF buffer as it is transmitted by DMA now */
        vReleaseNetworkBufferAndDescriptor(pxNetworkBuffer);
        /* Return packet info to free pool */
        EnetQueue_enq(&tx->freePktInfoQ, &pCurrDmaPacket->node);
        pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(pPktQ);
    }

    // TODO: take care of stats LWIP2ENETSTATS_ADDNUM(&tx->stats.freeAppPktEnq, packetCount);

    return packetCount;
}

void EnetNetIF_Enet_txPktHandler(xEnetDriverHandle hEnet)
{
    uint32_t txChNum;

    for (txChNum = 0U; txChNum < hEnet->numTxChannels; txChNum++)
    {
        EnetNetIF_retrieveTxPkts(&hEnet->tx[txChNum]);
    }


}

void EnetNetIF_txPktHandler(NetworkInterface_t * pxInterface)
{
    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
    xEnetDriverHandle hEnet = pxNetIFArgs->hEnet;
    EnetNetIF_Enet_txPktHandler(hEnet);
}


static void EnetNetIF_txPacketTask(void *arg)
{
    NetworkInterface_t * pxInterface = (NetworkInterface_t *) arg;
    while (!shutDownFlag)
    {
        /*
         * Wait for the Tx ISR to notify us that empty packets are available
         * that were used to send data
         */
        SemaphoreP_pend(&txPktSem, SystemP_WAIT_FOREVER);
        EnetNetIF_txPktHandler(pxInterface);
    }

    /* We are shutting down, notify that we are done */
    SemaphoreP_post(&shutDownSemObj);
}

void EnetNetIFApp_createTxPktHandlerTask(NetworkInterface_t * pxInterface)
{
    TaskP_Params params;
    int32_t status;

    /* Create TX packet task */
    TaskP_Params_init(&params);
    params.name = "EnetNetIF_txPacketTask";
    params.priority       = ENETNETIF_TX_PACKET_TASK_PRI;
    params.stack          = &gPktTxTaskStack[0U];
    params.stackSize      = sizeof(gPktTxTaskStack);
    params.args           = pxInterface;
    params.taskMain       = &EnetNetIF_txPacketTask;

    status = TaskP_construct(&txTask , &params);
    configASSERT(status == SystemP_SUCCESS);
}

static uint32_t EnetNetIF_prepRxPktQ(EnetNetIF_RxObj *rx,
                                     EnetDma_PktQ *pPktQ)
{
    uint32_t packetCount = 0U;
    EnetDma_Pkt *pCurrDmaPacket;
    bool isChksumError = false;
    uint32_t validLen = 0U;

    pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(pPktQ);
    while (pCurrDmaPacket)
    {
        /* Get the full PBUF packet that needs to be returned to the LwIP stack */
        NetworkBufferDescriptor_t * pxDescriptor = (NetworkBufferDescriptor_t *)pCurrDmaPacket->appPriv;
        isChksumError = false;
        if (pxDescriptor)
        {
            validLen = pCurrDmaPacket->sgList.list[0].segmentFilledLen;

            /* Fill in PBUF packet length field */
            pxDescriptor->xDataLength = validLen;
            // pxDescriptor->tot_len = validLen;
            configASSERT(pxDescriptor->pucEthernetBuffer != NULL);

// TODO: Handle ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
// #if ((ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT) == 1) && (ENET_ENABLE_PER_CPSW == 1))
//             {
//                 struct ip_hdr* pIpPkt = (struct ip_hdr* ) LWIPIF_LWIP_getIpPktStart((uint8_t*) pxDescriptor->payload);
//                 if (IPH_PROTO(pIpPkt) == IP_PROTO_UDPLITE)
//                 {
//                     isChksumError = LWIPIF_LWIP_UdpLiteValidateChkSum(pxDescriptor);
//                 }
//                 else
//                 {
//                     /* We don't check if HW checksum offload is enabled while checking for checksum error
//                      * as default value of this field when offload not enabled is false */
//                     const uint32_t csumInfo =  pCurrDmaPacket->chkSumInfo;

//                     if ( ENETDMA_RXCSUMINFO_GET_IPV4_FLAG(csumInfo) ||
//                             ENETDMA_RXCSUMINFO_GET_IPV6_FLAG(csumInfo))
//                     {
//                         isChksumError = ENETDMA_RXCSUMINFO_GET_CHKSUM_ERR_FLAG(csumInfo);
//                     }
//                 }
//             }
// #endif
            if (!isChksumError)
            {
                /* Pass the received packet to the LwIP stack */
                AM243x_Eth_NetworkInterfaceInput(rx, pCurrDmaPacket->rxPortNum, pxDescriptor);
                packetCount++;
            }
            else
            {
                /* Put PBUF buffer in free Q as we are not passing to stack */
                EnetQueue_enq(&rx->freePktInfoQ, &pCurrDmaPacket->node);
                // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&rx->stats.freeAppPktEnq);
                // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&rx->stats.chkSumErr);
            }

            /* Put packet info into free Q as we have removed the PBUF buffers
             * from the it */
            pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(pPktQ);
        }
        else
        {
            /* Should never happen as this is received from HW */
            configASSERT(FALSE);
        }
    }

    /* return as many packets to driver as we can */
    EnetNetIF_submitRxPktQ(rx);

    return packetCount;
}

void EnetNetIF_rxPktHandler(xEnetDriverHandle hEnet)
{
    EnetDma_PktQ tempQueue;
    int32_t retVal;
    uint32_t pktCnt, rxChNum;

    for(rxChNum = 0U; rxChNum < hEnet->numRxChannels; rxChNum++)
    {
        pktCnt = 0U;
        // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&hEnet->rx[rxChNum].stats.pktStats.rawNotifyCnt);

        /* Retrieve the used (filled) packets from the channel */
        {
            EnetQueue_initQ(&tempQueue);
            retVal = EnetDma_retrieveRxPktQ(hEnet->rx[rxChNum].hFlow, &tempQueue);
            if (ENET_SOK != retVal)
            {
                FreeRTOS_printf(("Lwip2Enet_rxPacketTask: failed to retrieve RX pkts: %d\n",
                                retVal));
            }
        }
        if (tempQueue.count == 0U)
        {
            // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&hEnet->rx[rxChNum].stats.pktStats.zeroNotifyCnt);
        }

        /*
         * Call Lwip2Enet_prepRxPktQ() even if no packets were received.
         * This allows new packets to be submitted if PBUF buffers became
         * newly available and there were outstanding free packets.
         */
        {
            /*
             * Get all used Rx DMA packets from the hardware, then send the buffers
             * of those packets on to the LwIP stack to be parsed/processed.
             */
            pktCnt = EnetNetIF_prepRxPktQ(&hEnet->rx[rxChNum], &tempQueue);
        }

        /*
         * We don't want to time the semaphore post used to notify the LwIP stack as that may cause a
         * task transition. We don't want to time the semaphore pend, since that would time us doing
         * nothing but waiting.
         */
        if (pktCnt != 0U)
        {
            // TODO: take care of stats Lwip2Enet_updateRxNotifyStats(&hEnet->rx[rxChNum].stats.pktStats, pktCnt, 0U);
        }

        // ClockP_start(&hEnet->pacingClkObj);

        if (!hEnet->rx[rxChNum].disableEvent)
        {
            EnetDma_enableRxEvent(hEnet->rx[rxChNum].hFlow);
        }
    }


}

void EnetNetIF_Enet_rxPktHandler(NetworkInterface_t * pxInterface)
{
    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
    xEnetDriverHandle hEnet = pxNetIFArgs->hEnet;
    EnetNetIF_rxPktHandler(hEnet);
}

static void EnetNetIFApp_rxPacketTask(void *arg)
{
    NetworkInterface_t * pxInterface = (NetworkInterface_t *) arg;
    while (!shutDownFlag)
    {
        /* Wait for the Rx ISR to notify us that packets are available with data */
        SemaphoreP_pend(&rxPktSem, SystemP_WAIT_FOREVER);
        if (shutDownFlag)
        {
            /* This translation layer is shutting down, don't give anything else to the stack */
            break;
        }

        EnetNetIF_Enet_rxPktHandler(pxInterface);
    }

    /* We are shutting down, notify that we are done */
    SemaphoreP_post(&shutDownSemObj);
}

void EnetNetIFApp_createRxPktHandlerTask(NetworkInterface_t * pxInterface)
{
    TaskP_Params params;
    int32_t status;

    /* Create RX packet task */
    TaskP_Params_init(&params);
    params.name = "EnetNetIFApp_rxPacketTask";
    params.priority       = ENETNETIF_RX_PACKET_TASK_PRI;
    params.stack          = &gPktRxTaskStack[0U];
    params.stackSize      = sizeof(gPktRxTaskStack);
    params.args           = pxInterface;
    params.taskMain       = &EnetNetIFApp_rxPacketTask;

    status = TaskP_construct(&rxTask , &params);
    EnetAppUtils_assert(status == SystemP_SUCCESS);
}

static void EnetNetIF_setSGList(EnetDma_Pkt *pCurrDmaPacket, NetworkBufferDescriptor_t *netBufPkt, bool isRx)
{
    NetworkBufferDescriptor_t * curNetBuf = netBufPkt;
    uint32_t totalPacketFilledLen = 0U;

    pCurrDmaPacket->sgList.numScatterSegments = 0;
    while (curNetBuf != NULL)
    {
        EnetDma_SGListEntry *list;

        configASSERT(pCurrDmaPacket->sgList.numScatterSegments < ENET_ARRAYSIZE(pCurrDmaPacket->sgList.list));
        list = &pCurrDmaPacket->sgList.list[pCurrDmaPacket->sgList.numScatterSegments];
        list->bufPtr = (uint8_t*) curNetBuf->pucEthernetBuffer;
        list->segmentFilledLen = (isRx == true) ? 0U : curNetBuf->xDataLength;
        list->segmentAllocLen = curNetBuf->xDataLength;
        // TODO: check use of curNetBuf->type_internal == PBUF_ROM
        // if ((curNetBuf->type_internal == PBUF_ROM) || (curNetBuf->type_internal == PBUF_REF))
        // {
        //     list->disableCacheOps = true;
        // }
        // else
        // {
        //     list->disableCacheOps = false;
        // }
        list->disableCacheOps = true; // TODO: check use of curNetBuf->type_internal == PBUF_ROM

        totalPacketFilledLen += curNetBuf->xDataLength;
        pCurrDmaPacket->sgList.numScatterSegments++;

        #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
            curNetBuf = curNetBuf->pxNextBuffer;
        #else
            break;
        #endif
    }
    configASSERT(totalPacketFilledLen == netBufPkt->xDataLength);
}

/* May lead to infinite loop if no free memory
 * available*/
static void EnetNetIF_pbufQ2PktInfoQ(EnetNetIF_TxObj *tx,
                                     NetBufQueue *netBufPktQ,
                                     EnetDma_PktQ *pDmaPktInfoQ,
                                     Enet_MacPort macPort)
{
    EnetDma_Pkt *pCurrDmaPacket;
    NetworkBufferDescriptor_t * netBufPkt = NULL;

    while(uNetworkBufferDescriptorQueue_count(netBufPktQ) != 0U)
    {

        /* Dequeue one free TX Eth packet */
        pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&tx->freePktInfoQ);

        if (pCurrDmaPacket == NULL)
        {
        /* If we run out of packet info Q, retrieve packets from HW
            * and try to dequeue free packet again */
        EnetNetIF_retrieveTxPkts(tx);
        pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&tx->freePktInfoQ);
        }

        if (NULL != pCurrDmaPacket)
        {
            netBufPkt = NetBufQueue_deQ(netBufPktQ);
            EnetDma_initPktInfo(pCurrDmaPacket);

            EnetNetIF_setSGList(pCurrDmaPacket, netBufPkt, false);
            pCurrDmaPacket->appPriv    = netBufPkt;

            pCurrDmaPacket->node.next = NULL;
            pCurrDmaPacket->chkSumInfo = 0U;
            pCurrDmaPacket->txPortNum  = macPort;

// TODO: Handle ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
// #if ((ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT) == 1) && (ENET_ENABLE_PER_CPSW == 1))
//             pCurrDmaPacket->chkSumInfo = LWIPIF_LWIP_getChkSumInfo(netBufPkt);
// #endif

            ENET_UTILS_COMPILETIME_ASSERT(offsetof(EnetDma_Pkt, node) == 0U);
            EnetQueue_enq(pDmaPktInfoQ, &(pCurrDmaPacket->node));

            // TODO update stats macro LWIP2ENETSTATS_ADDONE(&tx->stats.freeAppPktDeq);
        }
        else
        {
            break;
        }
    }
}

static void EnetNetIF_pktInfoQ2PbufQ(EnetDma_PktQ *pDmaPktInfoQ,
                                     NetBufQueue *netBufPktQ)
{
    EnetDma_Pkt *pDmaPacket;
    NetworkBufferDescriptor_t * netBufPkt;

    while (EnetQueue_getQCount(pDmaPktInfoQ) != 0U)
    {
        pDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(pDmaPktInfoQ);
        netBufPkt = (NetworkBufferDescriptor_t *)(pDmaPacket->appPriv);

        configASSERT(netBufPkt != NULL);
        /*Don't want to make a copy, since it would cause waste memory*/
        NetBufQueue_enQ(netBufPktQ, netBufPkt);
    }
}

static void EnetNetIF_submitTxPackets(EnetNetIF_TxObj *tx,
                                      EnetDma_PktQ *pSubmitQ)
{
    int32_t retVal;

    retVal = EnetDma_submitTxPktQ(tx->hCh, pSubmitQ);
    if (ENET_SOK != retVal)
    {
        FreeRTOS_printf(("EnetDma_submitTxPktQ: failed to submit pkts: %d\n",
                        retVal));
    }

    if (EnetQueue_getQCount(pSubmitQ))
    {
        /* TODO: txUnUsedPBMPktQ is needed for packets that were not able to be
         *       submitted to driver.  It can be removed if stack supported any
         *       mechanism to enqueue them to the head of the queue. */
        EnetNetIF_pktInfoQ2PbufQ(pSubmitQ, &tx->unusedPbufQ);
        EnetQueue_append(&tx->freePktInfoQ, pSubmitQ);
        // TODO update stats macro LWIP2ENETSTATS_ADDNUM(&tx->stats.freeAppPktEnq, EnetQueue_getQCount(pSubmitQ));
    }
}

void EnetNetIF_sendTxPackets(EnetNetIF_TxObj *tx,
                             Enet_MacPort macPort)
{
    xEnetDriverHandle hEnet;
    EnetDma_Pkt *pCurrDmaPacket;
    NetworkBufferDescriptor_t * netBufPkt;

    hEnet = tx->hEnetNetIF;

    /* If link is not up, simply return */
    if (hEnet->linkIsUp)
    {
        EnetDma_PktQ txSubmitQ;

        EnetQueue_initQ(&txSubmitQ);

        if (uNetworkBufferDescriptorQueue_count(&tx->unusedPbufQ))
        {
            /* send any pending TX Q's */
            EnetNetIF_pbufQ2PktInfoQ(tx, &tx->unusedPbufQ, &txSubmitQ, macPort);
        }

        /* Check if there is anything to transmit, else simply return */
        while (uNetworkBufferDescriptorQueue_count(&tx->readyPbufQ) != 0U)
        {
            /* Dequeue one free TX Eth packet */
            pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&tx->freePktInfoQ);

            if (pCurrDmaPacket == NULL)
            {
                /* If we run out of packet info Q, retrieve packets from HW
                * and try to dequeue free packet again */
                EnetNetIF_retrieveTxPkts(tx);
                pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&tx->freePktInfoQ);
            }

            if (NULL != pCurrDmaPacket)
            {
                netBufPkt = NetBufQueue_deQ(&tx->readyPbufQ);
                EnetDma_initPktInfo(pCurrDmaPacket);

                EnetNetIF_setSGList(pCurrDmaPacket, netBufPkt, false);
                pCurrDmaPacket->appPriv    = netBufPkt;
                pCurrDmaPacket->txPortNum  = macPort;
                pCurrDmaPacket->node.next  = NULL;
                pCurrDmaPacket->chkSumInfo = 0U;
// TODO: Handle ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
// #if ((ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT) == 1) && (ENET_ENABLE_PER_CPSW == 1))
//                 pCurrDmaPacket->chkSumInfo = LWIPIF_LWIP_getChkSumInfo(netBufPkt);
// #endif

                ENET_UTILS_COMPILETIME_ASSERT(offsetof(EnetDma_Pkt, node) == 0U);
                EnetQueue_enq(&txSubmitQ, &(pCurrDmaPacket->node));

                // TODO update stats macro LWIP2ENETSTATS_ADDONE(&tx->stats.freeAppPktDeq);
                // TODO update stats macro LWIP2ENETSTATS_ADDONE(&tx->stats.readyPbufPktDeq);
            }
            else
            {
                break;
            }
        }

        /* Submit the accumulated packets to the hardware for transmission */
        EnetNetIF_submitTxPackets(tx, &txSubmitQ);
    }
}

 void EnetNetIF_periodicFxn(NetworkInterface_t * pxInterface)
{
    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
    xEnetDriverHandle hEnet = pxNetIFArgs->hEnet;

    uint32_t prevLinkState     = hEnet->linkIsUp;
    uint32_t prevLinkInterface = hEnet->currLinkedIf;

#if (1U == ENET_CFG_DEV_ERROR)
#if defined (ENET_SOC_HOSTPORT_DMA_TYPE_UDMA)
    int32_t status;
#endif

    for(uint32_t i = 0U; i < hEnet->numTxChannels; i++)
    {
        EnetQueue_verifyQCount(&hEnet->tx[i].freePktInfoQ);

#if defined (ENET_SOC_HOSTPORT_DMA_TYPE_UDMA)
        status = EnetUdma_checkTxChSanity(hEnet->tx[i].hCh, 5U);
        if (status != ENET_SOK)
        {
            FreeRTOS_printf(("EnetUdma_checkTxChSanity Failed\n"));
        }
#endif
    }

    for(uint32_t i = 0U; i < hEnet->numRxChannels; i++)
    {
        EnetQueue_verifyQCount(&hEnet->rx[i].freePktInfoQ);

#if defined (ENET_SOC_HOSTPORT_DMA_TYPE_UDMA)
        status = EnetUdma_checkRxFlowSanity(hEnet->rx[i].hFlow, 5U);
        if (status != ENET_SOK)
        {
            FreeRTOS_printf(("EnetUdma_checkRxFlowSanity Failed\n"));
        }
#endif
    }


#endif

    /*
     * Return the same DMA packets back to the DMA channel (but now
     * associated with a new PBUF Packet and buffer)
     */
    for(uint32_t i = 0U; i < hEnet->numRxChannels; i++)
    {
        if (EnetQueue_getQCount(&hEnet->rx[i].freePktInfoQ) != 0U)
        {
            EnetNetIF_submitRxPktQ(&hEnet->rx[i]);
        }
    }
#if 0 //The below CPU load profilling logic has to be re-worked for all OS variants
#if defined(LWIPIF_INSTRUMENTATION_ENABLED)
    static uint32_t loadCount = 0U;
    TaskP_Load stat;

    hEnet->stats.cpuLoad[loadCount] = TaskP_loadGetTotalCpuLoad();

    TaskP_loadGet(&hEnet->rxPacketTaskObj, &stat);
    for(uint32_t i = 0U; i < hEnet->numRxChannels; i++)
    {
        hEnet->rx[i].stats.pktStats.taskLoad[loadCount] = stat.cpuLoad;
    }

    TaskP_loadGet(&hEnet->txPacketTaskObj, &stat);
    for(uint32_t i = 0U; i < hEnet->numRxChannels; i++)
    {
        hEnet->tx[i].stats.pktStats.taskLoad[loadCount] = stat.cpuLoad;
    }

    loadCount = (loadCount + 1U) & (HISTORY_CNT - 1U);
#endif
#endif
    /* Get current link status as reported by the hardware driver */
    hEnet->linkIsUp = hEnet->appInfo.isPortLinkedFxn(hEnet->appInfo.hEnet);

    /* If the interface changed, discard any queue packets (since the MAC would now be wrong) */
    if (prevLinkInterface != hEnet->currLinkedIf)
    {
        /* ToDo: Discard all queued packets */
    }

    for(uint32_t i = 0U; i < hEnet->numTxChannels; i++)
    {
        /* If link status changed from down->up, then send any queued packets */
        if ((prevLinkState == 0U) && (hEnet->linkIsUp))
        {
            EnetNetIF_TxHandle hTxHandle;
            Enet_MacPort macPort;

            hTxHandle  = hEnet->mapNetif2Tx[pxNetIFArgs->xNetIFID];
            macPort    = hEnet->mapNetif2TxPortNum[pxNetIFArgs->xNetIFID];
            EnetNetIF_sendTxPackets(hTxHandle, macPort);
        }
    }

}

void EnetNetIF_periodic_polling(NetworkInterface_t * pxFirstInterface)
{
    NetworkInterface_t * pxInterface = pxFirstInterface;
    do // loop along all the netifs (reverse linked list)
    {
        xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
        xEnetDriverHandle hEnet = (xEnetDriverHandle) pxNetIFArgs->hEnet;

        /* Periodic Function to update Link status */
        EnetNetIF_periodicFxn(pxInterface);

        if (!(hEnet->linkIsUp == pxNetIFArgs->xLinkUp))
        {
            if (hEnet->linkIsUp)
            {
                pxNetIFArgs->xLinkUp = pdTRUE;
            }
            else
            {
                pxNetIFArgs->xLinkUp = pdFALSE;
            }
        }
        pxInterface = FreeRTOS_NextNetworkInterface(pxInterface);
    } while ( pxInterface != NULL );
    
}

static void EnetNetIF_EnetApp_poll(void *arg)
{
    /* Call the driver's periodic polling function */
    volatile bool flag = 1;
    NetworkInterface_t * pxInterface = (NetworkInterface_t *) arg;

    while (flag)
    {
        SemaphoreP_pend(&pollSem, SystemP_WAIT_FOREVER);
        //sys_lock_tcpip_core();
        EnetNetIF_periodic_polling(pxInterface);
        //sys_unlock_tcpip_core();
    }
}

static void EnetNetIF_EnetApp_postPollLink(ClockP_Object *clkObj, void *arg)
{
    if(arg != NULL)
    {
        SemaphoreP_Object *hpollSem = (SemaphoreP_Object *) arg;
        SemaphoreP_post(hpollSem);
    }
}

static int8_t EnetNetIF_EnetApp_createPollTask(NetworkInterface_t * pxInterface)
{
    TaskP_Params params;
    int32_t status;
    ClockP_Params clkPrms;
    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);

    if (NULL != pxNetIFArgs->hEnet)
    {
        /*Initialize semaphore to call synchronize the poll function with a timer*/
        status = SemaphoreP_constructBinary(&pollSem, 0U);
        configASSERT(status == SystemP_SUCCESS);

        /* Initialize the poll function as a thread */
        TaskP_Params_init(&params);
        params.name = "EnetNetIF_EnetApp_poll";
        params.priority       = ENETNETIF_POLL_TASK_PRI;
        params.stack          = &gPollTaskStack[0U];
        params.stackSize      = sizeof(gPollTaskStack);
        params.args           = pxInterface; //&(gNetif[ENET_SYSCFG_NETIF_COUNT - 1]);
        params.taskMain       = &EnetNetIF_EnetApp_poll;

        status = TaskP_construct(&pollTask, &params);
        configASSERT(status == SystemP_SUCCESS);

        ClockP_Params_init(&clkPrms);
        clkPrms.start     = 0;
        clkPrms.period    = ENETNETIF_APP_POLL_PERIOD;
        clkPrms.args      = &pollSem;
        clkPrms.callback  = &EnetNetIF_EnetApp_postPollLink;
        clkPrms.timeout   = ENETNETIF_APP_POLL_PERIOD;

        /* Creating timer and setting timer callback function*/
        status = ClockP_construct(&pollLinkClkObj,
                                  &clkPrms);
        if (status == SystemP_SUCCESS)
        {
            /* Set timer expiry time in OS ticks */
            ClockP_setTimeout(&pollLinkClkObj, ENETNETIF_APP_POLL_PERIOD);
            ClockP_start(&pollLinkClkObj);
        }
        else
        {
            configASSERT (status == SystemP_SUCCESS);
        }

        /* Filter not defined */
        /* Inform the world that we are operational. */
        FreeRTOS_debug_printf(("[EnetNetIF] Enet has been started successfully\r\n"));

        return 0;
    }
    else
    {
        configASSERT(pdFALSE);
        return -2;
    }
}

void EnetNetIFApp_startSchedule(NetworkInterface_t * pxInterface)
{
    uint32_t status;
    status = SemaphoreP_constructBinary(&txPktSem, 0U);
    EnetAppUtils_assert(status == SystemP_SUCCESS);

    status = SemaphoreP_constructBinary(&rxPktSem, 0U);
    EnetAppUtils_assert(status == SystemP_SUCCESS);

    Enet_notify_t rxNotify =
        {
           .cbFxn = &EnetNetIFApp_postSemaphore, //gives different cb fxn for different events.
           .cbArg = &rxPktSem //
        };
    Enet_notify_t txNotify =
        {
                .cbFxn = &EnetNetIFApp_postSemaphore,
                .cbArg = &txPktSem
        };

    EnetNetIF_setNotifyCallbacks(pxInterface, &rxNotify, &txNotify);
    // /* Initialize Tx task*/
    EnetNetIFApp_createTxPktHandlerTask(pxInterface);

    // /* Initialize Rx Task*/
    EnetNetIFApp_createRxPktHandlerTask(pxInterface);

    // /* Initialize Polling task*/
    EnetNetIF_EnetApp_createPollTask(pxInterface);
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
    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);

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

    configASSERT(pxNetIFArgs != NULL);
    xNetIFNum = pxNetIFArgs->xNetIFID;

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

        /* Get initial link/interface status from the driver */
        hEnet->linkIsUp = hEnet->appInfo.isPortLinkedFxn(hEnet->appInfo.hEnet);

        for (i = 0U; i < hEnet->numTxChannels; i++)
        {
            if (hEnet->tx[i].disableEvent)
            {
                EnetDma_disableTxEvent(hEnet->tx[i].hCh);
            }
        }

        for (i = 0U; i < hEnet->numRxChannels; i++)
        {
            if ((hEnet->rx[i].enabled) &&  (hEnet->rx[i].disableEvent))
            {
                EnetDma_disableRxEvent(hEnet->rx[i].hFlow);
            }
        }
        /* assert if clk period is not valid  */
        configASSERT(0U != hEnet->appInfo.timerPeriodUs);
        EnetNetIF_createTimer(hEnet);
        // ClockP_start(&hEnet->pacingClkObj);

        hEnet->initDone = TRUE;
        pxNetIFArgs->hEnet = hEnet;
    }

    // TODO: Wait till link is up before returing, because if the open() returns,
    // the IP-task will start and send packets immediately,
    
    // FIXME: NOTE: This is a temporary hack for minimal testing
    while(hEnet->appInfo.isPortLinkedFxn(hEnet->appInfo.hEnet) == 0)
    {
        vTaskDelay(pdMS_TO_TICKS(100));
    }

    if((hEnet->initDone == TRUE) && xNetIFNum == 0)
    {
        EnetNetIFApp_startSchedule(pxInterface);
    }

    return hEnet;

}
