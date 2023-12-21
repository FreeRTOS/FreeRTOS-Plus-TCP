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

#include <limits.h>

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
#include "Enet_Config.h"
#include "Enet_NetIFQueue.h"

#include "FreeRTOS_Routing.h"
#include "NetworkBufferManagement.h"

// static uint32_t totalISRCnt;
// static uint32_t tx_event = 0, rx_event = 0;

/* ========================================================================== */
/*                           Macros & Typedefs                                */
/* ========================================================================== */
#define ENETNETIF_PACKET_POLL_PERIOD_US (1000U)

#define ENETNETIF_APP_POLL_PERIOD       (500U)
/*! \brief RX packet task stack size */
#define ENETNETIF_TX_RX_PACKET_TASK_STACK    (4096U)

/*! \brief Links status poll task stack size */
#if (_DEBUG_ == 1)
#define ENETNETIF_POLL_TASK_STACK         (4096U)
#else
#define ENETNETIF_POLL_TASK_STACK         (1024U)
#endif

#define OS_TASKPRIHIGH              8U

#define ENETNETIF_RX_PACKET_TASK_PRI      (OS_TASKPRIHIGH)

#define ENETNETIF_TX_PACKET_TASK_PRI      (OS_TASKPRIHIGH)

#define ENETNETIF_POLL_TASK_PRI           (OS_TASKPRIHIGH - 1U)

// #define ENET_SYSCFG_DEFAULT_NETIF_IDX              (0U)

#define NETIF_INST_ID0           (0U)

NetBufNode gFreeTxNetBufArr[ENET_SYSCFG_TOTAL_NUM_TX_PKT];

static void EnetNetIF_notifyTxPackets(void *cbArg);

static xEnetDriverObj gEnetDriverObj = {.isInitDone = false, .isAllocated = false };

static void EnetNetIF_submitRxPktQ(EnetNetIF_RxObj *rx);

static void EnetNetIF_processRxUnusedQ(EnetNetIF_RxObj *rx,
                                       EnetDma_PktQ *unUsedQ);

static void EnetNetIF_submitRxPackets(EnetNetIF_RxObj *rx,
                                      EnetDma_PktQ *pSubmitQ);

static uint32_t EnetNetIF_prepTxPktQ(EnetNetIF_TxObj *tx,
                                     EnetDma_PktQ *pPktQ);

void AM243x_Eth_NetworkInterfaceInput(EnetNetIF_RxObj *rx,
                       NetworkInterface_t * pxInterfaceFromDriver,
                       NetworkBufferDescriptor_t * pxDescriptor);

void EnetNetIFAppCb_getEnetIFInstInfo(Enet_Type enetType, uint32_t instId, EnetNetIF_AppIf_GetEnetIFInstInfo *outArgs);

NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor_RX( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks );

uint8_t gPktTxRxTaskStack[ENETNETIF_TX_RX_PACKET_TASK_STACK] __attribute__ ((aligned(sizeof(long long))));
uint8_t gPollTaskStack[ENETNETIF_POLL_TASK_STACK] __attribute__ ((aligned(sizeof(long long))));

#define ENET_TX_NOTIFY_BIT      (1U)
#define ENET_RX_NOTIFY_BIT      (2U)

StaticTask_t xTxRxTaskStaticObj;
TaskHandle_t xTxRxTask;

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

uint8_t * getEnetAppBuffMem(uint32_t req_Size, uint8_t *pktAddr)
{
    (void) req_Size;
    (void) pktAddr;

    NetworkBufferDescriptor_t * pxReturn = pxGetNetworkBufferWithDescriptor_RX(1536U, 0);
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
    EnetNetIF_TxHandle pTx = (EnetNetIF_TxHandle)cbArg;

    /* do not post events if init not done or shutdown in progress */
    if ((pTx->refCount > 0) && (pTx->txPktNotify.cbFxn != NULL))
    {
        /* Notify Callbacks to post event/semephore */
        pTx->txPktNotify.cbFxn(pTx->txPktNotify.cbArg);
    }
}

static void EnetNetIF_notifyRxPackets(void *cbArg)
{
    EnetNetIF_RxHandle pRx = (EnetNetIF_RxHandle)cbArg;

    /* do not post events if init not done or shutdown in progress */
    if (pRx->refCount > 0)
    {
        if (pRx->disableEvent)
        {
            EnetDma_disableRxEvent(pRx->hFlow);
        }
        if (pRx->rxPktNotify.cbFxn != NULL)
        {
            pRx->rxPktNotify.cbFxn(pRx->rxPktNotify.cbArg);
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




// static void EnetNetIFAppCb_getEnetIFInstInfo(EnetNetIF_AppIf_GetEnetIFInstInfo *outArgs)
// {
//     EnetPer_AttachCoreOutArgs attachInfo;
//     EnetApp_HandleInfo handleInfo;
//     Enet_Type enetType;
//     uint32_t instId;

//     uint32_t coreId = EnetSoc_getCoreId();


//     EnetApp_getEnetInstInfo(&enetType,
//                             &instId);

//     EnetApp_acquireHandleInfo(enetType, instId, &handleInfo);
//     EnetApp_coreAttach(enetType,instId, coreId, &attachInfo);

//     outArgs->hEnet         = handleInfo.hEnet;
//     outArgs->hostPortRxMtu = attachInfo.rxMtu;
//     ENET_UTILS_ARRAY_COPY(outArgs->txMtu, attachInfo.txMtu);
//     outArgs->isPortLinkedFxn = &EnetApp_isPortLinked;
// 	outArgs->timerPeriodUs   = ENETNETIF_PACKET_POLL_PERIOD_US;

//     outArgs->maxNumNetif = ENET_FREERTOS_TCP_NETIF_COUNT;
//     outArgs->numRxChannels = ENET_SYSCFG_RX_FLOWS_NUM;
//     outArgs->numTxChannels = ENET_SYSCFG_TX_CHANNELS_NUM;

//     outArgs->pFreeTx = gFreeTxNetBufArr;
//     outArgs->pFreeTxSize = ENET_SYSCFG_TOTAL_NUM_TX_PKT;
//     // LWIP_MEMPOOL_INIT(RX_POOL); // TODO: Replace custom buffer (cbuf) based RX packet allocation with
//     // custom pxGetNetworkBufferWithDescriptor which has a separate owner that can be checked
//     // to release the packet back to the HW when vReleaseNetworkBufferAndDescriptor is called.


// #if ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
//     int32_t status;
//     /* Confirm HW checksum offload is enabled when LWIP chksum offload is enabled */
//         Enet_IoctlPrms prms;
//         bool csumOffloadFlg;
//         ENET_IOCTL_SET_OUT_ARGS(&prms, &csumOffloadFlg);
//         ENET_IOCTL(handleInfo.hEnet,
//                    coreId,
//                    ENET_HOSTPORT_IS_CSUM_OFFLOAD_ENABLED,
//                    &prms,
//                    status);
//         if (status != ENET_SOK)
//         {
//             EnetAppUtils_print("() Failed to get checksum offload info: %d\r\n", status);
//         }

//         configASSERT(true == csumOffloadFlg);
// #endif
// }

static void EnetNetIF_saveAppIfCfg(xEnetDriverHandle hEnet,
                                    EnetNetIF_AppIf_GetEnetIFInstInfo *appInfo)
{

}

static void EnetNetIF_initTxObj(Enet_Type enetType, uint32_t instId, uint32_t chEntryIdx, EnetNetIF_TxObj* pTx)
{
    if(pTx->refCount > 0)
    {
        pTx->refCount++;
    }
    else
    {
        EnetNetIFAppIf_GetTxHandleInArgs inArgs;
        EnetNetIFAppIf_TxHandleInfo outArgs;

        inArgs.chId = chEntryIdx;
        inArgs.cbArg = pTx;
        inArgs.notifyCb = &EnetNetIF_notifyTxPackets;
        inArgs.pktInfoQ = &pTx->freePktInfoQ;
        inArgs.enetType = enetType;
        inArgs.instId = instId;
        EnetNetIFAppCb_getTxHandleInfo(&inArgs, &outArgs);

        pTx->numPackets = outArgs.numPackets;
        pTx->hCh = outArgs.hTxChannel;
        configASSERT(pTx->hCh != NULL);
        pTx->disableEvent = outArgs.disableEvent;

        pTx->stats.freeAppPktEnq = outArgs.numPackets;

        /* Initialize the TX network buffer queues */
        NetBufQueue_init(&pTx->readyPbufQ);
        NetBufQueue_init(&pTx->unusedPbufQ);

        pTx->refCount = 1U;
        pTx->chEntryIdx = chEntryIdx;
    }
    return;
}


// static void EnetNetIF_mapNetif2Tx(NetworkInterface_t * pxInterface,
//                         bool isDirected,
//                         EnetNetIF_TxHandle hTxEnet,
//                         xEnetDriverHandle hEnet)
// {
//     xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
//     BaseType_t xNetIFNum;

//     configASSERT(pxNetIFArgs != NULL);
//     xNetIFNum = pxNetIFArgs->xNetIFID;

//     configASSERT(xNetIFNum < ENET_FREERTOS_TCP_NETIF_COUNT);

//     hEnet->mapNetif2Tx[xNetIFNum] = hTxEnet;
//     if(isDirected)
//     {
//         hEnet->mapNetif2TxPortNum[xNetIFNum] = ENET_MACPORT_DENORM(xNetIFNum);
//     }
// }

// void EnetNetIF_AppCb_ReleaseNetDescriptor(NetworkBufferDescriptor_t * const pxNetworkBuffer)
// {
//     EnetNetIF_AppIf_CustomNetBuf * xCNetBuf = (EnetNetIF_AppIf_CustomNetBuf *) pxNetworkBuffer;
//     uint32_t key = HwiP_disable();

//     EnetQueue_enq(xCNetBuf->freePktInfoQ, &xCNetBuf->pktInfoMem->node);

//     HwiP_restore(key);
// }

static inline void  EnetNetIF_CustomNetBuffInit(EnetNetIF_AppIf_CustomNetBuf *xCNetBuf)
{
    xCNetBuf->next            = NULL;
    xCNetBuf->alivePbufCount  = 0U;
    xCNetBuf->orgBufLen       = 0U;
    xCNetBuf->orgBufPtr       = NULL;
}

void EnetNetIF_AppCb_ReleaseNetDescriptor(NetworkBufferDescriptor_t * const pxNetworkBuffer)
{
    EnetNetIF_AppIf_CustomNetBuf * xCNetBuf = (EnetNetIF_AppIf_CustomNetBuf *) pxNetworkBuffer;
    EnetNetIF_AppIf_CustomNetBuf *start = xCNetBuf;
    EnetDma_SGListEntry *list = NULL;
    uint32_t scatterSegmentIndex = 0;
    EnetNetIF_RxObj *rx = (EnetNetIF_RxObj *) xCNetBuf->customNetBufArgs;
    EnetNetIF_AppIf_CustomNetBuf *cPbufNext = NULL;

#if (1U == ENET_CFG_DEV_ERROR)
    custom_pbuf_validateChain(xCNetBuf);
    configASSERT(xCNetBuf->alivePbufCount != 0);
    configASSERT(xCNetBuf->next != NULL);
#endif

    /* Decrement the alivePbufCount of the every xCNetBuf in the chain */
    start->alivePbufCount--;
    xCNetBuf = xCNetBuf->next;
    while(start != xCNetBuf)
    {
        xCNetBuf->alivePbufCount--;
        xCNetBuf = xCNetBuf->next;
    }
    configASSERT(start == xCNetBuf);
    if(xCNetBuf->alivePbufCount == 0)
    {
        /* This pbuf chain is no longer in use. */
        /* Loop through the xCNetBuf chain and enq in a dmapktinfo. */
        EnetDma_Pkt *pDmaPacket =  (EnetDma_Pkt *)EnetQueue_deq(&rx->freeRxPktInfoQ);
        // LWIP2ENETSTATS_ADDONE(&rx->stats.freeAppPktDeq);
        configASSERT(pDmaPacket != NULL);
        EnetDma_checkPktState(&pDmaPacket->pktState,
                               ENET_PKTSTATE_MODULE_APP,
                               ENET_PKTSTATE_APP_WITH_FREEQ,
                               ENET_PKTSTATE_APP_WITH_READYQ);
        do {
            list = &pDmaPacket->sgList.list[scatterSegmentIndex];
            list->bufPtr = xCNetBuf->orgBufPtr;
            list->segmentFilledLen = 0;
            configASSERT(xCNetBuf->orgBufLen != 0);
            list->segmentAllocLen  = xCNetBuf->orgBufLen;
            cPbufNext = xCNetBuf->next;
            EnetNetIF_CustomNetBuffInit(xCNetBuf);
            /* Enqueue the pbuf into freePbufInfoQ */
            // NetBufQueue_enQ(&rx->freePbufInfoQ, (NetworkBufferDescriptor_t *) xCNetBuf);
            // LWIP2ENETSTATS_ADDONE(&rx->stats.freePbufPktEnq);
            scatterSegmentIndex++;
            configASSERT(scatterSegmentIndex <= ENET_ARRAYSIZE(pDmaPacket->sgList.list));
            xCNetBuf = cPbufNext;
        } while(start != xCNetBuf);

        pDmaPacket->sgList.numScatterSegments = scatterSegmentIndex;
        EnetQueue_enq(&rx->readyRxPktQ, &pDmaPacket->node);
    }
}


static void EnetNetIF_initRxObj(Enet_Type enetType, uint32_t instId, uint32_t chEntryIdx, EnetNetIF_RxHandle hRx)
{

    if (hRx->refCount > 0)
    {
        hRx->refCount++;
    }
    else
    {
        EnetNetIFAppIf_GetRxHandleInArgs inArgs;
        EnetNetIFAppIf_RxHandleInfo outArgs = {0};

        inArgs.enetType        = enetType;
        inArgs.instId          = instId;
        inArgs.cbArg           = hRx;
        inArgs.notifyCb        = &EnetNetIF_notifyRxPackets;
        inArgs.chId            = chEntryIdx;
        // inArgs.pFreePbufInfoQ  = &hRx->freePbufInfoQ;
        inArgs.pReadyRxPktQ    = &hRx->readyRxPktQ;
        inArgs.pFreeRxPktInfoQ = &hRx->freeRxPktInfoQ;

        EnetNetIFAppCb_getRxHandleInfo(&inArgs, &outArgs);

        hRx->numPackets = outArgs.numPackets;
        hRx->flowIdx     = outArgs.rxFlowIdx;
        hRx->flowStartIdx = outArgs.rxFlowStartIdx;
        hRx->hFlow       = outArgs.hRxFlow;
        configASSERT(hRx->hFlow != NULL);
        hRx->disableEvent = outArgs.disableEvent;

        hRx->stats.freeAppPktEnq = outArgs.numPackets;

        hRx->refCount = 1U;
        hRx->chEntryIdx = chEntryIdx;
        for (uint32_t portIdx = 0; portIdx < CPSW_STATS_MACPORT_MAX; portIdx++)
        {
            hRx->mapPortToInterface[portIdx] = NULL;
        }
    }

    return;
}

// static void EnetNetIF_mapNetif2Rx(NetworkInterface_t * pxInterface,
//                         bool isDirected,
//                         EnetNetIF_RxHandle hRxEnet,
//                         xEnetDriverHandle hEnet)
// {

//     xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
//     BaseType_t xNetIFNum;

//     configASSERT(pxNetIFArgs != NULL);
//     xNetIFNum = pxNetIFArgs->xNetIFID;

//     configASSERT(xNetIFNum < ENET_FREERTOS_TCP_NETIF_COUNT);

//     hEnet->mapNetif2Rx[xNetIFNum] = hRxEnet;
//     hEnet->mapRxPort2Netif[xNetIFNum] = pxInterface;
// #if (ENET_ENABLE_PER_ICSSG == 1)
//     /* ToDo: ICSSG doesnot fill rxPortNum correctly, so using the hRxEnet->flowIdx to map to pxInterface*/
//     hEnet->mapRxPort2Netif[LWIP_RXFLOW_2_PORTIDX(hRxEnet->flowIdx)] = pxInterface;
// #endif
//     /* For non-directed packets, we map both ports to the first pxInterface*/
//     if(!isDirected)
//     {
//         for(uint32_t portIdx = 0U; portIdx < CPSW_STATS_MACPORT_MAX; portIdx++)
//         {
//             if(portIdx < FREERTOS_TCPIF_MAX_NETIFS_SUPPORTED)
//             {
//             hEnet->mapRxPort2Netif[portIdx] = pxInterface;
//             }
//         }
//     }
// }

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
            EnetQueue_enq(&rx->readyRxPktQ, &pDmaPacket->node);
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
    EnetDma_Pkt *pCurrDmaPacket = NULL;

    EnetQueue_initQ(&resubmitPktQ);
    pCurrDmaPacket = (EnetDma_Pkt*) EnetQueue_deq(&rx->readyRxPktQ);
    while (pCurrDmaPacket != NULL)
    {
        EnetDma_checkPktState(&pCurrDmaPacket->pktState,
                               ENET_PKTSTATE_MODULE_APP,
                               ENET_PKTSTATE_APP_WITH_READYQ,
                               ENET_PKTSTATE_APP_WITH_DRIVER);
        if ((pCurrDmaPacket->sgList.numScatterSegments <= 0)
                || (pCurrDmaPacket->sgList.numScatterSegments > ENET_ARRAYSIZE(pCurrDmaPacket->sgList.list))
                || (pCurrDmaPacket->sgList.list[0].bufPtr == NULL))
        {
            configASSERT(FALSE);
        }
        else
        {
            EnetQueue_enq(&resubmitPktQ, &pCurrDmaPacket->node);
        }

        pCurrDmaPacket = (EnetDma_Pkt*) EnetQueue_deq(&rx->readyRxPktQ);
    }
    if (EnetQueue_getQCount(&resubmitPktQ))
    {
        EnetNetIF_submitRxPackets(rx, &resubmitPktQ);
    }

}

// /*
//  * Enqueue a new packet and make sure that buffer descriptors are properly linked.
//  * NOTE: Not thread safe
//  */
// static void EnetNetIF_submitRxPktQ(EnetNetIF_RxObj *rx)
// {
//     EnetDma_PktQ resubmitPktQ;
//     NetworkBufferDescriptor_t * pxNetDesc;
//     EnetDma_Pkt *pCurrDmaPacket;
//     xEnetDriverHandle hEnet = rx->hEnetNetIF;

//     EnetQueue_initQ(&resubmitPktQ);

//     /*
//      * Fill in as many packets as we can with new PBUF buffers so they can be
//      * returned to the stack to be filled in.
//      */
//     pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&rx->readyRxPktQ);

//     while (pCurrDmaPacket != NULL)
//     {
//         pxNetDesc = (NetworkBufferDescriptor_t *)pCurrDmaPacket->appPriv;
//         if (pxNetDesc)
//         {
//             // TODO: deal with planned RX buffer allocation scheme for FR+TCP

//             EnetNetIF_AppIf_CustomNetBuf * pxCustomNetDesc = (EnetNetIF_AppIf_CustomNetBuf *) pxNetDesc;
            
//             pxCustomNetDesc->pktInfoMem = pCurrDmaPacket;
//             pxCustomNetDesc->freePktInfoQ = &rx->readyRxPktQ;
//             pxNetDesc->xDataLength = ENET_MEM_LARGE_POOL_PKT_SIZE; //FIXME: less than ENET_MEM_LARGE_POOL_PKT_SIZE because of padding
//             configASSERT(ENET_UTILS_ALIGN(hEnet->appInfo.hostPortRxMtu, ENETDMA_CACHELINE_ALIGNMENT) == ENET_MEM_LARGE_POOL_PKT_SIZE); //TODO check!

//             // LwipifEnetAppIf_custom_rx_pbuf* my_pbuf  = (LwipifEnetAppIf_custom_rx_pbuf*)pxNetDesc;

//             // my_pbuf->p.custom_free_function = LwipifEnetAppCb_pbuf_free_custom;
//             // my_pbuf->pktInfoMem         = pCurrDmaPacket;
//             // my_pbuf->freePktInfoQ         = &rx->freePktInfoQ;
//             // my_pbuf->p.pbuf.flags |= PBUF_FLAG_IS_CUSTOM;

//             // bufSize = ENET_UTILS_ALIGN(hEnet->appInfo.hostPortRxMtu, ENETDMA_CACHELINE_ALIGNMENT);
//             // pxNetDesc = pbuf_alloced_custom(PBUF_RAW, bufSize, PBUF_POOL, &my_pbuf->p, pCurrDmaPacket->sgList.list[0].bufPtr, pCurrDmaPacket->sgList.list[0].segmentAllocLen);

//             // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&rx->stats.freePbufPktDeq);
//             // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&rx->stats.freeAppPktDeq);

//             EnetQueue_enq(&resubmitPktQ, &pCurrDmaPacket->node);

//             pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&rx->freePktInfoQ);
//         }
//         else
//         {
//             EnetQueue_enq(&rx->freePktInfoQ, &pCurrDmaPacket->node);
//             break;
//         }
//     }

//     /*
//      * Return the same DMA packets back to the DMA channel (but now
//      * associated with a new PBM Packet and buffer)
//      */
//     if (EnetQueue_getQCount(&resubmitPktQ))
//     {
//         EnetNetIF_submitRxPackets(rx, &resubmitPktQ);
//     }
// }

// static int32_t EnetNetIF_startRxTx(xEnetDriverHandle hEnet)
// {
//     int32_t status = ENET_SOK;
//     uint32_t i;

//     for(i = 0U; i< hEnet->numRxChannels; i++)
//     {
//         configASSERT(NULL != hEnet->rx[i].hFlow);
//     }

//     for(i = 0U; i< hEnet->numTxChannels; i++)
//     {
//         configASSERT(NULL != hEnet->tx[i].hCh);
//         status = EnetDma_enableTxEvent(hEnet->tx[i].hCh);
//     }

//     for(i = 0U; i< hEnet->numRxChannels; i++)
//     {
//         /* Submit all allocated packets to DMA so it can use for packet RX */
//         EnetNetIF_submitRxPktQ(&hEnet->rx[i]);
//     }

//     return status;
// }

void EnetNetIF_retrieveTxPkts(EnetNetIF_TxHandle hTx)
{
    EnetDma_PktQ tempQueue;
    uint32_t packetCount = 0U;
    int32_t retVal;

    // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&hTx->stats.pktStats.rawNotifyCnt);
    packetCount = 0U;

    /* Retrieve the used (sent/empty) packets from the channel */
    {
        EnetQueue_initQ(&tempQueue);
        /* Retrieve all TX packets and keep them locally */
        retVal = EnetDma_retrieveTxPktQ(hTx->hCh, &tempQueue);
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
        packetCount = EnetNetIF_prepTxPktQ(hTx, &tempQueue);
    }
    else
    {
        // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&hTx->stats.pktStats.zeroNotifyCnt);
    }

    if (packetCount != 0U)
    {
        // TODO: take care of stats Lwip2Enet_updateTxNotifyStats(&hTx->stats.pktStats, packetCount, 0U);
    }
}

// static void EnetNetIF_timerCb(ClockP_Object *hClk, void * arg)
// {
// #if defined (ENET_SOC_HOSTPORT_DMA_TYPE_UDMA)
//     /* Post semaphore to rx handling task */
//     xEnetDriverHandle hEnet = (xEnetDriverHandle)arg;

//     if (hEnet->initDone)
//     {
//         for (uint32_t i = 0U; i < hEnet->numTxChannels; i++)
//         {
//             if (hEnet->tx[i].enabled)
//             {
//                 EnetNetIF_retrieveTxPkts(&hEnet->tx[i]);
//             }
//         }

//         if (hEnet->rxPktNotify.cbFxn != NULL)
//         {
//             hEnet->rxPktNotify.cbFxn(hEnet->rxPktNotify.cbArg);
//         }
//     }
// #endif
// }

static void EnetNetIF_timerCb(ClockP_Object *hClk, void * arg)
{
#if defined (ENET_SOC_HOSTPORT_DMA_TYPE_UDMA)
    /* Post semaphore to Rx and Tx Pkt handling task */
    xEnetDriverHandle hEnet = (xEnetDriverHandle)arg;

    if (hEnet->isInitDone)
    {
        for (uint32_t txChIdx = 0U; txChIdx < CONFIG_MAX_TX_CHANNELS; txChIdx++)
        {
            if ((hEnet->tx[txChIdx].refCount > 0) && (hEnet->tx[txChIdx].txPktNotify.cbFxn != NULL))
            {
                hEnet->tx[txChIdx].txPktNotify.cbFxn(hEnet->tx[txChIdx].txPktNotify.cbArg);
            }
        }

        for (uint32_t rxChIdx = 0U; rxChIdx < CONFIG_MAX_RX_CHANNELS; rxChIdx++)
        {
                if ((hEnet->rx[rxChIdx].refCount > 0) && (hEnet->rx[rxChIdx].rxPktNotify.cbFxn != NULL))
                {
                    hEnet->rx[rxChIdx].rxPktNotify.cbFxn(hEnet->rx[rxChIdx].rxPktNotify.cbArg);
                }
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

void EnetNetIF_setRxNotifyCallback(EnetNetIF_RxHandle hRx, Enet_notify_t *pRxPktNotify)
{
    hRx->rxPktNotify = *pRxPktNotify;
}

void EnetNetIF_setTxNotifyCallback(EnetNetIF_TxHandle hTx, Enet_notify_t *pTxPktNotify)
{
    hTx->txPktNotify = *pTxPktNotify;
}

// void EnetNetIF_setNotifyCallbacks(NetworkInterface_t * pxInterface, Enet_notify_t *pRxNotify, Enet_notify_t *pTxNotify)
// {

//     xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
//     xEnetDriverHandle hEnet = pxNetIFArgs->hEnet;
//     EnetNetIF_setRxNotifyCallback(hEnet, pRxNotify);
//     EnetNetIF_setTxNotifyCallback(hEnet, pTxNotify);
// }

void EnetNetIF_setNotifyCallbacks(NetworkInterface_t * pxInterface, Enet_notify_t *pRxNotify, Enet_notify_t *pTxNotify)
{
    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
    FreeRTOSTCP2Enet_netif_t * pxCustomInterface = &(pxNetIFArgs->hEnet->xInterface[pxNetIFArgs->xNetIFID]);

    for (uint32_t idx = 0; idx < pxCustomInterface->count_hTx; idx++)
    {
        EnetNetIF_setTxNotifyCallback(pxCustomInterface->hTx[idx], pTxNotify);
    }

    for (uint32_t idx = 0; idx < pxCustomInterface->count_hRx; idx++)
    {
        EnetNetIF_setRxNotifyCallback(pxCustomInterface->hRx[idx], pRxNotify);
    }
}

/*
* create a function called postEvent[i]. each event, each postfxn.
*/
static void EnetNetIFApp_postSemaphore(void *pArg)
{

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    if(xTxRxTask)
    {
        if(HwiP_inISR())
        {
            xTaskNotifyFromISR( xTxRxTask, (uint32_t) pArg, eSetBits, &xHigherPriorityTaskWoken );
            portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
        }
        else
        {
            xTaskNotify( xTxRxTask, (uint32_t) pArg, eSetBits );
        }
    }
    
}

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
        /* Free network buffer as it is transmitted by DMA now */
        vReleaseNetworkBufferAndDescriptor(pxNetworkBuffer);
        /* Return packet info to free pool */
        EnetQueue_enq(&tx->freePktInfoQ, &pCurrDmaPacket->node);
        pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(pPktQ);
    }

    // TODO: take care of stats LWIP2ENETSTATS_ADDNUM(&tx->stats.freeAppPktEnq, packetCount);

    return packetCount;
}

// void EnetNetIF_Enet_txPktHandler(xEnetDriverHandle hEnet)
// {
//     uint32_t txChNum;

//     for (txChNum = 0U; txChNum < hEnet->numTxChannels; txChNum++)
//     {
//         EnetNetIF_retrieveTxPkts(&hEnet->tx[txChNum]);
//     }


// }

// void EnetNetIF_txPktHandler(NetworkInterface_t * pxInterface)
// {
//     xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
//     xEnetDriverHandle hEnet = pxNetIFArgs->hEnet;
//     EnetNetIF_Enet_txPktHandler(hEnet);
// }

void EnetNetIF_txPktHandler(EnetNetIF_TxHandle hTx)
{
    EnetNetIF_retrieveTxPkts(hTx);
}

void EnetNetIF_Enet_txPktHandler(NetworkInterface_t * pxInterface)
{
    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
    FreeRTOSTCP2Enet_netif_t *pInterface = pxNetIFArgs->pInterface;
    for (uint32_t idx = 0; idx < pInterface->count_hTx; idx++)
    {
        EnetNetIF_txPktHandler(pInterface->hTx[idx]);
    }
}


#define   ETHTYPE_VLAN      (0x8100U)
#define SIZEOF_VLAN_HDR (4)
#define IP_PROTO_UDPLITE 136
#define PP_HTONS(x) ((uint16_t)((((x) & (uint16_t)0x00ffU) << 8) | (((x) & (uint16_t)0xff00U) >> 8)))
uint8_t* EnetNetIF_getIpPktStart(uint8_t* pEthpkt)
{
    const uint16_t type = ((EthernetHeader_t*)pEthpkt)->usFrameType;
    const uint32_t ipPacketStartOffset = (type == PP_HTONS(ETHTYPE_VLAN)) ?
                                         (ipSIZE_OF_ETH_HEADER + SIZEOF_VLAN_HDR) : (ipSIZE_OF_ETH_HEADER);

    return &pEthpkt[ipPacketStartOffset];
}

// bool LWIPIF_LWIP_UdpLiteValidateChkSum(NetworkBufferDescriptor_t * pxDescriptor)
// {
//     Lwip2Enet_assert(pxDescriptor->xDataLength >= (ipSIZE_OF_IP_HEADER + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER));

//     bool isChksumPass = true;
//     IPHeader_t * pIpPkt   = (IPHeader_t *)EnetNetIF_getIpPktStart((uint8_t*) pxDescriptor->pucEthernetBuffer);
//     uint8_t *pIpPayload     = (uint8_t*)pIpPkt + ((pIpPkt->ucVersionHeaderLength & 0x0F) << 2);
//     UDPHeader_t * pUdpHdr = (UDPHeader_t * )pIpPayload;
//     ip_addr_t srcIp;
//     ip_addr_t dstIp;

//     LWIPIF_LWIP_getSrcIp((uint8_t *)pIpPkt, &srcIp);
//     LWIPIF_LWIP_getDstIp((uint8_t *)pIpPkt, &dstIp);

//     const uint32_t chkSumCovLen = (lwip_ntohs(pUdpHdr->len) == 0) ? (lwip_ntohs(IPH_LEN(pIpPkt)) - (IPH_HL(pIpPkt) << 2)) : lwip_ntohs(pUdpHdr->len);

//     if (chkSumCovLen < sizeof(struct udp_hdr))
//     {
//         isChksumPass = false;
//         return false;
//     }

//     if (0 == LWIPIF_LWIP_getUdpLiteChksum(p, (IPH_HL(pIpPkt) << 2), (lwip_ntohs(IPH_LEN(pIpPkt)) - (IPH_HL(pIpPkt) << 2)), pUdpHdr, &srcIp, &dstIp))
//     {
//         isChksumPass = true;
//     }
//     else
//     {
//         isChksumPass = false;
//     }

//     /* Return value should indicate true if checksum error found */
//     return (!isChksumPass);
// }

// static uint32_t EnetNetIF_prepRxPktQ(EnetNetIF_RxObj *rx,
//                                      EnetDma_PktQ *pPktQ)
// {
//     uint32_t packetCount = 0U;
//     EnetDma_Pkt *pCurrDmaPacket;
//     bool isChksumError = false;
//     uint32_t validLen = 0U;

//     pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(pPktQ);
//     while (pCurrDmaPacket)
//     {
//         /* Get the full PBUF packet that needs to be returned to the LwIP stack */
//         NetworkBufferDescriptor_t * pxDescriptor = (NetworkBufferDescriptor_t *)pCurrDmaPacket->appPriv;
//         isChksumError = false;
//         if (pxDescriptor)
//         {
//             validLen = pCurrDmaPacket->sgList.list[0].segmentFilledLen;

//             /* Fill in PBUF packet length field */
//             pxDescriptor->xDataLength = validLen;
//             // pxDescriptor->tot_len = validLen;
//             configASSERT(pxDescriptor->pucEthernetBuffer != NULL);

// #if ((ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT) == 1) && (ENET_ENABLE_PER_CPSW == 1))
//             {
//                 IPHeader_t * pIpPkt = ( IPHeader_t * ) EnetNetIF_getIpPktStart((uint8_t*) pxDescriptor->pucEthernetBuffer);
//                 if (pIpPkt->ucProtocol == IP_PROTO_UDPLITE)
//                 {
//                     // TODO take care of UDP Lite
//                     configASSERT(pdFALSE);
//                     //isChksumError = LWIPIF_LWIP_UdpLiteValidateChkSum(pxDescriptor);
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
//             if (!isChksumError)
//             {
//                 /* Pass the received packet to the LwIP stack */
//                 IPHeader_t * pIpPkt   = (IPHeader_t *)EnetNetIF_getIpPktStart((uint8_t*) pxDescriptor->pucEthernetBuffer);
//                 if(pIpPkt->ucProtocol != 0x70) 
//                 {
//                     AM243x_Eth_NetworkInterfaceInput(rx, pCurrDmaPacket->rxPortNum, pxDescriptor);
//                     packetCount++;
//                 }
//                 else
//                 {
//                     EnetQueue_enq(&rx->freePktInfoQ, &pCurrDmaPacket->node);
//                 }
                
//             }
//             else
//             {
//                 /* Put PBUF buffer in free Q as we are not passing to stack */
//                 EnetQueue_enq(&rx->freePktInfoQ, &pCurrDmaPacket->node);
//                 // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&rx->stats.freeAppPktEnq);
//                 // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&rx->stats.chkSumErr);
//             }

//             /* Put packet info into free Q as we have removed the PBUF buffers
//              * from the it */
//             pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(pPktQ);
//         }
//         else
//         {
//             /* Should never happen as this is received from HW */
//             configASSERT(FALSE);
//         }
//     }

//     /* return as many packets to driver as we can */
//     EnetNetIF_submitRxPktQ(rx);

//     return packetCount;
// }

static uint32_t EnetNetIF_prepRxPktQ(EnetNetIF_RxObj *rx,
                                     EnetDma_PktQ *pPktQ)
{
    uint32_t packetCount = 0U;
    EnetDma_Pkt *pCurrDmaPacket;
    bool isChksumError = false;
    uint32_t scatterSegmentIndex = 0U;
    EnetDma_SGListEntry *list = NULL;
    // struct pbuf *hPbufPacket = NULL;
    NetworkBufferDescriptor_t *pxhNetworkBuffer = NULL;
    EnetNetIF_AppIf_CustomNetBuf *cPbuf = NULL;
    EnetNetIF_AppIf_CustomNetBuf *cPbufPrev = NULL;

    pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(pPktQ);
    while (pCurrDmaPacket)
    {
        isChksumError = false;
        configASSERT(pCurrDmaPacket->sgList.numScatterSegments <= ENET_ARRAYSIZE(pCurrDmaPacket->sgList.list));
        configASSERT(pCurrDmaPacket->sgList.numScatterSegments != 0);
        // if (uNetworkBufferDescriptorQueue_count(&rx->freePbufInfoQ) >= pCurrDmaPacket->sgList.numScatterSegments)
        // {
            EnetDma_checkPktState(&pCurrDmaPacket->pktState,
                                  ENET_PKTSTATE_MODULE_APP,
                                  ENET_PKTSTATE_APP_WITH_DRIVER,
                                  ENET_PKTSTATE_APP_WITH_FREEQ);
            scatterSegmentIndex = 0;
            Enet_MacPort rxPortNum = pCurrDmaPacket->rxPortNum;
            while (scatterSegmentIndex < pCurrDmaPacket->sgList.numScatterSegments)
            {
                list = &pCurrDmaPacket->sgList.list[scatterSegmentIndex];
                configASSERT(list->bufPtr != NULL);

                // cPbuf  = (Rx_CustomPbuf *)NetBufQueue_deQ(&rx->freePbufInfoQ);
                cPbuf = (EnetNetIF_AppIf_CustomNetBuf *) pxPacketBuffer_to_NetworkBuffer(list->bufPtr);
                // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&rx->stats.freePbufPktDeq);
                if (scatterSegmentIndex == 0)
                {
                    /* store the head of the pbuf */
                    pxhNetworkBuffer = &(cPbuf->xNetworkBuffer);
                }
                configASSERT(pxhNetworkBuffer != NULL);
                /* Fill the pbuf with the sg list data */
                // if (Lwip2Enet_setCustomPbuf(PBUF_RAW, list->segmentFilledLen, PBUF_POOL, &(cPbuf->p), list->bufPtr, list->segmentAllocLen) == NULL)
                // {
                //     Lwip2Enet_assert(false);
                // }
                cPbuf->orgBufLen = list->segmentAllocLen;
                cPbuf->orgBufPtr = list->bufPtr;
                cPbuf->alivePbufCount = pCurrDmaPacket->sgList.numScatterSegments;

                configASSERT(scatterSegmentIndex < 1);

                // if (scatterSegmentIndex > 0)
                // {
                //     cPbufPrev->next = cPbuf;
                //     pbuf_cat(hPbufPacket, &(cPbuf->p.pbuf));
                // }

                if (scatterSegmentIndex == pCurrDmaPacket->sgList.numScatterSegments - 1)
                {
                    /* Make sure the next pointer of last pbuf is NULL */
                    // cPbuf->p.pbuf.next = NULL;
                    // cPbuf->xNetworkBuffer.
                    /* Point the last to first. If there is only one segment, it points to itself. */
                    cPbuf->next = (EnetNetIF_AppIf_CustomNetBuf *) pxhNetworkBuffer;
                }
                
                cPbufPrev = cPbuf;
                scatterSegmentIndex++;
            }


            {
                configASSERT(pxhNetworkBuffer->pucEthernetBuffer != NULL);
                IPHeader_t * pIpPkt   = (IPHeader_t *) EnetNetIF_getIpPktStart((uint8_t*) pxhNetworkBuffer->pucEthernetBuffer);

                (void) pIpPkt;
                
                // TODO: Take care of checksum offload
                
                // if (IPH_PROTO(pIpPkt) == IP_PROTO_UDPLITE)
                // {
                //     /* As HW is can not compute checksum offload for UDP-lite packet, trigger SW checksum validation */
                //     isChksumError = LWIPIF_LWIP_UdpLiteValidateChkSum(pxhNetworkBuffer);
                // }
                // else
                // {
                //     /* We don't check if HW checksum offload is enabled while checking for checksum error
                //      * as default value of this field when offload not enabled is false */
                //     const uint32_t csumInfo =  pCurrDmaPacket->chkSumInfo;

                //     if (ENETDMA_RXCSUMINFO_GET_IPV4_FLAG(csumInfo) ||
                //         ENETDMA_RXCSUMINFO_GET_IPV6_FLAG(csumInfo))
                //     {
                //         isChksumError = ENETDMA_RXCSUMINFO_GET_CHKSUM_ERR_FLAG(csumInfo);
                //     }
                // }
            }

            EnetDma_initPktInfo(pCurrDmaPacket);
            EnetQueue_enq(&rx->freeRxPktInfoQ, &pCurrDmaPacket->node);
            // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&rx->stats.freeAppPktEnq);

            if (!isChksumError)
            {
                NetworkInterface_t * pxInterface = NULL;
                /* Pass the received packet to the LwIP stack */
                switch (rx->mode)
                {
                case EnetNetIF_RxMode_SwitchSharedChannel:
                case EnetNetIF_RxMode_MacSharedChannel:
                {
                    configASSERT(rxPortNum < FREERTOS_TCPIF_MAX_NUM_MAC_PORTS);
                    pxInterface = rx->mapPortToInterface[rxPortNum];
                    break;
                }
                case EnetNetIF_RxMode_MacPort1Channel:
                case EnetNetIF_RxMode_SwitchPort1Channel:
                {
                    pxInterface = rx->mapPortToInterface[ENET_MAC_PORT_1];
                    break;
                }
                case EnetNetIF_RxMode_MacPort2Channel:
                case EnetNetIF_RxMode_SwitchPort2Channel:
                {
                    configASSERT(FREERTOS_TCPIF_MAX_NUM_MAC_PORTS == 2);
                    pxInterface = rx->mapPortToInterface[FREERTOS_TCPIF_MAX_NUM_MAC_PORTS - 1];
                    break;
                }
                default:
                {
                    configASSERT(false);
                }
                }

                configASSERT(pxInterface != NULL);
                AM243x_Eth_NetworkInterfaceInput(rx, pxInterface, pxhNetworkBuffer);
                packetCount++;
            }
            else
            {
                /* Free the pbuf as we are not submitting to the stack */
                vReleaseNetworkBufferAndDescriptor(pxhNetworkBuffer);
                // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&rx->stats.chkSumErr);
            }
        // }
        // else
        // {
        //     /*! This should not occur as we have equal number of pbufInfos and bufptrs */
        //     Lwip2Enet_assert(FALSE);
        // }
        pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(pPktQ);
    }

    /* return as many packets to driver as we can */
    EnetNetIF_submitRxPktQ(rx);

    return packetCount;
}

// void EnetNetIF_rxPktHandler(xEnetDriverHandle hEnet)
// {
//     EnetDma_PktQ tempQueue;
//     int32_t retVal;
//     uint32_t pktCnt, rxChNum;

//     for(rxChNum = 0U; rxChNum < hEnet->numRxChannels; rxChNum++)
//     {
//         pktCnt = 0U;
//         // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&hEnet->rx[rxChNum].stats.pktStats.rawNotifyCnt);

//         /* Retrieve the used (filled) packets from the channel */
//         {
//             EnetQueue_initQ(&tempQueue);
//             retVal = EnetDma_retrieveRxPktQ(hEnet->rx[rxChNum].hFlow, &tempQueue);
//             if (ENET_SOK != retVal)
//             {
//                 FreeRTOS_printf(("Lwip2Enet_rxPacketTask: failed to retrieve RX pkts: %d\n",
//                                 retVal));
//             }
//         }
//         if (tempQueue.count == 0U)
//         {
//             // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&hEnet->rx[rxChNum].stats.pktStats.zeroNotifyCnt);
//         }

//         /*
//          * Call Lwip2Enet_prepRxPktQ() even if no packets were received.
//          * This allows new packets to be submitted if PBUF buffers became
//          * newly available and there were outstanding free packets.
//          */
//         {
//             /*
//              * Get all used Rx DMA packets from the hardware, then send the buffers
//              * of those packets on to the LwIP stack to be parsed/processed.
//              */
//             pktCnt = EnetNetIF_prepRxPktQ(&hEnet->rx[rxChNum], &tempQueue);
//         }

//         /*
//          * We don't want to time the semaphore post used to notify the LwIP stack as that may cause a
//          * task transition. We don't want to time the semaphore pend, since that would time us doing
//          * nothing but waiting.
//          */
//         if (pktCnt != 0U)
//         {
//             // TODO: take care of stats Lwip2Enet_updateRxNotifyStats(&hEnet->rx[rxChNum].stats.pktStats, pktCnt, 0U);
//         }

//         // ClockP_start(&hEnet->pacingClkObj);

//         if (!hEnet->rx[rxChNum].disableEvent)
//         {
//             EnetDma_enableRxEvent(hEnet->rx[rxChNum].hFlow);
//         }
//     }

// }

void EnetNetIF_rxPktHandler(EnetNetIF_RxHandle hRx)
{
    EnetDma_PktQ tempQueue;
    int32_t retVal;
    uint32_t pktCnt = 0U;

    // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&hRx->stats.pktStats.rawNotifyCnt);

    /* Retrieve the used (filled) packets from the channel */
    {
        EnetQueue_initQ(&tempQueue);
        retVal = EnetDma_retrieveRxPktQ(hRx->hFlow, &tempQueue);
        if (ENET_SOK != retVal)
        {
            FreeRTOS_printf(("Lwip2Enet_rxPacketTask: failed to retrieve RX pkts: %d\n",
                    retVal));
        }
    }
    if (tempQueue.count == 0U)
    {
        // TODO: take care of stats LWIP2ENETSTATS_ADDONE(&hRx->stats.pktStats.zeroNotifyCnt);
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
        pktCnt = EnetNetIF_prepRxPktQ(hRx, &tempQueue);
    }

    /*
     * We don't want to time the semaphore post used to notify the LwIP stack as that may cause a
     * task transition. We don't want to time the semaphore pend, since that would time us doing
     * nothing but waiting.
     */
    if (pktCnt != 0U)
    {
        // TODO: take care of stats Lwip2Enet_updateRxNotifyStats(&hRx->stats.pktStats, pktCnt, 0U);
    }

    // ClockP_start(&hLwip2Enet->pacingClkObj);

    if (!hRx->disableEvent)
    {
        EnetDma_enableRxEvent(hRx->hFlow);
    }

}

// void EnetNetIF_Enet_rxPktHandler(NetworkInterface_t * pxInterface)
// {
//     xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
//     xEnetDriverHandle hEnet = pxNetIFArgs->hEnet;
//     EnetNetIF_rxPktHandler(hEnet);
// }

void EnetNetIF_Enet_rxPktHandler(NetworkInterface_t * pxInterface)
{
    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
    FreeRTOSTCP2Enet_netif_t *pInterface = pxNetIFArgs->pInterface;
    for (uint32_t idx = 0; idx < pInterface->count_hRx; idx++)
    {
        EnetNetIF_rxPktHandler(pInterface->hRx[idx]);
    }
}


static void EnetNetIFApp_txrxPacketTask(void *arg)
{
    NetworkInterface_t * pxInterface = (NetworkInterface_t *) arg;
    uint32_t ulNotifiedValue;
    while (!shutDownFlag)
    {
        xTaskNotifyWait(0, ULONG_MAX, &ulNotifiedValue, portMAX_DELAY );

        if (ulNotifiedValue & ENET_RX_NOTIFY_BIT)
        {
            /* Wait for the Rx ISR to notify us that packets are available with data */
            
            //FreeRTOS_debug_printf(("===> RX CMPLT DSR: %d, TOT: %d\n", rxISRCnt, totalISRCnt));
            if (shutDownFlag)
            {
                /* This translation layer is shutting down, don't give anything else to the stack */
                break;
            }

            EnetNetIF_Enet_rxPktHandler(pxInterface);
        }
        
        if (ulNotifiedValue & ENET_TX_NOTIFY_BIT)
        {
            /*
            * Wait for the Tx ISR to notify us that empty packets are available
            * that were used to send data
            */
            EnetNetIF_Enet_txPktHandler(pxInterface);
        }
        
    }

    /* We are shutting down, notify that we are done */
    SemaphoreP_post(&shutDownSemObj);
}

void EnetNetIFApp_createTxRxPktHandlerTask(NetworkInterface_t * pxInterface)
{


    xTxRxTask = xTaskCreateStatic(&EnetNetIFApp_txrxPacketTask, "EnetNetIFApp_rxPacketTask", sizeof(gPktTxRxTaskStack) / (sizeof(configSTACK_DEPTH_TYPE)), \
    pxInterface, ENETNETIF_RX_PACKET_TASK_PRI, (StackType_t*) &gPktTxRxTaskStack[0], &xTxRxTaskStaticObj);
    
    // configASSERT(ret_status == pdPASS);

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
        list->disableCacheOps = false; // TODO: check use of curNetBuf->type_internal == PBUF_ROM

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

// void EnetNetIF_sendTxPackets(EnetNetIF_TxObj *tx,
//                              Enet_MacPort macPort)
// {
//     xEnetDriverHandle hEnet;
//     EnetDma_Pkt *pCurrDmaPacket;
//     NetworkBufferDescriptor_t * netBufPkt;

//     hEnet = tx->hEnetNetIF;

//     /* If link is not up, simply return */
//     if (hEnet->isLinkUp)
//     {
//         EnetDma_PktQ txSubmitQ;

//         EnetQueue_initQ(&txSubmitQ);

//         if (uNetworkBufferDescriptorQueue_count(&tx->unusedPbufQ))
//         {
//             /* send any pending TX Q's */
//             EnetNetIF_pbufQ2PktInfoQ(tx, &tx->unusedPbufQ, &txSubmitQ, macPort);
//         }

//         /* Check if there is anything to transmit, else simply return */
//         while (uNetworkBufferDescriptorQueue_count(&tx->readyPbufQ) != 0U)
//         {
//             /* Dequeue one free TX Eth packet */
//             pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&tx->freePktInfoQ);

//             if (pCurrDmaPacket == NULL)
//             {
//                 /* If we run out of packet info Q, retrieve packets from HW
//                 * and try to dequeue free packet again */
//                 EnetNetIF_retrieveTxPkts(tx);
//                 pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&tx->freePktInfoQ);
//             }

//             if (NULL != pCurrDmaPacket)
//             {
//                 netBufPkt = NetBufQueue_deQ(&tx->readyPbufQ);
//                 EnetDma_initPktInfo(pCurrDmaPacket);

//                 EnetNetIF_setSGList(pCurrDmaPacket, netBufPkt, false);
//                 pCurrDmaPacket->appPriv    = netBufPkt;
//                 pCurrDmaPacket->txPortNum  = macPort;
//                 pCurrDmaPacket->node.next  = NULL;
//                 pCurrDmaPacket->chkSumInfo = 0U;
// // TODO: Handle ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
// // #if ((ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT) == 1) && (ENET_ENABLE_PER_CPSW == 1))
// //                 pCurrDmaPacket->chkSumInfo = LWIPIF_LWIP_getChkSumInfo(netBufPkt);
// // #endif

//                 ENET_UTILS_COMPILETIME_ASSERT(offsetof(EnetDma_Pkt, node) == 0U);
//                 EnetQueue_enq(&txSubmitQ, &(pCurrDmaPacket->node));

//                 // TODO update stats macro LWIP2ENETSTATS_ADDONE(&tx->stats.freeAppPktDeq);
//                 // TODO update stats macro LWIP2ENETSTATS_ADDONE(&tx->stats.readyPbufPktDeq);
//             }
//             else
//             {
//                 break;
//             }
//         }

//         /* Submit the accumulated packets to the hardware for transmission */
//         EnetNetIF_submitTxPackets(tx, &txSubmitQ);
//     }
// }

void EnetNetIF_sendTxPackets(FreeRTOSTCP2Enet_netif_t* pInterface, const Enet_MacPort macPort)
{
    NetworkBufferDescriptor_t * netBufPkt;

    /* If link is not up, simply return */
    if (pInterface->isLinkUp)
    {
        EnetDma_PktQ txSubmitQ;
        EnetNetIF_TxHandle hTx = pInterface->hTx[0];
        EnetQueue_initQ(&txSubmitQ);

        if (uNetworkBufferDescriptorQueue_count(&hTx->unusedPbufQ))
        {
            /* send any pending TX Q's */
            EnetNetIF_pbufQ2PktInfoQ(hTx, &hTx->unusedPbufQ, &txSubmitQ, macPort);
        }

        /* Check if there is anything to transmit, else simply return */
        while (uNetworkBufferDescriptorQueue_count(&hTx->readyPbufQ) != 0U)
        {
            /* Dequeue one free TX Eth packet */
            EnetDma_Pkt *pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&hTx->freePktInfoQ);

            if (pCurrDmaPacket == NULL)
            {
                /* If we run out of packet info Q, retrieve packets from HW
                * and try to dequeue free packet again */
                EnetNetIF_retrieveTxPkts(hTx);
                pCurrDmaPacket = (EnetDma_Pkt *)EnetQueue_deq(&hTx->freePktInfoQ);
            }

            if (NULL != pCurrDmaPacket)
            {

                netBufPkt = NetBufQueue_deQ(&hTx->readyPbufQ);
                EnetDma_initPktInfo(pCurrDmaPacket);

                configASSERT(netBufPkt);

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

                // TODO update stats macro LWIP2ENETSTATS_ADDONE(&hTx->stats.freeAppPktDeq);
                // TODO update stats macro LWIP2ENETSTATS_ADDONE(&hTx->stats.readyPbufPktDeq);
            }
            else
            {
                break;
            }
        }

        /* Submit the accumulated packets to the hardware for transmission */
        EnetNetIF_submitTxPackets(hTx, &txSubmitQ);
    }
}


void EnetNetIF_periodicFxn(NetworkInterface_t * pxInterface)
{
    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
    FreeRTOSTCP2Enet_netif_t* pInterface = (FreeRTOSTCP2Enet_netif_t*)pxNetIFArgs->pInterface;

    configASSERT(pInterface != NULL);
    configASSERT(pInterface->hRx != NULL);
    configASSERT(pInterface->hTx != NULL);
    uint32_t prevLinkState = pInterface->isLinkUp;

#if (1U == ENET_CFG_DEV_ERROR)
#if defined (ENET_SOC_HOSTPORT_DMA_TYPE_UDMA)
    int32_t status;
#endif

    for(uint32_t i = 0U; i < pInterface->count_hTx; i++)
    {
        EnetQueue_verifyQCount(&pInterface->hTx[i]->freePktInfoQ);

#if defined (ENET_SOC_HOSTPORT_DMA_TYPE_UDMA)
        status = EnetUdma_checkTxChSanity(pInterface->hTx[i]->hCh, 5U);
        if (status != ENET_SOK)
        {
            FreeRTOS_printf((pInterface->hTx[i]->hEnetNetIF, "EnetUdma_checkTxChSanity Failed\n"));
        }
#endif
    }

    for(uint32_t i = 0U; i <  pInterface->count_hRx; i++)
    {
        EnetQueue_verifyQCount(&pInterface->hRx[i]->readyRxPktQ);

#if defined (ENET_SOC_HOSTPORT_DMA_TYPE_UDMA)
        status = EnetUdma_checkRxFlowSanity(pInterface->hRx[i]->hFlow, 5U);
        if (status != ENET_SOK)
        {
            FreeRTOS_printf((pInterface->hRx[i]->hEnetNetIF, "EnetUdma_checkRxFlowSanity Failed\n"));
        }
#endif
    }
#endif

    /*
     * Return the same DMA packets back to the DMA channel (but now
     * associated with a new PBUF Packet and buffer)
     */

    for (uint32_t idx = 0; idx < pInterface->count_hRx; idx++)
    {
        if (EnetQueue_getQCount(&pInterface->hRx[idx]->readyRxPktQ) > 0U)
        {
            EnetNetIF_submitRxPktQ(pInterface->hRx[idx]);
        }
    }

    /* Get current link status as reported by the hardware driver */
    pInterface->isLinkUp = pInterface->isPortLinkedFxn(pInterface->hEnet);
    for (uint32_t idx = 0; idx < pInterface->count_hRx; idx++)
    {
        const uint32_t prevLinkInterface = pInterface->hRx[idx]->hEnetNetIF->currLinkedIf;
        // get the linked interface details.
        /* If the interface changed, discard any queue packets (since the MAC would now be wrong) */
        if (prevLinkInterface != pInterface->hRx[idx]->hEnetNetIF->currLinkedIf)
        {
            /* ToDo: Discard all queued packets */
        }
    }

    /* If link status changed from down->up, then send any queued packets */
    if ((prevLinkState == 0U) && (pInterface->isLinkUp))
    {
        const Enet_MacPort macPort = pInterface->macPort;
        EnetNetIF_sendTxPackets(pInterface, macPort);
    }


#if 0 //The below CPU load profilling logic has to be re-worked for all OS variants
#if defined(LWIPIF_INSTRUMENTATION_ENABLED)
    static uint32_t loadCount = 0U;
    TaskP_Load stat;

    hEnetNetIF->stats.cpuLoad[loadCount] = TaskP_loadGetTotalCpuLoad();

    TaskP_loadGet(&hEnetNetIF->rxPacketTaskObj, &stat);
    for(uint32_t i = 0U; i < hEnetNetIF->numRxChannels; i++)
    {
        hEnetNetIF->rx[i].stats.pktStats.taskLoad[loadCount] = stat.cpuLoad;
    }

    TaskP_loadGet(&hEnetNetIF->txPacketTaskObj, &stat);
    for(uint32_t i = 0U; i < hEnetNetIF->numRxChannels; i++)
    {
        hEnetNetIF->tx[i].stats.pktStats.taskLoad[loadCount] = stat.cpuLoad;
    }

    loadCount = (loadCount + 1U) & (HISTORY_CNT - 1U);
#endif
#endif


}

void EnetNetIF_periodic_polling(NetworkInterface_t * pxFirstInterface)
{
    NetworkInterface_t * pxInterface = pxFirstInterface;
    do // loop along all the netifs (reverse linked list)
    {
        xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
        FreeRTOSTCP2Enet_netif_t * pInterface = (FreeRTOSTCP2Enet_netif_t *) pxNetIFArgs->pInterface;

        /* Periodic Function to update Link status */
        EnetNetIF_periodicFxn(pxInterface);

        if (!(pInterface->isLinkUp == pxNetIFArgs->xLinkUp))
        {
            if (pInterface->isLinkUp)
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
        params.args           = pxInterface; //&(gNetif[ENET_FREERTOS_TCP_NETIF_COUNT - 1]);
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
    // uint32_t status;
    
    Enet_notify_t rxNotify =
        {
           .cbFxn = &EnetNetIFApp_postSemaphore, //gives different cb fxn for different events.
           .cbArg = (void *) ENET_RX_NOTIFY_BIT //
        };
    Enet_notify_t txNotify =
        {
                .cbFxn = &EnetNetIFApp_postSemaphore,
                .cbArg = (void *) ENET_TX_NOTIFY_BIT
        };

    EnetNetIF_setNotifyCallbacks(pxInterface, &rxNotify, &txNotify);

    /* Initialize TX RX Task*/
    EnetNetIFApp_createTxRxPktHandlerTask(pxInterface);

    // /* Initialize Polling task*/
    EnetNetIF_EnetApp_createPollTask(pxInterface);
}

static xEnetDriverHandle FreeRTOSTCP2Enet_allocateObj(void)
{
    uintptr_t key = EnetOsal_disableAllIntr();
    xEnetDriverHandle hEnet = &gEnetDriverObj;

    if (!hEnet->isAllocated)
    {
        hEnet = &gEnetDriverObj;
        //phn initialize hEnet
        hEnet->isAllocated = true;
        hEnet->isInitDone = false;

        for (uint32_t rxChIdIdx = 0; rxChIdIdx < CONFIG_MAX_RX_CHANNELS; rxChIdIdx++)
        {
            hEnet->rx[rxChIdIdx].refCount = 0;
        }

        for (uint32_t txChIdIdx = 0; txChIdIdx < CONFIG_MAX_TX_CHANNELS; txChIdIdx++)
        {
            hEnet->tx[txChIdIdx].refCount = 0;
        }
    }

    EnetOsal_restoreAllIntr(key);

    return hEnet;
}

static EnetNetIF_RxHandle EnetNetIF_allocateRxHandle(xEnetDriverHandle hEnet, Enet_Type enetType, uint32_t instId, const uint32_t objIdx)
{
    uintptr_t key = EnetOsal_disableAllIntr();
    EnetNetIF_RxHandle hRx = NULL;
    if (objIdx < FREERTOS_TCPIF_MAX_RX_CHANNELS)
    {
        hRx = &hEnet->rx[objIdx];
    }

    EnetOsal_restoreAllIntr(key);

    return hRx;
}

static EnetNetIF_TxHandle EnetNetIF_allocateTxHandle(xEnetDriverHandle hEnet, Enet_Type enetType, uint32_t instId, const uint32_t objIdx)
{
    uintptr_t key = EnetOsal_disableAllIntr();
    EnetNetIF_TxHandle hTx = NULL;
    if (objIdx < FREERTOS_TCPIF_MAX_TX_CHANNELS)
    {
        hTx = &hEnet->tx[objIdx];
    }

    EnetOsal_restoreAllIntr(key);

    return hTx;
}

Enet_MacPort EnetNetIF_findMacPortFromEnet(Enet_Type enetType, uint32_t instId) // move to Cb file autogenerated
{
    Enet_MacPort macPort = ENET_MAC_PORT_INV;
    if (enetType == ENET_ICSSG_DUALMAC)
    {
        macPort = (Enet_MacPort)(instId & 0x01);
    }
    return macPort;
}

xEnetDriverHandle FreeRTOSTCPEnet_open(NetworkInterface_t * pxInterface)
{
 
    uint32_t txChIdList[FREERTOS_TCPIF_MAX_TX_CHANNELS_PER_PHERIPHERAL];
    uint32_t rxChIdList[FREERTOS_TCPIF_MAX_TX_CHANNELS_PER_PHERIPHERAL];
    EnetApp_GetMacAddrOutArgs          macAddr;
    EnetApp_HandleInfo                 handleInfo;
    xEnetDriverHandle    hEnet = FreeRTOSTCP2Enet_allocateObj();
    FreeRTOSTCP2Enet_netif_t*  pInterface = &(hEnet->xInterface[hEnet->numOpenedNetifs++]);
    uint32_t txChIdCount = 0, rxChIdCount = 0;
    NetworkEndPoint_t * pxEndPoint;
    xNetIFArgs *pxNetIFArgs = ( (xNetIFArgs *) pxInterface->pvArgument);
    const uint32_t FreeRTOSldx2Enet[ENET_FREERTOS_TCP_NETIF_COUNT][2] = {{ENET_CPSW_3G, 0},};
    BaseType_t xNetIFNum;

        /* Peripheral type */
    Enet_Type enetType = FreeRTOSldx2Enet[0][0];

    /* Peripheral instance */
    uint32_t instId = FreeRTOSldx2Enet[0][1];

    /* get TxChID & RxChID and the corresponding channel counts */
    
    EnetApp_getTxChIDs(enetType, instId, &txChIdCount, &txChIdList[0]);
    EnetApp_getRxChIDs(enetType, instId, &rxChIdCount, &rxChIdList[0]);


    EnetApp_acquireHandleInfo(enetType, instId, &handleInfo);
    configASSERT(handleInfo.hEnet != NULL);
    pInterface->hEnet = handleInfo.hEnet;
    pInterface->pxInterface = pxInterface;

    /* MCast List is EMPTY */
    hEnet->MCastCnt = 0U;

    /* Init internal bookkeeping fields */
    hEnet->oldMCastCnt = 0U;

    if (hEnet->isInitDone == false)
    {
        /* First init tasks, semaphores and clocks. This is required because
         * EnetDma event cb ISR can happen immediately after opening rx flow
         * in LwipifEnetAppCb_getHandle and all semaphores, clocks and tasks should
         * be valid at that point
         */

        EnetNetIFAppCb_getEnetIFInstInfo(enetType, instId, &hEnet->appInfo);

        /* Save params received from application interface */
        EnetNetIF_saveAppIfCfg(hEnet, &hEnet->appInfo);

        configASSERT(hEnet->appInfo.isPortLinkedFxn != NULL);
        configASSERT(hEnet->appInfo.pPbufInfo != NULL);

        NetBufQueue_init_freeQ(hEnet->appInfo.pPbufInfo, hEnet->appInfo.pPbufInfoSize);

        /* set the print function callback if not null */
        hEnet->print = (Enet_Print) &EnetUtils_printf;
        hEnet->isInitDone = true;
        EnetNetIF_createTimer(hEnet);
    }

    /* Associate with corresponding Tx Channels */
    for (uint32_t txChIdIndex = 0; txChIdIndex < txChIdCount; txChIdIndex++)
    {
        const uint32_t txChId = txChIdList[txChIdIndex];
        pInterface->hTx[txChIdIndex] = EnetNetIF_allocateTxHandle(hEnet, enetType, instId, txChId);
        EnetNetIF_initTxObj(enetType, instId, txChId, pInterface->hTx[txChIdIndex]);
        pInterface->hTx[txChIdIndex]->hEnetNetIF = hEnet;
        configASSERT(NULL != pInterface->hTx[txChIdIndex]->hCh);
        if (pInterface->hTx[txChIdIndex]->refCount == 1)
        {
            hEnet->allocPktInfo += pInterface->hTx[txChIdIndex]->numPackets;
            EnetDma_enableTxEvent(pInterface->hTx[txChIdIndex]->hCh);
        }
    }
    pInterface->count_hTx = txChIdCount;

    /* Associate with corresponding Rx Channels */
    for (uint32_t rxChIdIdx = 0; rxChIdIdx < rxChIdCount; rxChIdIdx++)
    {
        const uint32_t rxChId = rxChIdList[rxChIdIdx];
        pInterface->hRx[rxChIdIdx] = EnetNetIF_allocateRxHandle(hEnet, enetType, instId, rxChId);

        configASSERT( rxChIdIdx < 1 );

        extern BaseType_t xNetworkBuffersInitialise_RX( void );
        xNetworkBuffersInitialise_RX();

        EnetNetIF_initRxObj(enetType, instId, rxChId, pInterface->hRx[rxChIdIdx]);

        /* Process pxInterface related parameters*/
        pInterface->hRx[rxChIdIdx]->mode = EnetApp_getRxMode(enetType, instId);
        if ((pInterface->hRx[rxChIdIdx]->mode == EnetNetIF_RxMode_SwitchSharedChannel) ||
            (pInterface->hRx[rxChIdIdx]->mode == EnetNetIF_RxMode_SwitchPort1Channel) ||
            (pInterface->hRx[rxChIdIdx]->mode == EnetNetIF_RxMode_SwitchPort2Channel))
        {
            for (uint32_t portIdx = 0; portIdx < CPSW_STATS_MACPORT_MAX; portIdx++)
            {
                pInterface->hRx[rxChIdIdx]->mapPortToInterface[portIdx] = pxInterface;
            }
            pInterface->macPort = ENET_MAC_PORT_INV;
        }
        else if (pInterface->hRx[rxChIdIdx]->mode == EnetNetIF_RxMode_MacSharedChannel)
        {
            const Enet_MacPort macPort = (Enet_MacPort)((pInterface->hRx[rxChIdIdx]->refCount -1));
            configASSERT(macPort < FREERTOS_TCPIF_MAX_NUM_MAC_PORTS);
            pInterface->hRx[rxChIdIdx]->mapPortToInterface[macPort] = pxInterface;
            pInterface->macPort = macPort;
        }
        else
        {
            /* rxChIdx is treated as MAC PORT in case of dedicated CH per pxInterface.
             * This is in both ICSSG dual mac and switch usecase */
            const Enet_MacPort macPort = EnetNetIF_findMacPortFromEnet(enetType, instId);
            configASSERT(macPort < FREERTOS_TCPIF_MAX_NUM_MAC_PORTS);
            pInterface->hRx[rxChIdIdx]->mapPortToInterface[macPort] = pxInterface;
            pInterface->macPort = macPort;
        }

        // MAC address allocation for the Netifs
        EnetApp_getMacAddress(rxChId, &macAddr);
        if (macAddr.macAddressCnt > 0)
        {
            /* fall here only for the Rx Channel that has valid mac address */
            // configASSERT(netif->hwaddr_len == 0);
            configASSERT(macAddr.macAddressCnt >= (pInterface->hRx[rxChIdIdx]->refCount - 1));
            pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
            EnetUtils_copyMacAddr(pxEndPoint->xMACAddress.ucBytes, &macAddr.macAddr[pInterface->hRx[rxChIdIdx]->refCount - 1][0U]);
            // netif->hwaddr_len = ENET_MAC_ADDR_LEN;
            #if ENET_ENABLE_PER_ICSSG
            if // TODO: pending porting // Lwip2Enet_setMacAddress(enetType, instId, pInterface->hEnet, &macAddr.macAddr[pInterface->hRx[rxChIdIdx]->refCount - 1][0U]);
            #endif // ENET_ENABLE_PER_ICSSG
        }

        pInterface->hRx[rxChIdIdx]->hEnetNetIF = hEnet;
        configASSERT(NULL != pInterface->hRx[rxChIdIdx]->hFlow);
        /* Submit all allocated packets to DMA so it can use for packet RX */
        if (pInterface->hRx[rxChIdIdx]->refCount == 1)
        {
            hEnet->allocPktInfo += pInterface->hRx[rxChIdIdx]->numPackets;
            EnetNetIF_submitRxPktQ(pInterface->hRx[rxChIdIdx]);
        }
    }
    pInterface->count_hRx = rxChIdCount;

    /* Get initial link/interface status from the driver */
    pInterface->isLinkUp = hEnet->appInfo.isPortLinkedFxn(pInterface->hEnet);
    pInterface->isPortLinkedFxn = hEnet->appInfo.isPortLinkedFxn;

    pxNetIFArgs->pInterface = pInterface;
    pxNetIFArgs->hEnet = hEnet;
    xNetIFNum = pxNetIFArgs->xNetIFID;

    /* assert if clk period is not valid  */
    configASSERT(0U != hEnet->appInfo.timerPeriodUs);

    ClockP_start(&hEnet->pacingClkObj);

    // TODO: Wait till link is up before returing, because if the open() returns,
    // the IP-task will start and send packets immediately,
    
    // FIXME: NOTE: This is a temporary hack for minimal testing
    while((pInterface->isLinkUp = hEnet->appInfo.isPortLinkedFxn(pInterface->hEnet)) == 0)
    {
        vTaskDelay(pdMS_TO_TICKS(100));
    }

    if((hEnet->isInitDone == TRUE) && xNetIFNum == 0)
    {
        EnetNetIFApp_startSchedule(pxInterface);
    }

    return hEnet;

}
