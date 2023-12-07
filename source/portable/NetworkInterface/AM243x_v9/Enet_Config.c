/*
 *  Copyright (c) Texas Instruments Incorporated 2022
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*!
 * \file ti_enet_lwipif.c
 *
 * \brief This file contains enet Lwip interface layer implementation for driver callback.
 */

/* ========================================================================== */
/*                             Include Files                                  */
/* ========================================================================== */

#include <stdio.h>
#include <stdarg.h>
#include <string.h>

#include "ti_enet_config.h"
#include "ti_enet_lwipif.h"
#include <lwip/tcpip.h>
#include <assert.h>

#include <kernel/dpl/TaskP.h>
#include <kernel/dpl/SemaphoreP.h>
#include <kernel/dpl/ClockP.h>
#include <kernel/dpl/SystemP.h>
#include <kernel/dpl/HwiP.h>

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
#include <networking/enet/core/lwipif/inc/pbufQ.h>

#include <lwip2lwipif.h>
#include <custom_pbuf.h>

/* ========================================================================== */
/*                           Macros & Typedefs                                */
/* ========================================================================== */
#if ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
#if !LWIP_CHECKSUM_CTRL_PER_NETIF
#error "LWIP_CHECKSUM_CTRL_PER_NETIF is not set in lwipopts.h"
#endif
#endif

#define ENETLWIP_PACKET_POLL_PERIOD_US (1000U)

#define ENETLWIP_APP_POLL_PERIOD       (500U)

#define LWIPIF_NUM_RX_PACKET_TASKS     (1U)

#define LWIPIF_NUM_TX_PACKET_TASKS     (1U)

#define NUM_NETIF_SUPPORTED_MAX        (2U)

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

/* \brief Enable LC-DMA statically linked Rx scatter-gather. Also need to update scatterSegments
 * for EnetMem_allocEthPkt while allocating pkts to enable Rx scatter-gather */
#define UDMA_STATIC_RX_SG_ENABLE        0U

/* ========================================================================== */
/*                            Global Variables                                */
/* ========================================================================== */

typedef struct LwipifEnetApp_RxTaskInfo_s
{
    TaskP_Object      task;
    uint8_t stack[LWIPIF_RX_PACKET_TASK_STACK] __attribute__ ((aligned(sizeof(long long))));
    SemaphoreP_Object sem;
    struct netif *netif;
    /*
     * Handle to counting shutdown semaphore, which all subtasks created in the
     * open function must post before the close operation can complete.
     */
    SemaphoreP_Object shutDownSemObj;
    /** Boolean to indicate shutDownFlag status of translation layer.*/
    volatile bool shutDownFlag;
} LwipifEnetApp_RxTaskInfo;

typedef struct LwipifEnetApp_TxTaskInfo_s
{
    TaskP_Object      task;
    uint8_t stack[LWIPIF_TX_PACKET_TASK_STACK] __attribute__ ((aligned(sizeof(long long))));
    SemaphoreP_Object sem;
    struct netif *netif;
    /*
     * Handle to counting shutdown semaphore, which all subtasks created in the
     * open function must post before the close operation can complete.
     */
    SemaphoreP_Object shutDownSemObj;
    /** Boolean to indicate shutDownFlag status of translation layer.*/
    volatile bool shutDownFlag;
} LwipifEnetApp_TxTaskInfo;

typedef struct LwipifEnetApp_PollTaskInfo_s
{
    TaskP_Object      task;
    uint8_t stack[LWIPIF_POLL_TASK_STACK] __attribute__ ((aligned(sizeof(long long))));
    SemaphoreP_Object sem;
    struct netif *netif;
    /*
     * Handle to counting shutdown semaphore, which all subtasks created in the
     * open function must post before the close operation can complete.
     */
    SemaphoreP_Object shutDownSemObj;
    /** Boolean to indicate shutDownFlag status of translation layer.*/
    volatile bool shutDownFlag;

    /*
     * Clock handle for triggering the packet Rx notify
     */
    ClockP_Object pollLinkClkObj;
} LwipifEnetApp_PollTaskInfo;

typedef struct LwipifEnetApp_TaskInfo_s
{
    LwipifEnetApp_RxTaskInfo rxTask[LWIPIF_NUM_RX_PACKET_TASKS];
    LwipifEnetApp_TxTaskInfo txTask[LWIPIF_NUM_TX_PACKET_TASKS];
    LwipifEnetApp_PollTaskInfo pollTask;
} LwipifEnetApp_TaskInfo;

typedef struct LwipifEnetApp_Object_s
{
    LwipifEnetApp_TaskInfo task;
    struct netif gNetif[ENET_SYSCFG_NETIF_COUNT];
    /*
    * Clock handle for triggering the packet Rx notify
    */
    ClockP_Object pollLinkClkObj;
} LwipifEnetApp_Object;
/*
 * Clock handle for triggering the packet Rx notify
 */
    ClockP_Object pollLinkClkObj;


/* For Cpdma Rx scatter-gather implies that #rxpkts = #rxbuffers = #rxpbufs
   For Udma's static Rx scatter-gather, #rxbuffers = #rxpbufs = 4 * #rxpkts */
#if UDMA_STATIC_RX_SG_ENABLE
LWIP_MEMPOOL_DECLARE(RX_POOL, ENET_SYSCFG_TOTAL_NUM_RX_PKT * 4, sizeof(Rx_CustomPbuf), "Rx Custom Pbuf pool");
/* These must be sufficient for total number of rx pbufs and tx packets */
NetBufNode gFreePbufArr[ENET_SYSCFG_TOTAL_NUM_RX_PKT * 5];
#else
LWIP_MEMPOOL_DECLARE(RX_POOL, ENET_SYSCFG_TOTAL_NUM_RX_PKT, sizeof(Rx_CustomPbuf), "Rx Custom Pbuf pool");
/* These must be sufficient for total number of rx pbufs and tx packets */
NetBufNode gFreePbufArr[ENET_SYSCFG_TOTAL_NUM_RX_PKT * 2];

#endif
static LwipifEnetApp_Object gLwipifEnetAppObj;
/* ========================================================================== */
/*                            Function Declaration                            */
/* ========================================================================== */

void LwipifEnetApp_createRxPktHandlerTask(LwipifEnetApp_RxTaskInfo* pTxTaskInfo, struct netif *netif);

void LwipifEnetApp_createTxPktHandlerTask(LwipifEnetApp_TxTaskInfo* pTxTaskInfo, struct netif *netif);

static void LwipifEnetApp_rxPacketTask(void *arg);

static void LwipifEnetApp_txPacketTask(void *arg);

static err_t LwipifEnetApp_createPollTask(LwipifEnetApp_PollTaskInfo* pPollTaskInfo);

static void LwipifEnetApp_poll(void *arg);

static void LwipifEnetApp_postPollLink(ClockP_Object *clkObj, void *arg);


LwipifEnetApp_Handle LwipifEnetApp_getHandle()
{
    return (LwipifEnetApp_Handle)&gLwipifEnetAppObj;
}

struct netif* LwipifEnetApp_netifOpen(LwipifEnetApp_Handle handle, uint32_t netifIdx, const ip4_addr_t *ipaddr, const ip4_addr_t *netmask, const ip4_addr_t *gw)
{
    const uint32_t lwipIdx2Enet[ENET_SYSCFG_NETIF_COUNT][2] = {{ENET_CPSW_3G, 0},};
        /* Peripheral type */
    Enet_Type enetType = lwipIdx2Enet[netifIdx][0];

    /* Peripheral instance */
    uint32_t instId = lwipIdx2Enet[netifIdx][1];

    LwipifEnetApp_Object* pObj = (LwipifEnetApp_Object*) handle;
    if (netifIdx < ENET_SYSCFG_NETIF_COUNT)
    {
#if ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)

        /* Enable all Flags except below checksumflags. */
        const uint32_t lwIPChcksumDisableFlags = 0U | NETIF_CHECKSUM_GEN_TCP | NETIF_CHECKSUM_GEN_UDP | NETIF_CHECKSUM_CHECK_TCP | NETIF_CHECKSUM_CHECK_UDP;
        const uint32_t lwIPChcksumSetFlags = (NETIF_CHECKSUM_ENABLE_ALL & ~lwIPChcksumDisableFlags);
#endif
        netif_add(&pObj->gNetif[netifIdx],
                    ipaddr, 
                    netmask,
                    gw,
                    NULL,
                    LWIPIF_LWIP_init, 
                    tcpip_input
                 );
        LWIPIF_LWIP_start(enetType, instId, &pObj->gNetif[netifIdx]);

        if(netifIdx == ENET_SYSCFG_DEFAULT_NETIF_IDX)
        {
            netif_set_default(&pObj->gNetif[netifIdx]);
        }
#if ENET_CFG_IS_ON(CPSW_CSUM_OFFLOAD_SUPPORT)
        NETIF_SET_CHECKSUM_CTRL(&pObj->gNetif[netifIdx], lwIPChcksumSetFlags);
#endif
    }
    else
    {
        DebugP_log("ERROR: NetifIdx is out of valid range!\r\n");
        EnetAppUtils_assert(FALSE);
    }
    return (&pObj->gNetif[netifIdx]);
}

void LwipifEnetApp_netifClose(LwipifEnetApp_Handle handle, const uint32_t netifIdx)
{
    LwipifEnetApp_Object* pObj = (LwipifEnetApp_Object*) handle;
    netif_remove(&pObj->gNetif[netifIdx]);
}

struct netif* LwipifEnetApp_getNetifFromId(LwipifEnetApp_Handle handle, uint32_t netifIdx)
{
    LwipifEnetApp_Object* pObj = (LwipifEnetApp_Object*) handle;
    struct netif * pNetif = NULL;
    if(netifIdx < ENET_SYSCFG_NETIF_COUNT)
    {
        pNetif = &pObj->gNetif[netifIdx];
    }
    else{
            DebugP_log("ERROR: NetifIdx is out of valid range!\r\n");
            EnetAppUtils_assert(FALSE);
    }

    return pNetif;
}

void EnetNetIFAppCb_getEnetIFInstInfo(Enet_Type enetType, uint32_t instId, EnetNetIF_AppIf_GetEnetIFInstInfo *outArgs)
{
    EnetPer_AttachCoreOutArgs attachInfo;
    EnetApp_HandleInfo handleInfo;

    uint32_t coreId = EnetSoc_getCoreId();

    EnetApp_coreAttach(enetType, instId, coreId, &attachInfo);
    EnetApp_acquireHandleInfo(enetType, instId, &handleInfo);

    outArgs->hostPortRxMtu = attachInfo.rxMtu;
    ENET_UTILS_ARRAY_COPY(outArgs->txMtu, attachInfo.txMtu);
    outArgs->isPortLinkedFxn = &EnetApp_isPortLinked;
    outArgs->timerPeriodUs   = ENETLWIP_PACKET_POLL_PERIOD_US;
    outArgs->pPbufInfo = gFreePbufArr;
    outArgs->pPbufInfoSize = sizeof(gFreePbufArr)/sizeof(NetBufNode);
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

        EnetAppUtils_assert(true == csumOffloadFlg);
#endif
}

void EnetNetIFAppCb_getTxHandleInfo(LwipifEnetAppIf_GetTxHandleInArgs *inArgs,
                                     LwipifEnetAppIf_TxHandleInfo *outArgs)
{
    uint32_t i;
    EnetDma_Pkt *pPktInfo;
    EnetApp_GetTxDmaHandleOutArgs  txChInfo;
    EnetApp_GetDmaHandleInArgs     txInArgs;

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

        EnetAppUtils_assert(pPktInfo != NULL);
        ENET_UTILS_SET_PKT_APP_STATE(&pPktInfo->pktState, ENET_PKTSTATE_APP_WITH_FREEQ);
        EnetQueue_enq(inArgs->pktInfoQ, &pPktInfo->node);

    }

}

void EnetNetIFAppCb_getRxHandleInfo(LwipifEnetAppIf_GetRxHandleInArgs *inArgs,
                                     LwipifEnetAppIf_RxHandleInfo *outArgs)
{
    uint32_t i;
    EnetDma_Pkt *pPktInfo;
    // Rx_CustomPbuf *cPbuf;
    EnetNetIF_AppIf_CustomNetBuf * pxNetDesc;
    bool useRingMon = false;
    EnetApp_HandleInfo handleInfo;
    EnetPer_AttachCoreOutArgs attachInfo;
    uint32_t coreId          = EnetSoc_getCoreId();
    EnetApp_GetRxDmaHandleOutArgs  rxChInfo;
    EnetApp_GetDmaHandleInArgs     rxInArgs;
    uint32_t numCustomPbuf;
    uint32_t scatterSegments[] =
    {
        ENET_MEM_LARGE_POOL_PKT_SIZE  /* Keep this size aligned with R5F cacheline of 32B */
    };
    EnetApp_acquireHandleInfo(inArgs->enetType, inArgs->instId, &handleInfo);
    EnetApp_coreAttach(inArgs->enetType, inArgs->instId, coreId, &attachInfo);

    /* Open RX channel */
    rxInArgs.cbArg     = inArgs->cbArg;
    rxInArgs.notifyCb  = inArgs->notifyCb;

    EnetApp_getRxDmaHandle(inArgs->chId,
                          &rxInArgs,
                          &rxChInfo);
#if UDMA_STATIC_RX_SG_ENABLE
    numCustomPbuf = rxChInfo.maxNumRxPkts * 4;
#else
    numCustomPbuf = rxChInfo.maxNumRxPkts;
#endif
    outArgs->rxFlowStartIdx = rxChInfo.rxFlowStartIdx;
    outArgs->rxFlowIdx = rxChInfo.rxFlowIdx;
    outArgs->hRxFlow  = rxChInfo.hRxCh;
    outArgs->numPackets  = rxChInfo.maxNumRxPkts;
    outArgs->disableEvent = !useRingMon;
    for (uint32_t i = 0; i < rxChInfo.numValidMacAddress; i++)
    {
        EnetUtils_copyMacAddr(&outArgs->macAddr[inArgs->chId][0U], rxChInfo.macAddr[i]);
        EnetAppUtils_print("Host MAC address-%d : ",inArgs->chId);
        EnetAppUtils_printMacAddr(&outArgs->macAddr[inArgs->chId][0U]);
    }

    /* Initialize the DMA free queue */
    EnetQueue_initQ(inArgs->pReadyRxPktQ);
    EnetQueue_initQ(inArgs->pFreeRxPktInfoQ);
    NetBufQueue_init(inArgs->pFreePbufInfoQ);

    for (i = 0U; i < rxChInfo.maxNumRxPkts; i++)
    {

        pPktInfo = EnetMem_allocEthPkt(&inArgs->cbArg,
                           ENETDMA_CACHELINE_ALIGNMENT,
                           ENET_ARRAYSIZE(scatterSegments),
                           scatterSegments);
        EnetAppUtils_assert(pPktInfo != NULL);
        ENET_UTILS_SET_PKT_APP_STATE(&pPktInfo->pktState, ENET_PKTSTATE_APP_WITH_READYQ);

        /* Put all the filled pPktInfo into readyRxPktQ and submit to driver */
        EnetQueue_enq(inArgs->pReadyRxPktQ, &pPktInfo->node);
    }

    EnetQueue_verifyQCount(inArgs->pReadyRxPktQ);
    for (i = 0U; i < numCustomPbuf; i++)
    {
        /* Allocate the Custom Pbuf structures and put them in freePbufInfoQ */
        pxNetDesc = NULL;
        pxNetDesc = (EnetNetIF_AppIf_CustomNetBuf *) pxGetNetworkBufferWithDescriptor_RX( scatterSegments[0], 0);
        EnetAppUtils_assert(pxNetDesc != NULL);
        pxNetDesc->customNetBufArgs       = (Rx_CustomNetBuf_Args)inArgs->cbArg;
        pxNetDesc->next                   = NULL;
        pxNetDesc->alivePbufCount         = 0U;
        pxNetDesc->orgBufLen              = 0U;
        pxNetDesc->orgBufPtr              = NULL;
        NetBufQueue_enQ(inArgs->pFreePbufInfoQ, &(pxNetDesc->xNetworkBuffer));
    }

}

void LwipifEnetAppCb_releaseTxHandle(LwipifEnetAppIf_ReleaseTxHandleInfo *releaseInfo)
{
    EnetApp_HandleInfo handleInfo;
    EnetPer_AttachCoreOutArgs attachInfo;
    EnetDma_PktQ fqPktInfoQ;
    EnetDma_PktQ cqPktInfoQ;
    uint32_t coreId = EnetSoc_getCoreId();

    EnetApp_acquireHandleInfo(releaseInfo->enetType, releaseInfo->instId, &handleInfo);
    EnetApp_coreAttach(releaseInfo->enetType, releaseInfo->instId, coreId, &attachInfo);

    /* Close TX channel */
    EnetQueue_initQ(&fqPktInfoQ);
    EnetQueue_initQ(&cqPktInfoQ);
    EnetApp_closeTxDma(releaseInfo->txChNum,
                       handleInfo.hEnet,
                       attachInfo.coreKey,
                       coreId,
                       &fqPktInfoQ,
                       &cqPktInfoQ);
    releaseInfo->txFreePktCb(releaseInfo->txFreePktCbArg, &fqPktInfoQ, &cqPktInfoQ);
    EnetApp_coreDetach(releaseInfo->enetType, releaseInfo->instId, coreId, attachInfo.coreKey);
    EnetApp_releaseHandleInfo(releaseInfo->enetType, releaseInfo->instId);
}

void LwipifEnetAppCb_releaseRxHandle(LwipifEnetAppIf_ReleaseRxHandleInfo *releaseInfo)
{
    EnetApp_HandleInfo handleInfo;
    EnetPer_AttachCoreOutArgs attachInfo;
    EnetDma_PktQ fqPktInfoQ;
    EnetDma_PktQ cqPktInfoQ;
    uint32_t coreId = EnetSoc_getCoreId();

    EnetApp_acquireHandleInfo(releaseInfo->enetType, releaseInfo->instId, &handleInfo);
    EnetApp_coreAttach(releaseInfo->enetType, releaseInfo->instId, coreId, &attachInfo);

    /* Close RX channel */
    EnetQueue_initQ(&fqPktInfoQ);
    EnetQueue_initQ(&cqPktInfoQ);
    EnetApp_closeRxDma(releaseInfo->rxChNum,
                       handleInfo.hEnet,
                       attachInfo.coreKey,
                       coreId,
                       &fqPktInfoQ,
                       &cqPktInfoQ);

    releaseInfo->rxFreePktCb(releaseInfo->rxFreePktCbArg, &fqPktInfoQ, &cqPktInfoQ);
    EnetApp_coreDetach(releaseInfo->enetType, releaseInfo->instId, coreId, attachInfo.coreKey);
    EnetApp_releaseHandleInfo(releaseInfo->enetType, releaseInfo->instId);
}

static err_t LwipifEnetApp_createPollTask(LwipifEnetApp_PollTaskInfo* pPollTaskInfo)
{
    TaskP_Params params;
    int32_t status;
    ClockP_Params clkPrms;

    if (NULL != pPollTaskInfo)
    {
        /*Initialize semaphore to call synchronize the poll function with a timer*/
        status = SemaphoreP_constructBinary(&pPollTaskInfo->sem, 0U);
        EnetAppUtils_assert(status == SystemP_SUCCESS);

        /*Initialize semaphore to call synchronize the poll function with a timer*/
        status = SemaphoreP_constructBinary(&pPollTaskInfo->shutDownSemObj, 0U);
        EnetAppUtils_assert(status == SystemP_SUCCESS);

        /* Initialize the poll function as a thread */
        TaskP_Params_init(&params);
        params.name           = "Lwipif_Lwip_poll";
        params.priority       = LWIP_POLL_TASK_PRI;
        params.stack          = pPollTaskInfo->stack;
        params.stackSize      = sizeof(pPollTaskInfo->stack);
        params.args           = pPollTaskInfo;
        params.taskMain       = &LwipifEnetApp_poll;

        status = TaskP_construct(&pPollTaskInfo->task, &params);
        EnetAppUtils_assert(status == SystemP_SUCCESS);

        ClockP_Params_init(&clkPrms);
        clkPrms.start     = 0;
        clkPrms.period    = ENETLWIP_APP_POLL_PERIOD;
        clkPrms.args      = &pPollTaskInfo->sem; // make a proper semaphore structure for this.
        clkPrms.callback  = &LwipifEnetApp_postPollLink;
        clkPrms.timeout   = ENETLWIP_APP_POLL_PERIOD;

        /* Creating timer and setting timer callback function*/
        status = ClockP_construct(&pPollTaskInfo->pollLinkClkObj, &clkPrms);
        if (status == SystemP_SUCCESS)
        {
            /* Set timer expiry time in OS ticks */
            ClockP_setTimeout(&pPollTaskInfo->pollLinkClkObj, ENETLWIP_APP_POLL_PERIOD);
            ClockP_start(&pPollTaskInfo->pollLinkClkObj);
        }
        else
        {
            EnetAppUtils_assert(status == SystemP_SUCCESS);
        }

        /* Filter not defined */
        /* Inform the world that we are operational. */
        EnetAppUtils_print("[LWIPIF_LWIP] Enet has been started successfully\r\n");

        return ERR_OK;
    }
    else
    {
        return ERR_BUF;
    }
}
/*
* create a function called postEvent[i]. each event, each postfxn.
*/
static void LwipifEnetApp_postSemaphore(void *pArg)
{
    SemaphoreP_Object *pSem = (SemaphoreP_Object *) pArg;
    SemaphoreP_post(pSem);
}

int32_t LwipifEnetApp_getNetifIdx(LwipifEnetApp_Handle handle, struct netif* netif)
{
    LwipifEnetApp_Object* pObj = (LwipifEnetApp_Object*) handle;

    int32_t idx = -1;

    for (uint32_t i = 0; i < 2; i++)
    {
        if (&pObj->gNetif[i] == netif)
        {
            idx = i;
            break;
        }
    }

    return idx;
}
void LwipifEnetApp_startSchedule(LwipifEnetApp_Handle handle, struct netif *netif
    )
{
    LwipifEnetApp_Object* pObj = (LwipifEnetApp_Object*) handle;
    uint32_t status = ENET_SOK;
    const uint32_t netifIdx = LwipifEnetApp_getNetifIdx(handle, netif);

    EnetAppUtils_assert(netifIdx < LWIPIF_NUM_TX_PACKET_TASKS);
    EnetAppUtils_assert(netifIdx < LWIPIF_NUM_RX_PACKET_TASKS);

    status = SemaphoreP_constructBinary(&pObj->task.txTask[netifIdx].shutDownSemObj, 0U);
    EnetAppUtils_assert(status == SystemP_SUCCESS);

    status = SemaphoreP_constructBinary(&pObj->task.rxTask[netifIdx].shutDownSemObj, 0U);
    EnetAppUtils_assert(status == SystemP_SUCCESS);

    status = SemaphoreP_constructBinary(&pObj->task.txTask[netifIdx].sem, 0U);
    EnetAppUtils_assert(status == SystemP_SUCCESS);

    status = SemaphoreP_constructBinary(&pObj->task.rxTask[netifIdx].sem, 0U);
    EnetAppUtils_assert(status == SystemP_SUCCESS);

    Enet_notify_t txNotify =
    {
            .cbFxn = &LwipifEnetApp_postSemaphore,
            .cbArg = &pObj->task.txTask[netifIdx].sem,
    };

    Enet_notify_t rxNotify =
    {
            .cbFxn = &LwipifEnetApp_postSemaphore,
            .cbArg = &pObj->task.rxTask[netifIdx].sem,
    };

    LWIPIF_LWIP_setNotifyCallbacks(netif, &rxNotify, &txNotify);

    /* Initialize Tx task*/
    pObj->task.txTask[netifIdx].shutDownFlag =false;
    LwipifEnetApp_createTxPktHandlerTask(&pObj->task.txTask[netifIdx], netif);

    /* Initialize Rx Task*/
    pObj->task.rxTask[netifIdx].shutDownFlag =false;
    LwipifEnetApp_createRxPktHandlerTask(&pObj->task.rxTask[netifIdx], netif);

    if (netifIdx == 0)
    {
        pObj->task.pollTask.shutDownFlag =false;
        pObj->task.pollTask.netif = &pObj->gNetif[0]; // link to the first in the list
        /* Initialize Polling task*/
        LwipifEnetApp_createPollTask(&pObj->task.pollTask);
    }

}

void EnetApp_getRxChIDs(const Enet_Type enetType, const uint32_t instId, uint32_t* pRxChIdCount, uint32_t rxChIdList[LWIPIF_MAX_RX_CHANNELS_PER_PHERIPHERAL])
{
    const uint32_t rxChIdMap[ENET_SYSCFG_MAX_ENET_INSTANCES][4] = {{ENET_CPSW_3G, 0,ENET_DMA_RX_CH0,1},};
    uint32_t chCount = 0;
    uint32_t chIdStrart = 0;
    for (uint32_t idx = 0; idx < ENET_SYSCFG_MAX_ENET_INSTANCES; idx++)
    {
        if ((rxChIdMap[idx][0] == enetType) && (rxChIdMap[idx][1] == instId))
        {
            chIdStrart = rxChIdMap[idx][2];
            chCount    = rxChIdMap[idx][3];
        }
    }

    /* verifiy the user params */
    switch (enetType)
    {
    case ENET_ICSSG_SWITCH:
    {
        EnetAppUtils_assert(chCount == 2);
        break;
    }
    case ENET_ICSSG_DUALMAC:
    case ENET_CPSW_3G:
    case ENET_CPSW_2G:
    {
        EnetAppUtils_assert(chCount == 1);
        break;
    }
    default:
    {
        EnetAppUtils_assert(false);
    }
    }

    /* fill ChId List */
    EnetAppUtils_assert(chCount <= LWIPIF_MAX_RX_CHANNELS_PER_PHERIPHERAL);
    *pRxChIdCount = chCount;
    for (uint32_t idx = 0; idx < chCount; idx++)
    {
        rxChIdList[idx] = chIdStrart + idx; 
    }
    return;
}

void EnetApp_getTxChIDs(const Enet_Type enetType, const uint32_t instId, uint32_t* pTxChIdCount, uint32_t txChIdList[LWIPIF_MAX_TX_CHANNELS_PER_PHERIPHERAL])
{
    const uint32_t txChIdMap[ENET_SYSCFG_MAX_ENET_INSTANCES][4] = {{ENET_CPSW_3G, 0,ENET_DMA_TX_CH0,1},};
    uint32_t chCount = 0;
    uint32_t chIdStrart = 0;
    for (uint32_t idx = 0; idx < ENET_SYSCFG_MAX_ENET_INSTANCES; idx++)
    {
        if ((txChIdMap[idx][0] == enetType) && (txChIdMap[idx][1] == instId))
        {
            chIdStrart  = txChIdMap[idx][2];
            chCount     = txChIdMap[idx][3];
        }
    }

    /* verifiy the user params */
    switch (enetType)
    {
    case ENET_ICSSG_SWITCH:
    case ENET_ICSSG_DUALMAC:
    case ENET_CPSW_3G:
    case ENET_CPSW_2G:
    {
        EnetAppUtils_assert(chCount == 1);
        break;
    }
    default:
    {
        EnetAppUtils_assert(false);
    }
    }

    /* fill ChId List */
    EnetAppUtils_assert(chCount <= LWIPIF_MAX_TX_CHANNELS_PER_PHERIPHERAL);
    *pTxChIdCount = chCount;
    for (uint32_t idx = 0; idx < chCount; idx++)
    {
        txChIdList[idx] = chIdStrart + idx; 
    }
    return;
}

EnetNetIF_RxMode_t EnetApp_getRxMode(Enet_Type enetType, uint32_t instId)
{
    const bool hasSwitchModeEnabled = true; 
    EnetNetIF_RxMode_t rxMode = Lwip2Enet_RxMode_SwitchSharedChannel;
    if (hasSwitchModeEnabled)
    {
        rxMode = EnetNetIF_RxMode_SwitchSharedChannel;
    }
    else
    {
        rxMode = EnetNetIF_RxMode_MacSharedChannel;
    }
    return rxMode;
}



void LwipifEnetApp_createRxPktHandlerTask(LwipifEnetApp_RxTaskInfo* pRxTaskInfo, struct netif *netif)
{
    TaskP_Params params;
    int32_t status;
    pRxTaskInfo->netif = netif;

    /* Create RX packet task */
    TaskP_Params_init(&params);
    params.name      = "LwipifEnetApp_RxPacketTask";
    params.priority  = LWIPIF_RX_PACKET_TASK_PRI;
    params.stack     = &pRxTaskInfo->stack[0];
    params.stackSize = sizeof(pRxTaskInfo->stack);
    params.args      = pRxTaskInfo;
    params.taskMain  = &LwipifEnetApp_rxPacketTask;

    status = TaskP_construct(&pRxTaskInfo->task, &params);
    EnetAppUtils_assert(status == SystemP_SUCCESS);
}

void LwipifEnetApp_createTxPktHandlerTask(LwipifEnetApp_TxTaskInfo* pTxTaskInfo, struct netif *netif)
{
    TaskP_Params params;
    int32_t status;

    pTxTaskInfo->netif = netif;
    /* Create TX packet task */
    TaskP_Params_init(&params);
    params.name = "LwipifEnetApp_TxPacketTask";
    params.priority       = LWIPIF_TX_PACKET_TASK_PRI;
    params.stack          = &pTxTaskInfo->stack[0];
    params.stackSize      = sizeof(pTxTaskInfo->stack);
    params.args           = pTxTaskInfo;
    params.taskMain       = &LwipifEnetApp_txPacketTask;

    status = TaskP_construct(&pTxTaskInfo->task , &params);
    EnetAppUtils_assert(status == SystemP_SUCCESS);
}

static void LwipifEnetApp_rxPacketTask(void *arg)
{
    LwipifEnetApp_RxTaskInfo* pTaskInfo = (LwipifEnetApp_RxTaskInfo*) arg;

    while (!pTaskInfo->shutDownFlag)
    {
        /* Wait for the Rx ISR to notify us that packets are available with data */
        SemaphoreP_pend(&pTaskInfo->sem, SystemP_WAIT_FOREVER);
        if (pTaskInfo->shutDownFlag)
        {
            /* This translation layer is shutting down, don't give anything else to the stack */
            break;
        }

        LWIPIF_LWIP_rxPktHandler(pTaskInfo->netif);
    }

    /* We are shutting down, notify that we are done */
    SemaphoreP_post(&pTaskInfo->shutDownSemObj);
}

static void LwipifEnetApp_txPacketTask(void *arg)
{
    LwipifEnetApp_TxTaskInfo* pTaskInfo = (LwipifEnetApp_TxTaskInfo*) arg;

    while (!pTaskInfo->shutDownFlag)
    {
        /*
         * Wait for the Tx ISR to notify us that empty packets are available
         * that were used to send data
         */
        SemaphoreP_pend(&pTaskInfo->sem, SystemP_WAIT_FOREVER);
        LWIPIF_LWIP_txPktHandler(pTaskInfo->netif);
    }

    /* We are shutting down, notify that we are done */
    SemaphoreP_post(&pTaskInfo->shutDownSemObj);
}

static void LwipifEnetApp_poll(void *arg)
{
    /* Call the driver's periodic polling function */
    LwipifEnetApp_PollTaskInfo* pTaskInfo = (LwipifEnetApp_PollTaskInfo*)arg;

    while (!pTaskInfo->shutDownFlag)
    {
        SemaphoreP_pend(&pTaskInfo->sem, SystemP_WAIT_FOREVER);
        sys_lock_tcpip_core();
        for (uint32_t i = 0; i < ENET_SYSCFG_NETIF_COUNT; i++)
        {
            if (&pTaskInfo->netif[i] != NULL)
            {
                LWIPIF_LWIP_periodic_polling(&pTaskInfo->netif[i]);
            }
        }
        sys_unlock_tcpip_core();
    }
    SemaphoreP_post(&pTaskInfo->shutDownSemObj);
}

static void LwipifEnetApp_postPollLink(ClockP_Object *clkObj, void *arg)
{
    if (arg != NULL)
    {
        SemaphoreP_Object *hPollSem = (SemaphoreP_Object *) arg;
        SemaphoreP_post(hPollSem);
    }
}


















