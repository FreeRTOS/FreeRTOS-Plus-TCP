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
#include "Enet_NetIF.h"

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

/* ========================================================================== */
/*                           Macros & Typedefs                                */
/* ========================================================================== */

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


/*
 * Clock handle for triggering the packet Rx notify
 */
    ClockP_Object pollLinkClkObj;


/* For Cpdma Rx scatter-gather implies that #rxpkts = #rxbuffers = #rxpbufs
   For Udma's static Rx scatter-gather, #rxbuffers = #rxpbufs = 4 * #rxpkts */
#if UDMA_STATIC_RX_SG_ENABLE
/* These must be sufficient for total number of rx pbufs and tx packets */
NetBufNode gFreePbufArr[ENET_SYSCFG_TOTAL_NUM_RX_PKT * 5];
#else
/* These must be sufficient for total number of rx pbufs and tx packets */
NetBufNode gFreePbufArr[ENET_SYSCFG_TOTAL_NUM_RX_PKT * 2];

#endif


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
    outArgs->timerPeriodUs   = ENETNETIF_PACKET_POLL_PERIOD_US;
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

void EnetNetIFAppCb_getTxHandleInfo(EnetNetIFAppIf_GetTxHandleInArgs *inArgs,
                                     EnetNetIFAppIf_TxHandleInfo *outArgs)
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

void EnetNetIFAppCb_getRxHandleInfo(EnetNetIFAppIf_GetRxHandleInArgs *inArgs,
                                     EnetNetIFAppIf_RxHandleInfo *outArgs)
{
    uint32_t i;
    EnetDma_Pkt *pPktInfo;
    // Rx_CustomPbuf *cPbuf;
    // EnetNetIF_AppIf_CustomNetBuf * pxNetDesc;
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
    // NetBufQueue_init(inArgs->pFreePbufInfoQ);

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
    // for (i = 0U; i < numCustomPbuf; i++)
    // {
    //     /* Allocate the Custom Pbuf structures and put them in freePbufInfoQ */
    //     pxNetDesc = NULL;
    //     pxNetDesc = (EnetNetIF_AppIf_CustomNetBuf *) pxGetNetworkBufferWithDescriptor_RX( scatterSegments[0], 0);
    //     EnetAppUtils_assert(pxNetDesc != NULL);
    //     pxNetDesc->customNetBufArgs       = (Rx_CustomNetBuf_Args)inArgs->cbArg;
    //     pxNetDesc->next                   = NULL;
    //     pxNetDesc->alivePbufCount         = 0U;
    //     pxNetDesc->orgBufLen              = 0U;
    //     pxNetDesc->orgBufPtr              = NULL;
    //     NetBufQueue_enQ(inArgs->pFreePbufInfoQ, &(pxNetDesc->xNetworkBuffer));
    // }

}


/*
* create a function called postEvent[i]. each event, each postfxn.
*/
static void LwipifEnetApp_postSemaphore(void *pArg)
{
    SemaphoreP_Object *pSem = (SemaphoreP_Object *) pArg;
    SemaphoreP_post(pSem);
}


void EnetApp_getRxChIDs(const Enet_Type enetType, const uint32_t instId, uint32_t* pRxChIdCount, uint32_t rxChIdList[FREERTOS_TCPIF_MAX_RX_CHANNELS_PER_PHERIPHERAL])
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
    EnetAppUtils_assert(chCount <= FREERTOS_TCPIF_MAX_RX_CHANNELS_PER_PHERIPHERAL);
    *pRxChIdCount = chCount;
    for (uint32_t idx = 0; idx < chCount; idx++)
    {
        rxChIdList[idx] = chIdStrart + idx; 
    }
    return;
}

void EnetApp_getTxChIDs(const Enet_Type enetType, const uint32_t instId, uint32_t* pTxChIdCount, uint32_t txChIdList[FREERTOS_TCPIF_MAX_TX_CHANNELS_PER_PHERIPHERAL])
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
    EnetAppUtils_assert(chCount <= FREERTOS_TCPIF_MAX_TX_CHANNELS_PER_PHERIPHERAL);
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
    EnetNetIF_RxMode_t rxMode = EnetNetIF_RxMode_SwitchSharedChannel;
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


