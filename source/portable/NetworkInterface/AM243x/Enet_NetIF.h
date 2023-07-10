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

/* Standard language headers */
#include <stdint.h>
#include <assert.h>

/* OS/Posix headers */
#include <kernel/dpl/TaskP.h>
#include <kernel/dpl/SemaphoreP.h>
#include <kernel/dpl/ClockP.h>

/* Sys config */
#include "ti_enet_config.h"

/* FreeRTOS+TCP Header files */

#include "FreeRTOS_IP.h"

#include <enet.h>
#include <enet_cfg.h>
#include "Enet_NetIFQueue.h"

#define NUM_RX_POOL_NETWORK_BUFFER_DESCRIPTORS      (ENET_SYSCFG_TOTAL_NUM_RX_PKT)

#define CONFIG_MAX_RX_CHANNELS      2
#define CONFIG_MAX_TX_CHANNELS      2

#define HISTORY_CNT ((uint32_t)2U)

typedef bool (*Enet_NetIF_AppIf_IsPhyLinkedCbFxn)(Enet_Handle hEnet);

void EnetNetIF_AppCb_ReleaseNetDescriptor(NetworkBufferDescriptor_t * const pxNetworkBuffer);

/* Multicast Address List Size */
#define CONFG_PKT_MAX_MCAST                   ((uint32_t)31U)

/* Callback used by ENET to allocate RX payload buffers */
uint8_t * getEnetAppBuffMem(uint32_t req_Size, uint8_t *pktAddr);

typedef struct EnetNetIF_PktTaskStats_s
{
    uint32_t rawNotifyCnt;
    uint32_t dataNotifyCnt;
    uint32_t zeroNotifyCnt;
    uint32_t totalPktCnt;
    uint32_t totalCycleCnt;

    uint32_t pktsPerNotifyMax;
    uint32_t pktsPerNotify[HISTORY_CNT];
    uint32_t cycleCntPerNotifyMax;
    uint32_t cycleCntPerNotify[HISTORY_CNT];
    uint32_t cycleCntPerPktMax;
    uint32_t cycleCntPerPkt[HISTORY_CNT];
    uint32_t taskLoad[HISTORY_CNT];
} EnetNetIF_PktTaskStats;

/*!
 * \brief lwIP interface layer's RX statistics.
 */
typedef struct EnetNetIF_RxStats_s
{
    EnetNetIF_PktTaskStats pktStats;
    uint32_t freePbufPktEnq;
    uint32_t freePbufPktDeq;
    uint32_t freeAppPktEnq;
    uint32_t freeAppPktDeq;
    uint32_t chkSumErr;
    uint32_t stackNotifyCnt;
	uint32_t pbufAllocFailCnt;
	uint32_t rxLwipInputFail;
} EnetNetIF_RxStats;

/*!
 * \brief lwIP interface layer's TX statistics.
 */
typedef struct EnetNetIF_TxStats_s
{
    EnetNetIF_PktTaskStats pktStats;
    uint32_t readyPbufPktEnq;
    uint32_t readyPbufPktDeq;
    uint32_t freeAppPktEnq;
    uint32_t freeAppPktDeq;
} EnetNetIF_TxStats;

typedef struct EnetNetIF_Stats_s
{
    uint32_t cpuLoad[HISTORY_CNT];
    uint32_t hwiLoad[HISTORY_CNT];
} EnetNetIF_Stats;

typedef struct EnetNetIF_AppIf_GetHandleNetifInfo_s
{
    uint32_t numRxChannels;
    uint32_t numTxChannels;
    uint32_t rxChMask;
    uint32_t txChMask;
    bool isDirected;
} EnetNetIF_AppIf_GetHandleNetifInfo;

typedef struct EnetNetIF_AppIf_GetEnetIFInstInfo_s
{
    Enet_Handle hEnet;
    uint32_t txMtu[ENET_PRI_NUM];
    uint32_t hostPortRxMtu;

    /*! Number of netifs allocated by application */
    uint32_t maxNumNetif;
    uint32_t numRxChannels;
    uint32_t numTxChannels;
	Enet_NetIF_AppIf_IsPhyLinkedCbFxn isPortLinkedFxn;

    /** Timer interval for timer based RX pacing */
    uint32_t timerPeriodUs;
    NetBufNode *pFreeTx;
	uint32_t   pFreeTxSize;
} EnetNetIF_AppIf_GetEnetIFInstInfo;

typedef struct EnetNetIFAppIf_GetTxHandleInArgs_s
{
    void *cbArg;
    EnetDma_PktNotifyCb notifyCb;
    uint32_t chId;
    EnetDma_PktQ *pktInfoQ;
} EnetNetIFAppIf_GetTxHandleInArgs;

typedef struct EnetNetIFAppIf_GetRxHandleInArgs_s
{
    void *cbArg;
    EnetDma_PktNotifyCb notifyCb;
    uint32_t chId;
    EnetDma_PktQ *pktInfoQ;
} EnetNetIFAppIf_GetRxHandleInArgs;

typedef struct EnetNetIFAppIf_TxHandleInfo_s
{
    /** DMA transmit channel */
    EnetDma_TxChHandle hTxChannel;

    /*! Tx Channel Peer Id */
    uint32_t txChNum;

    /*! Whether to use TX event or not. When disabled, it uses "lazy" recycle mechanism
     *  to defer packet desc retrieval */
    bool disableEvent;

    /** Number of packets*/
    uint32_t numPackets;
} EnetNetIFAppIf_TxHandleInfo;

typedef struct EnetNetIFAppIf_RxHandleInfo_s
{
    /** ENET DMA receive channel */
    EnetDma_RxChHandle hRxFlow;
    /** Flow index for flow used  */
    uint32_t rxFlowStartIdx;
    /** Flow index for flow used  */
    uint32_t rxFlowIdx;
    /** Number of packets*/
    uint32_t numPackets;
    /*! Whether to use RX event or not. When disabled, it uses pacing timer to
     * retrieve packets periodically from driver */
    bool disableEvent;
        /** Mac Address allocated for the flow */
    uint8_t macAddr[ENET_CFG_NETIF_MAX][ENET_MAC_ADDR_LEN];
} EnetNetIFAppIf_RxHandleInfo;

/*!
 * \brief RX object which groups variables related to a particular RX channel/flow.
 */
typedef struct EnetNetIF_RxObj_s
{
    /*! Pointer to parent EnetNetIF object */
    struct xEnetDriverObj *hEnetNetIF;

    /*! Enet DMA receive channel (flow) */
    EnetDma_RxChHandle hFlow;

    /*! Whether this RX object is being used or not */
    bool enabled;

    /*! Reference count for RX flow */
    uint32_t refCount;

    /*! Start index for RX flow */
    uint32_t flowStartIdx;

    /*! Flow index for RX flow */
    uint32_t flowIdx;

    /*! DMA Rx free packet info queue (holds packets returned from the hardware) */
    EnetDma_PktQ freePktInfoQ;

    /*! Number of packets*/
    uint32_t numPackets;

    /*! lwIP interface statistics */
    EnetNetIF_RxStats stats;

    /*! Whether RX event should be disabled or not. When disabled, it relies on pacing timer
     *  to retrieve packets from RX channel/flow */
    bool disableEvent;
} EnetNetIF_RxObj, *EnetNetIF_RxHandle;

/*!
 * \brief TX object which groups variables related to a particular RX channel/flow.
 */
typedef struct EnetNetIF_TxObj_s
{
    /*! Pointer to parent EnetNetIF object */
    struct xEnetDriverObj *hEnetNetIF;

    /*! Enet DMA transmit channel */
    EnetDma_TxChHandle hCh;

    /*! TX channel peer id */
    uint32_t chNum;

    /*! Whether this TX object is being used or not */
    bool enabled;

    /*! Reference count for TX object */
    uint32_t refCount;

    /*! Number of packets*/
    uint32_t numPackets;

    /*! DMA free queue (holds free hardware packets awaiting) */
    EnetDma_PktQ freePktInfoQ;

    /*! Queue that holds packets ready to be sent to the hardware */
    NetBufQueue readyPbufQ;

    /*! Queue that holds packets that were not sent to the hardware in previous submit */
    NetBufQueue unusedPbufQ;

    /*! lwIP interface statistics */
    EnetNetIF_TxStats stats;

    Enet_notify_t txPktNotify;

    /*! Whether TX event should be disabled or not. When disabled, "lazy" descriptor recycle
     *  is used instead, which defers retrieval till none is available */
    bool disableEvent;
} EnetNetIF_TxObj, *EnetNetIF_TxHandle;

/**
 * \brief
 *  Packet device information
 *
 * \details
 *  This structure caches the device info.
 */
typedef struct xEnetDriverObj
{
    /*! RX object */
    EnetNetIF_RxObj rx[CONFIG_MAX_RX_CHANNELS];

    /*! Number of RX channels allocated by Application */
    uint32_t numRxChannels;

	/*! TX object */
    EnetNetIF_TxObj tx[CONFIG_MAX_TX_CHANNELS];

    /*! Number of TX channels allocated by Application */
    uint32_t numTxChannels;

    /*! lwIP network interface */
    NetworkInterface_t * pxInterface[ENET_CFG_NETIF_MAX];

    uint8_t macAddr[ENET_CFG_NETIF_MAX][ENET_MAC_ADDR_LEN];
	/*! Total number of allocated PktInfo elements */
    uint32_t allocPktInfo;

    EnetNetIF_AppIf_GetEnetIFInstInfo appInfo;
    /** Initialization flag.*/
    uint32_t initDone;
    /** Index of currently connect physical port.*/
    uint32_t currLinkedIf;

    /** Current RX filter */
    uint32_t rxFilter;
    /** Previous MCast Address Counter */
    uint32_t oldMCastCnt;
    /** Previous Multicast list configured by the Application.*/
    uint8_t bOldMCast[(uint32_t)ENET_MAC_ADDR_LEN * CONFG_PKT_MAX_MCAST];
    /** Current MCast Address Counter */
    uint32_t MCastCnt;
    /** Multicast list configured by the Application.*/
    uint8_t bMCast[(uint32_t)ENET_MAC_ADDR_LEN * CONFG_PKT_MAX_MCAST];
    /** Link is up flag. */
    uint32_t linkIsUp;
    /** Device is operating in test digital loopback mode.*/
    uint32_t inDLBMode;
    /** Total number of PBM packets allocated by application - used for debug purpose.*/
    uint32_t numAllocPbufPkts;

    /*
     * Clock handle for triggering the packet Rx notify
     */
    ClockP_Object pacingClkObj;

    /*
     * Handle to Binary Semaphore LWIP_LWIPIF_input when Rx packet queue is ready
     */
    SemaphoreP_Object pollLinkSemObj;

    /**< Print buffer */
    char printBuf[ENET_CFG_PRINT_BUF_LEN];

    /**< Print Function */
    Enet_Print print;

    /*! CPU load stats */
    EnetNetIF_Stats stats;

    EnetNetIF_RxHandle mapNetif2Rx[ENET_CFG_NETIF_MAX];

    EnetNetIF_TxHandle mapNetif2Tx[ENET_CFG_NETIF_MAX];

    NetworkInterface_t *mapRxPort2Netif[CPSW_STATS_MACPORT_MAX];

    Enet_MacPort mapNetif2TxPortNum[ENET_CFG_NETIF_MAX];


    Enet_notify_t rxPktNotify;

    Enet_notify_t txPktNotify;
}
xEnetDriverObj, *xEnetDriverHandle;

typedef struct _xNetIFArgs
{
    uint32_t xNetIFID;
    xEnetDriverHandle hEnet;
    uint32_t xLinkUp;
} xNetIFArgs;

typedef struct EnetNetIF_AppIf_CustomNetBuf_t
{
   NetworkBufferDescriptor_t xNetworkBuffer;
   EnetDma_Pkt *pktInfoMem;
   EnetDma_PktQ *freePktInfoQ;
} EnetNetIF_AppIf_CustomNetBuf;

xEnetDriverHandle FreeRTOSTCPEnet_open(NetworkInterface_t * pxInterface);

#define ENETNETIF_RXFLOW_2_PORTIDX(num) (num - 1U)
