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

/**
 *  \file ti_enet_lwipif.h
 *
 *  \brief Enet Lwip Interface header file.
 */

/* ========================================================================== */
/*                             Include Files                                  */
/* ========================================================================== */

#include <string.h>
#include <stdint.h>
#include <stdarg.h>

#include <lwip/netif.h>
#include <lwip/tcpip.h>

#include "lwip2enet.h"
#include <networking/enet/core/lwipif/inc/lwip2lwipif.h>
#include <networking/enet/core/lwipif/inc/lwipif2enet_AppIf.h>

#include "Enet_NetIF.h"

/* ========================================================================== */
/*                           Macros & Typedefs                                */
/* ========================================================================== */

/* ========================================================================== */
/*                         Structure Declarations                             */
/* ========================================================================== */
typedef enum NetifName_e
{
    NetifName_CPSW_SWITCH = 0,
//    NetifName_CPSW_DUAL_MAC_PORT1,
//    NetifName_CPSW_DUAL_MAC_PORT2,
    NetifName_NUM_NETIFS,
}NetifName_e;

typedef void* LwipifEnetApp_Handle;

/* ========================================================================== */
/*                          Function Declarations                             */
/* ========================================================================== */
LwipifEnetApp_Handle LwipifEnetApp_getHandle();
struct netif* LwipifEnetApp_netifOpen(LwipifEnetApp_Handle handle, uint32_t netifIdx, const ip4_addr_t *ipaddr, const ip4_addr_t *netmask, const ip4_addr_t *gw);
void LwipifEnetApp_netifClose(LwipifEnetApp_Handle handle, const uint32_t netifIdx);
struct netif * EnetNetIFAppCb_getEnetIFInstInfo(LwipifEnetApp_Handle handle, uint32_t netifIdx);

NetworkInterface_t * pxInterface FreeRTOSTCPifEnetAppCb_getEnetFreeRTOSTCPIfInstInfo(Enet_Type enetType, uint32_t instId, EnetNetIF_AppIf_GetEnetIFInstInfo *outArgs);

void LwipifEnetApp_getRxChIDs(const Enet_Type enetType, const uint32_t instId, uint32_t* pRxChIdCount, uint32_t rxChIdList[LWIPIF_MAX_RX_CHANNELS_PER_PHERIPHERAL]);
void LwipifEnetApp_getTxChIDs(const Enet_Type enetType, const uint32_t instId, uint32_t* pTxChIdCount, uint32_t txChIdList[LWIPIF_MAX_TX_CHANNELS_PER_PHERIPHERAL]);
void LwipifEnetAppCb_getTxHandleInfo(LwipifEnetAppIf_GetTxHandleInArgs *inArgs,
                                     LwipifEnetAppIf_TxHandleInfo *outArgs);
void LwipifEnetAppCb_getRxHandleInfo(LwipifEnetAppIf_GetRxHandleInArgs *inArgs,
                                     LwipifEnetAppIf_RxHandleInfo *outArgs);
void LwipifEnetAppCb_releaseTxHandle(LwipifEnetAppIf_ReleaseTxHandleInfo *releaseInfo);
void LwipifEnetAppCb_releaseRxHandle(LwipifEnetAppIf_ReleaseRxHandleInfo *releaseInfo);
void LwipifEnetAppCb_pbuf_free_custom(struct pbuf *p);


EnetNetIF_RxMode_t EnetApp_getRxMode(Enet_Type enetType, uint32_t instId);


/*
 *  Functions provided by enet_netif_manager.c to initialize a new netif, create tx & rx tasks, and start a scheduler OS agnostically.
 */
void LwipifEnetApp_startSchedule(LwipifEnetApp_Handle handle, struct netif *netif
);

struct netif * LwipifEnetApp_getNetifFromName(NetifName_e name);

