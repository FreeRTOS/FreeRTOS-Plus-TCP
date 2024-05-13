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


#include "Enet_NetIF.h"

#ifndef FREERTOS_ENET_CONFIG_H
    #define FREERTOS_ENET_CONFIG_H

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


void EnetNetIFAppCb_getTxHandleInfo(EnetNetIFAppIf_GetTxHandleInArgs *inArgs,
                                     EnetNetIFAppIf_TxHandleInfo *outArgs);
void EnetNetIFAppCb_getRxHandleInfo(EnetNetIFAppIf_GetRxHandleInArgs *inArgs,
                                     EnetNetIFAppIf_RxHandleInfo *outArgs);

void EnetApp_getTxChIDs(const Enet_Type enetType, const uint32_t instId, uint32_t* pTxChIdCount, uint32_t txChIdList[FREERTOS_TCPIF_MAX_TX_CHANNELS_PER_PHERIPHERAL]);

void EnetApp_getRxChIDs(const Enet_Type enetType, const uint32_t instId, uint32_t* pRxChIdCount, uint32_t rxChIdList[FREERTOS_TCPIF_MAX_RX_CHANNELS_PER_PHERIPHERAL]);

EnetNetIF_RxMode_t EnetApp_getRxMode(Enet_Type enetType, uint32_t instId);

EnetNetIF_RxMode_t EnetApp_getRxMode(Enet_Type enetType, uint32_t instId);

#endif /* FREERTOS_ENET_CONFIG_H */
