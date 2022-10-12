/*
 * FreeRTOS+TCP V3.1.0
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
 * @file FreeRTOS_IP_Timers.h
 * @brief Header file for IP Timers on FreeRTOS+TCP network stack.
 */

#ifndef FREERTOS_IP_TIMERS_H
#define FREERTOS_IP_TIMERS_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"

/*
 * Checks the ARP, DHCP and TCP timers to see if any periodic or timeout
 * processing is required.
 */
void vCheckNetworkTimers( void );

/*
 * Determine how long the IP task can sleep for, which depends on when the next
 * periodic or timeout processing must be performed.
 */
TickType_t xCalculateSleepTime( void );

void vIPTimerStartARPResolution( TickType_t xTime );

void vIPSetTCPTimerExpiredState( BaseType_t xExpiredState );

void vIPSetARPTimerEnableState( BaseType_t xEnableState );

void vIPSetARPResolutionTimerEnableState( BaseType_t xEnableState );

#if ( ipconfigUSE_DHCP != 0 )

/**
 * @brief Enable/disable the DHCP timer.
 * @param[in] xEnableState: pdTRUE - enable timer; pdFALSE - disable timer.
 */
    void vIPSetDHCPTimerEnableState( BaseType_t xEnableState );
#endif

#if ( ipconfigDNS_USE_CALLBACKS != 0 )

/**
 * @brief Enable/disable the DNS timer.
 * @param[in] xEnableState: pdTRUE - enable timer; pdFALSE - disable timer.
 */
    void vIPSetDNSTimerEnableState( BaseType_t xEnableState );
#endif

void vARPTimerReload( TickType_t xTime );
void vTCPTimerReload( TickType_t xTime );
#if ( ipconfigUSE_DHCP == 1 )
    void vDHCPTimerReload( TickType_t xLeaseTime );
#endif

#if ( ipconfigDNS_USE_CALLBACKS != 0 )
    void vDNSTimerReload( uint32_t ulCheckTime );
#endif

/* *INDENT-OFF* */
#ifdef __cplusplus
    } /* extern "C" */
#endif
/* *INDENT-ON* */

#endif /* FREERTOS_IP_TIMERS_H */
