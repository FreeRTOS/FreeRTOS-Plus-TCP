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
 * @file FreeRTOSIPDeprecatedDefinitions.h
 * @brief File that ensures defined configuration constants are using the most up to date naming.
 */

#ifndef FREERTOS_IP_DEPRECATED_DEFINITIONS_H
#define FREERTOS_IP_DEPRECATED_DEFINITIONS_H

#ifndef FREERTOS_IP_CONFIG_DEFAULTS_H
    #error FreeRTOSIPConfigDefaults.h has not been included yet
#endif

#ifdef dnsMAX_REQUEST_ATTEMPTS
    #error Now called: ipconfigDNS_REQUEST_ATTEMPTS
#endif

#ifdef FreeRTOS_lprintf
    #error Now called: FreeRTOS_debug_printf
#endif

#ifdef HAS_TX_CRC_OFFLOADING
    #error Now called: ipconfigHAS_TX_CRC_OFFLOADING
#endif

#ifdef HAS_RX_CRC_OFFLOADING
    #error Now called: ipconfigHAS_RX_CRC_OFFLOADING, Not used 
#endif

#ifdef ipconfigBUFFER_ALLOC_FIXED_SIZE
    #error ipconfigBUFFER_ALLOC_FIXED_SIZE was dropped and replaced by a const value, declared in BufferAllocation[12].c
#endif

#ifdef ipconfigDHCP_USES_USER_HOOK
    #error ipconfigDHCP_USES_USER_HOOK has been replaced by ipconfigUSE_DHCP_HOOK
#endif

#ifdef ipconfigDRIVER_INCLUDED_RX_IP_FILTERING
    #error Now called: ipconfigETHERNET_DRIVER_FILTERS_PACKETS
#endif

#ifdef ipconfigHAS_INLINE_FUNCTIONS
    #error ipconfigHAS_INLINE_FUNCTIONS is not used
#endif

#ifdef ipconfigMAX_SEND_BLOCK_TIME_TICKS
    #error Now called: ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS
#endif

#ifdef ipconfigNIC_SEND_PASSES_DMA
    #error Now called: ipconfigZERO_COPY_TX_DRIVER
#endif

#ifdef ipconfigNUM_NETWORK_BUFFERS
    #error Now called: ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS
#endif

#ifdef ipconfigRAND32
    #error ipconfigRAND32 has been replaced by xApplicationGetRandomNumber( uint32_t *pulValue )
#endif

#ifdef ipconfigTCP_HANG_PROT
    #error Now called: ipconfigTCP_HANG_PROTECTION
#endif

#ifdef ipconfigTCP_HANG_PROT_TIME
    #error Now called: ipconfigTCP_HANG_PROTECTION_TIME
#endif

#ifdef ipconfigTCP_RX_BUF_LEN
    #error ipconfigTCP_RX_BUF_LEN is Now called ipconfigTCP_RX_BUFFER_LENGTH
#endif

#ifdef ipconfigTCP_TX_BUF_LEN
    #error ipconfigTCP_TX_BUF_LEN is Now called ipconfigTCP_TX_BUFFER_LENGTH
#endif

#ifdef ipconfigUDP_TASK_PRIORITY
    #error Now called: ipconfigIP_TASK_PRIORITY
#endif

#ifdef ipconfigUDP_TASK_STACK_SIZE_WORDS
    #error Now called: ipconfigIP_TASK_STACK_SIZE_WORDS
#endif

#ifdef ipconfigUSE_RECEIVE_CONNECT_CALLBACKS
    #error Now called: ipconfigUSE_CALLBACKS
#endif

#ifdef ipconfigUSE_TCP_TIMESTAMPS
    #error ipconfigUSE_TCP_TIMESTAMPS is not used
#endif

#ifdef ipFILLER_SIZE
    #error Now called: ipconfigPACKET_FILLER_SIZE
#endif

#ifdef tcpconfigIP_TIME_TO_LIVE
    #error Now called: ipconfigTCP_TIME_TO_LIVE
#endif

#ifdef updconfigIP_TIME_TO_LIVE
    #error Now called: ipconfigUDP_TIME_TO_LIVE
#endif

#endif /* FREERTOS_IP_DEPRECATED_DEFINITIONS_H */