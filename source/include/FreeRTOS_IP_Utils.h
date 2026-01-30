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
 * @file FreeRTOS_IP_Utils.h
 * @brief Implements the utility functions for FreeRTOS_IP.c
 */

#ifndef FREERTOS_IP_UTILS_H
#define FREERTOS_IP_UTILS_H

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
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"

#include "FreeRTOS_IPv4_Utils.h"
#include "FreeRTOS_IPv6_Utils.h"

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

#if ipconfigIS_ENABLED( ipconfigSUPPORT_IP_MULTICAST )
    /** @brief A structure holding information about a multicast group address. Used during generation of IGMP/ICMPv6 reports. */
    typedef struct MCastReportDescription
    {
        IPv46_Address_t xMCastGroupAddress; /**< Holds the IPv4/IPv6 multicast group address. xMCastGroupAddress.xIs_IPv6 denotes whether this represents and IGMP or MLD report. */
        ListItem_t xListItem;               /**< List item for adding to the global list of reports. */
        NetworkInterface_t * pxInterface;   /**< The network interface used for sending this report. NULL to send on all interfaces. */
        BaseType_t xNumSockets;             /**< The number of sockets that are subscribed to this multicast group. */
        BaseType_t xCountDown;
    } MCastReportData_t;

/** @brief A structure to hold all data related to an multicast socket option "action". When someone calls FreeRTOS_setsockopt()
 * with one of the multicast socket options, the code allocates a structure like this and stores all the relevant information.
 * The structure is then passed to the IP task for handling. This approach allows us to return an error if we don't have enough
 * memory for a multicast report and allows all actual manipulations to happen within the IP task therefore avoiding the need
 * for critical sections. An exception to this is setting the TTL/HopLimit as it can be done straight from the user task. as
 * an atomic write operation. */
    typedef struct xMCastGroupDesc
    {
        IP_Address_t xMulticastGroup;          /**< Holds the IPv4/IPv6 multicast group address */
        NetworkInterface_t * pxInterface;      /**< Not implemented yet, but should point to a specific interface or NULL for all/default interface */
        FreeRTOS_Socket_t * pxSocket;          /**< The socket this action is applied to */
        MCastReportData_t * pxMCastReportData; /**< Holds the allocated IGMP report descriptor while passing from user code to the IP Task. */
    } MulticastAction_t;
#endif /* ipconfigIS_ENABLED( ipconfigSUPPORT_IP_MULTICAST ) */


/* Forward declaration. */
struct xNetworkInterface;
struct xNetworkEndPoint;

#if ( ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 ) )

/**
 * @brief Create a DHCP event.
 *
 * @return pdPASS or pdFAIL, depending on whether xSendEventStructToIPTask()
 *         succeeded.
 */
    BaseType_t xSendDHCPEvent( struct xNetworkEndPoint * pxEndPoint );
#endif

#if ( ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 ) )

/* Returns the current state of a DHCP process. */
    eDHCPState_t eGetDHCPState( const struct xNetworkEndPoint * pxEndPoint );

#endif

#if ( ipconfigZERO_COPY_TX_DRIVER != 0 ) || ( ipconfigZERO_COPY_RX_DRIVER != 0 )

/**
 * @brief Get the network buffer from the packet buffer.
 *
 * @param[in] pvBuffer: Pointer to the packet buffer.
 *
 * @return The network buffer if the alignment is correct. Else a NULL is returned.
 */
    NetworkBufferDescriptor_t * pxPacketBuffer_to_NetworkBuffer( const void * pvBuffer );
#endif

/**
 * @brief Check the values of configuration options and assert on it. Also verify that the IP-task
 *        has not already been initialized.
 */
void vPreCheckConfigs( void );

/**
 * @brief Called to create a network connection when the stack is first
 *        started, or when the network connection is lost.
 */
void prvProcessNetworkDownEvent( struct xNetworkInterface * pxInterface );

/**
 * @brief Release single UDP packet from a given socket
 */
void vReleaseSinglePacketFromUDPSocket( const ConstSocket_t xSocket );

/* *INDENT-OFF* */
#ifdef __cplusplus
    } /* extern "C" */
#endif
/* *INDENT-ON* */

#endif /* FREERTOS_IP_UTILS_H */
