/*
 * FreeRTOS+TCP V2.3.4
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
#include "FreeRTOS_Routing.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"

#if ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 )

/*
 * Send a message to the IP-task, which will call vDHCPProcess().
 */
    BaseType_t xSendDHCPEvent( struct xNetworkEndPoint * pxEndPoint );
#endif /* ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 ) */

#if ( ipconfigZERO_COPY_TX_DRIVER != 0 )

/*
 * For the case where the network driver passes a buffer directly to a DMA
 * descriptor, this function can be used to translate a 'network buffer' to
 * a 'network buffer descriptor'.
 */
    NetworkBufferDescriptor_t * pxPacketBuffer_to_NetworkBuffer( const void * pvBuffer );
#endif

void vPreCheckConfigs( void );

/*
 * Called to create a network connection when the stack is first started, or
 * when the network connection is lost.
 */
void prvProcessNetworkDownEvent( NetworkInterface_t * pxInterface );

/* Set the MAC-address that belongs to a given IPv4 multi-cast address. */
void vSetMultiCastIPv4MacAddress( uint32_t ulIPAddress,
                                  MACAddress_t * pxMACAddress );

#if ( ipconfigUSE_IPv6 != 0 )
    /* Set the MAC-address that belongs to a given IPv6 multi-cast address. */
    void vSetMultiCastIPv6MacAddress( IPv6_Address_t * pxAddress,
                                      MACAddress_t * pxMACAddress );
#endif

/* *INDENT-OFF* */
#ifdef __cplusplus
    } /* extern "C" */
#endif
/* *INDENT-ON* */

#endif /* FREERTOS_IP_UTILS_H */
