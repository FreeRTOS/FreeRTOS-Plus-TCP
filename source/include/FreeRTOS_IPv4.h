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

#ifndef FREERTOS_IPV4_H
#define FREERTOS_IPV4_H

#include "FreeRTOS.h"
#include "task.h"

/* Application level configuration options. */
#include "FreeRTOSIPConfig.h"
#include "FreeRTOSIPConfigDefaults.h"
#include "IPTraceMacroDefaults.h"

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* Forward declarations. */
struct xNETWORK_BUFFER;
enum eFrameProcessingResult;
struct xIP_PACKET;

#define ipSIZE_OF_IPv4_HEADER               20U
#define ipSIZE_OF_IPv4_ADDRESS              4U
#define ipSIZE_OF_ICMPv4_HEADER             8U
#define ipTYPE_IPv4                         ( 0x40U )

#define ipFIRST_LOOPBACK_IPv4               0x7F000000UL         /**< Lowest IPv4 loopback address (including). */
#define ipLAST_LOOPBACK_IPv4                0x80000000UL         /**< Highest IPv4 loopback address (excluding). */

/* The first byte in the IPv4 header combines the IP version (4) with
 * with the length of the IP header. */
#define ipIPV4_VERSION_HEADER_LENGTH_MIN    0x45U /**< Minimum IPv4 header length. */
#define ipIPV4_VERSION_HEADER_LENGTH_MAX    0x4FU /**< Maximum IPv4 header length. */

/*
 *  These functions come from the IPv4-only library.
 *  TODO : They should get an extra parameter, the end-point
 *  void FreeRTOS_SetIPAddress( uint32_t ulIPAddress );
 *  void FreeRTOS_SetNetmask( uint32_t ulNetmask );
 *  void FreeRTOS_SetGatewayAddress( uint32_t ulGatewayAddress );
 *  uint32_t FreeRTOS_GetGatewayAddress( void );
 *  uint32_t FreeRTOS_GetDNSServerAddress( void );
 *  uint32_t FreeRTOS_GetNetmask( void );
 */

void FreeRTOS_SetIPAddress( uint32_t ulIPAddress );
void FreeRTOS_SetNetmask( uint32_t ulNetmask );
void FreeRTOS_SetGatewayAddress( uint32_t ulGatewayAddress );
uint32_t FreeRTOS_GetGatewayAddress( void );
uint32_t FreeRTOS_GetDNSServerAddress( void );
uint32_t FreeRTOS_GetNetmask( void );
uint32_t FreeRTOS_GetIPAddress( void );

/* Show all valid ARP entries
 */
#if ( ipconfigHAS_PRINTF != 0 ) || ( ipconfigHAS_DEBUG_PRINTF != 0 )
    void FreeRTOS_PrintARPCache( void );
#endif

/* Return pdTRUE if the IPv4 address is a multicast address. */
BaseType_t xIsIPv4Multicast( uint32_t ulIPAddress );

/* The function 'prvAllowIPPacket()' checks if a packets should be processed. */
enum eFrameProcessingResult prvAllowIPPacketIPv4( const struct xIP_PACKET * const pxIPPacket,
                                                  const struct xNETWORK_BUFFER * const pxNetworkBuffer,
                                                  UBaseType_t uxHeaderLength );

/* Check if the IP-header is carrying options. */
enum eFrameProcessingResult prvCheckIP4HeaderOptions( struct xNETWORK_BUFFER * const pxNetworkBuffer );


/* *INDENT-OFF* */
#ifdef __cplusplus
    } /* extern "C" */
#endif
/* *INDENT-ON* */

#endif /* FREERTOS_IP_H */
