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

#ifndef FREERTOS_IPV4_SOCKETS_H
    #define FREERTOS_IPV4_SOCKETS_H

    #ifdef __cplusplus
        extern "C" {
    #endif

/* Standard includes. */
    #include <string.h>

/* FreeRTOS includes. */
    #include "FreeRTOS.h"

/* Application level configuration options. */
    #include "FreeRTOSIPConfig.h"
    #include "FreeRTOSIPConfigDefaults.h"


/** @brief For this limited implementation, only two members are required in the
 * Berkeley style sockaddr structure. */
struct freertos_sockaddr
{
    uint8_t sin_len;                                  /**< Ignored, still present for backward compatibility. */
    uint8_t sin_family;                               /**< Set to FREERTOS_AF_INET. */
    uint16_t sin_port;                                /**< The port number in network-endian format. */
    uint32_t sin_addr;                                /**< The IP-address in network-endian format. */
    #if ( ipconfigUSE_IPv6 != 0 )
        uint8_t sin_filler[ ipSIZE_OF_IPv6_ADDRESS ]; /**< Make sure that the IPv4 and IPv6 socket addresses have an equal size. */
    #endif
};

/** @brief Introduce a short name to make casting easier. */
typedef struct freertos_sockaddr sockaddr4_t;

/* Translate from 192.168.1.1 to a 32-bit number. */
    BaseType_t FreeRTOS_inet_pton4( const char * pcSource,
                                void * pvDestination );
    const char * FreeRTOS_inet_ntop4( const void * pvSource,
                                  char * pcDestination,
                                  socklen_t uxSize );

    /* Function to get the remote address and IP port */
    BaseType_t FreeRTOS_GetRemoteAddress( ConstSocket_t xSocket,
                                              struct freertos_sockaddr * pxAddress );
     size_t FreeRTOS_GetLocalAddress( ConstSocket_t xSocket,
                                     struct freertos_sockaddr6 * pxAddress6 );

static __inline BaseType_t FreeRTOS_GetIPType( ConstSocket_t xSocket )
{
                ( void ) xSocket;
                return ( BaseType_t ) ipTYPE_IPv4;
}

    #ifdef __cplusplus
        } /* extern "C" */
    #endif
#endif /* FREERTOS_IPV4_SOCKETS_H */

