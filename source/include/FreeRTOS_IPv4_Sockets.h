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

/* Standard includes. */
    #include <string.h>

/* FreeRTOS includes. */
    #include "FreeRTOS.h"

    #ifdef __cplusplus
        extern "C" {
    #endif


/* Translate from 192.168.1.1 to a 32-bit number. */
    BaseType_t FreeRTOS_inet_pton4( const char * pcSource,
                                    void * pvDestination );

    const char * FreeRTOS_inet_ntop4( const void * pvSource,
                                      char * pcDestination,
                                      socklen_t uxSize );

/**
 * @brief Called by prvSendUDPPacket(), this function will UDP packet
 *        fields and IPv4 address for the packet to be send.
 */
    void * xSend_UDP_Update_IPv4( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                  const struct freertos_sockaddr * pxDestinationAddress );

/**
 * @brief Called by FreeRTOS_recvfrom(), this function will update socket
 *        address with IPv4 address from the packet received.
 */
    size_t xRecv_Update_IPv4( const NetworkBufferDescriptor_t * pxNetworkBuffer,
                              struct freertos_sockaddr * pxSourceAddress );

    #ifdef __cplusplus
}         /* extern "C" */
    #endif
#endif /* FREERTOS_IPV4_SOCKETS_H */
