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

#ifndef FREERTOS_IPV6_SOCKETS_H
    #define FREERTOS_IPV6_SOCKETS_H

    #ifdef __cplusplus
        extern "C" {
    #endif

/* Standard includes. */
    #include <string.h>

/* FreeRTOS includes. */
    #include "FreeRTOS.h"
    #include "task.h"

/* Application level configuration options. */
    #include "FreeRTOSIPConfig.h"
    #include "FreeRTOSIPConfigDefaults.h"

    #include "FreeRTOS_IP_Common.h"

   /** @brief When ucASCIIToHex() can not convert a character,
 *         the value 255 will be returned.
 */
#define socketINVALID_HEX_CHAR    0xffU

struct freertos_sockaddr6
{
    uint8_t sin_len;           /**< Ignored, still present for backward compatibility. */
    uint8_t sin_family;        /**< Set to FREERTOS_AF_INET6. */
    uint16_t sin_port;         /**< The port number in network-endian format. */
    uint32_t sin_flowinfo;     /**< IPv6 flow information, not used in this library. */
    IPv6_Address_t sin_addrv6; /**< The IPv6 address. */
};
/** @brief Introduce a short name to make casting easier. */
    typedef struct freertos_sockaddr6 sockaddr6_t;

/** @brief The struct sNTOP6_Set is a set of parameters used by  the function FreeRTOS_inet_ntop6().
 * It passes this set to a few helper functions. */
struct sNTOP6_Set
{
    const uint16_t * pusAddress; /**< The network address, 8 short values. */
    BaseType_t xZeroStart;       /**< The position of the first byte of the longest train of zero values. */
    BaseType_t xZeroLength;      /**< The number of short values in the longest train of zero values. */
    BaseType_t xIndex;           /**< The read index in the array of short values, the network address. */
    socklen_t uxTargetIndex;     /**< The write index in 'pcDestination'. */
};

/** @brief The struct sNTOP6_Set is a set of parameters used by  the function FreeRTOS_inet_ntop6().
 * It passes this set to a few helper functions. */
struct sPTON6_Set
{
    uint32_t ulValue;         /**< A 32-bit accumulator, only 16 bits are used. */
    BaseType_t xHadDigit;     /**< Becomes pdTRUE as soon as ulValue has valid data. */
    BaseType_t xTargetIndex;  /**< The index in the array pucTarget to write the next byte. */
    BaseType_t xColon;        /**< The position in the output where the train of zero's will start. */
    BaseType_t xHighestIndex; /**< The highest allowed value of xTargetIndex. */
    uint8_t * pucTarget;      /**< The array of bytes in which the resulting IPv6 address is written. */
};



uint8_t ucASCIIToHex( char cChar );
/*
 * Convert a string like 'fe80::8d11:cd9b:8b66:4a80'
 * to a 16-byte IPv6 address
 */
    BaseType_t FreeRTOS_inet_pton6( const char * pcSource,
                                    void * pvDestination );
    const char * FreeRTOS_inet_ntop6( const void * pvSource,
                                      char * pcDestination,
                                      socklen_t uxSize );

    /* Function to get the remote address and IP port */
    BaseType_t FreeRTOS_GetRemoteAddress6( ConstSocket_t xSocket,
                                              struct freertos_sockaddr6 * pxAddress );
    size_t FreeRTOS_GetLocalAddress( ConstSocket_t xSocket,
                                     struct freertos_sockaddr * pxAddress );

    #ifdef __cplusplus
        } /* extern "C" */
    #endif

#endif /* FREERTOS_IPV6_SOCKETS_H */