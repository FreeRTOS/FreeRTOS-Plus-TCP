/*
 * FreeRTOS+TCP
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


/* Include Unity header */
#include <unity.h>

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"


const BaseType_t xBufferAllocFixedSize = pdTRUE;

/* The IPv6 mDNS and LLMNR groups, used by the tests that check the multicast
 * carve-out in DNS_ReadReply. The real definitions live in FreeRTOS_DNS.c,
 * which is not part of this test suite. */
const IPv6_Address_t ipMDNS_IP_ADDR_IPv6 =
{
    { 0xffU, 0x02U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U,
      0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0xfbU }
};

/* ff02::1:3 */
const IPv6_Address_t ipLLMNR_IP_ADDR_IPv6 =
{
    { 0xffU, 0x02U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U,
      0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x01U, 0x00U, 0x03U }
};

/* Source address that a stubbed FreeRTOS_recvfrom() will report back to the
 * caller, and the number of test doubles configured. Tests set xStubFromAddress
 * before calling DNS_ReadReply(). */
struct freertos_sockaddr xStubFromAddress;

int32_t FreeRTOS_recvfrom_ReturnFromAddress( const ConstSocket_t xSocket,
                                             void * pvBuffer,
                                             size_t uxBufferLength,
                                             BaseType_t xFlags,
                                             struct freertos_sockaddr * pxSourceAddress,
                                             socklen_t * pxSourceAddressLength,
                                             int cmock_num_calls )
{
    ( void ) xSocket;
    ( void ) pvBuffer;
    ( void ) uxBufferLength;
    ( void ) xFlags;
    ( void ) pxSourceAddressLength;
    ( void ) cmock_num_calls;

    if( pxSourceAddress != NULL )
    {
        ( void ) memcpy( pxSourceAddress, &xStubFromAddress, sizeof( *pxSourceAddress ) );
    }

    /* Non-zero payload length so DNS_ReadReply proceeds to the source check. */
    return 300;
}

void vPortEnterCritical( void )
{
}

void vPortExitCritical( void )
{
}

BaseType_t xApplicationDNSQueryHook_Multi( struct xNetworkEndPoint * pxEndPoint,
                                           const char * pcName )
{
}
