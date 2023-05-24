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


/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"
#include "FreeRTOS_IP.h"

/* =========================== EXTERN VARIABLES =========================== */

FreeRTOS_Socket_t * prvHandleListen_IPV6( FreeRTOS_Socket_t * pxSocket,
                                          NetworkBufferDescriptor_t * pxNetworkBuffer );

FreeRTOS_Socket_t xSocket, * pxSocket;
NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    pxSocket = NULL;
    pxNetworkBuffer = NULL;
}

/* ============================== Test Cases ============================== */

void test_prvHandleListen_IPV6_NullSocket( void )
{
    FreeRTOS_Socket_t * pxReturn;

    pxNetworkBuffer = &xNetworkBuffer;

    pxReturn = prvHandleListen_IPV6( NULL, pxNetworkBuffer );
}
