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
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_list.h"

#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_task.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_TCP_State_Handling.h"
#include "mock_FreeRTOS_TCP_Reception.h"
#include "mock_FreeRTOS_TCP_Utils.h"
#include "mock_TCP_Transmission_DiffConfig_list_macros.h"

#include "FreeRTOS_TCP_IP.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"
#include "FreeRTOSIPConfigDefaults.h"

#include "FreeRTOS_TCP_Transmission_DiffConfig_stubs.c"
#include "FreeRTOS_TCP_Transmission.h"

/* ============================ Test Variables ============================ */

static FreeRTOS_Socket_t xSocket;
static NetworkBufferDescriptor_t xNetworkBuffer;
static uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];
static StreamBuffer_t xStreamBuffer;

/* ============================ Test Helpers ============================ */

/* Prepares an established socket with 500 bytes ready in its TX window, and
 * returns the TCP flags of the segment that prvTCPPrepareSend() builds. The
 * argument is the number of bytes queued from the segment start. */
static uint8_t ucPrepareSendFlags( size_t uxQueuedBytes )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    int32_t lBytesSent;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    xBufferAllocFixedSize = pdFALSE;

    xSocket.u.xTCP.txStream = &xStreamBuffer;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.usMSS = 1000;
    xSocket.u.xTCP.bits.bSendKeepAlive = pdTRUE;
    xSocket.u.xTCP.ucKeepRepCount = 1;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 500 );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();
    uxStreamBufferDistance_IgnoreAndReturn( uxQueuedBytes );
    uxStreamBufferGet_IgnoreAndReturn( 20 );

    lBytesSent = prvTCPPrepareSend( &xSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 540, lBytesSent );

    return ( ( TCPPacket_t * ) ucEthernetBuffer )->xTCPHeader.ucTCPFlags;
}

/* ============================== Test Cases ============================== */

/**
 * @brief test_prvTCPPrepareSend_PSH_LastSegment
 * To validate if prvTCPPrepareSend() sets PSH on the segment that empties the
 * send queue.
 */
void test_prvTCPPrepareSend_PSH_LastSegment( void )
{
    uint8_t ucFlags = ucPrepareSendFlags( 500 );

    TEST_ASSERT_EQUAL( tcpTCP_FLAG_PSH, ucFlags & tcpTCP_FLAG_PSH );
}

/**
 * @brief test_prvTCPPrepareSend_PSH_MoreQueued
 * To validate if prvTCPPrepareSend() leaves PSH off a segment when more data
 * is queued after it.
 */
void test_prvTCPPrepareSend_PSH_MoreQueued( void )
{
    uint8_t ucFlags = ucPrepareSendFlags( 1000 );

    TEST_ASSERT_EQUAL( 0, ucFlags & tcpTCP_FLAG_PSH );
}
