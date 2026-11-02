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

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_TCP_Transmission.h"

#include "FreeRTOS_TCP_IP.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_TCP_Reception_DiffConfig_stubs.c"
#include "FreeRTOS_TCP_Reception.h"

int32_t prvSingleStepTCPHeaderOptions( const uint8_t * const pucPtr,
                                       size_t uxTotalLength,
                                       FreeRTOS_Socket_t * const pxSocket,
                                       BaseType_t xHasSYNFlag );

/* ============================ Test Variables ============================ */

static FreeRTOS_Socket_t xSocket;

/* ============================ Test Helpers ============================ */

/* Passes an MSS option that advertises usPeerMSS to a socket using
 * ipconfigTCP_MSS, and returns the segment size the TX window then uses. */
static uint16_t usWindowMSSAfterPeerMSS( uint16_t usPeerMSS )
{
    const uint8_t ucTCPOptions[] = { 0x02, 0x04, 0x00, 0x00 };
    int32_t lResult;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.u.xTCP.usMSS = ipconfigTCP_MSS;
    xSocket.u.xTCP.xTCPWindow.usMSS = ipconfigTCP_MSS;
    usChar2u16_ExpectAnyArgsAndReturn( usPeerMSS );
    FreeRTOS_min_uint32_ExpectAndReturn( usPeerMSS, ipconfigTCP_TX_MSS, ( usPeerMSS < ipconfigTCP_TX_MSS ) ? usPeerMSS : ipconfigTCP_TX_MSS );

    lResult = prvSingleStepTCPHeaderOptions( ucTCPOptions, sizeof( ucTCPOptions ), &xSocket, pdTRUE );

    TEST_ASSERT_EQUAL( 4, lResult );
    TEST_ASSERT_EQUAL( ipconfigTCP_MSS, xSocket.u.xTCP.usMSS );

    return xSocket.u.xTCP.xTCPWindow.usMSS;
}

/* ============================== Test Cases ============================== */

/**
 * @brief test_prvSingleStepTCPHeaderOptions_TxMSS_PeerMSS
 * To validate if a peer that advertises an MSS above ipconfigTCP_MSS gets
 * segments of that size, while the socket keeps advertising ipconfigTCP_MSS.
 */
void test_prvSingleStepTCPHeaderOptions_TxMSS_PeerMSS( void )
{
    TEST_ASSERT_EQUAL( 1400, usWindowMSSAfterPeerMSS( 1400 ) );
}

/**
 * @brief test_prvSingleStepTCPHeaderOptions_TxMSS_Limit
 * To validate if the segment size stays at ipconfigTCP_TX_MSS when the peer
 * advertises a larger MSS.
 */
void test_prvSingleStepTCPHeaderOptions_TxMSS_Limit( void )
{
    TEST_ASSERT_EQUAL( ipconfigTCP_TX_MSS, usWindowMSSAfterPeerMSS( 9000 ) );
}
