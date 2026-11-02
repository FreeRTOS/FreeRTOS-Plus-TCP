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

#include "FreeRTOS.h"

#include "catch_assert.h"

#include "FreeRTOSConfig.h"
#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_TCP_WIN.h"

#include "mock_list.h"
#include "mock_FreeRTOS_TCP_WIN_DiffConfig_list_macros.h"
#include "mock_portable.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_task.h"

extern List_t xSegmentList;

/* ============================ Unity Fixtures ============================ */

/*! called before each test case */
void setUp( void )
{
    /* The empty list end points to itself. */
    xSegmentList.pxIndex = ( ListItem_t * ) &( xSegmentList.xListEnd );
    xSegmentList.xListEnd.xItemValue = portMAX_DELAY;
    xSegmentList.xListEnd.pxNext = ( ListItem_t * ) &( xSegmentList.xListEnd );
    xSegmentList.xListEnd.pxPrevious = ( ListItem_t * ) &( xSegmentList.xListEnd );
    xSegmentList.uxNumberOfItems = 0U;
}

/*! called after each test case */
void tearDown( void )
{
}

/* ============================ Test Helpers ============================ */

/* Makes xTCPWindowTxDropJumbo() find pxSegment at the head of the wait queue. */
static void vExpectWaitQueueHead( TCPSegment_t * pxSegment )
{
    static ListItem_t xListItem;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( pxSegment );
}

/* ============================== Test Cases ============================== */

/**
 * @brief test_xTCPWindowTxDropJumbo_NoSegmentWaiting
 * To validate if xTCPWindowTxDropJumbo() keeps the window when no segment
 * waits for an ACK.
 */
void test_xTCPWindowTxDropJumbo_NoSegmentWaiting( void )
{
    TCPWindow_t xWindow = { 0 };

    xWindow.usMSS = ipconfigTCP_TX_MSS;
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    TEST_ASSERT_EQUAL( pdFALSE, xTCPWindowTxDropJumbo( &xWindow ) );
    TEST_ASSERT_EQUAL( ipconfigTCP_TX_MSS, xWindow.usMSS );
}

/**
 * @brief test_xTCPWindowTxDropJumbo_FewSends
 * To validate if xTCPWindowTxDropJumbo() keeps the window while a jumbo
 * segment has been sent fewer than three times.
 */
void test_xTCPWindowTxDropJumbo_FewSends( void )
{
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };

    xWindow.usMSS = ipconfigTCP_TX_MSS;
    xSegment.lDataLength = ipconfigTCP_TX_MSS;
    xSegment.u.bits.ucTransmitCount = 2U;
    vExpectWaitQueueHead( &xSegment );

    TEST_ASSERT_EQUAL( pdFALSE, xTCPWindowTxDropJumbo( &xWindow ) );
    TEST_ASSERT_EQUAL( ipconfigTCP_TX_MSS, xWindow.usMSS );
}

/**
 * @brief test_xTCPWindowTxDropJumbo_StandardSegment
 * To validate if xTCPWindowTxDropJumbo() keeps the window when a segment no
 * larger than ipconfigTCP_MSS is lost.
 */
void test_xTCPWindowTxDropJumbo_StandardSegment( void )
{
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };

    xWindow.usMSS = ipconfigTCP_TX_MSS;
    xSegment.lDataLength = ipconfigTCP_MSS;
    xSegment.u.bits.ucTransmitCount = 3U;
    vExpectWaitQueueHead( &xSegment );

    TEST_ASSERT_EQUAL( pdFALSE, xTCPWindowTxDropJumbo( &xWindow ) );
    TEST_ASSERT_EQUAL( ipconfigTCP_TX_MSS, xWindow.usMSS );
}

/**
 * @brief test_xTCPWindowTxDropJumbo_Lost
 * To validate if xTCPWindowTxDropJumbo() frees the unacknowledged segments,
 * rewinds the next sequence number and falls back to ipconfigTCP_MSS after a
 * jumbo segment is sent three times.
 */
void test_xTCPWindowTxDropJumbo_Lost( void )
{
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };

    xWindow.usMSS = ipconfigTCP_TX_MSS;
    xWindow.pxHeadSegment = &xSegment;
    xWindow.tx.ulCurrentSequenceNumber = 1000U;
    xWindow.tx.ulHighestSequenceNumber = 5000U;
    xWindow.ulNextTxSequenceNumber = 5000U;
    xSegment.lDataLength = ipconfigTCP_TX_MSS;
    xSegment.u.bits.ucTransmitCount = 3U;
    vExpectWaitQueueHead( &xSegment );

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1U );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xSegment );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0U );

    TEST_ASSERT_EQUAL( pdTRUE, xTCPWindowTxDropJumbo( &xWindow ) );
    TEST_ASSERT_EQUAL( ipconfigTCP_MSS, xWindow.usMSS );
    TEST_ASSERT_NULL( xWindow.pxHeadSegment );
    TEST_ASSERT_EQUAL( 1000U, xWindow.ulNextTxSequenceNumber );
    TEST_ASSERT_EQUAL( 1000U, xWindow.tx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSegment.lDataLength );
}
