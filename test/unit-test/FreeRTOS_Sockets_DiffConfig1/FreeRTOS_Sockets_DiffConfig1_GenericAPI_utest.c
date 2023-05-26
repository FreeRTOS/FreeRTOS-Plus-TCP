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

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_Sockets_DiffConfig1_list_macros.h"
#include "mock_event_groups.h"
#include "mock_portable.h"

#include "mock_FreeRTOS_IP.h"

#include "FreeRTOS_Sockets.h"

#include "FreeRTOS_Sockets_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* ============================== Test Cases ============================== */

/**
 * @brief Creation of socket when the protocol is TCPv6 with MSS less than
 * the difference of IPv6 & IPv4 header length.
 */
void test_FreeRTOS_socket_TCPv6SocketLowMSS( void )
{
    Socket_t xSocket;
    FreeRTOS_Socket_t * pxSocket;
    BaseType_t xDomain = FREERTOS_AF_INET6, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    uint8_t ucSocket[ ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ) ];
    uint8_t xEventGroup[ sizeof( uintptr_t ) ];

    pxSocket = ( FreeRTOS_Socket_t * ) ucSocket;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), ( void * ) ucSocket );

    xEventGroupCreate_ExpectAndReturn( ( EventGroupHandle_t ) xEventGroup );

    FreeRTOS_round_up_ExpectAndReturn( ipconfigTCP_TX_BUFFER_LENGTH, ipconfigTCP_MSS, 0xAABB );
    FreeRTOS_max_size_t_ExpectAndReturn( 1U, ( uint32_t ) ( ipconfigTCP_RX_BUFFER_LENGTH / 2U ) / ipconfigTCP_MSS, 0x1234 );
    FreeRTOS_max_size_t_ExpectAndReturn( 1U, ( uint32_t ) ( 0xAABB / 2U ) / ipconfigTCP_MSS, 0x3456 );

    vListInitialiseItem_Expect( &( pxSocket->xBoundSocketListItem ) );

    listSET_LIST_ITEM_OWNER_Expect( &( pxSocket->xBoundSocketListItem ), pxSocket );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( ucSocket, xSocket );
    TEST_ASSERT_EQUAL( xSocket->xEventGroup, xEventGroup );
    TEST_ASSERT_EQUAL( xSocket->xReceiveBlockTime, ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->xSendBlockTime, ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->ucSocketOptions, ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT );
    TEST_ASSERT_EQUAL( xSocket->ucProtocol, ( uint8_t ) xProtocol );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.usMSS, ( uint16_t ) ipconfigTCP_MSS );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.uxRxStreamSize, ( size_t ) ipconfigTCP_RX_BUFFER_LENGTH );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.uxTxStreamSize, 0xAABB );
    TEST_ASSERT_EQUAL( 0x1234, pxSocket->u.xTCP.uxRxWinSize );
    TEST_ASSERT_EQUAL( 0x3456, pxSocket->u.xTCP.uxTxWinSize );
}
