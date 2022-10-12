/*
 * FreeRTOS+TCP V3.1.0
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
#include "mock_Sockets_DiffConfig_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_portable.h"

#include "FreeRTOSIPConfig.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"

#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"

#include "catch_assert.h"

extern List_t xBoundUDPSocketsList;
extern List_t xBoundTCPSocketsList;

BaseType_t prvValidSocket( const FreeRTOS_Socket_t * pxSocket,
                           BaseType_t xProtocol,
                           BaseType_t xIsBound );

uint8_t ucASCIIToHex( char cChar );

BaseType_t bMayConnect( FreeRTOS_Socket_t const * pxSocket );

static uint32_t xRandomNumberToReturn;
static BaseType_t xRNGStatus;
static UBaseType_t uxGlobalCallbackCount;
static BaseType_t xLocalReceiveCallback_Return;
static uint8_t xLocalReceiveCallback_Called = 0;

static FreeRTOS_Socket_t xGlobalSocket;

static void vUserCallbackLocal( FreeRTOS_Socket_t * xSocket )
{
    uxGlobalCallbackCount++;
}

static BaseType_t xStubApplicationGetRandomNumber( uint32_t * xRndNumber,
                                                   int count )
{
    ( void ) count;
    *xRndNumber = xRandomNumberToReturn;
    return xRNGStatus;
}

static void vpxListFindListItemWithValue_NotFound( void )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );
}

static void vpxListFindListItemWithValue_Found( const List_t * pxList,
                                                TickType_t xWantedItemValue,
                                                const ListItem_t * pxReturn )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( &( pxList->xListEnd ), pxReturn );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( pxReturn, xWantedItemValue );
}

static BaseType_t xStubForEventGroupWaitBits( EventGroupHandle_t xEventGroup,
                                              const EventBits_t uxBitsToWaitFor,
                                              const BaseType_t xClearOnExit,
                                              const BaseType_t xWaitForAllBits,
                                              TickType_t xTicksToWait,
                                              int CallbackCount )
{
    xGlobalSocket.u.xTCP.eTCPState = eESTABLISHED;
}

static BaseType_t xLocalReceiveCallback( Socket_t xSocket,
                                         void * pvData,
                                         size_t xLength )
{
    xLocalReceiveCallback_Called++;
    return xLocalReceiveCallback_Return;
}

/*
 * @brief Binding successful.
 */
void test_vSocketBind_TCP( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xReturn = vSocketBind( &xSocket, NULL, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRNOTAVAIL, xReturn );
}

/*
 * @brief Binding successful.
 */
void test_vSocketBind_TCP1( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
}
