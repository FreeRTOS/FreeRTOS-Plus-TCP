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
#include "mock_IP_Utils_DiffConfig_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "FreeRTOSIPConfig.h"

#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_TCP_IP.h"
#include "mock_FreeRTOS_ICMP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_UDP_IP.h"

#include "FreeRTOS_IP_Utils.h"

#include "catch_assert.h"

#if ( ipconfigUSE_NETWORK_EVENT_HOOK == 1 )
    extern BaseType_t xCallEventHook;
#endif

extern UBaseType_t uxLastMinBufferCount;
extern size_t uxMinLastSize;
extern UBaseType_t uxLastMinQueueSpace;

void test_pxPacketBuffer_to_NetworkBuffer( void )
{
    NetworkBufferDescriptor_t * pxReturn;

    pxReturn = pxPacketBuffer_to_NetworkBuffer( NULL );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

void test_prvProcessNetworkDownEvent_Pass( void )
{
    xCallEventHook = pdFALSE;

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_ClearARP_Expect();

    xNetworkInterfaceInitialise_ExpectAndReturn( pdPASS );

    vIPNetworkUpCalls_Expect();

    prvProcessNetworkDownEvent();
}

void test_FreeRTOS_round_up( void )
{
    uint32_t ulReturn;
    uint32_t a = 10;

    ulReturn = FreeRTOS_round_up( a, 0 );

    TEST_ASSERT_EQUAL( 10, ulReturn );
}

void test_FreeRTOS_round_down( void )
{
    uint32_t ulReturn;
    uint32_t a = 10;

    ulReturn = FreeRTOS_round_down( a, 0 );

    TEST_ASSERT_EQUAL( 0, ulReturn );
}

void test_vPrintResourceStats_MinSizeIsBigger( void )
{
    uxLastMinBufferCount = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
    uxMinLastSize = 10u;
    uxLastMinQueueSpace = 0;

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 1024U * 1025U );

    uxGetMinimumIPQueueSpace_ExpectAndReturn( 0 );

    vPrintResourceStats();

    TEST_ASSERT_EQUAL( 10, uxMinLastSize );
    TEST_ASSERT_EQUAL( 0, uxLastMinQueueSpace );
}

void test_vPrintResourceStats_LastQueueNECurrentQueue( void )
{
    uxLastMinBufferCount = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
    uxMinLastSize = 10u;
    uxLastMinQueueSpace = 0;

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 1024U * 1025U );

    uxGetMinimumIPQueueSpace_ExpectAndReturn( 10 );

    vPrintResourceStats();

    TEST_ASSERT_EQUAL( 10, uxMinLastSize );
    TEST_ASSERT_EQUAL( 10, uxLastMinQueueSpace );
}
