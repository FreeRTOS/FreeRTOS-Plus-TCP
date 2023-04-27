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
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Timers.h"

/*#include "FreeRTOS_IP_stubs.c" */
#include "catch_assert.h"

#include "FreeRTOS_DHCPv6.h"
#include "FreeRTOS_DHCPv6_stubs.c"

/* ===========================  EXTERN VARIABLES  =========================== */

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
    InitializeUnitTest();
}

/*! called after each test case */
void tearDown( void )
{
}

/* ======================== Stub Callback Functions ========================= */

Socket_t xStubFreeRTOS_setsockopt_xSocket;
size_t xStubFreeRTOS_setsockopt_uxOptionLength;
int32_t xStubFreeRTOS_setsockopt_lOptionName_BitMap;

void prvSetCheckerAndReturn_FreeRTOS_setsockopt( Socket_t xSocket,
                                                 size_t uxOptionLength )
{
    xStubFreeRTOS_setsockopt_xSocket = xSocket;
    xStubFreeRTOS_setsockopt_uxOptionLength = uxOptionLength;
    xStubFreeRTOS_setsockopt_lOptionName_BitMap = 0;
}

BaseType_t xStubFreeRTOS_setsockopt( Socket_t xSocket,
                                     int32_t lLevel,
                                     int32_t lOptionName,
                                     const void * pvOptionValue,
                                     size_t uxOptionLength,
                                     int NumCalls )
{
    TEST_ASSERT_EQUAL( xStubFreeRTOS_setsockopt_xSocket, xSocket );
    TEST_ASSERT_EQUAL( xStubFreeRTOS_setsockopt_uxOptionLength, uxOptionLength );

    xStubFreeRTOS_setsockopt_lOptionName_BitMap |= ( 1 << lOptionName );

    return pdTRUE;
}

FreeRTOS_Socket_t * xStubvSocketBind_pxSocket;

void prvSetCheckerAndReturn_vSocketBind( FreeRTOS_Socket_t * pxSocket )
{
    xStubvSocketBind_pxSocket = pxSocket;
}

BaseType_t xStubvSocketBind( FreeRTOS_Socket_t * pxSocket,
                             struct freertos_sockaddr * pxBindAddress,
                             size_t uxAddressLength,
                             BaseType_t xInternal,
                             int NumCalls )
{
    TEST_ASSERT_EQUAL( xStubvSocketBind_pxSocket, pxSocket );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, pxBindAddress->sin_family );
    TEST_ASSERT_EQUAL( sizeof( struct freertos_sockaddr ), pxBindAddress->sin_len );
    TEST_ASSERT_EQUAL( ipDHCPv6_CLIENT_PORT, FreeRTOS_ntohs( pxBindAddress->sin_port ) );
    TEST_ASSERT_EQUAL( pdFALSE, xInternal );

    return 0;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief test_eGetDHCPv6State_happy_path
 * Check if eGetDHCPv6State can return DHCP state correctly.
 *
 * Test step:
 *  - Set endpoint's DHCP state.
 *  - Call eGetDHCPv6State to get state and check if it's correct.
 */
void test_eGetDHCPv6State_happy_path()
{
    NetworkEndPoint_t xEndPoint;
    eDHCPState_t eState = eInitialWait, eStateMax = eNotUsingLeasedAddress;
    eDHCPState_t eReturnState;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    for( eState = eInitialWait; eState <= eNotUsingLeasedAddress; eState++ )
    {
        xEndPoint.xDHCPData.eDHCPState = eState;
        eReturnState = eGetDHCPv6State( &xEndPoint );
        TEST_ASSERT_EQUAL( eState, eReturnState );
    }
}

/**
 * @brief test_eGetDHCPv6State_null
 * Check if eGetDHCPv6State trigger assertion when input is NULL.
 *
 * Test step:
 *  - Call eGetDHCPv6State with NULL.
 */
void test_eGetDHCPv6State_null()
{
    catch_assert( eGetDHCPv6State( NULL ) );
}

/**
 * @brief test_vDHCPv6Process_null
 * Check if vDHCPv6Process trigger assertion when input is NULL.
 *
 * Test step:
 *  - Call vDHCPv6Process with NULL endpoint.
 */
void test_vDHCPv6Process_null()
{
    catch_assert( vDHCPv6Process( pdTRUE, NULL ) );
    catch_assert( vDHCPv6Process( pdFALSE, NULL ) );
}

/**
 * @brief test_vDHCPv6Process_reset_from_init
 * Check if vDHCPv6Process can reset successfully from eInitialWait.
 *
 * Test step:
 *  - Set endpoint's DHCP state to eInitialWait.
 *  - Call vDHCPv6Process with reset flag and check the state after calling.
 */
void test_vDHCPv6Process_reset_from_init()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPv6Socket, 0, sizeof( Socket_t ) );

    xEndPoint.xDHCPData.eDHCPState = eInitialWait;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xDHCPv6Socket );
    xSocketValid_ExpectAndReturn( &xDHCPv6Socket, pdTRUE );
    prvSetCheckerAndReturn_FreeRTOS_setsockopt( &xDHCPv6Socket, sizeof( TickType_t ) );
    FreeRTOS_setsockopt_Stub( xStubFreeRTOS_setsockopt );
    prvSetCheckerAndReturn_vSocketBind( &xDHCPv6Socket );
    vSocketBind_Stub( xStubvSocketBind );
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdTRUE, &xEndPoint );

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingSendFirstDiscover. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint.xDHCPData.eDHCPState );
    /* We should set 2 socket options (FREERTOS_SO_RCVTIMEO and FREERTOS_SO_SNDTIMEO). */
    TEST_ASSERT_EQUAL( ( 1 << FREERTOS_SO_RCVTIMEO | 1 << FREERTOS_SO_SNDTIMEO ), xStubFreeRTOS_setsockopt_lOptionName_BitMap );
}

/**
 * @brief test_vDHCPv6Process_reset_from_lease
 * Check if vDHCPv6Process can reset successfully from eLeasedAddress.
 *
 * Test step:
 *  - Set endpoint's DHCP state to eLeasedAddress.
 *     - Set IPv6 address to 2001::1.
 *  - Call vDHCPv6Process with reset flag and check the state after calling.
 */
void test_vDHCPv6Process_reset_from_lease()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xDHCPv6Socket;
    const IP_Address_t xIPAddress = { 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPv6Socket, 0, sizeof( Socket_t ) );

    xEndPoint.xDHCPData.eDHCPState = eLeasedAddress;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xIPAddress.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xDHCPv6Socket );
    xSocketValid_ExpectAndReturn( &xDHCPv6Socket, pdTRUE );
    prvSetCheckerAndReturn_FreeRTOS_setsockopt( &xDHCPv6Socket, sizeof( TickType_t ) );
    FreeRTOS_setsockopt_Stub( xStubFreeRTOS_setsockopt );
    prvSetCheckerAndReturn_vSocketBind( &xDHCPv6Socket );
    vSocketBind_Stub( xStubvSocketBind );
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdTRUE, &xEndPoint );

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingSendFirstDiscover. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint.xDHCPData.eDHCPState );
    /* We should set 2 socket options (FREERTOS_SO_RCVTIMEO and FREERTOS_SO_SNDTIMEO). */
    TEST_ASSERT_EQUAL( ( 1 << FREERTOS_SO_RCVTIMEO | 1 << FREERTOS_SO_SNDTIMEO ), xStubFreeRTOS_setsockopt_lOptionName_BitMap );
}
