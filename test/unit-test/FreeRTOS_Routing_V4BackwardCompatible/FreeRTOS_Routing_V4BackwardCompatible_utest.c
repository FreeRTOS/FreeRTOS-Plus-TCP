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
#include "FreeRTOS_Routing_V4BackwardCompatible_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "FreeRTOS_Routing.h"
#include "FreeRTOS_Routing_V4BackwardCompatible_stubs.c"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* ===========================  EXTERN VARIABLES  =========================== */

/* ============================  Unity Fixtures  ============================ */

/*! called before each testcase */
void setUp( void )
{
    InitializeUnitTest();
}

/*! called after each testcase */
void tearDown( void )
{
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief test_FreeRTOS_AddNetworkInterface_happy_path
 * The purpose of this test is to verify FreeRTOS_AddNetworkInterface when input parameter
 * is not NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_AddNetworkInterface with one valid network interface.
 *  - Check if the input network interface is stored into pxNetworkInterfaces.
 */
void test_FreeRTOS_AddNetworkInterface_happy_path( void )
{
    NetworkInterface_t xNetworkInterface;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );

    ( void ) FreeRTOS_AddNetworkInterface( &xNetworkInterface );

    TEST_ASSERT_EQUAL( &xNetworkInterface, pxNetworkInterfaces );
    TEST_ASSERT_EQUAL( NULL, pxNetworkInterfaces->pxNext );
}

/**
 * @brief test_FreeRTOS_AddNetworkInterface_two_in_a_row
 * The purpose of this test is to verify FreeRTOS_AddNetworkInterface two times with
 * different valid input parameters.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_AddNetworkInterface two times with three different network interfaces.
 *  - Check if assertion triggered at the second time.
 */
void test_FreeRTOS_AddNetworkInterface_two_in_a_row( void )
{
    NetworkInterface_t xNetworkInterface[ 2 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    int i = 0;

    for( i = 0; i < 2; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );
    }

    ( void ) FreeRTOS_AddNetworkInterface( &( xNetworkInterface[ 0 ] ) );
    TEST_ASSERT_EQUAL( &( xNetworkInterface[ 0 ] ), pxNetworkInterfaces );

    /* In backward compatible, we only support 1 interface */
    catch_assert( FreeRTOS_AddNetworkInterface( &( xNetworkInterface[ 1 ] ) ) );
}

/**
 * @brief test_FreeRTOS_AddNetworkInterface_null
 * The purpose of this test is to verify FreeRTOS_AddNetworkInterface when input parameter
 * is NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_AddNetworkInterface with input NULL.
 *  - Check if pxNetworkInterfaces is still NULL.
 */
void test_FreeRTOS_AddNetworkInterface_null( void )
{
    ( void ) FreeRTOS_AddNetworkInterface( NULL );
    TEST_ASSERT_EQUAL( NULL, pxNetworkInterfaces );
}

/**
 * @brief test_FreeRTOS_FirstNetworkInterface_happy_path
 * FreeRTOS_FirstNetworkInterface should be able to find the first network interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Assign a network interface into pxNetworkInterfaces.
 *  - Call FreeRTOS_FirstNetworkInterface to get first network interface.
 *  - Check if the return is same as the input.
 */
void test_FreeRTOS_FirstNetworkInterface_happy_path( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    pxNetworkInterface = FreeRTOS_FirstNetworkInterface();

    TEST_ASSERT_EQUAL( &xNetworkInterface, pxNetworkInterface );
}

/**
 * @brief test_FreeRTOS_FirstNetworkInterface_null
 * FreeRTOS_FirstNetworkInterface should be able to return NULL if there is no network interface avilable.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_FirstNetworkInterface to get first network interface.
 *  - Check if the return is NULL.
 */
void test_FreeRTOS_FirstNetworkInterface_null( void )
{
    NetworkInterface_t * pxNetworkInterface = NULL;

    pxNetworkInterface = FreeRTOS_FirstNetworkInterface();

    TEST_ASSERT_EQUAL( NULL, pxNetworkInterface );
}


// FreeRTOS_FirstNetworkInterface
// FreeRTOS_NextNetworkInterface
// FreeRTOS_FirstEndPoint
// FreeRTOS_NextEndPoint
// FreeRTOS_FindEndPointOnIP_IPv4
// FreeRTOS_FindEndPointOnMAC
// FreeRTOS_FindEndPointOnNetMask
// FreeRTOS_InterfaceEndPointOnNetMask
// FreeRTOS_MatchingEndpoint
// FreeRTOS_FindGateWay
// FreeRTOS_FillEndPoint
// pxGetSocketEndpoint
// vSetSocketEndpoint
// pcEndpointName
// xIPv6_GetIPType
