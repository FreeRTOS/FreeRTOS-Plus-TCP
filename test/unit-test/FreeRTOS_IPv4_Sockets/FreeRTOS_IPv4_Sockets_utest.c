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
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_portable.h"
#include "mock_FreeRTOS_Sockets.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

char cStubNtoaString[ 128 ];

static void prvSetString_FreeRTOS_inet_ntoa( char * pcBuffer )
{
    strcpy( cStubNtoaString, pcBuffer );
}

static const char * pucStub_FreeRTOS_inet_ntoa( uint32_t ulIPAddress,
                                                char * pcBuffer )
{
    strcpy( pcBuffer, cStubNtoaString );

    return pcBuffer;
}

void setUp()
{
    memset( cStubNtoaString, 0, sizeof( cStubNtoaString ) );
}

/*
 * @brief Test for FreeRTOS_inet_pton4 function.
 */
void test_FreeRTOS_inet_pton4( void )
{
    char * pucValidString1 = "192.68.1.1";
    uint32_t ulValidResponse1 = 0x010144C0;
    char * pucValidString2 = "192.0.1.1";
    uint32_t ulValidResponse2 = 0x010100C0;
    char * pucValidString3 = "192.68.1.0";
    uint32_t ulValidResponse3 = 0x000144C0;
    char * pucValidString4 = "0.0.0.0";
    uint32_t ulValidResponse4 = 0x00000000;
    char * pucValidString5 = "0.68.1.1";
    uint32_t ulValidResponse5 = 0x01014400;

    char * pucInvalidString1 = "0192.68.1.1";
    char * pucInvalidString2 = "192.68.00.1";
    char * pucInvalidString3 = "192.00.1.1";
    char * pucInvalidString4 = "freertos.com";
    char * pucInvalidString5 = "192.freertos.com";
    char * pucInvalidString6 = "\0";
    char * pucInvalidString7 = "1234.68.1.1";
    char * pucInvalidString8 = "123.68.0a.1";
    uint32_t ulInValidResponse = 0x00;

    BaseType_t xResult;
    uint32_t ulIPAddress;

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucValidString1, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulValidResponse1, ulIPAddress, "Could not convert string 1 correctly." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucValidString2, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulValidResponse2, ulIPAddress, "Could not convert string 2 correctly." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucValidString3, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulValidResponse3, ulIPAddress, "Could not convert string 3 correctly." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucValidString4, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulValidResponse4, ulIPAddress, "Could not convert string 4 correctly." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucValidString5, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulValidResponse5, ulIPAddress, "Could not convert string 5 correctly." );

    /* Invalid test cases. */
    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString1, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 1." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString2, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 2." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString3, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 3." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString4, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 4." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString5, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 5." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString6, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 6." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString7, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 7." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString8, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 8." );
}

/*
 * @brief Less size of the string being passed to the function.
 */
void test_FreeRTOS_inet_ntop4_LessBufferLength( void )
{
    char * pucReturn;
    uint32_t ulSource = 0x12345678U;
    const socklen_t uxSize = 15;
    char pcDestination[ uxSize ];

    pucReturn = FreeRTOS_inet_ntop4( &ulSource, pcDestination, uxSize );

    TEST_ASSERT_EQUAL( NULL, pucReturn );
}

/*
 * @brief Happy path.
 */
void test_FreeRTOS_inet_ntop4_HappyCase( void )
{
    char * pucReturn;
    uint32_t ulSource;
    const socklen_t uxSize = 16;
    char pcDestination[ uxSize ];

    ulSource = 0xFFFFFFFF;
    prvSetString_FreeRTOS_inet_ntoa( "255.255.255.255" );
    FreeRTOS_inet_ntoa_Stub( pucStub_FreeRTOS_inet_ntoa );
    pucReturn = FreeRTOS_inet_ntop4( &ulSource, pcDestination, uxSize );

    TEST_ASSERT_EQUAL_STRING( "255.255.255.255", pcDestination );

    ulSource = 0;
    prvSetString_FreeRTOS_inet_ntoa( "0.0.0.0" );
    FreeRTOS_inet_ntoa_Stub( pucStub_FreeRTOS_inet_ntoa );
    pucReturn = FreeRTOS_inet_ntop4( &ulSource, pcDestination, uxSize );

    TEST_ASSERT_EQUAL_STRING( "0.0.0.0", pcDestination );

    // ulSource = 0xABCDEF12;
    prvSetString_FreeRTOS_inet_ntoa( "18.239.205.171" );
    FreeRTOS_inet_ntoa_Stub( pucStub_FreeRTOS_inet_ntoa );
    pucReturn = FreeRTOS_inet_ntop4( &ulSource, pcDestination, uxSize );

    TEST_ASSERT_EQUAL_STRING( "18.239.205.171", pcDestination );
}
