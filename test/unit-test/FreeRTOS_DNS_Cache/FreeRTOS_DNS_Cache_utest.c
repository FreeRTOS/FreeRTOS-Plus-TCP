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

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_task.h"
#include "mock_list.h"
#include "mock_queue.h"

#include "mock_FreeRTOS_DNS_Callback.h"
#include "mock_FreeRTOS_DNS_Parser.h"
#include "mock_FreeRTOS_DNS_Networking.h"
#include "mock_NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"


#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#define LLMNR_ADDRESS     "freertos"
#define GOOD_ADDRESS      "www.freertos.org"
#define BAD_ADDRESS       "this is a bad address"
#define DOTTED_ADDRESS    "192.268.0.1"

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                uint32_t /* ulIPAddress */ );

/* ===========================   GLOBAL VARIABLES =========================== */
static int callback_called = 0;


/* ===========================  STATIC FUNCTIONS  =========================== */
static void dns_callback( const char * pcName,
                          void * pvSearchID,
                          uint32_t ulIPAddress )
{
    callback_called = 1;
}


/* ============================  TEST FIXTURES  ============================= */

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
    FreeRTOS_dnsclear();
    callback_called = 0;
}

/**
 * @brief calls at the end of each test case
 */
void tearDown( void )
{
}


/* =============================  TEST CASES  =============================== */

/**
 * @brief catch assertion on name being non-NULL.
 */
void test_processDNS_CACHE_CatchAssert( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;

    xTaskGetTickCount_ExpectAndReturn( 5000 ); /* 5 seconds */

    catch_assert( FreeRTOS_dnslookup( NULL ) );
}

/**
 * @brief Ensures that the same entry is inserted into the cache and retrieved
 */
void test_processDNS_CACHE_Success( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;

    xTaskGetTickCount_ExpectAndReturn( 3000 ); /* 3 seconds */

    FreeRTOS_dns_update( "hello",
                         &pulIP,
                         FreeRTOS_htonl( 3 ) ); /* lives 3 seconds */

    xTaskGetTickCount_ExpectAndReturn( 5000 );  /* 5 seconds */

    x = FreeRTOS_dnslookup( "hello" );

    TEST_ASSERT_EQUAL( pulIP, x );
}

/**
 * @brief Ensures empty cache returns zero
 */
void test_processDNS_CACHE_empty_cache( void )
{
    BaseType_t x;

    xTaskGetTickCount_ExpectAndReturn( 3000 );

    x = FreeRTOS_dnslookup( "hello" );

    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief Ensures entry not found returns zero
 */
void test_processDNS_CACHE_entry_not_found( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;

    xTaskGetTickCount_ExpectAndReturn( 3000 );

    FreeRTOS_dns_update( "world",
                         &pulIP,
                         400 );

    xTaskGetTickCount_ExpectAndReturn( 3000 );

    x = FreeRTOS_dnslookup( "hello" );

    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief Ensures entry not found returns zero
 */
void test_processDNS_CACHE_update_entry( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;

    xTaskGetTickCount_ExpectAndReturn( 3000 );

    FreeRTOS_dns_update( "world",
                         &pulIP,
                         400 );

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_dns_update( "world",
                         &pulIP,
                         500 );

    xTaskGetTickCount_ExpectAndReturn( 3000 );

    x = FreeRTOS_dnslookup( "hello" );

    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief Ensures that if an entry is expired it is zeroed
 */
void test_processDNS_CACHE_expired_entry( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;

    xTaskGetTickCount_ExpectAndReturn( 3000 ); /* 3 seconds */

    FreeRTOS_dns_update( "world",
                         &pulIP,
                         FreeRTOS_htonl( 20 ) ); /* lives 20 seconds */

    xTaskGetTickCount_ExpectAndReturn( 50000 );  /* 50 Seconds */
    x = FreeRTOS_dnslookup( "world" );

    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief Exceeding ip limit for an entry
 */
void test_processDNS_CACHE_exceed_IP_entry_limit( void )
{
    BaseType_t x;
    uint32_t pulIP = 789;
    uint32_t pulIP_arr[ ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY ] = { 123 };

    memset( pulIP_arr, 123, ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY );

    for( int i = 0; i < ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY; i++ )
    {
        xTaskGetTickCount_ExpectAndReturn( 3000 );

        FreeRTOS_dns_update( "world",
                             &pulIP_arr[ i ],
                             400 );
    }

    xTaskGetTickCount_ExpectAndReturn( 3000 );

    FreeRTOS_dns_update( "world",
                         &pulIP,
                         FreeRTOS_htonl( 400 ) ); /* lives 400 seconds */

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    x = FreeRTOS_dnslookup( "world" );

    TEST_ASSERT_EQUAL( 789, x );
}

/**
 * @brief Exceeding host limit for an entry, circles back to zero
 */
void test_processDNS_CACHE_exceed_host_entry_limit( void )
{
    BaseType_t x;
    uint32_t pulIP_arr[ ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1 ] = { 123 };
    uint32_t pulIP = 456;
    char hosts[ ipconfigDNS_CACHE_NAME_LENGTH ] = { "hello" };
    char template[] = "helloXXXXXX";

    for( int i = 0; i < ipconfigDNS_CACHE_ENTRIES; i++ )
    {
        memcpy( template, "helloXXXXXX", strlen( template ) );
        char * name = mktemp( template );
        memcpy( hosts, name, ipconfigDNS_CACHE_ENTRIES );
        xTaskGetTickCount_ExpectAndReturn( 3000 );

        FreeRTOS_dns_update( hosts,
                             &pulIP_arr[ i ],
                             FreeRTOS_htonl( 400 ) ); /* lives 400 seconds */
    }

    xTaskGetTickCount_ExpectAndReturn( 3000 );

    FreeRTOS_dns_update( "world",
                         &pulIP,
                         400 );

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    x = FreeRTOS_dnslookup( "world" );

    TEST_ASSERT_EQUAL( 456, x );
}

/**
 * @brief Exceeding dns name limit
 */
void test_processDNS_CACHE_exceed_dns_name_limit( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;
    char long_dns_name[ ipconfigDNS_CACHE_NAME_LENGTH + 3 ];

    memset( long_dns_name, 'a', ipconfigDNS_CACHE_NAME_LENGTH + 3 );
    long_dns_name[ ipconfigDNS_CACHE_NAME_LENGTH + 2 ] = '\0';

    xTaskGetTickCount_ExpectAndReturn( 3000 );

    FreeRTOS_dns_update( long_dns_name,
                         &pulIP,
                         400 );

    xTaskGetTickCount_ExpectAndReturn( 50000 );
    x = FreeRTOS_dnslookup( long_dns_name );

    TEST_ASSERT_EQUAL( 0, x );
}
