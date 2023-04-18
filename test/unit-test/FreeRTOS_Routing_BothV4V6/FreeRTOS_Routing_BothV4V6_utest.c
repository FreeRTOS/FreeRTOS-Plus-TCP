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
#include "Routing_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IPv6.h"

#include "FreeRTOS_Routing.h"
#include "FreeRTOS_Routing_BothV4V6_stubs.c"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* ===========================  EXTERN VARIABLES  =========================== */

const uint8_t ucDefaultIPAddress_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 192, 168, 123, 223 };
const uint8_t ucDefaultNetMask_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 255, 255, 255, 0 };
const uint8_t ucDefaultGatewayAddress_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 192, 168, 123, 254 };
const uint8_t ucDefaultDNSServerAddress_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 192, 168, 123, 1 };
const uint8_t ucDefaultMACAddress_IPv4[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };

/* Default IPv6 address is set to 2001::1 */
const IPv6_Address_t xDefaultIPAddress_IPv6 = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
/* Default IPv6 address is set to 2001:: */
const IPv6_Address_t xDefaultNetPrefix_IPv6 = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
const size_t xDefaultPrefixLength = 64U;
/* Default IPv6 address is set to 2001::fffe */
const IPv6_Address_t xDefaultGatewayAddress_IPv6 = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xfe };
/* Default IPv6 address is set to 2001::ffee */
const IPv6_Address_t xDefaultDNSServerAddress_IPv6 = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xee };
const uint8_t ucDefaultMACAddress_IPv6[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x22, 0x33, 0xab, 0xcd, 0xef };

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
 * @brief test_FreeRTOS_FillEndPoint_happy_path
 * The purpose of this test is to verify FreeRTOS_FillEndPoint when all input parameters
 * are valid IPv4 default setting.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint.
 *  - Check if pxNetworkEndPoints is same as input endpoint.
 *  - Check if all setting are correctly stored in endpoint.
 */
void test_FreeRTOS_FillEndPoint_happy_path( void )
{
    NetworkInterface_t xInterfaces;
    NetworkEndPoint_t xEndPoint;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    FreeRTOS_FillEndPoint( &xInterfaces,
                           &xEndPoint,
                           ucDefaultIPAddress_IPv4,
                           ucDefaultNetMask_IPv4,
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultDNSServerAddress_IPv4,
                           ucDefaultMACAddress_IPv4 );

    TEST_ASSERT_EQUAL( &xEndPoint, pxNetworkEndPoints );
    TEST_ASSERT_EQUAL( &xEndPoint, xInterfaces.pxEndPoint );
    /* 192.168.123.223 is same as 0xDF7BA8C0. */
    TEST_ASSERT_EQUAL( 0xDF7BA8C0, xEndPoint.ipv4_defaults.ulIPAddress );
    /* 255.255.255.0 is same as 0x00FFFFFF. */
    TEST_ASSERT_EQUAL( 0x00FFFFFF, xEndPoint.ipv4_defaults.ulNetMask );
    /* 192.168.123.254 is same as 0xFE7BA8C0. */
    TEST_ASSERT_EQUAL( 0xFE7BA8C0, xEndPoint.ipv4_defaults.ulGatewayAddress );
    /* 192.168.123.1 is same as 0x017BA8C0. */
    TEST_ASSERT_EQUAL( 0x017BA8C0, xEndPoint.ipv4_defaults.ulDNSServerAddresses[ 0 ] );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xEndPoint.bits.bIPv6 );
}

/**
 * @brief test_FreeRTOS_FillEndPoint_null_interface
 * The purpose of this test is to verify FreeRTOS_FillEndPoint when network interface is NULL.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint with NULL network interface.
 *  - Check if pxNetworkEndPoints is NULL.
 */
void test_FreeRTOS_FillEndPoint_null_interface( void )
{
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    FreeRTOS_FillEndPoint( NULL,
                           &xEndPoint,
                           ucDefaultIPAddress_IPv4,
                           ucDefaultNetMask_IPv4,
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultDNSServerAddress_IPv4,
                           ucDefaultMACAddress_IPv4 );

    TEST_ASSERT_EQUAL( NULL, pxNetworkEndPoints );
}

/**
 * @brief test_FreeRTOS_FillEndPoint_null_endpoint
 * The purpose of this test is to verify FreeRTOS_FillEndPoint when enpoint is NULL.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint with NULL endpoint.
 *  - Check if pxNetworkEndPoints is NULL.
 */
void test_FreeRTOS_FillEndPoint_null_endpoint( void )
{
    NetworkInterface_t xInterfaces;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );

    FreeRTOS_FillEndPoint( &xInterfaces,
                           NULL,
                           ucDefaultIPAddress_IPv4,
                           ucDefaultNetMask_IPv4,
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultDNSServerAddress_IPv4,
                           ucDefaultMACAddress_IPv4 );

    TEST_ASSERT_EQUAL( NULL, pxNetworkEndPoints );
}

/**
 * @brief test_FreeRTOS_FillEndPoint_IPv6_happy_path
 * The purpose of this test is to verify FreeRTOS_FillEndPoint_IPv6 when all input parameters
 * are valid IPv6 default setting.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint_IPv6 to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint.
 *  - Check if pxNetworkEndPoints is same as input endpoint.
 *  - Check if all setting are correctly stored in endpoint.
 */
void test_FreeRTOS_FillEndPoint_IPv6_happy_path( void )
{
    NetworkInterface_t xInterfaces;
    NetworkEndPoint_t xEndPoint;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                &xEndPoint,
                                &xDefaultIPAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );

    TEST_ASSERT_EQUAL( &xEndPoint, pxNetworkEndPoints );
    TEST_ASSERT_EQUAL( &xEndPoint, xInterfaces.pxEndPoint );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultIPAddress_IPv6, xEndPoint.ipv6_defaults.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultNetPrefix_IPv6, xEndPoint.ipv6_defaults.xPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( xDefaultPrefixLength, xEndPoint.ipv6_defaults.uxPrefixLength );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultGatewayAddress_IPv6, xEndPoint.ipv6_defaults.xGatewayAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultDNSServerAddress_IPv6, xEndPoint.ipv6_defaults.xDNSServerAddresses[ 0 ].ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xEndPoint.bits.bIPv6 );
}

/**
 * @brief test_FreeRTOS_FillEndPoint_IPv6_null_interface
 * The purpose of this test is to verify FreeRTOS_FillEndPoint when network interface is NULL.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint_IPv6 to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint with NULL network interface.
 *  - Check if pxNetworkEndPoints is NULL.
 */
void test_FreeRTOS_FillEndPoint_IPv6_null_interface( void )
{
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    FreeRTOS_FillEndPoint_IPv6( NULL,
                                &xEndPoint,
                                &xDefaultIPAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );

    TEST_ASSERT_EQUAL( NULL, pxNetworkEndPoints );
}

/**
 * @brief test_FreeRTOS_FillEndPoint_IPv6_null_endpoint
 * The purpose of this test is to verify FreeRTOS_FillEndPoint_IPv6 when enpoint is NULL.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint_IPv6 to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint with NULL endpoint.
 *  - Check if pxNetworkEndPoints is NULL.
 */
void test_FreeRTOS_FillEndPoint_IPv6_null_endpoint( void )
{
    NetworkInterface_t xInterfaces;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                NULL,
                                &xDefaultIPAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );

    TEST_ASSERT_EQUAL( NULL, pxNetworkEndPoints );
}

/*TODO: NULL input to FreeRTOS_FillEndPoint_IPv6 */

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
 * @brief test_FreeRTOS_AddNetworkInterface_three_in_a_row
 * The purpose of this test is to verify FreeRTOS_AddNetworkInterface three times with
 * different valid input parameters.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_AddNetworkInterface three times with three different network interfaces.
 *  - Check if all input network interfaces are stored into pxNetworkInterfaces.
 */
void test_FreeRTOS_AddNetworkInterface_three_in_a_row( void )
{
    NetworkInterface_t xNetworkInterface[ 3 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    int i = 0;

    for( i = 0; i < 3; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );

        ( void ) FreeRTOS_AddNetworkInterface( &( xNetworkInterface[ i ] ) );
    }

    pxNetworkInterface = pxNetworkInterfaces;

    for( i = 0; i < 3; i++ )
    {
        TEST_ASSERT_EQUAL( &( xNetworkInterface[ i ] ), pxNetworkInterface );
        pxNetworkInterface = pxNetworkInterface->pxNext;
    }

    TEST_ASSERT_EQUAL( NULL, pxNetworkInterface );
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
 * @brief test_FreeRTOS_AddNetworkInterface_duplicate_interface
 * FreeRTOS_AddNetworkInterface should only add same interface once into
 * the pxNetworkInterfaces.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_AddNetworkInterface with same input twice.
 *  - Check if pxNetworkInterfaces is same as input.
 *  - Check if pxNetworkInterfaces->pxNext is NULL.
 */
void test_FreeRTOS_AddNetworkInterface_duplicate_interface( void )
{
    NetworkInterface_t xNetworkInterface;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );

    ( void ) FreeRTOS_AddNetworkInterface( &xNetworkInterface );
    ( void ) FreeRTOS_AddNetworkInterface( &xNetworkInterface );

    TEST_ASSERT_EQUAL( &xNetworkInterface, pxNetworkInterfaces );
    TEST_ASSERT_EQUAL( NULL, pxNetworkInterfaces->pxNext );
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

/**
 * @brief test_FreeRTOS_NextNetworkInterface_happy_path
 * FreeRTOS_NextNetworkInterface returns next network interface correctly.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Create 3 network interfaces and attach them into pxNetworkInterfaces.
 *  - Check if pxNetworkInterfaces is same as first input.
 *  - Check if we can query next two network interfaces correctly by calling FreeRTOS_NextNetworkInterface.
 */
void test_FreeRTOS_NextNetworkInterface_happy_path( void )
{
    NetworkInterface_t xNetworkInterface[ 3 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    int i = 0;

    for( i = 0; i < 3; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );

        if( pxNetworkInterfaces == NULL )
        {
            pxNetworkInterfaces = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterfaces;
        }
        else
        {
            pxNetworkInterface->pxNext = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterface->pxNext;
        }
    }

    pxNetworkInterface = pxNetworkInterfaces;

    for( i = 0; i < 3; i++ )
    {
        TEST_ASSERT_EQUAL( &( xNetworkInterface[ i ] ), pxNetworkInterface );
        pxNetworkInterface = FreeRTOS_NextNetworkInterface( pxNetworkInterface );
    }

    TEST_ASSERT_EQUAL( NULL, pxNetworkInterface );
}

/**
 * @brief test_FreeRTOS_NextNetworkInterface_null
 * FreeRTOS_NextNetworkInterface returns NULL if the input is NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_NextNetworkInterface with NULL input.
 *  - Check if return is NULL.
 */
void test_FreeRTOS_NextNetworkInterface_null( void )
{
    NetworkInterface_t * pxNetworkInterface = NULL;

    pxNetworkInterface = FreeRTOS_NextNetworkInterface( NULL );

    TEST_ASSERT_EQUAL( NULL, pxNetworkInterface );
}

/**
 * @brief test_FreeRTOS_FirstEndPoint_happy_path
 * FreeRTOS_FirstEndPoint should return endpoint attached on the input network interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Set a network interface into pxNetworkInterfaces.
 *  - Attach an endpoint to the network interface.
 *  - Call FreeRTOS_FirstEndPoint to get attached endpoint.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_happy_path( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    xEndPoint.pxNetworkInterface = pxNetworkInterfaces;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FirstEndPoint( pxNetworkInterfaces );

    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FirstEndPoint_null
 * FreeRTOS_FirstEndPoint should return first endpoint in the list if input is NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Set a network interface into pxNetworkInterfaces.
 *  - Attach an endpoint to the network interface.
 *  - Call FreeRTOS_FirstEndPoint to get attached endpoint with NULL input.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_null( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    int i = 0;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    xEndPoint.pxNetworkInterface = pxNetworkInterfaces;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FirstEndPoint_another_interface
 * FreeRTOS_FirstEndPoint should return first endpoint with specified interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 3 network interfaces and 3 endpoints.
 *  - Attach one endpoint each network interface.
 *  - Put interfaces & endpoints into the list.
 *  - Loop to call FreeRTOS_FirstEndPoint to get attached endpoint with each network interface.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_another_interface( void )
{
    /* Attach one endpoint to one network interface. Check if we can get correct endpoint by API. */
    NetworkInterface_t xNetworkInterface[ 3 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint[ 3 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    int i = 0;

    for( i = 0; i < 3; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );
        memset( &( xEndPoint[ i ] ), 0, sizeof( NetworkEndPoint_t ) );

        if( pxNetworkInterfaces == NULL )
        {
            pxNetworkInterfaces = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterfaces;

            pxNetworkEndPoints = &( xEndPoint[ i ] );
            pxEndPoint = pxNetworkEndPoints;
        }
        else
        {
            pxNetworkInterface->pxNext = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterface->pxNext;

            pxEndPoint->pxNext = &( xEndPoint[ i ] );
            pxEndPoint = pxEndPoint->pxNext;
        }

        xEndPoint[ i ].pxNetworkInterface = pxNetworkInterface;
    }

    for( i = 0; i < 3; i++ )
    {
        pxEndPoint = FreeRTOS_FirstEndPoint( &( xNetworkInterface[ i ] ) );
        TEST_ASSERT_EQUAL( &( xEndPoint[ i ] ), pxEndPoint );
    }
}

/**
 * @brief test_FreeRTOS_NextEndPoint_happy_path
 * FreeRTOS_NextEndPoint should return next endpoint with specified endpoint.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 3 endpoints and stored then into pxNetworkEndPoints.
 *  - Loop to call FreeRTOS_NextEndPoint to get endpoints.
 *  - Check if endpoints are returned in correct order.
 */
void test_FreeRTOS_NextEndPoint_happy_path( void )
{
    NetworkEndPoint_t xEndPoint[ 3 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    int i = 0;


    for( i = 0; i < 3; i++ )
    {
        memset( &( xEndPoint[ i ] ), 0, sizeof( NetworkEndPoint_t ) );

        if( pxNetworkEndPoints == NULL )
        {
            pxNetworkEndPoints = &( xEndPoint[ i ] );
            pxEndPoint = pxNetworkEndPoints;
        }
        else
        {
            pxEndPoint->pxNext = &( xEndPoint[ i ] );
            pxEndPoint = pxEndPoint->pxNext;
        }
    }

    pxEndPoint = pxNetworkEndPoints;

    for( i = 0; i < 3; i++ )
    {
        TEST_ASSERT_EQUAL( &( xEndPoint[ i ] ), pxEndPoint );
        pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint );
    }

    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_NextEndPoint_another_interface
 * FreeRTOS_NextEndPoint should return next endpoint with specified interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 3 interfaces and 9 endpoints (e0~e8).
 *  - Put interfaces & endpoints into the list.
 *     - Attach 3 endpoints into each network interface
 *       - Network interface 0: endpoint e0/e1/e2
 *       - Network interface 1: endpoint e3/e4/e5
 *       - Network interface 2: endpoint e6/e7/e8
 *     - Stored endpoints in below order.
 *       - e0,e3,e6,e1,e4,e7,e2,e5,e8
 *  - Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 0.
 *  - Check if returned endpoints are e0 -> e1 -> e2.
 *  - Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 1.
 *  - Check if returned endpoints are e3 -> e4 -> e5.
 *  - Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 2.
 *  - Check if returned endpoints are e6 -> e7 -> e8.
 */
void test_FreeRTOS_NextEndPoint_another_interface( void )
{
    NetworkInterface_t xNetworkInterface[ 3 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint[ 9 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    int i = 0;
    const int specifiedEndpointOrder[ 9 ][ 2 ] = \
        /* {network_interface_index, endpoint_index} */
    {
        { 0, 0 },
        { 1, 3 },
        { 2, 6 },
        { 0, 1 },
        { 1, 4 },
        { 2, 7 },
        { 0, 2 },
        { 1, 5 },
        { 2, 8 }
    };

    /* Initialize network interface list. */
    for( i = 0; i < 3; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );

        if( pxNetworkInterfaces == NULL )
        {
            pxNetworkInterfaces = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterfaces;
        }
        else
        {
            pxNetworkInterface->pxNext = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterface->pxNext;
        }
    }

    /* Initialize endpoint list. */
    for( i = 0; i < 9; i++ )
    {
        memset( &( xEndPoint[ specifiedEndpointOrder[ i ][ 1 ] ] ), 0, sizeof( NetworkEndPoint_t ) );

        if( pxNetworkEndPoints == NULL )
        {
            pxNetworkEndPoints = &( xEndPoint[ specifiedEndpointOrder[ i ][ 1 ] ] );
            pxEndPoint = pxNetworkEndPoints;
        }
        else
        {
            pxEndPoint->pxNext = &( xEndPoint[ specifiedEndpointOrder[ i ][ 1 ] ] );
            pxEndPoint = pxEndPoint->pxNext;
        }

        pxEndPoint->pxNetworkInterface = &( xNetworkInterface[ specifiedEndpointOrder[ i ][ 0 ] ] );
    }

    /* Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 0. */
    /* Check if returned endpoints are e0 -> e1 -> e2. */
    pxEndPoint = NULL;
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 0 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 0 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 0 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 1 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 0 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 2 ] ), pxEndPoint );

    /* Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 1. */
    /* Check if returned endpoints are e3 -> e4 -> e5. */
    pxEndPoint = NULL;
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 1 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 3 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 1 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 4 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 1 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 5 ] ), pxEndPoint );

    /* Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 2. */
    /* Check if returned endpoints are e6 -> e7 -> e8. */
    pxEndPoint = NULL;
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 2 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 6 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 2 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 7 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 2 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 8 ] ), pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindEndPointOnIP_IPv4_happy_path
 * FreeRTOS_FindEndPointOnIP_IPv4 should return the endpoint with specified IPv4 address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query with same IP address stored in endpoint.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv4_happy_path( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    /* 0xDF7BA8C0 is 192.168.123.223. */
    xEndPoint.ipv4_settings.ulIPAddress = 0xDF7BA8C0;

    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( 0xDF7BA8C0, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindEndPointOnIP_IPv4_not_found
 * FreeRTOS_FindEndPointOnIP_IPv4 should return NULL if no matched endpoint found.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv4_not_found( void )
{
    NetworkEndPoint_t * pxEndPoint = NULL;

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( 0xDF7BA8C0, 0 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindEndPointOnIP_IPv6_happy_path
 * FreeRTOS_FindEndPointOnIP_IPv6 should return the endpoint with specified IPv6 address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv6 to query with same IP address stored in endpoint.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv6_happy_path( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    /* IP address -- 2001::1 */
    const IPv6_Address_t xIPAddress = { 0x21, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    /* 0xDF7BA8C0 is 192.168.123.223. */
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xIPAddress.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    pxNetworkEndPoints = &xEndPoint;

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint.ipv6_settings.xIPAddress ), &xIPAddress, xEndPoint.ipv6_settings.uxPrefixLength, 0 );

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( &xIPAddress );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindEndPointOnIP_IPv6_not_found
 * FreeRTOS_FindEndPointOnIP_IPv6 should return NULL if no matched endpoint found.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FindEndPointOnIP_IPv6 to query.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv6_not_found( void )
{
    NetworkEndPoint_t * pxEndPoint = NULL;
    /* IP address -- 2001::1 */
    const IPv6_Address_t xIPAddress = { 0x21, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( &xIPAddress );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}



/* TODO FreeRTOS_FindEndPointOnMAC */
/* TODO FreeRTOS_FindEndPointOnNetMask */
/* TODO FreeRTOS_InterfaceEndPointOnNetMask */
/* TODO FreeRTOS_FindEndPointOnNetMask_IPv6 */
/* TODO FreeRTOS_FirstEndPoint_IPv6 */
/* TODO FreeRTOS_MatchingEndpoint */
/* TODO FreeRTOS_FindGateWay */
/* TODO pxGetSocketEndpoint */
/* TODO vSetSocketEndpoint */
/* TODO pcEndpointName */
/* TODO xIPv6_GetIPType */
