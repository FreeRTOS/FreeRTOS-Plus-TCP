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
#include "mock_FreeRTOS_Sockets.h"

#include "FreeRTOS_Routing.h"
#include "FreeRTOS_Routing_BothV4V6_stubs.c"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* Default IPv4 address is 192.168.123.223, which is 0xDF7BA8C0. */
#define IPV4_DEFAULT_ADDRESS       ( 0xDF7BA8C0 )
/* Default IPv4 netmask is 255.255.255.0, which is 0x00FFFFFF. */
#define IPV4_DEFAULT_NETMASK       ( 0x00FFFFFF )
/* Default IPv4 netmask is 192.168.123.254, which is 0xFE7BA8C0. */
#define IPV4_DEFAULT_GATEWAY       ( 0xFE7BA8C0 )
/* Default IPv4 netmask is 192.168.123.1, which is 0x017BA8C0. */
#define IPV4_DEFAULT_DNS_SERVER    ( 0x017BA8C0 )

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

/* ============================  Stub Callback Functions  ============================ */

BaseType_t xStubFreeRTOS_inet_ntop_TargetFamily;
const void * pvStubFreeRTOS_inet_ntop_TargetSource;
char * pcStubFreeRTOS_inet_ntop_TargetDestination;
socklen_t uxStubFreeRTOS_inet_ntop_TargetSize;
char * pcStubFreeRTOS_inet_ntop_TargetCopySource;
socklen_t uxStubFreeRTOS_inet_ntop_CopySize;

static const char * pcStubFreeRTOS_inet_ntop( BaseType_t xAddressFamily,
                                              const void * pvSource,
                                              char * pcDestination,
                                              socklen_t uxSize )
{
    TEST_ASSERT_EQUAL( xStubFreeRTOS_inet_ntop_TargetFamily, xAddressFamily );
    TEST_ASSERT_EQUAL( pvStubFreeRTOS_inet_ntop_TargetSource, pvSource );
    TEST_ASSERT_EQUAL( pcStubFreeRTOS_inet_ntop_TargetDestination, pcDestination );
    TEST_ASSERT_EQUAL( uxStubFreeRTOS_inet_ntop_TargetSize, uxSize );

    if( ( pcDestination != NULL ) && ( pcStubFreeRTOS_inet_ntop_TargetCopySource != NULL ) )
    {
        memcpy( pcDestination, pcStubFreeRTOS_inet_ntop_TargetCopySource, uxStubFreeRTOS_inet_ntop_CopySize );
    }
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
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_ADDRESS, xEndPoint.ipv4_defaults.ulIPAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_NETMASK, xEndPoint.ipv4_defaults.ulNetMask );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_GATEWAY, xEndPoint.ipv4_defaults.ulGatewayAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_DNS_SERVER, xEndPoint.ipv4_defaults.ulDNSServerAddresses[ 0 ] );
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
 * @brief test_FreeRTOS_FirstEndPoint_IPv6_happy_path
 * FreeRTOS_FirstEndPoint_IPv6 should return an IPv6 endpoint attached on the input network interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Set a network interface into pxNetworkInterfaces.
 *  - Attach an endpoint to the network interface.
 *     - Set IPv6 bit in endpoint.
 *  - Call FreeRTOS_FirstEndPoint to get attached endpoint.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_IPv6_happy_path( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.pxNetworkInterface = pxNetworkInterfaces;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FirstEndPoint_IPv6( pxNetworkInterfaces );

    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FirstEndPoint_IPv6_null
 * FreeRTOS_FirstEndPoint_IPv6 should return first endpoint in the list if input is NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Set a network interface into pxNetworkInterfaces.
 *  - Attach an endpoint to the network interface.
 *     - Set IPv6 bit in endpoint.
 *  - Call FreeRTOS_FirstEndPoint_IPv6 to get attached endpoint with NULL input.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_IPv6_null( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.pxNetworkInterface = pxNetworkInterfaces;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FirstEndPoint_IPv6( NULL );

    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FirstEndPoint_IPv6_another_interface
 * FreeRTOS_FirstEndPoint_IPv6 should return first endpoint with specified interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 3 network interfaces and 6 endpoints (e0~e5).
 *  - Attach 2 endpoints each network interface.
 *     - One endpoint with IPv6 bit set.
 *     - The other endpoint with IPv6 bit clear.
 *     - The other endpoint with IPv6 bit clear.
 *       - Network interface 0: endpoint e0(IPv4)/e3(IPv6)
 *       - Network interface 1: endpoint e1(IPv4)/e4(IPv6)
 *       - Network interface 2: endpoint e2(IPv4)/e5(IPv6)
 *  - Put interfaces & endpoints into the list.
 *  - Loop to call FreeRTOS_FirstEndPoint_IPv6 to get attached IPv6 endpoint with each network interface.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_IPv6_another_interface( void )
{
    /* Attach one endpoint to one network interface. Check if we can get correct endpoint by API. */
    NetworkInterface_t xNetworkInterface[ 3 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint[ 6 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
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

    for( i = 0; i < 6; i++ )
    {
        bool bShouldBeIPv6 = i >= 3 ? true : false;
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

        if( bShouldBeIPv6 )
        {
            xEndPoint[ i ].pxNetworkInterface = &( xNetworkInterface[ i - 3 ] );
            xEndPoint[ i ].bits.bIPv6 = pdTRUE;
        }
        else
        {
            xEndPoint[ i ].pxNetworkInterface = &( xNetworkInterface[ i ] );
            xEndPoint[ i ].bits.bIPv6 = pdFALSE;
        }
    }

    for( i = 0; i < 3; i++ )
    {
        pxEndPoint = FreeRTOS_FirstEndPoint_IPv6( &( xNetworkInterface[ i ] ) );
        TEST_ASSERT_EQUAL( &( xEndPoint[ i + 3 ] ), pxEndPoint );
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
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;

    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( IPV4_DEFAULT_ADDRESS, 0 );
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

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( IPV4_DEFAULT_ADDRESS, 0 );
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

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    pxNetworkEndPoints = &xEndPoint;

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint.ipv6_settings.xIPAddress ), &xDefaultIPAddress_IPv6, xEndPoint.ipv6_settings.uxPrefixLength, 0 );

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( &xDefaultIPAddress_IPv6 );
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

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( &xDefaultIPAddress_IPv6 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindEndPointOnMAC_happy_path
 * FreeRTOS_FindEndPointOnMAC should return the endpoint with specified MAC address & network interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 network interface and add it to the list.
 *  - Create 1 endpoint, attach to the interface, and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnMAC to query with same MAC address stored in endpoint.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnMAC_happy_path( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    /* MAC address:  */
    const MACAddress_t xMACAddress = { 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc };
    NetworkInterface_t xNetworkInterface;

    /* Initialize network interface and add it to the list. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnMAC( &xMACAddress, &xNetworkInterface );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindEndPointOnMAC_null_interface
 * FreeRTOS_FindEndPointOnMAC should return the endpoint with specified MAC address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnMAC to query with same MAC address stored in endpoint.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnMAC_null_interface( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    /* MAC address:  */
    const MACAddress_t xMACAddress = { 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc };

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnMAC( &xMACAddress, NULL );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindEndPointOnMAC_null_mac
 * FreeRTOS_FindEndPointOnMAC should return the endpoint with NULL pointer as MAC address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnMAC to query with NULL pointer as MAC address.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnMAC_null_mac( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    /* MAC address:  */
    const MACAddress_t xMACAddress = { 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc };

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnMAC( NULL, NULL );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindEndPointOnMAC_multiple_interface
 * FreeRTOS_FindEndPointOnMAC should return the endpoint attached to the specified interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 2 interfaces and add them to the list.
 *  - Create 2 endpoints with same MAC address, attach to each interface, and add them to the list.
 *  - Call FreeRTOS_FindEndPointOnMAC to query attached in first interface.
 *  - Check if returned endpoint is same as first endpoint.
 *  - Call FreeRTOS_FindEndPointOnMAC to query attached in second interface.
 *  - Check if returned endpoint is same as second endpoint.
 */
void test_FreeRTOS_FindEndPointOnMAC_multiple_interface( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    NetworkInterface_t xNetworkInterface[ 2 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    /* MAC address:  */
    const MACAddress_t xMACAddress = { 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc };
    int i = 0;

    /* Initialize network interfaces and add them to the list. */
    for( i = 0; i < 2; i++ )
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

    /* Initialize network endpoints and add them to the list. */
    for( i = 0; i < 2; i++ )
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

        pxEndPoint->pxNetworkInterface = &xNetworkInterface[ i ];
        memcpy( pxEndPoint->xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    }

    /* Check if we can get correct endpoint by specified network interface. */
    for( i = 0; i < 2; i++ )
    {
        pxEndPoint = FreeRTOS_FindEndPointOnMAC( &xMACAddress, &xNetworkInterface[ i ] );
        TEST_ASSERT_EQUAL( &( xEndPoint[ i ] ), pxEndPoint );
    }
}

/**
 * @brief test_FreeRTOS_FindEndPointOnNetMask_happy_path
 * FreeRTOS_FindEndPointOnNetMask should be able to find the endpoint within same network region.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *     - Set the IP address to 192.168.123.223.
 *     - Set the netmask to 255.255.255.0.
 *  - Call FreeRTOS_FindEndPointOnNetMask to query for IP address 192.168.123.1.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnNetMask_happy_path( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    xEndPoint.ipv4_settings.ulNetMask = IPV4_DEFAULT_NETMASK;
    pxNetworkEndPoints = &xEndPoint;

    /* IPV4_DEFAULT_DNS_SERVER is 192.168.123.1 within the network region. */
    pxEndPoint = FreeRTOS_FindEndPointOnNetMask( IPV4_DEFAULT_DNS_SERVER, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindEndPointOnNetMask_not_found
 * FreeRTOS_FindEndPointOnNetMask should be able to return NULL if no endpoint is in same network region.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *     - Set the netmask to 255.255.255.0.
 *     - Set the IP address to 192.168.123.223.
 *  - Call FreeRTOS_FindEndPointOnNetMask to query for IP address 192.168.1.1.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnNetMask_not_found( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    xEndPoint.ipv4_settings.ulNetMask = IPV4_DEFAULT_NETMASK;
    pxNetworkEndPoints = &xEndPoint;

    /* 192.168.1.1 is . */
    pxEndPoint = FreeRTOS_FindEndPointOnNetMask( 0x0101A8C0, 0 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindEndPointOnNetMask_IPv6_happy_path
 * FreeRTOS_FindEndPointOnNetMask_IPv6 should be able to find the endpoint within same network region.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *     - Set the IP address to 2001::1.
 *     - Set the prefix address to 2001::.
 *     - Set the prefix length to 64.
 *  - Call FreeRTOS_FindEndPointOnNetMask to query for IP address 2001::fffe.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnNetMask_IPv6_happy_path( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = xDefaultPrefixLength;
    xEndPoint.bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints = &xEndPoint;

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint.ipv6_settings.xIPAddress ), &xDefaultGatewayAddress_IPv6, xDefaultPrefixLength, 0 );

    /* xDefaultGatewayAddress_IPv6 is 2001::fffe within the network region. */
    pxEndPoint = FreeRTOS_FindEndPointOnNetMask_IPv6( &xDefaultGatewayAddress_IPv6 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindEndPointOnNetMask_IPv6_not_found
 * FreeRTOS_FindEndPointOnNetMask_IPv6 should be able to return NULL if no endpoint is in same network region.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *     - Set the IP address to 2001::1.
 *     - Set the prefix address to 2001::.
 *     - Set the prefix length to 64.
 *  - Call FreeRTOS_FindEndPointOnNetMask to query for IP address 2002::fffe.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnNetMask_IPv6_not_found( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    const IPv6_Address_t xTargetAddress = { 0x20, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xfe };

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = xDefaultPrefixLength;
    xEndPoint.bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints = &xEndPoint;

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint.ipv6_settings.xIPAddress ), &xTargetAddress, xDefaultPrefixLength, 1 );

    pxEndPoint = FreeRTOS_FindEndPointOnNetMask_IPv6( &xTargetAddress );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindGateWay_IPv4_happy_path
 * FreeRTOS_FindGateWay should be able to find the endpoint with valid IPv4 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv4 endpoint and add it to the list.
 *     - Set the gateway address to 192.168.123.254 (ucDefaultGatewayAddress_IPv4).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv4.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindGateWay_IPv4_happy_path( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulGatewayAddress = ucDefaultGatewayAddress_IPv4;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv4 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindGateWay_IPv4_not_found
 * FreeRTOS_FindGateWay should be able to return NULL if no valid IPv4 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv6 endpoint and add it to the list.
 *     - Set the gateway address to 2001::fffe (xDefaultGatewayAddress_IPv6).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv4.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindGateWay_IPv4_not_found( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.ipv6_settings.xGatewayAddress.ucBytes, &xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv4 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindGateWay_IPv4_multiple_endpoints
 * FreeRTOS_FindGateWay should be able to return the endpoint with valid IPv4 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv6 endpoint and add it to the list.
 *     - Set the gateway address to 2001::fffe (xDefaultGatewayAddress_IPv6).
 *  - Create 1 IPv4 endpoint and add it to the list.
 *     - Set the gateway address to 192.168.123.254 (xDefaultGatewayAddress_IPv4).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv4.
 *  - Check if returned endpoint is same as second endpoint.
 */
void test_FreeRTOS_FindGateWay_IPv4_multiple_endpoints( void )
{
    NetworkEndPoint_t xEndPointV4;
    NetworkEndPoint_t xEndPointV6;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize IPv6 network endpoint and add it to the list. */
    memset( &xEndPointV6, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPointV6.ipv6_settings.xGatewayAddress.ucBytes, &xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPointV6.bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints = &xEndPointV6;

    /* Initialize IPv4 network endpoint and add it to the list. */
    memset( &xEndPointV4, 0, sizeof( NetworkEndPoint_t ) );
    xEndPointV4.ipv4_settings.ulGatewayAddress = ucDefaultGatewayAddress_IPv4;
    pxNetworkEndPoints->pxNext = &xEndPointV4;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv4 );
    TEST_ASSERT_EQUAL( &xEndPointV4, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindGateWay_IPv6_happy_path
 * FreeRTOS_FindGateWay should be able to find the endpoint with valid IPv6 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv6 endpoint and add it to the list.
 *     - Set the gateway address to 2001::fffe (xDefaultGatewayAddress_IPv6).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv6.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindGateWay_IPv6_happy_path( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.ipv6_settings.xGatewayAddress.ucBytes, &xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv6 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindGateWay_IPv6_not_found
 * FreeRTOS_FindGateWay should be able to return NULL if no valid IPv6 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv4 endpoint and add it to the list.
 *     - Set the gateway address to 192.168.123.254 (ucDefaultGatewayAddress_IPv4).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv6.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindGateWay_IPv6_not_found( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulGatewayAddress = ucDefaultGatewayAddress_IPv4;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv6 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief test_FreeRTOS_FindGateWay_IPv6_multiple_endpoints
 * FreeRTOS_FindGateWay should be able to return the endpoint with valid IPv6 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv4 endpoint and add it to the list.
 *     - Set the gateway address to 192.168.123.254 (xDefaultGatewayAddress_IPv4).
 *  - Create 1 IPv6 endpoint and add it to the list.
 *     - Set the gateway address to 2001::fffe (xDefaultGatewayAddress_IPv6).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv4.
 *  - Check if returned endpoint is same as second endpoint.
 */
void test_FreeRTOS_FindGateWay_IPv6_multiple_endpoints( void )
{
    NetworkEndPoint_t xEndPointV4;
    NetworkEndPoint_t xEndPointV6;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize IPv4 network endpoint and add it to the list. */
    memset( &xEndPointV4, 0, sizeof( NetworkEndPoint_t ) );
    xEndPointV4.ipv4_settings.ulGatewayAddress = ucDefaultGatewayAddress_IPv4;
    pxNetworkEndPoints = &xEndPointV4;

    /* Initialize IPv6 network endpoint and add it to the list. */
    memset( &xEndPointV6, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPointV6.ipv6_settings.xGatewayAddress.ucBytes, &xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPointV6.bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints->pxNext = &xEndPointV6;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv6 );
    TEST_ASSERT_EQUAL( &xEndPointV6, pxEndPoint );
}

/**
 * @brief test_pxGetSocketEndpoint_happy_path
 * pxGetSocketEndpoint should be able to return the endpoint attached in socket handler.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Create 1 socket handler.
 *     - Attach previous endpoint to socket handler.
 *  - Call pxGetSocketEndpoint with socket handler.
 *  - Check if returned endpoint is same.
 */
void test_pxGetSocketEndpoint_happy_path()
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    FreeRTOS_Socket_t xSocket;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize socket handler. */
    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    xSocket.pxEndPoint = &xEndPoint;

    pxEndPoint = pxGetSocketEndpoint( &xSocket );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief test_pxGetSocketEndpoint_null
 * pxGetSocketEndpoint should be able to return NULL if socket handler is also NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call pxGetSocketEndpoint with NULL.
 *  - Check if returned endpoint is NULL.
 */
void test_pxGetSocketEndpoint_null()
{
    NetworkEndPoint_t * pxEndPoint = NULL;

    pxEndPoint = pxGetSocketEndpoint( NULL );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief test_vSetSocketEndpoint_happy_path
 * vSetSocketEndpoint can set endpoint to socket handler successfully.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Create 1 socket handler.
 *  - Call pxGetSocketEndpoint to attach previous endpoint to this socket handler.
 *  - Check if the endpoint in socket handler is same.
 */
void test_vSetSocketEndpoint_happy_path()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize socket handler. */
    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    vSetSocketEndpoint( &xSocket, &xEndPoint );

    TEST_ASSERT_EQUAL( &xEndPoint, xSocket.pxEndPoint );
}

/**
 * @brief test_vSetSocketEndpoint_null_socket
 * vSetSocketEndpoint can return normally when socket handler is NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call pxGetSocketEndpoint with NULL socket handler.
 */
void test_vSetSocketEndpoint_null_socket()
{
    vSetSocketEndpoint( NULL, NULL );
}

/**
 * @brief test_pcEndpointName_IPv4_happy_path
 * pcEndpointName can get IPv4 address in string from endpoint.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint.
 *     - Set the IP address to 192.168.123.223 (IPV4_DEFAULT_ADDRESS).
 *  - Call pcEndpointName with enough buffer size.
 *  - Check if return buffer string is "192.168.123.223".
 */
void test_pcEndpointName_IPv4_happy_path()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;
    const char cIPString[] = "192.168.123.223";
    int lNameSize = sizeof( cIPString ) + 1;
    char cName[ lNameSize ];
    char * pcName = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;

    memset( &cName, 0, sizeof( cName ) );

    xStubFreeRTOS_inet_ntop_TargetFamily = FREERTOS_AF_INET4;
    pvStubFreeRTOS_inet_ntop_TargetSource = &( xEndPoint.ipv4_settings.ulIPAddress );
    pcStubFreeRTOS_inet_ntop_TargetDestination = cName;
    uxStubFreeRTOS_inet_ntop_TargetSize = lNameSize;
    pcStubFreeRTOS_inet_ntop_TargetCopySource = cIPString;
    uxStubFreeRTOS_inet_ntop_CopySize = lNameSize;
    FreeRTOS_inet_ntop_Stub( pcStubFreeRTOS_inet_ntop );

    pcName = pcEndpointName( &xEndPoint, cName, lNameSize );
    TEST_ASSERT_EQUAL_MEMORY( pcName, cIPString, lNameSize );
}

/**
 * @brief test_pcEndpointName_IPv4_null_buffer_pointer
 * pcEndpointName can return normally without accessing null pointer.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call pcEndpointName with null buffer pointer.
 */
void test_pcEndpointName_IPv4_null_buffer_pointer()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;
    const char cIPString[] = "192.168.123.223";
    int lNameSize = sizeof( cIPString ) + 1;
    char * pcName = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;

    xStubFreeRTOS_inet_ntop_TargetFamily = FREERTOS_AF_INET4;
    pvStubFreeRTOS_inet_ntop_TargetSource = &( xEndPoint.ipv4_settings.ulIPAddress );
    pcStubFreeRTOS_inet_ntop_TargetDestination = NULL;
    uxStubFreeRTOS_inet_ntop_TargetSize = lNameSize;
    pcStubFreeRTOS_inet_ntop_TargetCopySource = NULL;
    uxStubFreeRTOS_inet_ntop_CopySize = 0;
    FreeRTOS_inet_ntop_Stub( pcStubFreeRTOS_inet_ntop );

    pcName = pcEndpointName( &xEndPoint, NULL, lNameSize );
    TEST_ASSERT_EQUAL( NULL, pcName );
}

/**
 * @brief test_pcEndpointName_IPv4_truncate_buffer
 * pcEndpointName can get partial IPv4 address in string from endpoint when the buffer size is less than necessary size.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint.
 *     - Set the IP address to 192.168.123.223 (IPV4_DEFAULT_ADDRESS).
 *  - Call pcEndpointName with ( enough buffer size - 3 ).
 *  - Check if return buffer string is "192.168.123.".
 */
void test_pcEndpointName_IPv4_truncate_buffer()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;
    const char cIPString[] = "192.168.123.223";
    int lNameSize = sizeof( cIPString ) - 3;
    char cName[ lNameSize ];
    char * pcName = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;

    memset( &cName, 0, sizeof( cName ) );

    xStubFreeRTOS_inet_ntop_TargetFamily = FREERTOS_AF_INET4;
    pvStubFreeRTOS_inet_ntop_TargetSource = &( xEndPoint.ipv4_settings.ulIPAddress );
    pcStubFreeRTOS_inet_ntop_TargetDestination = cName;
    uxStubFreeRTOS_inet_ntop_TargetSize = lNameSize;
    pcStubFreeRTOS_inet_ntop_TargetCopySource = cIPString;
    uxStubFreeRTOS_inet_ntop_CopySize = lNameSize;
    FreeRTOS_inet_ntop_Stub( pcStubFreeRTOS_inet_ntop );

    pcName = pcEndpointName( &xEndPoint, cName, lNameSize );
    TEST_ASSERT_EQUAL_MEMORY( pcName, cIPString, lNameSize );
}

/**
 * @brief test_pcEndpointName_IPv6_happy_path
 * pcEndpointName can get IPv6 address in string from endpoint.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint.
 *     - Set the IP address to 2001::1 (xDefaultIPAddress_IPv6).
 *  - Call pcEndpointName with enough buffer size.
 *  - Check if return buffer string is "2001::1".
 */
void test_pcEndpointName_IPv6_happy_path()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;
    const char cIPString[] = "2001::1";
    int lNameSize = sizeof( cIPString ) + 1;
    char cName[ lNameSize ];
    char * pcName = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );

    memset( &cName, 0, sizeof( cName ) );

    xStubFreeRTOS_inet_ntop_TargetFamily = FREERTOS_AF_INET6;
    pvStubFreeRTOS_inet_ntop_TargetSource = xEndPoint.ipv6_settings.xIPAddress.ucBytes;
    pcStubFreeRTOS_inet_ntop_TargetDestination = cName;
    uxStubFreeRTOS_inet_ntop_TargetSize = lNameSize;
    pcStubFreeRTOS_inet_ntop_TargetCopySource = cIPString;
    uxStubFreeRTOS_inet_ntop_CopySize = lNameSize;
    FreeRTOS_inet_ntop_Stub( pcStubFreeRTOS_inet_ntop );

    pcName = pcEndpointName( &xEndPoint, cName, lNameSize );
    TEST_ASSERT_EQUAL_MEMORY( pcName, cIPString, lNameSize );
}

/**
 * @brief test_pcEndpointName_IPv6_truncate_buffer
 * pcEndpointName can get partial IPv6 address in string from endpoint when the buffer size is less than necessary size.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint.
 *     - Set the IP address to 2001::1 (xDefaultIPAddress_IPv6).
 *  - Call pcEndpointName with ( enough buffer size - 3 ).
 *  - Check if return buffer string is "2001".
 */
void test_pcEndpointName_IPv6_truncate_buffer()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;
    const char cIPString[] = "2001::1";
    int lNameSize = sizeof( cIPString ) - 3;
    char cName[ lNameSize ];
    char * pcName = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );

    memset( &cName, 0, sizeof( cName ) );

    xStubFreeRTOS_inet_ntop_TargetFamily = FREERTOS_AF_INET6;
    pvStubFreeRTOS_inet_ntop_TargetSource = xEndPoint.ipv6_settings.xIPAddress.ucBytes;
    pcStubFreeRTOS_inet_ntop_TargetDestination = cName;
    uxStubFreeRTOS_inet_ntop_TargetSize = lNameSize;
    pcStubFreeRTOS_inet_ntop_TargetCopySource = cIPString;
    uxStubFreeRTOS_inet_ntop_CopySize = lNameSize;
    FreeRTOS_inet_ntop_Stub( pcStubFreeRTOS_inet_ntop );

    pcName = pcEndpointName( &xEndPoint, cName, lNameSize );
    TEST_ASSERT_EQUAL_MEMORY( pcName, cIPString, lNameSize );
}

/* TODO xIPv6_GetIPType */
/* TODO FreeRTOS_MatchingEndpoint */
