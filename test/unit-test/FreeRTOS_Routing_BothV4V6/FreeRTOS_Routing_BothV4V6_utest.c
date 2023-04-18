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
    TEST_ASSERT_EQUAL( 0x017BA8C0, xEndPoint.ipv4_defaults.ulDNSServerAddresses[0] );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xEndPoint.bits.bIPv6 );
}

//TODO: NULL input to test_FreeRTOS_FillEndPoint

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
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultDNSServerAddress_IPv6, xEndPoint.ipv6_defaults.xDNSServerAddresses[0].ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xEndPoint.bits.bIPv6 );
}

//TODO: NULL input to FreeRTOS_FillEndPoint_IPv6

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
    NetworkInterface_t xNetworkInterface[3];
    NetworkInterface_t * pxNetworkInterface = NULL;
    int i = 0;

    for( i=0 ; i<3 ; i++ )
    {
        memset( &(xNetworkInterface[i]), 0, sizeof( NetworkInterface_t ) );

        ( void ) FreeRTOS_AddNetworkInterface( &(xNetworkInterface[i]) );
    }

    pxNetworkInterface = pxNetworkInterfaces;
    for( i=0 ; i<3 ; i++ )
    {
        TEST_ASSERT_EQUAL( &(xNetworkInterface[i]), pxNetworkInterface );
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

// void test_FreeRTOS_FirstNetworkInterface_happy_path( void )
// {
//     NetworkInterface_t xNetworkInterface;
//     NetworkInterface_t * pxNetworkInterface = NULL;

//     InitializeUnitTest();
//     memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
//     pxNetworkInterfaces = &xNetworkInterface;

//     pxNetworkInterface = FreeRTOS_FirstNetworkInterface();

//     TEST_ASSERT_EQUAL( &xNetworkInterface, pxNetworkInterface );
// }

// void test_FreeRTOS_FirstNetworkInterface_null( void )
// {
//     NetworkInterface_t * pxNetworkInterface = NULL;

//     InitializeUnitTest();

//     pxNetworkInterface = FreeRTOS_FirstNetworkInterface();

//     TEST_ASSERT_EQUAL( NULL, pxNetworkInterface );
// }

// void test_FreeRTOS_NextNetworkInterface_happy_path( void )
// {
//     NetworkInterface_t xNetworkInterface[3];
//     NetworkInterface_t * pxNetworkInterface = NULL;
//     int i=0;

//     InitializeUnitTest();

//     for( i=0 ; i<3 ; i++ )
//     {
//         memset( &(xNetworkInterface[i]), 0, sizeof( NetworkInterface_t ) );

//         if( pxNetworkInterfaces == NULL )
//         {
//             pxNetworkInterfaces = &(xNetworkInterface[i]);
//             pxNetworkInterface = pxNetworkInterfaces;
//         }
//         else
//         {
//             pxNetworkInterface->pxNext = &(xNetworkInterface[i]);
//             pxNetworkInterface = pxNetworkInterface->pxNext;
//         }
//     }

//     pxNetworkInterface = pxNetworkInterfaces;

//     for( i=0 ; i<3 ; i++ )
//     {
//         TEST_ASSERT_EQUAL( &(xNetworkInterface[i]), pxNetworkInterface );
//         pxNetworkInterface = FreeRTOS_NextNetworkInterface( pxNetworkInterface );
//     }

//     TEST_ASSERT_EQUAL( NULL, pxNetworkInterface );
// }

// void test_FreeRTOS_NextNetworkInterface_null( void )
// {
//     NetworkInterface_t * pxNetworkInterface = NULL;

//     InitializeUnitTest();

//     pxNetworkInterface = FreeRTOS_NextNetworkInterface( NULL );

//     TEST_ASSERT_EQUAL( NULL, pxNetworkInterface );
// }

// void test_FreeRTOS_FirstEndPoint_happy_path( void )
// {
//     NetworkInterface_t xNetworkInterface;
//     NetworkInterface_t * pxNetworkInterface = NULL;
//     NetworkEndPoint_t xEndPoint;
//     NetworkEndPoint_t * pxEndPoint = NULL;

//     InitializeUnitTest();
//     memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
//     pxNetworkInterfaces = &xNetworkInterface;
//     memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

//     xEndPoint.pxNetworkInterface = pxNetworkInterfaces;
//     pxNetworkEndPoints = &xEndPoint;

//     pxEndPoint = FreeRTOS_FirstEndPoint( pxNetworkInterfaces );

//     TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
// }

// void test_FreeRTOS_FirstEndPoint_null( void )
// {
//     NetworkInterface_t xNetworkInterface;
//     NetworkInterface_t * pxNetworkInterface = NULL;
//     NetworkEndPoint_t xEndPoint;
//     NetworkEndPoint_t * pxEndPoint = NULL;
//     int i=0;

//     InitializeUnitTest();
//     memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
//     pxNetworkInterfaces = &xNetworkInterface;
//     memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

//     xEndPoint.pxNetworkInterface = pxNetworkInterfaces;
//     pxNetworkEndPoints = &xEndPoint;

//     pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

//     TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
// }

// void test_FreeRTOS_FirstEndPoint_anotherNetIf( void )
// {
//     /* Attach one endpoint to one network interface. Check if we can get correct endpoint by API. */
//     NetworkInterface_t xNetworkInterface[3];
//     NetworkInterface_t * pxNetworkInterface = NULL;
//     NetworkEndPoint_t xEndPoint[3];
//     NetworkEndPoint_t * pxEndPoint = NULL;
//     int i=0;

//     InitializeUnitTest();

//     for( i=0 ; i<3 ; i++ )
//     {
//         memset( &(xNetworkInterface[i]), 0, sizeof( NetworkInterface_t ) );
//         memset( &(xEndPoint[i]), 0, sizeof( NetworkEndPoint_t ) );

//         if( pxNetworkInterfaces == NULL )
//         {
//             pxNetworkInterfaces = &(xNetworkInterface[i]);
//             pxNetworkInterface = pxNetworkInterfaces;

//             pxNetworkEndPoints = &(xEndPoint[i]);
//             pxEndPoint = pxNetworkEndPoints;
//         }
//         else
//         {
//             pxNetworkInterface->pxNext = &(xNetworkInterface[i]);
//             pxNetworkInterface = pxNetworkInterface->pxNext;

//             pxEndPoint->pxNext = &(xEndPoint[i]);
//             pxEndPoint = pxEndPoint->pxNext;
//         }

//         xEndPoint[i].pxNetworkInterface = pxNetworkInterface;
//     }

//     for( i=0 ; i<3 ; i++ )
//     {
//         pxEndPoint = FreeRTOS_FirstEndPoint( &(xNetworkInterface[i]) );
//         TEST_ASSERT_EQUAL( &(xEndPoint[i]), pxEndPoint );
//     }
// }

// void test_FreeRTOS_NextEndPoint_happy_path( void )
// {
//     NetworkEndPoint_t xEndPoint[3];
//     NetworkEndPoint_t * pxEndPoint = NULL;
//     int i=0;

//     InitializeUnitTest();

//     for( i=0 ; i<3 ; i++ )
//     {
//         memset( &(xEndPoint[i]), 0, sizeof( NetworkEndPoint_t ) );

//         if( pxNetworkEndPoints == NULL )
//         {
//             pxNetworkEndPoints = &(xEndPoint[i]);
//             pxEndPoint = pxNetworkEndPoints;
//         }
//         else
//         {
//             pxEndPoint->pxNext = &(xEndPoint[i]);
//             pxEndPoint = pxEndPoint->pxNext;
//         }
//     }

//     pxEndPoint = pxNetworkEndPoints;

//     for( i=0 ; i<3 ; i++ )
//     {
//         TEST_ASSERT_EQUAL( &(xEndPoint[i]), pxEndPoint );
//         pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint );
//     }

//     TEST_ASSERT_EQUAL( NULL, pxEndPoint );
// }

// void test_FreeRTOS_NextEndPoint_anotherNetIf( void )
// {
//     /* Attach 3 endpoints into each network interface:
//      * Network interface 0: endpoint 0/1/2
//      * Network interface 1: endpoint 3/4/5
//      * Network interface 2: endpoint 6/7/8
//      */
//     NetworkInterface_t xNetworkInterface[3];
//     NetworkInterface_t * pxNetworkInterface = NULL;
//     NetworkEndPoint_t xEndPoint[9];
//     NetworkEndPoint_t * pxEndPoint = NULL;
//     int i=0, j=0;

//     InitializeUnitTest();

//     for( i=0 ; i<3 ; i++ )
//     {
//         memset( &(xNetworkInterface[i]), 0, sizeof( NetworkInterface_t ) );

//         if( pxNetworkInterfaces == NULL )
//         {
//             pxNetworkInterfaces = &(xNetworkInterface[i]);
//             pxNetworkInterface = pxNetworkInterfaces;

//             pxNetworkEndPoints = &(xEndPoint[i]);
//             pxEndPoint = pxNetworkEndPoints;
//         }
//         else
//         {
//             pxNetworkInterface->pxNext = &(xNetworkInterface[i]);
//             pxNetworkInterface = pxNetworkInterface->pxNext;

//             pxEndPoint->pxNext = &(xEndPoint[i]);
//             pxEndPoint = pxEndPoint->pxNext;
//         }

//         xEndPoint[i].pxNetworkInterface = pxNetworkInterface;
//     }

//     for( j=0 ; j<9 ; j++ )
//     {
//         memset( &(xEndPoint[i]), 0, sizeof( NetworkEndPoint_t ) );
//     }

//     for( i=0 ; i<3 ; i++ )
//     {
//         pxEndPoint = FreeRTOS_FirstEndPoint( &(xNetworkInterface[i]) );
//         TEST_ASSERT_EQUAL( &(xEndPoint[i]), pxEndPoint );
//     }
// }


