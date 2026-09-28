/*
 * FreeRTOS+TCP
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
#include "FreeRTOS.h"

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IPv6.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_IPv6_Utils.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_NetworkBufferManagement.h"

#include "catch_assert.h"
#include "FreeRTOS_ND_stubs.c"
#include "FreeRTOS_ND.h"

/* ===========================  EXTERN VARIABLES  =========================== */

extern const char * pcMessageType( BaseType_t xType );
extern const char * pcNDStateName( eNDState_t eState );
extern const char * pcNDActionName( eNaAction_t eState );

/*  The ND cache. */
extern NDCacheRow_t xNDCache[ ipconfigND_CACHE_ENTRIES ];

/* Setting IPv6 address as "fe80::7009" */
static const IPv6_Address_t xDefaultIPAddress =
{
    0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x09
};

/* IPv6 multi-cast address is ff02::. */
static const IPv6_Address_t xMultiCastIPAddress =
{
    0xff, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};

/* Setting eIPv6_SiteLocal IPv6 address as "feC0::7009" */
static const IPv6_Address_t xSiteLocalIPAddress =
{
    0xfe, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x09
};

/* Setting IPv6 Gateway address as "fe80::1" */
static const IPv6_Address_t xGatewayIPAddress =
{
    0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01
};

/* IPv6 default MAC address. */
static const MACAddress_t xDefaultMACAddress = { 0x22, 0x22, 0x22, 0x22, 0x22, 0x22 };

#define xHeaderSize                                   ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t ) )

/** @brief When ucAge becomes 3 or less, it is time for a new
 * neighbour solicitation.
 */
#define ndMAX_CACHE_AGE_BEFORE_NEW_ND_SOLICITATION    ( 3U )

/* =============================== Test Cases =============================== */

/**
 * @brief This function find the MAC-address of a multicast IPv6 address
 *        with a valid endpoint.
 */
void test_eNDGetCacheEntry_MulticastEndPoint( void )
{
    eResolutionLookupResult_t eResult;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    ( void ) memcpy( xIPAddress.ucBytes, xMultiCastIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdTRUE );
    vSetMultiCastIPv6MacAddress_ExpectAnyArgs();

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheHit, eResult );
}

/**
 * @brief This function find the MAC-address of a multicast IPv6 address
 *        with a multiple endpoints endpoint.
 */
void test_eNDGetCacheEntry_MulticastEndPoint_NoEP( void )
{
    eResolutionLookupResult_t eResult;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint, xEndPoint2, * pxEndPoint = &xEndPoint;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xEndPoint2.bits.bIPv6 = pdFALSE_UNSIGNED;
    ( void ) memcpy( xIPAddress.ucBytes, xMultiCastIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdTRUE );
    vSetMultiCastIPv6MacAddress_ExpectAnyArgs();

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheMiss, eResult );
}


/**
 * @brief This function find the MAC-address of a multicast IPv6 address
 *        with a valid endpoint.
 */
void test_eNDGetCacheEntry_Multicast_ValidEndPoint( void )
{
    NetworkEndPoint_t xEndPoint1, xEndPoint2, xEndPoint3, * pxEndPoint = &xEndPoint1;
    eResolutionLookupResult_t eResult;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xEndPoint1.bits.bIPv6 = 0;
    xEndPoint2.bits.bIPv6 = 1;
    xEndPoint3.bits.bIPv6 = 1;
    ( void ) memcpy( xIPAddress.ucBytes, xMultiCastIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdTRUE );
    vSetMultiCastIPv6MacAddress_ExpectAnyArgs();

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint1 );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( &xEndPoint2 );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Unknown );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( &xEndPoint3 );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheHit, eResult );
}

/**
 * @brief This function find the MAC-address of a multicast IPv6 address
 *        with a NULL endpoint.
 */
void test_eNDGetCacheEntry_Multicast_InvalidEndPoint( void )
{
    NetworkEndPoint_t ** ppxEndPoint = NULL;
    eResolutionLookupResult_t eResult;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;

    ( void ) memcpy( xIPAddress.ucBytes, xMultiCastIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdTRUE );
    vSetMultiCastIPv6MacAddress_ExpectAnyArgs();

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Multicast );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, ppxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheMiss, eResult );
}


/**
 * @brief This function find the MAC-address of a multicast IPv6 address
 *        with a NULL endpoint, but no active IPv6 endpoints.
 */
void test_eNDGetCacheEntry_Multicast_InvalidEndPoint_NoEP( void )
{
    NetworkEndPoint_t ** ppxEndPoint = NULL;
    eResolutionLookupResult_t eResult;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint, xEndPoint1;

    ( void ) memcpy( xIPAddress.ucBytes, xMultiCastIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdTRUE );
    vSetMultiCastIPv6MacAddress_ExpectAnyArgs();

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Multicast );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( &xEndPoint1 );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, ppxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheMiss, eResult );
}


/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address, but the entry is present on the ND Cache,
 *        with an invalid EndPoint.
 */
void test_eNDGetCacheEntry_NDCacheLookupHit_InvalidEndPoint( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t ** ppxEndPoint = NULL;
    eResolutionLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE;

    /* On a cache hit the lookup formats the MAC for a debug trace. */
    FreeRTOS_EUI48_ntop_Ignore();

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, ppxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xNDCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( MACAddress_t ) );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address, but the entry is present on the ND Cache,
 *        with an valid EndPoint. The endpoint gets updated based on the
 *        endpoint in ND Cache.
 */
void test_eNDGetCacheEntry_NDCacheLookupHit_ValidEndPoint( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t * pxEndPoint, xEndPoint1, xEndPoint2;
    eResolutionLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint2, 0, sizeof( NetworkEndPoint_t ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE;
    xNDCache[ xUseEntry ].pxEndPoint = &xEndPoint2;
    pxEndPoint = &xEndPoint1;

    /* On a cache hit the lookup formats the MAC for a debug trace. */
    FreeRTOS_EUI48_ntop_Ignore();

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xNDCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL_MEMORY( pxEndPoint, &xEndPoint2, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address, ND cache lookup fails with invalid Endpoint.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_InvalidEntry( void )
{
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eResolutionLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucState = eND_FREE; /*Invalid Cache entry needs to be skipped */
    pxEndPoint = &xEndPoint;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheMiss, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address, ND cache lookup fails with invalid entry.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_InvalidEntry2( void )
{
    NetworkEndPoint_t ** ppxEndPoint = NULL, xEndPoint;
    eResolutionLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucState = eND_FREE; /*Invalid Cache entry needs to be skipped */

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( &xEndPoint );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, ppxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheMiss, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address & ND cache lookup fails as Entry is valid
 *        but the MAC-address doesn't match.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_NoEntry( void )
{
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eResolutionLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE; /*Valid Cache entry needs to be skipped */
    pxEndPoint = &xEndPoint;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheMiss, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address & ND cache lookup fails to find a valid
 *        Endpoint as well as no Endpoint of type eIPv6_LinkLocal.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_NoLinkLocal( void )
{
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eResolutionLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE; /*Valid Cache entry needs to be skipped */
    pxEndPoint = &xEndPoint;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheMiss, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address & ND cache lookup fails to find a valid
 *        Endpoint but was able to find of type eIPv6_LinkLocal.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_LinkLocal( void )
{
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eResolutionLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    pxEndPoint = &xEndPoint;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheMiss, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address when
 *        there is a Cache miss but gateway has an entry in the cache.
 */
void test_eNDGetCacheEntry_NDCacheLookupHit_Gateway( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t * pxEndPoint, xEndPoint1, xEndPoint2;
    eResolutionLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    pxEndPoint = &xEndPoint2;
    ( void ) memcpy( xEndPoint1.ipv6_settings.xGatewayAddress.ucBytes, xGatewayIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xGatewayIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE; /*Valid Cache entry needs to be skipped */
    ( void ) memcpy( xIPAddress.ucBytes, xSiteLocalIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( &xEndPoint1 );

    /* On a cache hit the lookup formats the MAC for a debug trace. */
    FreeRTOS_EUI48_ntop_Ignore();

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xNDCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( MACAddress_t ) );
}

/**
 * @brief This function can't find the MAC-address of an IPv6 address when
 *        there is a Cache miss and gateway has no entry in the cache.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_Gateway( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t * pxEndPoint, xEndPoint1, xEndPoint2;
    eResolutionLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    pxEndPoint = &xEndPoint2;
    ( void ) memset( &xEndPoint1, 0, sizeof( NetworkEndPoint_t ) );
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xGatewayIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE; /*Valid Cache entry needs to be skipped */
    ( void ) memcpy( xIPAddress.ucBytes, xSiteLocalIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( &xEndPoint1 );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheMiss, eResult );
}

/**
 * @brief This function can't find the MAC-address of an IPv6 address when
 *        there is a Cache miss and gateway has no entry in the cache.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_NoEP( void )
{
    MACAddress_t xMACAddress;
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eResolutionLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE; /*Valid Cache entry needs to be skipped */
    pxEndPoint = &xEndPoint;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( NULL );

    /* TODO: This function should take a const pointer; remove const cast when it does. */
    eResult = eNDGetCacheEntry( ( IPv6_Address_t * ) &xSiteLocalIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eResolutionCacheMiss, eResult );
}

/**
 * @brief This function verified that the ip address was not found on ND cache
 *        and there was no free space to store the New Entry, hence the
 *        IP-address, MAC-address and an end-point combination was not stored.
 */
void test_vNDRefreshCacheEntry_NoMatchingEntryCacheFull( void )
{
    MACAddress_t xMACAddress = { 0 };
    IPv6_Address_t xIPAddress = { 0 };
    NetworkEndPoint_t xEndPoint;
    int i;

    ( void ) memset( xIPAddress.ucBytes, 0, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /* Filling the ND cache with non matching IP/MAC combination */
    for( i = 0; i < ipconfigND_CACHE_ENTRIES; i++ )
    {
        ( void ) memcpy( xNDCache[ i ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
        xNDCache[ i ].ucAge = 255;
        xNDCache[ i ].ucState = eND_REACHABLE;
    }

    /* Pass a NULL IP address which will not match.*/
    vNDRefreshCacheEntry( &xMACAddress, &xIPAddress, &xEndPoint );
}

/**
 * @brief This function verified that the ip address was not found on ND cache
 *        and there was space to store the New Entry, hence the IP-address,
 *        MAC-address and an end-point combination was stored in that location.
 */
void test_vNDRefreshCacheEntry_NoMatchingEntryAdd( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 0;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* The insert path timestamps the entry (ulLastMatchingNA) and formats the
     * MAC for a debug trace. */
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    /* Since no matching entry will be found, 0th entry will be updated to have the below details. */
    vNDRefreshCacheEntry( &xMACAddress, &xIPAddress, &xEndPoint );

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, ( uint8_t ) ipconfigMAX_ND_AGE );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_REACHABLE );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].pxEndPoint, &xEndPoint, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function verified that the ip address was found on ND cache
 *        and the entry was refreshed at the same location.
 */
void test_vNDRefreshCacheEntry_MatchingEntryRefresh( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE;

    /* The update path timestamps the entry (ulLastMatchingNA) and formats the
     * MAC for a debug trace. */
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    /* Since a matching entry is found at xUseEntry = 1st location, the entry will be refreshed.*/
    vNDRefreshCacheEntry( &xMACAddress, &xIPAddress, &xEndPoint );

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, ( uint8_t ) ipconfigMAX_ND_AGE );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].pxEndPoint, &xEndPoint, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function verifies all invalid cache entry condition.
 */
void test_vNDAgeCache_InvalidCache( void )
{
    int i;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /* Invalidate all cache entry. */
    for( i = 0; i < ipconfigND_CACHE_ENTRIES; i++ )
    {
        xNDCache[ i ].ucAge = 0;
    }

    vNDAgeCache();
}

/**
 * @brief This function wipes out the entries from ND cache
 *        when the age reaches 0.
 */
void test_vNDAgeCache_AgeZero( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1, i;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /* Invalidate all cache entry. */
    for( i = 0; i < ipconfigND_CACHE_ENTRIES; i++ )
    {
        xNDCache[ i ].ucAge = 0;
    }

    xNDCache[ xUseEntry ].ucAge = 1;
    /* A STALE entry whose age reaches 0 is freed and its IP wiped. */
    xNDCache[ xUseEntry ].ucState = eND_STALE;
    ( void ) memset( &xMACAddress, 0, sizeof( MACAddress_t ) );
    ( void ) memset( &xIPAddress, 0, ipSIZE_OF_IPv6_ADDRESS );

    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );

    vNDAgeCache();

    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, 0 );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_FREE );
}

/**
 * @brief A FREE cache entry is skipped entirely by vNDAgeCache - it is neither
 *        aged nor does it trigger any neighbour solicitation.
 */
void test_vNDAgeCache_InvalidEntry( void )
{
    BaseType_t xUseEntry = 1;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /* A FREE entry must be ignored by the ageing pass. */
    xNDCache[ xUseEntry ].ucAge = 10;
    xNDCache[ xUseEntry ].ucState = eND_FREE;

    /* No mock expectations: a FREE entry generates no buffer request. */
    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_FREE );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, 10 );
}

/**
 * @brief A REACHABLE entry whose age has fallen to the stale threshold moves to
 *        STALE on the next ageing pass. No solicitation is sent for this.
 */
void test_vNDAgeCache_ValidEntry( void )
{
    BaseType_t xUseEntry = 1;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /* REACHABLE at the stale threshold: next tick should demote it to STALE. */
    xNDCache[ xUseEntry ].ucAge = ndMAX_CACHE_AGE_BEFORE_NEW_ND_SOLICITATION;
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE;

    /* No mock expectations: the REACHABLE->STALE transition sends nothing. */
    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_STALE );
}

/**
 * @brief This function checks the case when The age has just ticked down,
 *        with nothing to do.
 */
void test_vNDAgeCache_ValidEntryDecrement( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint1, xEndPoint2;
    BaseType_t xUseEntry = 1, xAgeDefault = 10;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /*Update Entry one as Valid entry */
    xNDCache[ xUseEntry ].ucAge = xAgeDefault;
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE;

    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, xAgeDefault - 1 );
}

/**
 * @brief A PROBE entry reaching age 0 sends a unicast NS. When the entry has no
 *        end-point, vNDSendNeighbourSolicitation cannot build the packet, so the
 *        allocated buffer is simply left for the NS routine (endpoint guard fails).
 */

void test_vNDAgeCache_NSNullEP( void )
{
    BaseType_t xUseEntry = 1;
    NetworkBufferDescriptor_t xNetworkBuffer;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    /* PROBE with age 1: this tick expires and triggers a unicast NS probe. */
    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucState = eND_PROBE;
    xNDCache[ xUseEntry ].ucNumProbes = 0;
    xNDCache[ xUseEntry ].pxEndPoint = NULL;

    /* The probe allocates a buffer; the NS routine bails out on the NULL EP
     * and releases the descriptor it could not use. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    vNDAgeCache();

    /* A probe was attempted: counter incremented, short retry interval set. */
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucNumProbes, 1 );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, 1 );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_PROBE );
}

/**
 * @brief A PROBE probe with a buffer too small for the NS packet takes the
 *        duplicate-descriptor path; when duplication fails the original buffer
 *        is released and no frame is sent.
 */

void test_vNDAgeCache_NSIncorrectDataLen( void )
{
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1;
    NetworkBufferDescriptor_t xNetworkBuffer;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xNetworkBuffer.xDataLength = xHeaderSize - 1;
    /* PROBE with age 1: expires this tick and triggers a unicast NS probe. */
    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucState = eND_PROBE;
    xNDCache[ xUseEntry ].ucNumProbes = 0;
    xNDCache[ xUseEntry ].pxEndPoint = &xEndPoint;
    xEndPoint.bits.bIPv6 = 1;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    /* Buffer too small -> duplicate (fails) -> release the original. */
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucNumProbes, 1 );
}

/**
 * @brief This function handles Reducing the age counter in each entry within the ND cache.
 *        Just before getting to zero, 3 times a neighbour solicitation will be sent. It also takes
 *        care of Sending out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 *        add an entry into the ND table that indicates that an ND reply is
 *        outstanding so re-transmissions can be generated.
 */

void test_vNDAgeCache_NSHappyPath( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1, xAgeDefault = 10;
    NetworkBufferDescriptor_t xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket, * pxICMPPacket = &xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = &( pxICMPPacket->xICMPHeaderIPv6 );
    uint32_t ulPayloadLength = 32U;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    /* PROBE with age 1: expires this tick and sends a unicast NS. The buffer is
     * correctly sized, so the frame is built and handed to vReturnEthernetFrame. */
    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucState = eND_PROBE;
    xNDCache[ xUseEntry ].ucNumProbes = 0;
    xNDCache[ xUseEntry ].pxEndPoint = &xEndPoint;
    xEndPoint.bits.bIPv6 = 1;
    xNetworkBuffer.xDataLength = xHeaderSize;
    xNetworkBuffer.pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    vNDAgeCache();

    /* A probe was sent: counter incremented and short retry interval set. */
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucNumProbes, 1 );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, 1 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucVersionTrafficClass, 0x60 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.usPayloadLength, FreeRTOS_htons( ulPayloadLength ) );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucNextHeader, ipPROTOCOL_ICMP_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucHopLimit, 255 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfMessage, ipICMP_NEIGHBOR_SOLICITATION_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionType, ndICMP_SOURCE_LINK_LAYER_ADDRESS );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionLength, 1U ); /* times 8 bytes. */
}

/**
 * @brief An INCOMPLETE entry whose age reaches 0 is a failed resolution. When a
 *        packet is parked in pxNDWaitingNetworkBuffer whose destination matches
 *        the entry's IP, that buffer is released and the entry is freed.
 */
void test_vNDAgeCache_IncompleteTimeout_ReleasesMatchingParkedBuffer( void )
{
    BaseType_t xUseEntry = 1;
    NetworkBufferDescriptor_t xWaitingBuffer;
    ICMPPacket_IPv6_t xWaitingPacket;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xWaitingBuffer, 0, sizeof( xWaitingBuffer ) );
    ( void ) memset( &xWaitingPacket, 0, sizeof( xWaitingPacket ) );

    /* INCOMPLETE entry that expires on this tick. */
    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucState = eND_INCOMPLETE;
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    /* A packet is parked whose destination address matches the entry's IP. */
    ( void ) memcpy( xWaitingPacket.xIPHeader.xDestinationAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xWaitingBuffer.pucEthernetBuffer = ( uint8_t * ) &xWaitingPacket;
    pxNDWaitingNetworkBuffer = &xWaitingBuffer;

    /* Resolution timed out: the matching parked packet is dropped. */
    vReleaseNetworkBufferAndDescriptor_Expect( &xWaitingBuffer );

    vNDAgeCache();

    /* The parked buffer pointer is cleared and the entry is freed and wiped. */
    TEST_ASSERT_EQUAL( pxNDWaitingNetworkBuffer, NULL );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_FREE );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, xNDCache[ xUseEntry ].xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief An INCOMPLETE entry that times out while a NON-matching packet is parked
 *        must free the entry but leave the parked buffer untouched (it belongs to
 *        a different resolution).
 */
void test_vNDAgeCache_IncompleteTimeout_KeepsNonMatchingParkedBuffer( void )
{
    BaseType_t xUseEntry = 1;
    NetworkBufferDescriptor_t xWaitingBuffer;
    ICMPPacket_IPv6_t xWaitingPacket;
    IPv6_Address_t xOtherIP;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xWaitingBuffer, 0, sizeof( xWaitingBuffer ) );
    ( void ) memset( &xWaitingPacket, 0, sizeof( xWaitingPacket ) );

    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucState = eND_INCOMPLETE;
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    /* Parked packet is for a DIFFERENT destination address. */
    ( void ) memcpy( xOtherIP.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xOtherIP.ucBytes[ 15 ] ^= 0xFFU;
    ( void ) memcpy( xWaitingPacket.xIPHeader.xDestinationAddress.ucBytes, xOtherIP.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xWaitingBuffer.pucEthernetBuffer = ( uint8_t * ) &xWaitingPacket;
    pxNDWaitingNetworkBuffer = &xWaitingBuffer;

    /* No vReleaseNetworkBufferAndDescriptor expectation: the buffer is not ours. */
    vNDAgeCache();

    /* The non-matching parked buffer is preserved; the entry is still freed. */
    TEST_ASSERT_EQUAL( pxNDWaitingNetworkBuffer, &xWaitingBuffer );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_FREE );

    /* Cleanup so the parked pointer does not leak into other tests. */
    pxNDWaitingNetworkBuffer = NULL;
}

/**
 * @brief An INCOMPLETE entry that times out with no packet parked simply frees the
 *        entry (the pxNDWaitingNetworkBuffer == NULL branch).
 */
void test_vNDAgeCache_IncompleteTimeout_NoParkedBuffer( void )
{
    BaseType_t xUseEntry = 1;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    pxNDWaitingNetworkBuffer = NULL;

    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucState = eND_INCOMPLETE;
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_FREE );
}

/**
 * @brief A DELAY entry whose age reaches 0 received no upper-layer confirmation,
 *        so it transitions to PROBE, resets the probe counter, and arms a short
 *        1-second retry timer.
 */
void test_vNDAgeCache_DelayTimeout_MovesToProbe( void )
{
    BaseType_t xUseEntry = 1;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /* DELAY with age 1: expires this tick with no confirmation received. */
    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucState = eND_DELAY;
    xNDCache[ xUseEntry ].ucNumProbes = 7; /* Non-zero to prove it is reset. */

    /* No buffer request: the DELAY->PROBE move sends nothing this tick. */
    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_PROBE );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucNumProbes, 0 );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, 1 );

    /* This test intentionally leaves the entry in a non-FREE state (PROBE).
     * The suite has no setUp() that clears xNDCache between tests, and several
     * downstream tests (e.g. NeighborAdvertisement3) rely on a clean cache, so
     * wipe it here to restore the pre-test invariant. */
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}

/**
 * @brief A PROBE entry that reaches age 0 having already exhausted the maximum
 *        number of re-lookup attempts is declared gone: it is freed and its IP
 *        wiped, and no further solicitation is sent.
 */
void test_vNDAgeCache_ProbeExhausted_FreesEntry( void )
{
    BaseType_t xUseEntry = 1;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /* PROBE with age 1 and the probe budget already spent. The re-lookup
     * limit ipconfigMAX_ND_RE_LOOKUP_ATTEMPTS is defined privately in
     * FreeRTOS_ND.c as 3U and is not exported to the test, so use the literal. */
    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucState = eND_PROBE;
    xNDCache[ xUseEntry ].ucNumProbes = 3U;
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    /* No buffer request: max probes reached, the neighbour is freed. */
    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_FREE );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, xNDCache[ xUseEntry ].xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief vNDAgeCache on entries that are NOT expiring this tick: each state's
 *        age is decremented but stays above 0, so no state transition fires.
 *        This covers the "age still non-zero" (false) side of the per-state
 *        age==0 guards, plus an entry already at age 0 on entry (the
 *        skip-decrement side of the "age > 0" guard).
 */
void test_vNDAgeCache_EntriesNotExpiring_NoTransition( void )
{
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    pxNDWaitingNetworkBuffer = NULL;

    /* INCOMPLETE, age 3 -> 2: not zero, entry stays INCOMPLETE. */
    xNDCache[ 0 ].ucState = eND_INCOMPLETE;
    xNDCache[ 0 ].ucAge = 3;

    /* DELAY, age 3 -> 2: not zero, stays DELAY (no move to PROBE). */
    xNDCache[ 1 ].ucState = eND_DELAY;
    xNDCache[ 1 ].ucAge = 3;

    /* PROBE, age 3 -> 2: not zero, no probe sent this tick. */
    xNDCache[ 2 ].ucState = eND_PROBE;
    xNDCache[ 2 ].ucAge = 3;
    xNDCache[ 2 ].ucNumProbes = 0;

    /* STALE, age 3 -> 2: not zero, stays STALE. */
    xNDCache[ 3 ].ucState = eND_STALE;
    xNDCache[ 3 ].ucAge = 3;

    /* REACHABLE, age well above the stale threshold: decrements, stays REACHABLE. */
    xNDCache[ 4 ].ucState = eND_REACHABLE;
    xNDCache[ 4 ].ucAge = 200;

    /* An in-use entry already at age 0 on entry: exercises the skip-decrement
     * (age > 0 is false) path. STALE at age 0 will then be freed. */
    xNDCache[ 5 ].ucState = eND_STALE;
    xNDCache[ 5 ].ucAge = 0;

    vNDAgeCache();

    /* Non-expiring entries decremented but unchanged in state. */
    TEST_ASSERT_EQUAL( xNDCache[ 0 ].ucState, eND_INCOMPLETE );
    TEST_ASSERT_EQUAL( xNDCache[ 0 ].ucAge, 2 );
    TEST_ASSERT_EQUAL( xNDCache[ 1 ].ucState, eND_DELAY );
    TEST_ASSERT_EQUAL( xNDCache[ 1 ].ucAge, 2 );
    TEST_ASSERT_EQUAL( xNDCache[ 2 ].ucState, eND_PROBE );
    TEST_ASSERT_EQUAL( xNDCache[ 2 ].ucAge, 2 );
    TEST_ASSERT_EQUAL( xNDCache[ 3 ].ucState, eND_STALE );
    TEST_ASSERT_EQUAL( xNDCache[ 3 ].ucAge, 2 );
    TEST_ASSERT_EQUAL( xNDCache[ 4 ].ucState, eND_REACHABLE );

    /* Entry that was already at age 0: no decrement occurred (still 0), STALE freed. */
    TEST_ASSERT_EQUAL( xNDCache[ 5 ].ucAge, 0 );
    TEST_ASSERT_EQUAL( xNDCache[ 5 ].ucState, eND_FREE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}

/**
 * @brief Clear the Neighbour Discovery cache.
 */
void test_FreeRTOS_ClearND( void )
{
    NDCacheRow_t xTempNDCache[ ipconfigND_CACHE_ENTRIES ];

    /* Set xNDCache to non zero entries*/
    ( void ) memset( xNDCache, 1, sizeof( xNDCache ) );
    ( void ) memset( xTempNDCache, 0, sizeof( xTempNDCache ) );
    FreeRTOS_ClearND( NULL );

    TEST_ASSERT_EQUAL_MEMORY( xNDCache, xTempNDCache, sizeof( xNDCache ) );
}

/**
 * @brief Clear the Neighbour Discovery cache with specific endpoint.
 */
void test_FreeRTOS_ClearND_WithEndPoint( void )
{
    NDCacheRow_t xTempNDCache[ ipconfigND_CACHE_ENTRIES ];
    struct xNetworkEndPoint xEndPoint = { 0 };

    /* Set xNDCache to non zero entries*/
    ( void ) memset( xNDCache, 1, sizeof( xNDCache ) );
    ( void ) memset( xTempNDCache, 0, sizeof( xTempNDCache ) );
    xNDCache[ 1 ].pxEndPoint = &xEndPoint;
    FreeRTOS_ClearND( &xEndPoint );

    TEST_ASSERT_EQUAL_MEMORY( &xNDCache[ 1 ], xTempNDCache, sizeof( NDCacheRow_t ) );
}

/**
 * @brief Clear the Neighbour Discovery cache with endpoint.
 *        But the endpoint doesn't match any in cache.
 */
void test_FreeRTOS_ClearND_EndPointNotFound( void )
{
    NDCacheRow_t xTempNDCache[ ipconfigND_CACHE_ENTRIES ];
    struct xNetworkEndPoint xEndPoint = { 0 };

    /* Set xNDCache to non zero entries*/
    ( void ) memset( xNDCache, 1, sizeof( xNDCache ) );
    ( void ) memset( xTempNDCache, 1, sizeof( xTempNDCache ) );
    FreeRTOS_ClearND( &xEndPoint );

    TEST_ASSERT_EQUAL_MEMORY( xTempNDCache, xNDCache, sizeof( xNDCache ) );
}

/**
 * @brief Toggle happy path.
 */
void test_FreeRTOS_PrintNDCache( void )
{
    BaseType_t xUseEntry = 0;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    /* First Entry added as a valid Cache Entry to be printed */
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE;

    /* Printing a valid entry formats its MAC for the dump line. */
    FreeRTOS_EUI48_ntop_Ignore();

    FreeRTOS_PrintNDCache();
}

/**
 * @brief This function handles the case when vNDSendNeighbourSolicitation
 *        fails as endpoint is NULL.
 */
void test_vNDSendNeighbourSolicitation_NULL_EP( void )
{
    IPv6_Address_t xIPAddress;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xNetworkBuffer.pxEndPoint = NULL;

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    vNDSendNeighbourSolicitation( &xNetworkBuffer, &xIPAddress );
}

/**
 * @brief This function handles the case when vNDSendNeighbourSolicitation
 *        fails as bIPv6 is not set.
 */
void test_vNDSendNeighbourSolicitation_bIPv6_NotSet( void )
{
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xEndPoint.bits.bIPv6 = pdFALSE;
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    vNDSendNeighbourSolicitation( &xNetworkBuffer, &xIPAddress );
}

/**
 * @brief This function Send out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 *        add an entry into the ND table that indicates that an ND reply is
 *        outstanding so re-transmissions can be generated.
 */
void test_vNDSendNeighbourSolicitation_HappyPath( void )
{
    IPv6_Address_t xIPAddress;
    NetworkBufferDescriptor_t xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket, * pxICMPPacket = &xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = &( pxICMPPacket->xICMPHeaderIPv6 );
    NetworkEndPoint_t xEndPoint;
    uint32_t ulPayloadLength = 32U;

    xEndPoint.bits.bIPv6 = 1;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.xDataLength = xHeaderSize;
    xNetworkBuffer.pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    vNDSendNeighbourSolicitation( &xNetworkBuffer, &xIPAddress );

    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucVersionTrafficClass, 0x60 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.usPayloadLength, FreeRTOS_htons( ulPayloadLength ) );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucNextHeader, ipPROTOCOL_ICMP_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucHopLimit, 255 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfMessage, ipICMP_NEIGHBOR_SOLICITATION_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionType, ndICMP_SOURCE_LINK_LAYER_ADDRESS );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionLength, 1U ); /* times 8 bytes. */
}

/**
 * @brief This function handles NULL Endpoint case
 *        while sending a PING request which means
 *        No endpoint found for the target IP-address.
 */
void test_SendPingRequestIPv6_NULL_EP( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 0;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Unknown );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );


    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles case when find endpoint for
 *        pxIPAddress fails and while getting the endpoint for the
 *        same IP type bIPv6 is not set.
 */
void test_SendPingRequestIPv6_bIPv6_NotSet( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = ipconfigNETWORK_MTU;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 0;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles case when find endpoint for
 *        pxIPAddress fails and found the endpoint for the
 *        same IP type but there are no bytes to be send.
 *        uxNumberOfBytesToSend is set to 0.
 */
void test_SendPingRequestIPv6_bIPv6_NoBytesToSend( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 0;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles case when uxNumberOfBytesToSend
 *        is set to proper but there is not enough space.
 */
void test_SendPingRequestIPv6_bIPv6_NotEnoughSpace( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = ipconfigNETWORK_MTU;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles case when we do not
 *        have enough space for the Number of bytes to be send.
 */
void test_SendPingRequestIPv6_IncorrectBytesSend( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = ipconfigNETWORK_MTU;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );

    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 0U );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles failure case when network
 *        buffer returned is NULL.
 */
void test_SendPingRequestIPv6_NULL_Buffer( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 100;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );


    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );


    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles sending and IPv6 ping request
 *        assert as pxEndPoint->bits.bIPv6 is not set.
 */
void test_SendPingRequestIPv6_Assert( void )
{
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer = { 0 };
    uint8_t ucEthernetBuffer[ 1500 ] = { 0 };
    IPv6_Address_t xIPAddress = { 0 };
    size_t uxNumberOfBytesToSend = 100;
    BaseType_t xReturn;
    uint16_t usSequenceNumber = 1;

    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( ucEthernetBuffer );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );


    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    xSendEventStructToIPTask_IgnoreAndReturn( pdPASS );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    /*Returns ping sequence number */
    TEST_ASSERT_EQUAL( xReturn, usSequenceNumber );
}

/**
 * @brief This function handles sending and IPv6 ping request
 *        and returning the sequence number in case of success.
 */
void test_SendPingRequestIPv6_SendToIP_Pass( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer = { 0 }, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ 1500 ] = { 0 };
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 100;
    BaseType_t xReturn;
    uint16_t usSequenceNumber = 1;

    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( ucEthernetBuffer );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );


    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );
    xSendEventStructToIPTask_IgnoreAndReturn( pdPASS );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    /*Returns ping sequence number */
    TEST_ASSERT_EQUAL( xReturn, usSequenceNumber );
}

/**
 * @brief This function handles failure case while sending
 *        IPv6 ping request when sending an event to IP task fails.
 */
void test_SendPingRequestIPv6_SendToIP_Fail( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ 1500 ] = { 0 };
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 100;
    BaseType_t xReturn;
    uint16_t usSequenceNumber = 1;

    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( ucEthernetBuffer );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );


    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );
    xSendEventStructToIPTask_IgnoreAndReturn( pdFAIL );
    vReleaseNetworkBufferAndDescriptor_Ignore();

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}


/**
 * @brief This function process ICMP message when endpoint is valid
 *        but the bIPv6 bit is false indicating IPv4 message.
 */
void test_prvProcessICMPMessage_IPv6_EP( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    eFrameProcessingResult_t eReturn;
    NetworkEndPoint_t xEndPoint;

    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message has size
 *        less than ICMPv6 header size
 */
void test_prvProcessICMPMessage_IPv6_PacketSizeBelowHeaderSize( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_DEST_UNREACHABLE_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 2U;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_DEST_UNREACHABLE_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_DEST_UNREACHABLE_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_DEST_UNREACHABLE_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PACKET_TOO_BIG_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PACKET_TOO_BIG_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PACKET_TOO_BIG_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_TIME_EXCEEDED_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_TIME_EXCEEDED_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_TIME_EXCEEDED_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PARAMETER_PROBLEM_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PARAMETER_PROBLEM_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PARAMETER_PROBLEM_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_ROUTER_SOLICITATION_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_ROUTER_SOLICITATION_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_ROUTER_ADVERTISEMENT_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_ROUTER_ADVERTISEMENT_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_ADVERTISEMENT_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REQUEST_IPv6 but the data size is incorrect.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REQUEST_IPv6_IncorrectSize( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    size_t uxICMPSize, uxNeededSize;
    uint16_t usICMPSize;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xICMPPacket.xIPHeader.usPayloadLength = 100;
    usICMPSize = FreeRTOS_ntohs( xICMPPacket.xIPHeader.usPayloadLength );
    uxICMPSize = ( size_t ) usICMPSize;
    uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
    /* Assign less size than expected */
    pxNetworkBuffer->xDataLength = uxICMPSize;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REQUEST_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REQUEST_IPv6_CorrectSizeAssert1( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    size_t uxICMPSize, uxNeededSize;
    uint16_t usICMPSize;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xICMPPacket.xIPHeader.usPayloadLength = 100;
    usICMPSize = FreeRTOS_ntohs( xICMPPacket.xIPHeader.usPayloadLength );
    uxICMPSize = ( size_t ) usICMPSize;
    uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
    /* Assign less size than expected */
    pxNetworkBuffer->xDataLength = uxNeededSize + 1;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REQUEST_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REQUEST_IPv6_CorrectSize( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    size_t uxICMPSize, uxNeededSize;
    uint16_t usICMPSize;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xICMPPacket.xIPHeader.usPayloadLength = 100;
    usICMPSize = FreeRTOS_ntohs( xICMPPacket.xIPHeader.usPayloadLength );
    uxICMPSize = ( size_t ) usICMPSize;
    uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
    /* Assign less size than expected */
    pxNetworkBuffer->xDataLength = uxNeededSize + 1;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REPLY_IPv6.
 *        It handles case where A reply was received to an outgoing
 *        ping but the payload of the reply was not correct.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REPLY_IPv6_eInvalidData( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    ICMPEcho_IPv6_t * pxICMPEchoHeader = ( ( ICMPEcho_IPv6_t * ) pxICMPHeader_IPv6 );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    size_t uxICMPSize, uxNeededSize;
    uint16_t usICMPSize;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    xICMPPacket.xIPHeader.usPayloadLength = 100;
    usICMPSize = FreeRTOS_ntohs( xICMPPacket.xIPHeader.usPayloadLength );
    uxICMPSize = ( size_t ) usICMPSize;
    uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
    /* Assign less size than expected */
    pxNetworkBuffer->xDataLength = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    vApplicationPingReplyHook_Expect( eInvalidData, pxICMPEchoHeader->usIdentifier );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REPLY_IPv6.
 *        It handles case where A reply was received to an outgoing
 *        ping but the payload of the reply was not correct.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REPLY_IPv6_IncorrectSize( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t * pxICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6;
    ICMPEcho_IPv6_t * pxICMPEchoHeader;
    uint8_t ucBuffer[ sizeof( ICMPPacket_IPv6_t ) + ipBUFFER_PADDING ], * pucByte;
    NetworkEndPoint_t xEndPoint;
    size_t uxDataLength;
    eFrameProcessingResult_t eReturn;

    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &ucBuffer;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 5;
    pxICMPPacket = ( ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxICMPPacket->xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_ntohs( ipBUFFER_PADDING );
    pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( pxICMPPacket->xICMPHeaderIPv6 ) );
    pxICMPEchoHeader = ( ( ICMPEcho_IPv6_t * ) pxICMPHeader_IPv6 );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    uxDataLength = ipNUMERIC_CAST( size_t, FreeRTOS_ntohs( pxICMPPacket->xIPHeader.usPayloadLength ) );
    uxDataLength = uxDataLength - sizeof( ICMPEcho_IPv6_t );

    pucByte = ( ucBuffer + sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) + sizeof( ICMPEcho_IPv6_t ) );

    ( void ) memset( pucByte, ipECHO_DATA_FILL_BYTE, uxDataLength );

    /* vApplicationPingReplyHook_Expect( eSuccess, pxICMPEchoHeader->usIdentifier ); */

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}


/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REPLY_IPv6.
 *        It handles case where usPayloadLength is smaller than the
 *        ICMPEcho_IPv6_t header, causing an early break without
 *        calling vApplicationPingReplyHook.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REPLY_IPv6_PayloadTooSmallForEchoHeader( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t * pxICMPPacket;
    uint8_t ucBuffer[ sizeof( ICMPPacket_IPv6_t ) + ipBUFFER_PADDING ];
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    memset( ucBuffer, 0, sizeof( ucBuffer ) );

    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &ucBuffer;
    /* Buffer is large enough to pass the first size check. */
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 4;
    pxICMPPacket = ( ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxICMPPacket->xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;

    /* Set payload length to 4, which is less than sizeof(ICMPEcho_IPv6_t) = 8.
     * This passes the first check (uxNeededSize = 14+40+4 = 58 <= 58 = xDataLength)
     * but fails the second check (4 < 8). */
    pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_ntohs( 4 );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    /* No vApplicationPingReplyHook_Expect() — CMock's strict ordering mode
     * will fail this test if the hook is called unexpectedly. */
    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REPLY_IPv6.
 *        It handles case where A reply was received to an outgoing
 *        ping but the payload of the reply was not correct.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REPLY_IPv6_eSuccess( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t * pxICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6;
    ICMPEcho_IPv6_t * pxICMPEchoHeader;
    uint8_t ucBuffer[ sizeof( ICMPPacket_IPv6_t ) + ipBUFFER_PADDING ], * pucByte;
    NetworkEndPoint_t xEndPoint;
    size_t uxDataLength;
    eFrameProcessingResult_t eReturn;

    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( ucBuffer );
    pxICMPPacket = ( ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxICMPPacket->xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_ntohs( ipBUFFER_PADDING );
    pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( pxICMPPacket->xICMPHeaderIPv6 ) );
    pxICMPEchoHeader = ( ( ICMPEcho_IPv6_t * ) pxICMPHeader_IPv6 );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    uxDataLength = ipNUMERIC_CAST( size_t, FreeRTOS_ntohs( pxICMPPacket->xIPHeader.usPayloadLength ) );
    uxDataLength = uxDataLength - sizeof( ICMPEcho_IPv6_t );

    pucByte = ( ucBuffer + sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) + sizeof( ICMPEcho_IPv6_t ) );

    ( void ) memset( pucByte, ipECHO_DATA_FILL_BYTE, uxDataLength );

    vApplicationPingReplyHook_Expect( eSuccess, pxICMPEchoHeader->usIdentifier );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_SOLICITATION_IPv6.
 *        It handles case where endpoint was not found on the network.
 */
void test_prvProcessICMPMessage_IPv6_NeighborSolicitationNullEP( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer = { 0 }, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket = { 0 };
    NetworkEndPoint_t xEndPoint = { 0 };
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    ( void ) memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = sizeof( xICMPPacket );

    FreeRTOS_InterfaceEPInSameSubnet_IPv6_ExpectAnyArgsAndReturn( NULL );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_SOLICITATION_IPv6.
 *        It handles case where when data length is less than
 *        expected.
 */
void test_prvProcessICMPMessage_IPv6_NeighborSolicitationIncorrectLen( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 5;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_SOLICITATION_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_NeighborSolicitation( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxICMPHeader_IPv6->ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = xHeaderSize + ipBUFFER_PADDING;
    ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xEndPoint.xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );

    FreeRTOS_InterfaceEPInSameSubnet_IPv6_ExpectAnyArgsAndReturn( &xEndPoint );
    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfMessage, ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucCode, 0U );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionType, ndICMP_TARGET_LINK_LAYER_ADDRESS );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionLength, 1U );
    TEST_ASSERT_EQUAL_MEMORY( pxICMPHeader_IPv6->ucOptionBytes, xEndPoint.xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xICMPPacket.xIPHeader.ucHopLimit, 255U );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6.
 *        It handles case buffer size is less than expected.
 */
void test_prvProcessICMPMessage_IPv6_NeighborAdvertisement0( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 5;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
    pxNDWaitingNetworkBuffer = NULL;


    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6.
 *        It handles case when pxNDWaitingNetworkBuffer is NULL.
 */
void test_prvProcessICMPMessage_IPv6_NeighborAdvertisement1( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
    pxNDWaitingNetworkBuffer = NULL;

    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6.
 *        It handles case header is of ipSIZE_OF_IPv4_HEADER type.
 */
void test_prvProcessICMPMessage_IPv6_NeighborAdvertisement2( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    NetworkBufferDescriptor_t xNDWaitingNetworkBuffer;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;

    pxNDWaitingNetworkBuffer = &xNDWaitingNetworkBuffer;
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6.
 *        This verifies a case 'pxNDWaitingNetworkBuffer' was
 *        not waiting for this new address look-up.
 */
void test_prvProcessICMPMessage_IPv6_NeighborAdvertisement3( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    NetworkBufferDescriptor_t xNDWaitingNetworkBuffer;
    IPPacket_IPv6_t xIPPacket;
    IPHeader_IPv6_t * pxIPHeader = &( xIPPacket.xIPHeader );

    /* Zero the stack packets: prvProcessNA reads the flag word (ulReserved),
     * the IPv6 payload length (bounds the option walk) and the NDP option bytes
     * straight from this buffer. Leaving them as stack garbage makes the NA
     * parse -- and hence whether the waiting buffer is released -- depend on
     * whatever a prior test left on the stack. Zeroed, usPayloadLength is 0 so
     * the handler takes the "too short for an ICMPv6 header" early-out: the NA
     * never reaches vNDPCacheUpdate, nothing is released, and the result is a
     * deterministic eReleaseBuffer -- exactly this test's documented intent. */
    ( void ) memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    ( void ) memset( &xICMPPacket, 0, sizeof( xICMPPacket ) );
    ( void ) memset( &xIPPacket, 0, sizeof( xIPPacket ) );
    ( void ) memset( &xNDWaitingNetworkBuffer, 0, sizeof( xNDWaitingNetworkBuffer ) );

    pxNDWaitingNetworkBuffer = &xNDWaitingNetworkBuffer;
    pxNDWaitingNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xIPPacket;
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv6_HEADER );

    /* With the packet zeroed the NA is dropped before the cache-update /
     * waiting-packet path, but the ICMP dispatcher still releases the incoming
     * buffer. Allow that release without pinning a count; no resolve-path mocks
     * (send / timer) are needed because that path is never reached. */
    vReleaseNetworkBufferAndDescriptor_Ignore();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6.
 *        This verifies a case where a packet is handled as a new
 *        incoming IP packet when a neighbour advertisement has been received,
 *        and 'pxNDWaitingNetworkBuffer' was waiting for this new address look-up.
 */
void test_prvProcessICMPMessage_IPv6_NeighborAdvertisement4( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    NetworkBufferDescriptor_t xNDWaitingNetworkBuffer;
    IPPacket_IPv6_t xIPPacket;
    IPHeader_IPv6_t * pxIPHeader = &( xIPPacket.xIPHeader );

    pxNDWaitingNetworkBuffer = &xNDWaitingNetworkBuffer;
    pxNDWaitingNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xIPPacket;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
    ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( pxIPHeader->xSourceAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    /* RFC 4861: a valid NA must arrive with hop limit 255, else the handler
     * drops it before reaching the waiting-packet path. */
    xICMPPacket.xIPHeader.ucHopLimit = 255;


    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv6_HEADER );
    xSendEventStructToIPTask_IgnoreAndReturn( pdFAIL );
    vReleaseNetworkBufferAndDescriptor_Ignore();
    vIPSetNDResolutionTimerEnableState_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    TEST_ASSERT_EQUAL( pxNDWaitingNetworkBuffer, NULL );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6.
 *        This verifies a case where a packet is handled as a new
 *        incoming IP packet when a neighbour advertisement has been received,
 *        and 'pxNDWaitingNetworkBuffer' was waiting for this new address look-up.
 */
void test_prvProcessICMPMessage_IPv6_NeighborAdvertisement5( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    NetworkBufferDescriptor_t xNDWaitingNetworkBuffer;
    IPPacket_IPv6_t xIPPacket;
    IPHeader_IPv6_t * pxIPHeader = &( xIPPacket.xIPHeader );

    pxNDWaitingNetworkBuffer = &xNDWaitingNetworkBuffer;
    pxNDWaitingNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xIPPacket;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
    ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( pxIPHeader->xSourceAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    /* RFC 4861: a valid NA must arrive with hop limit 255, else the handler
     * drops it before reaching the waiting-packet path. */
    xICMPPacket.xIPHeader.ucHopLimit = 255;


    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv6_HEADER );
    xSendEventStructToIPTask_IgnoreAndReturn( pdPASS );
    vIPSetNDResolutionTimerEnableState_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    TEST_ASSERT_EQUAL( pxNDWaitingNetworkBuffer, NULL );
}

/*-----------------------------------------------------------*/
/* Tests for the RFC 4861 Neighbour Advertisement state machine                */
/* (prvProcessNA / prvDetermineAction).                                        */
/*                                                                             */
/* These drive the static logic through the public prvProcessICMPMessage_IPv6  */
/* entry point and assert the resulting xNDCache state, exercising each action */
/* branch of the decision table.                                               */
/*-----------------------------------------------------------*/

/* Flag bits inside the NA "Reserved" field (see FreeRTOS_ND.c). They are held
 * in host order in these locals and byte-swapped into the packet with htonl. */
#define ndTEST_FLAG_ROUTER                0x80000000U
#define ndTEST_FLAG_SOLICITED             0x40000000U
#define ndTEST_FLAG_OVERRIDE              0x20000000U

/* Payload length (host order) that admits exactly one 8-byte NDP option after
 * the 24-byte ICMPv6 ND header (ndICMPv6_HEADER_SIZE). */
#define ndTEST_PAYLOAD_WITH_ONE_OPTION    ( 32U )

/**
 * @brief Build a syntactically valid incoming Neighbour Advertisement packet in
 *        the supplied ICMP packet buffer.
 *
 * @param[out] pxICMPPacket  Packet storage to populate.
 * @param[in]  ulFlags       Host-order NA flags (ndTEST_FLAG_*).
 * @param[in]  pxTargetIP    Target IPv6 address the NA is advertising.
 * @param[in]  pxTargetMAC   Target MAC to place in the TLLA option, or NULL for
 *                           an NA that carries no target link-layer address.
 */
static void prvBuildNaPacket( ICMPPacket_IPv6_t * pxICMPPacket,
                              uint32_t ulFlags,
                              const IPv6_Address_t * pxTargetIP,
                              const MACAddress_t * pxTargetMAC )
{
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = &( pxICMPPacket->xICMPHeaderIPv6 );

    ( void ) memset( pxICMPPacket, 0, sizeof( *pxICMPPacket ) );

    pxICMPHeader_IPv6->ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
    /* RFC 4861: a received NA must have hop limit 255. */
    pxICMPPacket->xIPHeader.ucHopLimit = 255;
    pxICMPHeader_IPv6->ulReserved = FreeRTOS_htonl( ulFlags );
    ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, pxTargetIP->ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    if( pxTargetMAC != NULL )
    {
        /* One Target Link-Layer Address option: type 2, length 1 (x8 bytes). */
        pxICMPHeader_IPv6->ucOptionType = ndICMP_TARGET_LINK_LAYER_ADDRESS;
        pxICMPHeader_IPv6->ucOptionLength = 1U;
        ( void ) memcpy( pxICMPHeader_IPv6->ucOptionBytes, pxTargetMAC->ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
        pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( ndTEST_PAYLOAD_WITH_ONE_OPTION );
    }
    else
    {
        /* No options: payload is just the ND header. */
        pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( ( uint16_t ) ndICMPv6_HEADER_SIZE );
    }
}

/**
 * @brief A solicited NA that tries to overwrite
 *        an existing REACHABLE binding with a DIFFERENT MAC while Override=0 must
 *        NOT poison the cache. The old MAC must be preserved and the entry demoted
 *        to STALE (eNA_REJECT_MAC_SET_STALE).
 */
void test_prvProcessNA_OverrideZero_DifferentMac_KeepsOldMacSetsStale( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    BaseType_t xUseEntry = 0;
    MACAddress_t xAttackerMAC = { { 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF } };

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    /* Pre-existing trusted, REACHABLE binding for the target IP. */
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE;

    /* Attacker NA: Solicited=1, Override=0, carrying a DIFFERENT MAC. */
    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED, &xDefaultIPAddress, &xAttackerMAC );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* The attacker MAC must be REJECTED: the original MAC is still in the cache. */
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes,
                              xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    /* And the entry is demoted to STALE so reachability is re-verified. */
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_STALE );
}

/**
 * @brief An unknown neighbour advertised with a valid TLLA and Solicited=1 is
 *        created as a REACHABLE entry (eNA_CREATE_NEW).
 */
void test_prvProcessNA_NewNeighbour_Solicited_CreatesReachable( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    MACAddress_t xNewMAC = { { 0x02, 0x11, 0x22, 0x33, 0x44, 0x55 } };
    NDCacheRow_t * pxEntry;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED, &xDefaultIPAddress, &xNewMAC );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    /* The insert path timestamps the entry and formats the MAC for a trace. */
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* Assert on slot 0 directly: pxNDPCacheLookup has a STALE->DELAY side effect. */
    pxEntry = &( xNDCache[ 0 ] );
    TEST_ASSERT_EQUAL_MEMORY( pxEntry->xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( pxEntry->ucState, eND_REACHABLE );
    TEST_ASSERT_EQUAL_MEMORY( pxEntry->xMACAddress.ucBytes, xNewMAC.ucBytes, sizeof( MACAddress_t ) );
}

/**
 * @brief An unknown neighbour advertised UNSOLICITED with a valid TLLA is created
 *        as a STALE entry (eNA_CREATE_NEW, initial state STALE).
 */
void test_prvProcessNA_NewNeighbour_Unsolicited_CreatesStale( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    MACAddress_t xNewMAC = { { 0x02, 0xAB, 0xCD, 0xEF, 0x01, 0x02 } };
    NDCacheRow_t * pxEntry;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    /* No flags set: unsolicited. */
    prvBuildNaPacket( &xICMPPacket, 0U, &xDefaultIPAddress, &xNewMAC );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* Assert on slot 0 directly: pxNDPCacheLookup would demote STALE to DELAY. */
    pxEntry = &( xNDCache[ 0 ] );
    TEST_ASSERT_EQUAL_MEMORY( pxEntry->xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( pxEntry->ucState, eND_STALE );
}

/**
 * @brief A solicited NA with Override=1 and a NEW MAC updates the binding and
 *        marks it REACHABLE (eNA_UPDATE_REACHABLE). This is the legitimate MAC
 *        change path (contrast with the Override=0 rejection above).
 */
void test_prvProcessNA_OverrideOne_Solicited_UpdatesReachable( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    BaseType_t xUseEntry = 0;
    MACAddress_t xNewMAC = { { 0x02, 0x99, 0x88, 0x77, 0x66, 0x55 } };

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_STALE;

    /* Solicited=1, Override=1, new MAC: the stack may adopt it. */
    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED | ndTEST_FLAG_OVERRIDE, &xDefaultIPAddress, &xNewMAC );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* The new MAC is adopted and the entry is REACHABLE. */
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xNewMAC.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_REACHABLE );
}

/**
 * @brief A solicited NA for an existing entry that carries NO target link-layer
 *        address simply confirms reachability (eNA_CONFIRM_REACHABLE): the MAC is
 *        untouched and the state becomes REACHABLE.
 */
void test_prvProcessNA_ExistingEntry_NoTlla_Solicited_ConfirmsReachable( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    BaseType_t xUseEntry = 0;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_STALE;

    /* Solicited=1, no TLLA option. */
    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED, &xDefaultIPAddress, NULL );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_REACHABLE );
}

/**
 * @brief An NA whose target IP is multicast is rejected by prvIsValidNa and must
 *        not create or modify any cache entry.
 */
void test_prvProcessNA_MulticastTargetIP_Rejected( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    MACAddress_t xNewMAC = { { 0x02, 0x11, 0x22, 0x33, 0x44, 0x55 } };
    IPv6_Address_t xMulticastIP;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    /* Multicast target IP (first byte 0xFF) - invalid per RFC 4861 7.1.2. */
    ( void ) memcpy( xMulticastIP.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xMulticastIP.ucBytes[ 0 ] = 0xFFU;

    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED, &xMulticastIP, &xNewMAC );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* No entry should have been created for the multicast target. */
    TEST_ASSERT_EQUAL( xNDCache[ 0 ].ucState, eND_FREE );
}

/**
 * @brief An NA that arrives with a hop limit other than 255 is dropped before the
 *        state machine runs (RFC 4861 anti-spoofing): the cache is not modified.
 */
void test_prvProcessNA_BadHopLimit_Dropped( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    MACAddress_t xNewMAC = { { 0x02, 0x11, 0x22, 0x33, 0x44, 0x55 } };

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED, &xDefaultIPAddress, &xNewMAC );
    /* Corrupt the hop limit so the RFC 4861 guard rejects the packet. */
    xICMPPacket.xIPHeader.ucHopLimit = 64;

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* Packet dropped: no entry created. */
    TEST_ASSERT_EQUAL( xNDCache[ 0 ].ucState, eND_FREE );
}

/**
 * @brief An NA carrying a Target Link-Layer Address whose MAC has the multicast
 *        (I/G) bit set is invalid per RFC 4861 and must be rejected by
 *        prvIsValidNa: no cache entry is created.
 */
void test_prvProcessNA_TllaMulticastMac_Rejected( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    MACAddress_t xMcastMAC = { { 0x01, 0x11, 0x22, 0x33, 0x44, 0x55 } }; /* I/G bit set. */

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED, &xDefaultIPAddress, &xMcastMAC );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* Rejected by prvIsValidNa: nothing added to the cache. */
    TEST_ASSERT_EQUAL( xNDCache[ 0 ].ucState, eND_FREE );
}

/**
 * @brief An NA carrying a Target Link-Layer Address that is the all-zero MAC is
 *        invalid per RFC 4861 and must be rejected: no cache entry is created.
 */
void test_prvProcessNA_TllaZeroMac_Rejected( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    MACAddress_t xZeroMAC = { { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } };

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED, &xDefaultIPAddress, &xZeroMAC );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    TEST_ASSERT_EQUAL( xNDCache[ 0 ].ucState, eND_FREE );
}

/**
 * @brief An NA whose NDP option declares a length of 0 is malformed. The option
 *        walker flags the error and prvProcessNA drops the packet before the
 *        state machine runs: no cache entry is created.
 */
void test_prvProcessNA_MalformedOptionZeroLength_Dropped( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    MACAddress_t xNewMAC = { { 0x02, 0x11, 0x22, 0x33, 0x44, 0x55 } };

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED, &xDefaultIPAddress, &xNewMAC );
    /* Corrupt the option length to 0: a length-0 option can never advance the
     * walker, so the parser must flag it as malformed. */
    xICMPPacket.xICMPHeaderIPv6.ucOptionLength = 0U;

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* Malformed option: dropped, cache untouched. */
    TEST_ASSERT_EQUAL( xNDCache[ 0 ].ucState, eND_FREE );
}

/**
 * @brief For an existing entry, an UNSOLICITED, Override=1 NA whose MAC matches
 *        the cached one is a no-op (eNA_MAINTAIN): neither the MAC nor the state
 *        changes.
 */
void test_prvProcessNA_ExistingEntry_OverrideUnsolicited_SameMac_Maintains( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    BaseType_t xUseEntry = 0;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    /* Existing REACHABLE entry with a known MAC. */
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE;

    /* Unsolicited, Override=1, carrying the SAME MAC already cached. */
    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_OVERRIDE, &xDefaultIPAddress, &xDefaultMACAddress );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* MAINTAIN: MAC unchanged and still REACHABLE (no vNDPCacheUpdate call). */
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_REACHABLE );

    /* Leave the cache clean: the suite has no setUp() and downstream tests that
     * do not memset rely on a FREE cache. */
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}

/**
 * @brief For an existing entry, an UNSOLICITED NA that carries NO target
 *        link-layer address is a no-op (eNA_MAINTAIN): the entry is left exactly
 *        as it was.
 */
void test_prvProcessNA_ExistingEntry_NoTlla_Unsolicited_Maintains( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    BaseType_t xUseEntry = 0;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE;

    /* Unsolicited, no TLLA option. */
    prvBuildNaPacket( &xICMPPacket, 0U, &xDefaultIPAddress, NULL );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* MAINTAIN: unchanged MAC and state. */
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_REACHABLE );

    /* Leave the cache clean for downstream tests that do not memset on entry. */
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}

/**
 * @brief A solicited NA for a brand-new neighbour when the ND cache is completely
 *        full exercises the eviction path in prvGetFreeNDPCacheEntry: the
 *        lowest-age non-INCOMPLETE entry is reclaimed and reused for the new
 *        binding.
 */
void test_prvProcessNA_NewNeighbour_CacheFull_EvictsLowestAge( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    MACAddress_t xNewMAC = { { 0x02, 0xDE, 0xAD, 0xBE, 0xEF, 0x01 } };
    BaseType_t x;
    const BaseType_t xVictim = 5;
    NDCacheRow_t * pxEntry;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    /* Fill every slot so no free entry exists; give each a distinct IP and a
     * high age, except one victim with the lowest age (and not INCOMPLETE). */
    for( x = 0; x < ipconfigND_CACHE_ENTRIES; x++ )
    {
        xNDCache[ x ].ucState = eND_STALE;
        xNDCache[ x ].ucAge = 200U;
        ( void ) memcpy( xNDCache[ x ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
        xNDCache[ x ].xIPAddress.ucBytes[ 15 ] = ( uint8_t ) ( 0x10 + x );
    }

    xNDCache[ xVictim ].ucAge = 1U; /* Lowest age: this slot must be evicted. */

    /* New neighbour: solicited so it is created directly as REACHABLE. Use an IP
     * not already present in the full cache. */
    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED, &xDefaultIPAddress, &xNewMAC );
    xICMPPacket.xICMPHeaderIPv6.xIPv6Address.ucBytes[ 15 ] = 0xF1U;

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* The lowest-age victim slot was reclaimed for the new REACHABLE binding. */
    pxEntry = &( xNDCache[ xVictim ] );
    TEST_ASSERT_EQUAL( pxEntry->ucState, eND_REACHABLE );
    TEST_ASSERT_EQUAL_MEMORY( pxEntry->xMACAddress.ucBytes, xNewMAC.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( pxEntry->xIPAddress.ucBytes[ 15 ], 0xF1U );

    /* This test fills the whole cache; wipe it so downstream tests start clean. */
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}

/**
 * @brief For an existing entry, an UNSOLICITED, Override=1 NA carrying a DIFFERENT
 *        MAC adopts the new MAC but demotes the entry to STALE (eNA_UPDATE_STALE):
 *        the binding is updated yet reachability must be re-verified.
 */
void test_prvProcessNA_ExistingEntry_OverrideUnsolicited_DiffMac_UpdatesStale( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    BaseType_t xUseEntry = 0;
    MACAddress_t xNewMAC = { { 0x02, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E } };

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_REACHABLE;

    /* Unsolicited, Override=1, DIFFERENT MAC: adopt it but mark STALE. */
    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_OVERRIDE, &xDefaultIPAddress, &xNewMAC );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* New MAC adopted, but entry demoted to STALE for re-verification. */
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xNewMAC.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_STALE );

    /* Leave the cache clean for downstream tests that do not memset on entry. */
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}

/**
 * @brief A solicited NA for a brand-new neighbour whose Router (R) flag is set
 *        must create the entry AND record the router flag in ucFlags. Covers the
 *        xRouter != pdFALSE branch and the ucFlags |= ndpFLAG_IS_ROUTER line in
 *        vNDPCacheInsert.
 */
void test_prvProcessNA_NewNeighbour_RouterFlag_SetsRouterBit( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    MACAddress_t xNewMAC = { { 0x02, 0x52, 0x54, 0x00, 0x11, 0x22 } };
    NDCacheRow_t * pxEntry;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    /* Solicited + Router: create as REACHABLE and mark the router flag. */
    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED | ndTEST_FLAG_ROUTER, &xDefaultIPAddress, &xNewMAC );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    pxEntry = &( xNDCache[ 0 ] );
    TEST_ASSERT_EQUAL( pxEntry->ucState, eND_REACHABLE );
    /* ucFlags bit 0x01 is ndpFLAG_IS_ROUTER (private to FreeRTOS_ND.c). */
    TEST_ASSERT_TRUE( ( pxEntry->ucFlags & 0x01U ) != 0U );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}

/**
 * @brief A solicited NA with Override=1, a NEW MAC and the Router flag set for an
 *        EXISTING entry updates the binding to REACHABLE and records the router
 *        flag. Covers the xRouter != pdFALSE branch and ucFlags |= line in
 *        vNDPCacheUpdate.
 */
void test_prvProcessNA_ExistingEntry_RouterFlag_SetsRouterBit( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    BaseType_t xUseEntry = 0;
    MACAddress_t xNewMAC = { { 0x02, 0x52, 0x54, 0x00, 0x33, 0x44 } };

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_STALE;

    /* Solicited + Override + Router, new MAC: adopt it, REACHABLE, router flag set. */
    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED | ndTEST_FLAG_OVERRIDE | ndTEST_FLAG_ROUTER, &xDefaultIPAddress, &xNewMAC );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xNewMAC.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_REACHABLE );
    /* ucFlags bit 0x01 is ndpFLAG_IS_ROUTER (private to FreeRTOS_ND.c). */
    TEST_ASSERT_TRUE( ( xNDCache[ xUseEntry ].ucFlags & 0x01U ) != 0U );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}

/**
 * @brief For an existing entry, a SOLICITED NA with Override=0 carrying a TLLA
 *        whose MAC MATCHES the cached one confirms reachability
 *        (eNA_CONFIRM_REACHABLE): the O=0 / MAC-match / S=1 arm of
 *        prvDetermineAction. Covers line 1008.
 */
void test_prvProcessNA_ExistingEntry_OverrideZero_Solicited_SameMac_Confirms( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    BaseType_t xUseEntry = 0;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    /* Existing STALE entry whose MAC equals the NA target link-layer address. */
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_STALE;

    /* Solicited, Override=0, SAME MAC: O=0 + MAC-match + S=1 -> CONFIRM_REACHABLE. */
    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED, &xDefaultIPAddress, &xDefaultMACAddress );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* CONFIRM_REACHABLE: MAC unchanged, state promoted to REACHABLE. */
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_REACHABLE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}

/**
 * @brief vNDRefreshCacheEntryAge (upper-layer reachability hint) promotes a STALE
 *        entry to REACHABLE and resets its age, but must NOT resurrect an
 *        INCOMPLETE entry.
 */
void test_vNDRefreshCacheEntryAge_PromotesStaleNotIncomplete( void )
{
    BaseType_t xStale = 0, xIncomplete = 1;
    IPv6_Address_t xStaleIP, xIncompleteIP;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    ( void ) memcpy( xStaleIP.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xIncompleteIP.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xIncompleteIP.ucBytes[ 15 ] ^= 0x01U; /* Distinct address. */

    ( void ) memcpy( xNDCache[ xStale ].xIPAddress.ucBytes, xStaleIP.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xStale ].ucState = eND_STALE;
    xNDCache[ xStale ].ucAge = 1;

    ( void ) memcpy( xNDCache[ xIncomplete ].xIPAddress.ucBytes, xIncompleteIP.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xIncomplete ].ucState = eND_INCOMPLETE;

    /* Hint for the STALE entry -> promoted to REACHABLE, age reset. */
    vNDRefreshCacheEntryAge( &xDefaultMACAddress, &xStaleIP );
    TEST_ASSERT_EQUAL( xNDCache[ xStale ].ucState, eND_REACHABLE );
    TEST_ASSERT_EQUAL( xNDCache[ xStale ].ucAge, ( uint8_t ) ipconfigMAX_ND_AGE );

    /* Hint for the INCOMPLETE entry -> left untouched (still resolving). */
    vNDRefreshCacheEntryAge( &xDefaultMACAddress, &xIncompleteIP );
    TEST_ASSERT_EQUAL( xNDCache[ xIncomplete ].ucState, eND_INCOMPLETE );
}

/**
 * @brief This function process ICMP message when message type is incorrect.
 */
void test_prvProcessICMPMessage_IPv6_Default( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = 0;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This case validates failure in sending
 *        Neighbour Advertisement message because of
 *        failure in getting network buffer.
 */
void test_FreeRTOS_OutputAdvertiseIPv6_Default( void )
{
    NetworkEndPoint_t xEndPoint;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_OutputAdvertiseIPv6( &xEndPoint );
}

/**
 * @brief This case validates failure in sending
 *        Neighbour Advertisement message because of
 *        interface being NULL.
 */
void test_FreeRTOS_OutputAdvertiseIPv6_Assert( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;

    xEndPoint.pxNetworkInterface = NULL;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );

    catch_assert( FreeRTOS_OutputAdvertiseIPv6( &xEndPoint ) );
}

/**
 * @brief This case validates sending out
 *        Neighbour Advertisement message.
 */
void test_FreeRTOS_OutputAdvertiseIPv6_HappyPath( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket, * pxICMPPacket = &xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( pxICMPPacket->xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    NetworkInterface_t xInterface;

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    xEndPoint.pxNetworkInterface = &xInterface;
    ( void ) memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    pxICMPHeader_IPv6->usChecksum = 0U;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );
    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );

    FreeRTOS_OutputAdvertiseIPv6( &xEndPoint );

    TEST_ASSERT_EQUAL( pxICMPPacket->xEthernetHeader.usFrameType, ipIPv6_FRAME_TYPE );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucVersionTrafficClass, 0x60 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.usPayloadLength, FreeRTOS_htons( sizeof( ICMPHeader_IPv6_t ) ) );
    TEST_ASSERT_EQUAL_MEMORY( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfMessage, ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionType, ndICMP_TARGET_LINK_LAYER_ADDRESS );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionLength, 1 );
    TEST_ASSERT_EQUAL_MEMORY( pxICMPHeader_IPv6->xIPv6Address.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, sizeof( pxICMPHeader_IPv6->xIPv6Address.ucBytes ) );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->usChecksum, 0 );
}

/**
 * @brief Create an IPv6 address, based on a prefix.
 *        with the bits after the prefix having random value.
 *        But fails to get the random number.
 */
void test_FreeRTOS_CreateIPv6Address_RandomFail( void )
{
    IPv6_Address_t xIPAddress, xPrefix = { 0 };
    BaseType_t xDoRandom = pdTRUE, xReturn;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );

    xReturn = FreeRTOS_CreateIPv6Address( &xIPAddress, &xPrefix, sizeof( xPrefix ), xDoRandom );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief Create an IPv6 address, based on a prefix.
 *        with the bits after the prefix having random value
 *        but incorrect prefix length.
 */
void test_FreeRTOS_CreateIPv6Address_Assert1( void )
{
    IPv6_Address_t xIPAddress, xPrefix = { 0 };
    BaseType_t xDoRandom = pdTRUE, xReturn, xIndex;

    for( xIndex = 0; xIndex < 4; xIndex++ )
    {
        xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    }

    catch_assert( FreeRTOS_CreateIPv6Address( &xIPAddress, &xPrefix, 0, xDoRandom ) );
}

/**
 * @brief Create an IPv6 address, based on a prefix.
 *        with the bits after the prefix having random value
 *        but incorrect prefix length and xDoRandom is 0.
 */
void test_FreeRTOS_CreateIPv6Address_Assert2( void )
{
    IPv6_Address_t xIPAddress, xPrefix;
    /* The maximum allowed prefix length was increased to 128 because of the loopback address. */
    size_t uxPrefixLength = 8U * ipSIZE_OF_IPv6_ADDRESS + 1;
    BaseType_t xDoRandom = pdFALSE, xReturn, xIndex;

    catch_assert( FreeRTOS_CreateIPv6Address( &xIPAddress, &xPrefix, uxPrefixLength, xDoRandom ) );
}

/**
 * @brief Create an IPv6 address, based on a prefix.
 *        with the bits after the prefix having random value.
 */
void test_FreeRTOS_CreateIPv6Address_Pass1( void )
{
    IPv6_Address_t xIPAddress, xPrefix;
    size_t uxPrefixLength = 8U;
    BaseType_t xDoRandom = pdTRUE, xReturn, xIndex;

    for( xIndex = 0; xIndex < 4; xIndex++ )
    {
        xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    }

    xReturn = FreeRTOS_CreateIPv6Address( &xIPAddress, &xPrefix, uxPrefixLength, xDoRandom );

    TEST_ASSERT_EQUAL( xReturn, pdPASS );
}

/**
 * @brief Create an IPv6 address, based on a prefix.
 *        with the bits after the prefix having random value
 *        and uxPrefixLength is not a multiple of 8.
 */
void test_FreeRTOS_CreateIPv6Address_Pass2( void )
{
    IPv6_Address_t xIPAddress, xPrefix;
    size_t uxPrefixLength = 7;
    BaseType_t xDoRandom = pdTRUE, xReturn, xIndex;

    for( xIndex = 0; xIndex < 4; xIndex++ )
    {
        xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    }

    xReturn = FreeRTOS_CreateIPv6Address( &xIPAddress, &xPrefix, uxPrefixLength, xDoRandom );

    TEST_ASSERT_EQUAL( xReturn, pdPASS );
}

/**
 * @brief Create an IPv6 address, based on a prefix.
 *        with the bits after the prefix having random value
 *        and uxPrefixLength is 128 bites.
 */
void test_FreeRTOS_CreateIPv6Address_Pass3( void )
{
    IPv6_Address_t xIPAddress, xPrefix;
    size_t uxPrefixLength = 128;
    BaseType_t xDoRandom = pdTRUE, xReturn, xIndex;

    for( xIndex = 0; xIndex < 4; xIndex++ )
    {
        xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    }

    xReturn = FreeRTOS_CreateIPv6Address( &xIPAddress, &xPrefix, uxPrefixLength, xDoRandom );

    TEST_ASSERT_EQUAL( xReturn, pdPASS );
}

/**
 * @brief Cover all the pcMessageType print
 *        scenario.
 */
void test_pcMessageType_All( void )
{
    BaseType_t xType;

    xType = ipICMP_DEST_UNREACHABLE_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_PACKET_TOO_BIG_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_TIME_EXCEEDED_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_PARAMETER_PROBLEM_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_PING_REQUEST_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_PING_REPLY_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_ROUTER_SOLICITATION_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_ROUTER_ADVERTISEMENT_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_MULTICAST_LISTENER_REPORT_V1;
    ( void ) pcMessageType( xType );

    xType = ipICMP_MULTICAST_LISTENER_REPORT_V2;
    ( void ) pcMessageType( xType );

    xType = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6 + 1;
    ( void ) pcMessageType( xType );
}

/**
 * @brief heck if the network buffer requires resolution for different protocols.
 */
void test_xCheckIPv6RequiresResolution_Protocols( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];
    BaseType_t xResult;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    IPPacket_IPv6_t * pxIPPacket_V6 = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    IPHeader_IPv6_t * pxIPHeader_V6 = &( pxIPPacket_V6->xIPHeader );
    IPv6_Address_t * pxIPAddress = &( pxIPHeader_V6->xSourceAddress );
    pxIPPacket_V6->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    pxIPHeader_V6->ucNextHeader = 1;

    xResult = xCheckRequiresNDResolution( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );

    pxIPHeader_V6->ucNextHeader = ipPROTOCOL_UDP;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    xResult = xCheckRequiresNDResolution( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );

    pxIPHeader_V6->ucNextHeader = ipPROTOCOL_TCP;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    xResult = xCheckRequiresNDResolution( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/**
 * @brief Check if the network buffer requires resolution for addresses
 *        not on the local network.
 */
void test_xCheckRequiresNDResolution_TCPNotOnLocalNetwork( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];
    BaseType_t xResult;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    IPPacket_IPv6_t * pxIPPacket_V6 = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    IPHeader_IPv6_t * pxIPHeader_V6 = &( pxIPPacket_V6->xIPHeader );
    IPv6_Address_t * pxIPAddress = &( pxIPHeader_V6->xSourceAddress );
    pxIPPacket_V6->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    pxIPHeader_V6->ucNextHeader = ipPROTOCOL_TCP;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    xResult = xCheckRequiresNDResolution( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/**
 * @brief Cache hit occurs with an IP address in the multicast case.
 */
void test_xCheckRequiresNDResolution_Hit( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];
    BaseType_t xResult;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    xEndPoint.bits.bIPv6 = pdTRUE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    IPPacket_IPv6_t * pxIPPacket_V6 = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    IPHeader_IPv6_t * pxIPHeader_V6 = &( pxIPPacket_V6->xIPHeader );
    IPv6_Address_t * pxIPAddress = &( pxIPHeader_V6->xSourceAddress );
    pxIPPacket_V6->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    pxIPHeader_V6->ucNextHeader = ipPROTOCOL_TCP;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    xIsIPv6AllowedMulticast_ExpectAndReturn( pxIPAddress, pdTRUE );
    vSetMultiCastIPv6MacAddress_Expect( pxIPAddress, NULL );
    vSetMultiCastIPv6MacAddress_IgnoreArg_pxMACAddress();
    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    xResult = xCheckRequiresNDResolution( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/**
 * @brief ND cache miss scenarios.
 */
void test_xCheckRequiresNDResolution_Miss( void )
{
    struct xNetworkEndPoint xEndPoint, * pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer, * pxNewNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];
    BaseType_t xResult;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    xEndPoint.bits.bIPv6 = pdTRUE;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = ipconfigNETWORK_MTU;
    IPPacket_IPv6_t * pxIPPacket_V6 = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    IPHeader_IPv6_t * pxIPHeader_V6 = &( pxIPPacket_V6->xIPHeader );
    IPv6_Address_t * pxIPAddress = &( pxIPHeader_V6->xSourceAddress );
    pxIPPacket_V6->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    pxIPHeader_V6->ucNextHeader = ipPROTOCOL_TCP;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    xIsIPv6AllowedMulticast_ExpectAndReturn( pxIPAddress, pdFALSE );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0 );
    vReturnEthernetFrame_ExpectAnyArgs();

    xResult = xCheckRequiresNDResolution( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = ipconfigNETWORK_MTU;
    pxIPPacket_V6 = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxIPHeader_V6 = &( pxIPPacket_V6->xIPHeader );
    pxIPAddress = &( pxIPHeader_V6->xSourceAddress );
    pxIPPacket_V6->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    pxIPHeader_V6->ucNextHeader = ipPROTOCOL_TCP;
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    xIsIPv6AllowedMulticast_ExpectAndReturn( pxIPAddress, pdFALSE );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    xResult = xCheckRequiresNDResolution( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

/**
 * @brief Trigger assertion when Ethernet frame type is not IPv6 while calling xCheckRequiresNDResolution.
 */
void test_xCheckRequiresNDResolution_AssertInvalidFrameType( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];
    BaseType_t xResult;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    IPPacket_t * pxIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    IPHeader_t * pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    catch_assert( xCheckRequiresNDResolution( pxNetworkBuffer ) );
}

/**
 * @brief Exercise every case of the pcNDStateName() debug helper, including the
 *        default branch for an out-of-range state, so each switch arm and its
 *        string are covered.
 */
void test_pcNDStateName_All( void )
{
    TEST_ASSERT_EQUAL_STRING( "Free", pcNDStateName( eND_FREE ) );
    TEST_ASSERT_EQUAL_STRING( "Incomplete", pcNDStateName( eND_INCOMPLETE ) );
    TEST_ASSERT_EQUAL_STRING( "Reachable", pcNDStateName( eND_REACHABLE ) );
    TEST_ASSERT_EQUAL_STRING( "Stale", pcNDStateName( eND_STALE ) );
    TEST_ASSERT_EQUAL_STRING( "Delay", pcNDStateName( eND_DELAY ) );
    TEST_ASSERT_EQUAL_STRING( "Probe", pcNDStateName( eND_PROBE ) );

    /* Out-of-range value: exercises the default arm and the snprintf fallback.
     * The formatted contents depend on the harness's snprintf, so assert only
     * that the default path returns a valid (non-NULL) buffer. */
    TEST_ASSERT_TRUE( pcNDStateName( ( eNDState_t ) 99 ) != NULL );
}

/**
 * @brief Exercise every case of the pcNDActionName() debug helper, including the
 *        default branch for an out-of-range action.
 */
void test_pcNDActionName_All( void )
{
    TEST_ASSERT_EQUAL_STRING( "Drop", pcNDActionName( eNA_DROP ) );
    TEST_ASSERT_EQUAL_STRING( "Create_New", pcNDActionName( eNA_CREATE_NEW ) );
    TEST_ASSERT_EQUAL_STRING( "Update_Reachable", pcNDActionName( eNA_UPDATE_REACHABLE ) );
    TEST_ASSERT_EQUAL_STRING( "Update_Stale", pcNDActionName( eNA_UPDATE_STALE ) );
    TEST_ASSERT_EQUAL_STRING( "Confirm_Reachable", pcNDActionName( eNA_CONFIRM_REACHABLE ) );
    TEST_ASSERT_EQUAL_STRING( "Maintain", pcNDActionName( eNA_MAINTAIN ) );

    /* Out-of-range value: exercises the default arm and the snprintf fallback.
     * The formatted contents depend on the harness's snprintf, so assert only
     * that the default path returns a valid (non-NULL) buffer. */
    TEST_ASSERT_TRUE( pcNDActionName( ( eNaAction_t ) 99 ) != NULL );
}

/**
 * @brief The IPv6 ICMP dispatcher must silently accept (log and break) the
 *        message types it does not implement: Destination Unreachable, Packet
 *        Too Big, Time Exceeded and Parameter Problem. Covers those switch
 *        cases in prvProcessICMPMessage_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_UnhandledTypes_Break( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    const uint8_t ucTypes[] =
    {
        ipICMP_DEST_UNREACHABLE_IPv6,
        ipICMP_PACKET_TOO_BIG_IPv6,
        ipICMP_TIME_EXCEEDED_IPv6,
        ipICMP_PARAMETER_PROBLEM_IPv6
    };
    size_t i;

    for( i = 0; i < sizeof( ucTypes ) / sizeof( ucTypes[ 0 ] ); i++ )
    {
        ( void ) memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
        ( void ) memset( &xICMPPacket, 0, sizeof( xICMPPacket ) );
        ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
        ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

        xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
        pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
        pxNetworkBuffer->pxEndPoint = &xEndPoint;
        pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
        xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ucTypes[ i ];
        pxNDWaitingNetworkBuffer = NULL;

        eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

        /* Unimplemented types are logged and released. */
        TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    }
}

/**
 * @brief A PROBE entry expiring this tick when the network-buffer allocation
 *        FAILS (pxGetNetworkBufferWithDescriptor returns NULL) must still count
 *        the probe attempt and arm the retry, without dereferencing the buffer.
 *        Covers the pxNetworkBuffer != NULL false side in vNDAgeCache's PROBE arm.
 */
void test_vNDAgeCache_ProbeBufferAllocFails( void )
{
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucState = eND_PROBE;
    xNDCache[ xUseEntry ].ucNumProbes = 0;
    xNDCache[ xUseEntry ].pxEndPoint = &xEndPoint;

    /* Allocation fails: no NS is built, but the probe is still counted. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucNumProbes, 1 );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, 1 );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_PROBE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}

/**
 * @brief When the cache is full and every slot is INCOMPLETE, the eviction scan
 *        in prvGetFreeNDPCacheEntry must skip INCOMPLETE entries (they are
 *        mid-resolution) and therefore find nothing to evict, so a brand-new
 *        solicited NA cannot be inserted. Covers the ucState != eND_INCOMPLETE
 *        skip branch.
 */
void test_prvProcessNA_CacheFullAllIncomplete_NoEviction( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    MACAddress_t xNewMAC = { { 0x02, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE } };
    BaseType_t x;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    /* Every slot INCOMPLETE with a distinct IP: none is eligible for eviction. */
    for( x = 0; x < ipconfigND_CACHE_ENTRIES; x++ )
    {
        xNDCache[ x ].ucState = eND_INCOMPLETE;
        xNDCache[ x ].ucAge = 10U;
        ( void ) memcpy( xNDCache[ x ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
        xNDCache[ x ].xIPAddress.ucBytes[ 15 ] = ( uint8_t ) ( 0x20 + x );
    }

    /* New neighbour, solicited, IP absent from the cache: insert must find no
     * free/evictable slot and create nothing. */
    prvBuildNaPacket( &xICMPPacket, ndTEST_FLAG_SOLICITED, &xDefaultIPAddress, &xNewMAC );
    xICMPPacket.xICMPHeaderIPv6.xIPv6Address.ucBytes[ 15 ] = 0xF7U;

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    xTaskGetTickCount_IgnoreAndReturn( 0 );
    FreeRTOS_EUI48_ntop_Ignore();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* No INCOMPLETE slot was overwritten with the new binding. */
    for( x = 0; x < ipconfigND_CACHE_ENTRIES; x++ )
    {
        TEST_ASSERT_EQUAL( xNDCache[ x ].ucState, eND_INCOMPLETE );
    }

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}

/**
 * @brief For an existing entry, an UNSOLICITED, Override=0 NA whose MAC MATCHES
 *        keeps the entry unchanged (eNA_MAINTAIN via the S=0 arm), and one whose
 *        MAC DIFFERS also maintains (O=0, S=0). Covers the unsolicited (false)
 *        side of the two prvDetermineAction ternaries.
 */
void test_prvProcessNA_ExistingEntry_OverrideZero_Unsolicited_Maintains( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    BaseType_t xUseEntry = 0;
    MACAddress_t xDiffMAC = { { 0x02, 0x11, 0x22, 0x33, 0x44, 0x99 } };

    /* Case 1: unsolicited, O=0, matching MAC -> MAINTAIN (line 1008 S=0 side). */
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_STALE;

    prvBuildNaPacket( &xICMPPacket, 0U, &xDefaultIPAddress, &xDefaultMACAddress );
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* MAINTAIN keeps the action a no-op, but pxNDPCacheLookup promotes a STALE
     * entry to DELAY on lookup, so the resulting state is DELAY. */
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_DELAY );

    /* Case 2: unsolicited, O=0, DIFFERENT MAC -> MAINTAIN (line 1014 S=0 side),
     * old MAC preserved. */
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucState = eND_STALE;

    prvBuildNaPacket( &xICMPPacket, 0U, &xDefaultIPAddress, &xDiffMAC );
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = sizeof( ICMPPacket_IPv6_t );
    pxNDWaitingNetworkBuffer = NULL;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    /* MAINTAIN: old MAC kept. State is DELAY because pxNDPCacheLookup promoted
     * the STALE entry to DELAY on lookup and MAINTAIN did not change it. */
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucState, eND_DELAY );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}
