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
#include "FreeRTOS.h"

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IPv6.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_IPv6_Utils.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_NetworkBufferManagement.h"

#include "catch_assert.h"
#include "FreeRTOS_ND_stubs.c"
#include "FreeRTOS_ND.h"

/** @brief The ND cache. */
NDCacheRow_t xNDCache[ ipconfigND_CACHE_ENTRIES ];

/* Setting IPv6 address as "fe80::7009" */
const IPv6_Address_t xDefaultIPAddress =
{
    0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x09
};

/* IPv6 multi-cast address is ff02::. */
const IPv6_Address_t xMultiCastIPAddress =
{
    0xff, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};

/* Setting eIPv6_SiteLocal IPv6 address as "feC0::7009" */
const IPv6_Address_t xSiteLocalIPAddress =
{
    0xfe, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x09
};

/* Setting IPv6 Gateway address as "fe80::1" */
const IPv6_Address_t xGatewayIPAddress =
{
    0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01
};


/* IPv6 default MAC address. */
const MACAddress_t xDefaultMACAddress = { 0x22, 0x22, 0x22, 0x22, 0x22, 0x22 };

#define xHeaderSize ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t ) )
//#define xDataLength 100
/*
 * ===================================================
 *             Test for eNDGetCacheEntry
 * ===================================================
 */

/**
 * @brief This function find the MAC-address of a multicast IPv6 address
 *        with a valid endpoint.
 */
void test_eNDGetCacheEntry_Multicast_ValidEndPoint( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    eARPLookupResult_t eResult;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    pxEndPoint->bits.bIPv6 = 1;
    ( void ) memcpy(xIPAddress.ucBytes, xMultiCastIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdTRUE );
    vSetMultiCastIPv6MacAddress_ExpectAnyArgs();

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
}

/**
 * @brief This function find the MAC-address of a multicast IPv6 address
 *        with a NULL endpoint.
 */
void test_eNDGetCacheEntry_Multicast_InvalidEndPoint( void )
{
    NetworkEndPoint_t ** ppxEndPoint = NULL;
    eARPLookupResult_t eResult;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    ( void ) memcpy(xIPAddress.ucBytes, xMultiCastIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdTRUE );
    vSetMultiCastIPv6MacAddress_ExpectAnyArgs();

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, ppxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
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
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucValid = 1;

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, ppxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
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
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    memset( &xEndPoint2, 0, sizeof( NetworkEndPoint_t ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucValid = 1;
    xNDCache[ xUseEntry ].pxEndPoint = &xEndPoint2;
    pxEndPoint = &xEndPoint1;

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xNDCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL_MEMORY( pxEndPoint, &xEndPoint2, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address, ND cache lookup fails with invalid entry.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_InvalidEntry( void )
{
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    (void )memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucValid = 0; /*Invalid Cache entry needs to be skipped */
    pxEndPoint = &xEndPoint;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address & ND cache lookup fails as Entry is valid
 *        but the MAC-address doesn't match.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_NoEntry( void )
{
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucValid = 1; /*Valid Cache entry needs to be skipped */
    pxEndPoint = &xEndPoint;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
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
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    pxEndPoint = &xEndPoint1;
    memcpy( pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, xGatewayIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xGatewayIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucValid = 1; /*Valid Cache entry needs to be skipped */
    /*pxEndPoint = &xEndPoint; */
    memcpy( xIPAddress.ucBytes, xSiteLocalIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( &xEndPoint1 );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &xEndPoint2 );

    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
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
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    pxEndPoint = &xEndPoint1;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xGatewayIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucValid = 1; /*Valid Cache entry needs to be skipped */
    /*pxEndPoint = &xEndPoint; */
    memcpy( xIPAddress.ucBytes, xSiteLocalIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( &xEndPoint1 );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &xEndPoint2 );

    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
}

/**
 * @brief This function can't find the MAC-address of an IPv6 address when
 *        there is a Cache miss and gateway has no entry in the cache.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_NoEP( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) ;
    xNDCache[ xUseEntry ].ucValid = 1; /*Valid Cache entry needs to be skipped */
    pxEndPoint = &xEndPoint;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( NULL );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
}

/*
 * ===================================================
 *           Test for vNDRefreshCacheEntry
 * ===================================================
 */

/**
 * @brief This function veriifed that the ip address was not found on ND cache
 *        and there was no free space to store the New Entry, hence the
 *        IP-address, MAC-address and an end-point combination was not stored.
 */

void test_vNDRefreshCacheEntry_NoMatchingEntry_CacheFull( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    int i;

    memset( xIPAddress.ucBytes, 0, ipSIZE_OF_IPv6_ADDRESS );
    /* Filling the ND cache with non matching IP/MAC combination */
    for( i = 0; i < ipconfigND_CACHE_ENTRIES; i++ ) 
    {
        memcpy( xNDCache[ i ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
        xNDCache[ i ].ucAge = 255;
        xNDCache[ i ].ucValid = pdTRUE;
    }

    /* Pass a NULL IP address which will not match.*/
    vNDRefreshCacheEntry( &xMACAddress, &xIPAddress, &xEndPoint );
}


/**
 * @brief This function veriifed that the ip address was not found on ND cache
 *        and there was space to store the New Entry, hence the IP-address, 
 *        MAC-address and an end-point combination was stored in that location.
 */

void test_vNDRefreshCacheEntry_NoMatchingEntry_Add( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 0;

    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    ( void ) memcpy(xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Since no matching entry will be found, 0th entry will be updated to have the below details. */
    vNDRefreshCacheEntry( &xMACAddress, &xIPAddress, &xEndPoint );

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, ( uint8_t ) ipconfigMAX_ARP_AGE );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucValid, pdTRUE );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].pxEndPoint, &xEndPoint, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function veriifed that the ip address was found on ND cache
 *        and the entry was refreshedat the same location.
 */

void test_vNDRefreshCacheEntry_MatchingEntry_Refresh( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1;

    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    ( void ) memcpy(xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy (xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucValid = pdTRUE;

    /* Since a matching entry is found at xUseEntry = 1st location, the entry will be refreshed.*/
    vNDRefreshCacheEntry( &xMACAddress, &xIPAddress, &xEndPoint );

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, ( uint8_t ) ipconfigMAX_ARP_AGE );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].pxEndPoint, &xEndPoint, sizeof( NetworkEndPoint_t ) );
}

/*
 * ===================================================
 *           Test for vNDAgeCache
 * ===================================================
 */

/**
 * @brief This function verifies all invalid cache entry condition.
 */
void test_vNDAgeCache_InvalidCache( void )
{
    int i;

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

    /* Invalidate all cache entry. */
    for( i = 0; i < ipconfigND_CACHE_ENTRIES; i++ )
    {
        xNDCache[ i ].ucAge = 0;
    }
    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucValid = 1;
    memset(&xMACAddress,0,sizeof( MACAddress_t ) );
    memset(&xIPAddress,0,ipSIZE_OF_IPv6_ADDRESS );
    
    memcpy (xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy (xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );

    vNDAgeCache();

    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL(xNDCache[ xUseEntry ].ucAge ,0);
    TEST_ASSERT_EQUAL(xNDCache[ xUseEntry ].ucValid,0);
}

/**
 * @brief This function checks the case when the entry is not yet valid,
 *        then it is waiting an ND advertisement.
 */

void test_vNDAgeCache_InvalidEntry( void )
{
    BaseType_t xUseEntry = 1;

    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );

    //Update Entry one as invalid ucValid = 0
    xNDCache[ xUseEntry ].ucAge = 10;
    xNDCache[ xUseEntry ].ucValid = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    vNDAgeCache();
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

    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    
    //Update Entry one as Valid entry
    xNDCache[ xUseEntry ].ucAge = xAgeDefault;
    xNDCache[ xUseEntry ].ucValid = 1;

    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, xAgeDefault - 1);
}

/**
 * @brief This function handles Sending out an NS request for the IPv6 address,
 *        and fails as Endpoint is NULL.
 */

void test_vNDAgeCache_NS_NULL_EP( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint, *pxEndPoint=NULL;
    BaseType_t xUseEntry = 1, xAgeDefault = 10;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    
    //Update Entry one as Valid entry
    xNDCache[ xUseEntry ].ucAge = xAgeDefault;
    xNDCache[ xUseEntry ].ucValid = 0;
    xNDCache[ xUseEntry ].pxEndPoint = NULL;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );

    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, xAgeDefault - 1);
}

/**
 * @brief This function handles Sending out an NS request for the IPv6 address,
 *        and fails as pxDescriptor is NULL.
 */

void test_vNDAgeCache_NS_Incorrect_DataLen( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1, xAgeDefault = 10;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    
    xNetworkBuffer.xDataLength = xHeaderSize - 1;
    //Update Entry one as Valid entry
    xNDCache[ xUseEntry ].ucAge = xAgeDefault;
    xNDCache[ xUseEntry ].ucValid = 0;
    xNDCache[ xUseEntry ].pxEndPoint = &xEndPoint;
    xEndPoint.bits.bIPv6 = 1;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );

    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    
    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, xAgeDefault - 1);
}

/**
 * @brief This function handles Reducing the age counter in each entry within the ND cache.
 *        Just before getting to zero, 3 times a neighbour solicitation will be sent. It also takes
 *        care of Sending out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 *        add an entry into the ND table that indicates that an ND reply is
 *        outstanding so re-transmissions can be generated.
 */

void test_vNDAgeCache_NS_HappyPath( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1, xAgeDefault = 10;
    NetworkBufferDescriptor_t xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket, *pxICMPPacket = &xICMPPacket;
    ICMPHeader_IPv6_t *pxICMPHeader_IPv6 = &(pxICMPPacket->xICMPHeaderIPv6);
    uint32_t ulPayloadLength = 32U;

    memset( xNDCache, 0, sizeof( NDCacheRow_t ) * ipconfigND_CACHE_ENTRIES );
    
    //Update Entry one as Valid entry
    xNDCache[ xUseEntry ].ucAge = xAgeDefault;
    xNDCache[ xUseEntry ].ucValid = 0;
    xNDCache[ xUseEntry ].pxEndPoint = &xEndPoint;
    xEndPoint.bits.bIPv6 = 1;
    xNetworkBuffer.xDataLength = xHeaderSize;
    xNetworkBuffer.pucEthernetBuffer = &xICMPPacket;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, xAgeDefault - 1);
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucVersionTrafficClass, 0x60 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.usPayloadLength, FreeRTOS_htons( ulPayloadLength ));
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucNextHeader, ipPROTOCOL_ICMP_IPv6);
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucHopLimit, 255);
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfMessage, ipICMP_NEIGHBOR_SOLICITATION_IPv6);
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionType ,ndICMP_SOURCE_LINK_LAYER_ADDRESS);
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionLength , 1U); /* times 8 bytes. */
}

/*
 * ===================================================
 *           Test for FreeRTOS_ClearND
 * ===================================================
 */

/**
 * @brief Clear the Neighbour Discovery cache.
 */
void test_FreeRTOS_ClearND( void )
{
    NDCacheRow_t xTempNDCache[ ipconfigND_CACHE_ENTRIES ];

    /* Set xNDCache to non zero entries*/
    memset(xNDCache, 1, sizeof( xNDCache ));
    memset( xTempNDCache, 0, sizeof( xTempNDCache ));
    FreeRTOS_ClearND();

    TEST_ASSERT_EQUAL_MEMORY( xNDCache, xTempNDCache, sizeof( xNDCache ));
}

/*
 * ===================================================
 *           Test for FreeRTOS_PrintNDCache
 * ===================================================
 */


void test_FreeRTOS_PrintNDCache( void )
{
    BaseType_t xUseEntry = 0;

    memset( xNDCache, 0, sizeof( xNDCache ));
    /* Oth Entry added as a valid Cache Entry to be printed */
    xNDCache[ xUseEntry ].ucValid = 1;

    FreeRTOS_PrintNDCache();
}


/*
 * ===================================================
 *       Test for vNDSendNeighbourSolicitation
 * ===================================================
 */

/**
 * @brief This function Send out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 *        add an entry into the ND table that indicates that an ND reply is
 *        outstanding so re-transmissions can be generated.
 */

void test_vNDSendNeighbourSolicitation_HappyPath( void )
{
    IPv6_Address_t xIPAddress;
    NetworkBufferDescriptor_t xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket, *pxICMPPacket = &xICMPPacket;
    ICMPHeader_IPv6_t *pxICMPHeader_IPv6 = &(pxICMPPacket->xICMPHeaderIPv6);
    NetworkEndPoint_t xEndPoint;
    uint32_t ulPayloadLength = 32U;

    xEndPoint.bits.bIPv6 = 1;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.xDataLength = xHeaderSize;
    xNetworkBuffer.pucEthernetBuffer = &xICMPPacket;
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    vNDSendNeighbourSolicitation( &xNetworkBuffer, &xIPAddress);

    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucVersionTrafficClass, 0x60 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.usPayloadLength, FreeRTOS_htons( ulPayloadLength ));
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucNextHeader, ipPROTOCOL_ICMP_IPv6);
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucHopLimit, 255);
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfMessage, ipICMP_NEIGHBOR_SOLICITATION_IPv6);
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionType ,ndICMP_SOURCE_LINK_LAYER_ADDRESS);
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionLength , 1U); /* times 8 bytes. */
}

/*
 * ===================================================
 *       Test for FreeRTOS_SendPingRequestIPv6
 * ===================================================
 */

/**
 * @brief This function handles NULL Endpoint case
 *        while sending a PING request.
 */

void test_SendPingRequestIPv6_NULL_EP( void )
{
    NetworkEndPoint_t xEndPoint , *pxEndPoint = &xEndPoint;
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


    xReturn = FreeRTOS_SendPingRequestIPv6(&xIPAddress, uxNumberOfBytesToSend, 0);

    TEST_ASSERT_EQUAL( xReturn, pdFAIL);
}

/**
 * @brief This function handles case when we do not
 *        have enough space for the Number of bytes to be send.
 */

void test_SendPingRequestIPv6_IncorectBytesSend( void )
{
    NetworkEndPoint_t xEndPoint ,* pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = ipconfigNETWORK_MTU;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 0U );

    xReturn = FreeRTOS_SendPingRequestIPv6(&xIPAddress, uxNumberOfBytesToSend, 0);

    TEST_ASSERT_EQUAL( xReturn, pdFAIL);
}


/**
 * @brief This function handles failure case when network
 *        buffer returned is NULL.
 */

void test_SendPingRequestIPv6_NULL_Buffer( void )
{
    NetworkEndPoint_t xEndPoint ,* pxEndPoint = &xEndPoint;
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


    xReturn = FreeRTOS_SendPingRequestIPv6(&xIPAddress, uxNumberOfBytesToSend, 0);

    TEST_ASSERT_EQUAL( xReturn, pdFAIL);
}

/**
 * @brief This function handles sending and IPv6 ping request 
 *        and returning the sequence number in case of success.
 */

void test_SendPingRequestIPv6_SendToIP_Pass( void )
{
    NetworkEndPoint_t xEndPoint ,* pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 100;
    BaseType_t xReturn;
    uint16_t usSequenceNumber = 1;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );
    

    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );
    xSendEventStructToIPTask_IgnoreAndReturn( pdPASS );

    xReturn = FreeRTOS_SendPingRequestIPv6(&xIPAddress, uxNumberOfBytesToSend, 0);

    //Returns ping sequence number
    TEST_ASSERT_EQUAL( xReturn, usSequenceNumber);
}

/**
 * @brief This function handles failure case while sending
 *        IPv6 ping request when sending an event to IP task fails.
 */

void test_SendPingRequestIPv6_SendToIP_Fail( void )
{
    NetworkEndPoint_t xEndPoint ,* pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 100;
    BaseType_t xReturn;
    uint16_t usSequenceNumber = 1;

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

    xReturn = FreeRTOS_SendPingRequestIPv6(&xIPAddress, uxNumberOfBytesToSend, 0);

    TEST_ASSERT_EQUAL( xReturn, pdFAIL);
}


/*
 * ===================================================
 *       Test for prvProcessICMPMessage_IPv6
 * ===================================================
 */

/**
 * @brief This function process ICMP message when endpoint is NULL.
 */

void test_prvProcessICMPMessage_IPv6_NULL_EP( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    eFrameProcessingResult_t eReturn;

    pxNetworkBuffer->pxEndPoint = NULL;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_DEST_UNREACHABLE_IPv6.
 */

void test_prvProcessICMPMessage_IPv6_ipICMP_DEST_UNREACHABLE_IPv6( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_DEST_UNREACHABLE_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PACKET_TOO_BIG_IPv6.
 */

void test_prvProcessICMPMessage_IPv6_ipICMP_PACKET_TOO_BIG_IPv6( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PACKET_TOO_BIG_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_TIME_EXEEDED_IPv6.
 */

void test_prvProcessICMPMessage_IPv6_ipICMP_TIME_EXEEDED_IPv6( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_TIME_EXEEDED_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PARAMETER_PROBLEM_IPv6.
 */

void test_prvProcessICMPMessage_IPv6_ipICMP_PARAMETER_PROBLEM_IPv6( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PARAMETER_PROBLEM_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_ROUTER_SOLICITATION_IPv6.
 */

void test_prvProcessICMPMessage_IPv6_ipICMP_ROUTER_SOLICITATION_IPv6( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_ROUTER_ADVERTISEMENT_IPv6.
 */

void test_prvProcessICMPMessage_IPv6_ipICMP_ROUTER_ADVERTISEMENT_IPv6( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_ADVERTISEMENT_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REQUEST_IPv6 but the data size is incorrect.
 */

void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REQUEST_IPv6_IncorrectSize( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
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
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REQUEST_IPv6.
 */

void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REQUEST_IPv6_CorrectSize( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
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
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REPLY_IPv6.
 *        It handles case where A reply was received to an outgoing
 *        ping but the payload of the reply was not correct.
 */

void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REPLY_IPv6_eInvalidData( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    ICMPEcho_IPv6_t * pxICMPEchoHeader = ( ( const ICMPEcho_IPv6_t * ) pxICMPHeader_IPv6 );
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
    pxNetworkBuffer->xDataLength = uxICMPSize;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    vApplicationPingReplyHook_Expect(eInvalidData, pxICMPEchoHeader->usIdentifier);

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REPLY_IPv6.
 *        It handles case where A reply was received to an outgoing
 *        ping but the payload of the reply was not correct.
 */
//TODO
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REPLY_IPv6_eSuccess( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    ICMPEcho_IPv6_t * pxICMPEchoHeader = ( ( const ICMPEcho_IPv6_t * ) pxICMPHeader_IPv6 );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    size_t uxICMPSize, uxNeededSize;
    uint16_t usICMPSize;
    uint8_t ucBuffer[sizeof(ICMPPacket_IPv6_t) + ipBUFFER_PADDING ];

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    xICMPPacket.xIPHeader.usPayloadLength = ipBUFFER_PADDING;
    usICMPSize = FreeRTOS_ntohs( xICMPPacket.xIPHeader.usPayloadLength );
    uxICMPSize = ( size_t ) usICMPSize;
    uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
    /* Assign less size than expected */
    pxNetworkBuffer->xDataLength = uxICMPSize;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    //vApplicationPingReplyHook_Expect(eSuccess, pxICMPEchoHeader->usIdentifier);

   // eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

   // TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_SOLICITATION_IPv6.
 *        It handles case where endpoint was not found on the network.
 */

void test_prvProcessICMPMessage_IPv6_NEIGHBOR_SOLICITATION_NULL_EP( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_SOLICITATION_IPv6.
 *        It handles case where when data length is less than
 *        expected.
 */

void test_prvProcessICMPMessage_IPv6_NEIGHBOR_SOLICITATION_InorrectLen( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->xDataLength = 0;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( &xEndPoint );

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}


/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_SOLICITATION_IPv6.
 *        It handles case where when data length is less than
 *        expected.
 */

void test_prvProcessICMPMessage_IPv6_NEIGHBOR_SOLICITATION_IncorrectLen( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->xDataLength = xHeaderSize + ipBUFFER_PADDING;
    
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( &xEndPoint );

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_SOLICITATION_IPv6.
 *        It handles case where the ICMP header address does not
 *        match which means the message is not for us, 
 *        ignore it.
 */

void test_prvProcessICMPMessage_IPv6_NEIGHBOR_SOLICITATION( void)
{
    NetworkBufferDescriptor_t xNetworkBuffer, *pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxICMPHeader_IPv6->ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->xDataLength = xHeaderSize + ipBUFFER_PADDING;
    memcpy(pxICMPHeader_IPv6->xIPv6Address.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy(xEndPoint.ipv6_settings.xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy(xEndPoint.xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( &xEndPoint );

    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6(pxNetworkBuffer);

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer);
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfMessage, ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6);
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfService, 0U);
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionType, ndICMP_TARGET_LINK_LAYER_ADDRESS);
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionLength, 1U );
    TEST_ASSERT_EQUAL_MEMORY(pxICMPHeader_IPv6->ucOptionBytes, xEndPoint.xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xICMPPacket.xIPHeader.ucHopLimit, 255U);
                     

}