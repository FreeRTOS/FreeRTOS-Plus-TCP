/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* FreeRTOS includes */
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

/* Include header file(s) which have declaration
 * of functions under test */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"

#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_IP.h"

#include "FreeRTOS_IP_Private.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_ARP_stubs.c"

#include "catch_assert.h"

#define ARPCacheEntryToCheck    2

#if ARPCacheEntryToCheck >= ipconfigARP_CACHE_ENTRIES
    #error "ARPCacheEntryToCheck cannot be greater than ipconfigARP_CACHE_ENTRIES"
#endif

extern ARPCacheRow_t xARPCache[ ipconfigARP_CACHE_ENTRIES ];

void FillARPCache( void )
{
    int i, j;

    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        for( j = 0; j < ipMAC_ADDRESS_LENGTH_BYTES; j++ )
        {
            xARPCache[ i ].xMACAddress.ucBytes[ j ] = i * 10 + j;
        }

        xARPCache[ i ].ulIPAddress = i;
    }
}

void test_ulARPRemoveCacheEntryByMac_RemoveNormalEntry( void )
{
    int32_t lResult;
    uint8_t offset = ARPCacheEntryToCheck * 10;
    const MACAddress_t pxMACAddress = { offset + 0, offset + 1, offset + 2, offset + 3, offset + 4, offset + 5 };

    FillARPCache();

    lResult = ulARPRemoveCacheEntryByMac( &pxMACAddress );

    TEST_ASSERT_EQUAL( lResult, ARPCacheEntryToCheck );
}

void test_ulARPRemoveCacheEntryByMac_RemoveAbsentEntry( void )
{
    int32_t lResult;
    uint8_t offset = ARPCacheEntryToCheck * 10;
    const MACAddress_t pxMACAddress = { offset + 6, offset + 7, offset + 8, offset + 9, offset + 10, offset + 11 };

    FillARPCache();

    lResult = ulARPRemoveCacheEntryByMac( &pxMACAddress );

    TEST_ASSERT_EQUAL( lResult, 0 );
}


void test_ulARPRemoveCacheEntryByMac_UseNULLPointer( void )
{
    /* We expect this test to call ASSERT. */
    catch_assert( ulARPRemoveCacheEntryByMac( NULL ) );
}


void test_eARPGetCacheEntryByMac_GetNormalEntry( void )
{
    uint32_t ulIPPointer = 12345;
    eARPLookupResult_t xResult;
    uint8_t offset = ARPCacheEntryToCheck * 10;
    MACAddress_t xMACAddress = { offset + 0, offset + 1, offset + 2, offset + 3, offset + 4, offset + 5 };
    MACAddress_t * const pxMACAddress = &xMACAddress;

    FillARPCache();

    xResult = eARPGetCacheEntryByMac( pxMACAddress, &ulIPPointer );

    TEST_ASSERT_EQUAL( xResult, eARPCacheHit );
    TEST_ASSERT_EQUAL( ulIPPointer, ARPCacheEntryToCheck );
}

void test_eARPGetCacheEntryByMac_GetAbsentEntry( void )
{
    uint32_t ulIPPointer = 12345;
    eARPLookupResult_t xResult;
    uint8_t offset = ARPCacheEntryToCheck * 10;
    MACAddress_t xMACAddress = { offset + 5, offset + 4, offset + 3, offset + 2, offset + 1, offset + 0 };
    MACAddress_t * const pxMACAddress = &xMACAddress;

    FillARPCache();

    xResult = eARPGetCacheEntryByMac( pxMACAddress, &ulIPPointer );

    TEST_ASSERT_EQUAL( xResult, eARPCacheMiss );
    TEST_ASSERT_EQUAL( ulIPPointer, 12345 );
}

void test_eARPGetCacheEntryByMac_UseNULLPointer( void )
{
    uint32_t * ulIPPointer = NULL;
    MACAddress_t * const pxMACAddress = NULL;

    /* Expect this test to hit an ASSERT. */
    catch_assert( eARPGetCacheEntryByMac( pxMACAddress, ulIPPointer ) );
}

void test_eARPGetCacheEntry( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;

    {
        ulIPAddress = 0x1234;
        /* Not worried about what these functions do. */
        xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 1UL );
        vSetMultiCastIPv4MacAddress_Ignore();
        eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
        TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    }

    {
        ulIPAddress = ipBROADCAST_IP_ADDRESS;
        /* Not worried about what these functions do. */
        xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
        eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
        TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
        TEST_ASSERT_EQUAL_MEMORY( &xBroadcastMACAddress, &xMACAddress, sizeof( xMACAddress ) );
    }

    ulIPAddress = xNetworkAddressing.ulBroadcastAddress;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( &xBroadcastMACAddress, &xMACAddress, sizeof( xMACAddress ) );

    *ipLOCAL_IP_ADDRESS_POINTER = 0;
    ulIPAddress = 0x1234;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eCantSendPacket, eResult );

    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    ulIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );

    ulIPAddress = 0x4321;
    /* Add the IP address in the cache so that we'll have a cache hit. */
    xARPCache[ 1 ].ulIPAddress = xNetworkAddressing.ulGatewayAddress;
    /* But reset the valid bit. */
    xARPCache[ 1 ].ucValid = pdFALSE;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eCantSendPacket, eResult );

    /* Now try with a set valid bit. */
    xARPCache[ 1 ].ucValid = pdTRUE;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( &xARPCache[ 1 ].xMACAddress, &xMACAddress, sizeof( xMACAddress ) );

    uint32_t ulSavedGatewayAddress = xNetworkAddressing.ulGatewayAddress;
    xNetworkAddressing.ulGatewayAddress = 0;
    ulIPAddress = 0;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    xNetworkAddressing.ulGatewayAddress = ulSavedGatewayAddress;
    TEST_ASSERT_EQUAL( eCantSendPacket, eResult );

    ulSavedGatewayAddress = xNetworkAddressing.ulGatewayAddress;
    xNetworkAddressing.ulGatewayAddress = 0;
    ulIPAddress = 0x4321;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    xNetworkAddressing.ulGatewayAddress = ulSavedGatewayAddress;
    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );

    /* Get any address on the same netmask. */
    ulIPAddress = ( ( *ipLOCAL_IP_ADDRESS_POINTER ) & xNetworkAddressing.ulNetMask ) + 10;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
}
