/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_task.h"
#include "mock_NetworkBufferManagement.h"

#include "FreeRTOS_ARP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

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


void test_vARPRefreshCacheEntry( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;

    #if 1
        /* =================================================== */
        for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
        {
            xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
            xARPCache[ i ].ucAge = 255;
            xARPCache[ i ].ucValid = pdTRUE;
        }

        ulIPAddress = 0x00;
        /* Pass a NULL MAC Address and an IP address which will not match. */
        vARPRefreshCacheEntry( NULL, ulIPAddress );

        /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
        TEST_ASSERT_EQUAL( xARPCache[ 0 ].ucAge, ( uint8_t ) ipconfigMAX_ARP_RETRANSMISSIONS );
        TEST_ASSERT_EQUAL( xARPCache[ 0 ].ucValid, ( uint8_t ) pdFALSE );
        /* =================================================== */

        /* =================================================== */
        for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
        {
            xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
            xARPCache[ i ].ucAge = 255;
            xARPCache[ i ].ucValid = pdTRUE;
        }

        xARPCache[ 1 ].ulIPAddress = 0xAABBCCEE;

        ulIPAddress = 0xAABBCCEE;
        /* Pass a NULL MAC Address and an IP address which will match. */
        vARPRefreshCacheEntry( NULL, ulIPAddress );

        /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
        TEST_ASSERT_EQUAL( xARPCache[ 1 ].ucAge, 255 );
        TEST_ASSERT_EQUAL( xARPCache[ 1 ].ucValid, ( uint8_t ) pdTRUE );
        /* =================================================== */

        /* =================================================== */
        for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
        {
            xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
            xARPCache[ i ].ucAge = 255;
            xARPCache[ i ].ucValid = pdTRUE;
        }

        xUseEntry = 1;
        xARPCache[ xUseEntry ].ulIPAddress = 0xAABBCCEE;

        ulIPAddress = 0xAABBCCEE;
        memset( xMACAddress.ucBytes, 0x11, ipMAC_ADDRESS_LENGTH_BYTES );
        /* Pass a MAC Address which won't match and an IP address which will match. */
        vARPRefreshCacheEntry( &xMACAddress, ulIPAddress );

        /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
        TEST_ASSERT_EQUAL( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry ].ucAge );
        TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry ].ucValid );
        TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xARPCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( xMACAddress.ucBytes ) );
        /* =================================================== */

        /* =================================================== */
        for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
        {
            xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
            xARPCache[ i ].ucAge = 255;
            xARPCache[ i ].ucValid = pdFALSE;
        }

        xUseEntry = 1;
        xARPCache[ xUseEntry ].ulIPAddress = 0xAABBCCEE;
        /* Set a MAC address which will match */
        memset( xARPCache[ xUseEntry ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );

        ulIPAddress = 0xAABBCCEE;
        memset( xMACAddress.ucBytes, 0x11, ipMAC_ADDRESS_LENGTH_BYTES );
        /* Pass a MAC Address which will match and an IP address which will match too. */
        vARPRefreshCacheEntry( &xMACAddress, ulIPAddress );

        /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
        TEST_ASSERT_EQUAL( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry ].ucAge );
        TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry ].ucValid );
        TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xARPCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( xMACAddress.ucBytes ) );
        /* =================================================== */

        /* =================================================== */
        for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
        {
            xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
            xARPCache[ i ].ucAge = 255;
            xARPCache[ i ].ucValid = pdFALSE;
            memset( xARPCache[ i ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
        }

        xUseEntry = 0;

        ulIPAddress = 0xAABBCCEE;
        memset( xMACAddress.ucBytes, 0x22, ipMAC_ADDRESS_LENGTH_BYTES );
        /* Pass a MAC and IP Address which won't match. */
        vARPRefreshCacheEntry( &xMACAddress, ulIPAddress );

        /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
        TEST_ASSERT_EQUAL( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry ].ucAge );
        TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry ].ucValid );
        TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xARPCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( xMACAddress.ucBytes ) );
        /* =================================================== */

        /* =================================================== */
        for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
        {
            xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
            xARPCache[ i ].ucAge = 255;
            xARPCache[ i ].ucValid = pdFALSE;
            memset( xARPCache[ i ].xMACAddress.ucBytes, 0x22, sizeof( xMACAddress.ucBytes ) );
        }

        xUseEntry = 1;

        /* Set a MAC address which will match */
        memset( xARPCache[ xUseEntry ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );

        ulIPAddress = 0xAABBCCEE;
        memset( xMACAddress.ucBytes, 0x11, ipMAC_ADDRESS_LENGTH_BYTES );
        /* Pass a MAC Address which will match and an IP address which won't match. */
        vARPRefreshCacheEntry( &xMACAddress, ulIPAddress );

        /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
        TEST_ASSERT_EQUAL( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry ].ucAge );
        TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry ].ucValid );
        TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xARPCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( xMACAddress.ucBytes ) );
        /* =================================================== */
    #endif /* if 1 */

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = i + 1;
        xARPCache[ i ].ucValid = pdFALSE;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    }

    xUseEntry = 0;

    ulIPAddress = 0xAABBCCEE;
    memset( xMACAddress.ucBytes, 0x22, ipMAC_ADDRESS_LENGTH_BYTES );
    /* Pass a MAC and IP Address which won't match, but age is now a factor. */
    vARPRefreshCacheEntry( &xMACAddress, ulIPAddress );

    /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
    TEST_ASSERT_EQUAL( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry ].ucAge );
    TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry ].ucValid );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xARPCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( xMACAddress.ucBytes ) );
    /* =================================================== */

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = i + 1;
        xARPCache[ i ].ucValid = pdFALSE;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    }

    xUseEntry = 0;

    /* Make sure an entry matches. */
    xARPCache[ xUseEntry ].ulIPAddress = 0xAABBCCEE;
    ulIPAddress = 0xAABBCCEE;

    /* Also make sure that a MAC address matches. But a different one. */
    memset( xARPCache[ xUseEntry + 1 ].xMACAddress.ucBytes, 0x22, sizeof( xMACAddress.ucBytes ) );
    memset( xMACAddress.ucBytes, 0x22, ipMAC_ADDRESS_LENGTH_BYTES );

    /* Pass a MAC and IP Address which won't match, but age is now a factor. */
    vARPRefreshCacheEntry( &xMACAddress, ulIPAddress );

    /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
    TEST_ASSERT_EQUAL( xARPCache[ xUseEntry + 1 ].ulIPAddress, ulIPAddress );
    TEST_ASSERT_EQUAL( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry + 1 ].ucAge );
    TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry + 1 ].ucValid );

    uint8_t MemoryCompare[ sizeof( ARPCacheRow_t ) ];
    memset( MemoryCompare, 0, sizeof( ARPCacheRow_t ) );
    TEST_ASSERT_EQUAL_MEMORY( MemoryCompare, &xARPCache[ xUseEntry ], sizeof( ARPCacheRow_t ) );
    /* =================================================== */
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
    uint32_t ulSavedGatewayAddress;

    /* =================================================== */
    ulIPAddress = 0x1234;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 1UL );
    vSetMultiCastIPv4MacAddress_Ignore();
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 1" );
    /* =================================================== */

    /* =================================================== */
    ulIPAddress = ipBROADCAST_IP_ADDRESS;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 2" );
    TEST_ASSERT_EQUAL_MEMORY_MESSAGE( &xBroadcastMACAddress, &xMACAddress, sizeof( xMACAddress ), "Test 2" );
    /* =================================================== */

    /* =================================================== */
    ulIPAddress = xNetworkAddressing.ulBroadcastAddress;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 3" );
    TEST_ASSERT_EQUAL_MEMORY_MESSAGE( &xBroadcastMACAddress, &xMACAddress, sizeof( xMACAddress ), "Test 3" );
    /* =================================================== */

    /* =================================================== */
    *ipLOCAL_IP_ADDRESS_POINTER = 0;
    ulIPAddress = 0x1234;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eCantSendPacket, eResult, "Test 4" );
    /* =================================================== */

    /* =================================================== */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    ulIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 5" );
    /* =================================================== */

    /* =================================================== */
    ulIPAddress = 0x4321;
    /* Make both values (IP address and local IP pointer) different. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    /* Add the IP address in the cache so that we'll have a cache hit. */
    xARPCache[ 1 ].ulIPAddress = xNetworkAddressing.ulGatewayAddress;
    /* But reset the valid bit. */
    xARPCache[ 1 ].ucValid = pdFALSE;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eCantSendPacket, eResult, "Test 6" );
    /* =================================================== */

    /* =================================================== */
    ulIPAddress = 0x4321;
    /* Make both values (IP address and local IP pointer) different. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    /* Add the IP address in the cache so that we'll have a cache hit. */
    xARPCache[ 1 ].ulIPAddress = xNetworkAddressing.ulGatewayAddress;
    /* Now try with a set valid bit. */
    xARPCache[ 1 ].ucValid = pdTRUE;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 7" );
    TEST_ASSERT_EQUAL_MEMORY_MESSAGE( &xARPCache[ 1 ].xMACAddress, &xMACAddress, sizeof( xMACAddress ), "Test 7" );
    /* =================================================== */

    /* =================================================== */
    for( int i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ucValid = ( uint8_t ) pdFALSE;
    }

    ulSavedGatewayAddress = xNetworkAddressing.ulGatewayAddress;
    xNetworkAddressing.ulGatewayAddress = 0;
    /* Make IP address param == 0 */
    ulIPAddress = 0;
    /* Make both values (IP address and local IP pointer) different. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    xNetworkAddressing.ulGatewayAddress = ulSavedGatewayAddress;
    TEST_ASSERT_EQUAL_MESSAGE( eCantSendPacket, eResult, "Test 8" );
    /* =================================================== */

    /* =================================================== */
    ulSavedGatewayAddress = xNetworkAddressing.ulGatewayAddress;
    xNetworkAddressing.ulGatewayAddress = 0;
    ulIPAddress = 0x4321;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    xNetworkAddressing.ulGatewayAddress = ulSavedGatewayAddress;
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheMiss, eResult, "Test 9" );
    /* =================================================== */

    /* =================================================== */
    /* Make both values (IP address and local IP pointer) different. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    /* Get any address on the same netmask. */
    ulIPAddress = ( ( *ipLOCAL_IP_ADDRESS_POINTER ) & xNetworkAddressing.ulNetMask ) + 10;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheMiss, eResult, "Test 10" );
    /* =================================================== */

    /* =================================================== */
    ulIPAddress = 0;
    /* Make both values (IP address and local IP pointer) different. */
    /* Get any address on the same netmask. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x00000034;

    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eCantSendPacket, eResult, "Test 11" );
    /* =================================================== */
}

void test_vARPAgeCache( void )
{
    /* Invalidate the first cache entry. */
    for( int i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ucAge = 0;
    }

    uint8_t ucEntryToCheck = 1;

    /* =================================================== */
    /* Make second entry invlid but with age > 1. */
    xARPCache[ ucEntryToCheck ].ucAge = 1;
    xARPCache[ ucEntryToCheck ].ucValid = pdFALSE;
    /* Set an IP address */
    xARPCache[ ucEntryToCheck ].ulIPAddress = 0xAAAAAAAA;

    /* The function which calls 'pxGetNetworkBufferWithDescriptor' is 'FreeRTOS_OutputARPRequest'.
     * It doesn't return anything and will be tested separately. */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );

    /* Let the value returned first time be 100. */
    xTaskGetTickCount_IgnoreAndReturn( 100 );
    vARPAgeCache();
    /* =================================================== */

    /* =================================================== */
    /* Make second entry invlid but with age > 1. */
    xARPCache[ ucEntryToCheck ].ucAge = 1;
    xARPCache[ ucEntryToCheck ].ucValid = pdTRUE;
    /* Set an IP address */
    xARPCache[ ucEntryToCheck ].ulIPAddress = 0xAAAAAAAA;

    /* The function which calls 'pxGetNetworkBufferWithDescriptor' is 'FreeRTOS_OutputARPRequest'.
     * It doesn't return anything and will be tested separately. */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );

    /* Let the value returned second time be 100. */
    xTaskGetTickCount_IgnoreAndReturn( 100 );
    vARPAgeCache();
    /* =================================================== */

    /* =================================================== */
    /* Make second entry invlid but with age > 1. */
    xARPCache[ ucEntryToCheck ].ucAge = 100;
    xARPCache[ ucEntryToCheck ].ucValid = pdTRUE;
    /* Set an IP address */
    xARPCache[ ucEntryToCheck ].ulIPAddress = 0xAAAAAAAA;

    /* This time the pxGetNetworkBuffer will not be called. */
    /* Let the value returned third time as well 100. */
    xTaskGetTickCount_IgnoreAndReturn( 100 );
    vARPAgeCache();
    /* =================================================== */
}

void test_vARPSendGratuitous( void )
{
    /* The output is ignored. But we should check the input though. */
    xSendEventToIPTask_ExpectAndReturn( eARPTimerEvent, 0 );
    vARPSendGratuitous();
}

void test_FreeRTOS_OutputARPRequest( void )
{
    uint8_t ucBuffer[ sizeof( ARPPacket_t ) + ipBUFFER_PADDING + ipconfigETHERNET_MINIMUM_PACKET_BYTES ];
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulIPAddress = 0xAAAAAAAA;

    xNetworkBuffer.pucEthernetBuffer = ucBuffer;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );

    /* =================================================== */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, &xNetworkBuffer );
    xIsCallingFromIPTask_IgnoreAndReturn( pdTRUE );
    FreeRTOS_OutputARPRequest( ulIPAddress );
    /* =================================================== */

    /* =================================================== */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, &xNetworkBuffer );
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    xSendEventStructToIPTask_IgnoreAndReturn( pdFALSE );
    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    FreeRTOS_OutputARPRequest( ulIPAddress );
}


void vStoreTimeValue( TimeOut_t * const timeout,
                      int32_t callbacks )
{
    timeout->xOverflowCount = 0;
    timeout->xTimeOnEntering = 100;
}

void test_xARPWaitResolution( void )
{
    uint32_t ulIPAddress = 0xAAAAAAAA;
    BaseType_t xResult;
    int i;

    /* Catch the assertion for calling from IP task. */
    /* =================================================== */
    /* Assertion on calling from IP-task */
    xIsCallingFromIPTask_IgnoreAndReturn( pdTRUE );
    catch_assert( xARPWaitResolution( ulIPAddress, 0 ) );
    /* =================================================== */


    /* Make the resolution pass without any attempt by making
     * eARPGetCacheEntry return eARPCacheHit. */
    /* =================================================== */
    /* Assertion on calling from IP-task */
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 1UL );
    vSetMultiCastIPv4MacAddress_Ignore();
    xResult = xARPWaitResolution( ulIPAddress, 0 );
    TEST_ASSERT_EQUAL( xResult, 0 );
    /* =================================================== */

    /* Make the resolution fail with maximum tryouts. */
    /* =================================================== */
    /* Make sure that no address matches the IP address. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAAAAAAAA;
    }

    ulIPAddress = 0x00000031;
    /* Make both values (IP address and local IP pointer) different. */
    /* Get any address on the same netmask. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x00000034;

    /* Assertion on calling from IP-task */
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );

    vTaskSetTimeOutState_Stub( vStoreTimeValue );

    /* Make sure that there are enough stubs for all the repititive calls. */
    for( i = 0; i < ipconfigMAX_ARP_RETRANSMISSIONS; i++ )
    {
        pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
        vTaskDelay_Expect( pdMS_TO_TICKS( 250U ) );
        xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
        xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    }

    xResult = xARPWaitResolution( ulIPAddress, 0 );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRNOTAVAIL, xResult );
    /* =================================================== */

    /* Make the resolution fail after some attempts due to timeout. */
    /* =================================================== */
    /* Make sure that no address matches the IP address. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAAAAAAAA;
    }

    ulIPAddress = 0x00000031;
    /* Make both values (IP address and local IP pointer) different. */
    /* Get any address on the same netmask. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x00000034;

    /* Assertion on calling from IP-task */
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    /* Make eARPGetCacheEntry return a cache miss. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );

    vTaskSetTimeOutState_Stub( vStoreTimeValue );

    /* Make sure that there are enough stubs for all the repititive calls. */
    for( i = 0; i < ( ipconfigMAX_ARP_RETRANSMISSIONS - 1 ); i++ )
    {
        pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
        vTaskDelay_Expect( pdMS_TO_TICKS( 250U ) );
        xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
        xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    }

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
    vTaskDelay_Expect( pdMS_TO_TICKS( 250U ) );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );

    xResult = xARPWaitResolution( ulIPAddress, 0 );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRNOTAVAIL, xResult );
    /* =================================================== */

    /* Make the resolution pass after some attempts. */
    /* =================================================== */
    /* Make sure that no address matches the IP address. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAAAAAAAA;
    }

    ulIPAddress = 0x00000031;
    /* Make both values (IP address and local IP pointer) different. */
    /* Get any address on the same netmask. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x00000034;

    /* Assertion on calling from IP-task */
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );

    vTaskSetTimeOutState_Stub( vStoreTimeValue );

    /* Make sure that there are enough stubs for all the repititive calls. */
    for( i = 0; i < ( ipconfigMAX_ARP_RETRANSMISSIONS - 2 ); i++ )
    {
        pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
        vTaskDelay_Expect( pdMS_TO_TICKS( 250U ) );
        xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
        xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    }

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
    vTaskDelay_Expect( pdMS_TO_TICKS( 250U ) );
    /* Make eARPGetCacheEntry succeed. That is - make it return eARPCacheHit */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 1UL );
    vSetMultiCastIPv4MacAddress_Ignore();

    /* Make sure that there is no timeout. */
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );

    xResult = xARPWaitResolution( ulIPAddress, 0 );
    TEST_ASSERT_EQUAL( 0, xResult );
    /* =================================================== */
}

void test_vARPGenerateRequestPacket( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( ARPPacket_t ) + ipBUFFER_PADDING ];

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( ARPPacket_t );

    /* Catch some asserts. */
    catch_assert( vARPGenerateRequestPacket( NULL ) );

    pxNetworkBuffer->xDataLength = sizeof( ARPPacket_t ) - 10;
    catch_assert( vARPGenerateRequestPacket( pxNetworkBuffer ) );

    pxNetworkBuffer->xDataLength = sizeof( ARPPacket_t );
    vARPGenerateRequestPacket( pxNetworkBuffer );
}


void test_FreeRTOS_ClearARP( void )
{
    uint8_t ucArray[ sizeof( xARPCache ) ];

    memset( ucArray, 0, sizeof( xARPCache ) );

    FreeRTOS_ClearARP();
    TEST_ASSERT_EQUAL_MEMORY( ucArray, xARPCache, sizeof( xARPCache ) );
}


void test_xCheckLoopback( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    BaseType_t xResult;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( IPPacket_t );

    IPPacket_t * pxIPPacket = ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );

    /* =================================================== */
    /* Let the frame-type be anything else than IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE + 1;
    /* bReleaseAfterSend parameter doesn't matter here. */
    xResult = xCheckLoopback( pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );
    /* =================================================== */

    /* =================================================== */
    /* Let the frame-type be IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* But let the MAC address be different. */
    memset( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, 0xAA, ipMAC_ADDRESS_LENGTH_BYTES );
    /* bReleaseAfterSend parameter doesn't matter here. */
    xResult = xCheckLoopback( pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );
    /* =================================================== */

    /* =================================================== */
    /* Let the frame-type be IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* Make the MAC address same. */
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipLOCAL_MAC_ADDRESS, ipMAC_ADDRESS_LENGTH_BYTES );

    xSendEventStructToIPTask_IgnoreAndReturn( pdFALSE );
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    xResult = xCheckLoopback( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    /* =================================================== */

    /* =================================================== */
    resetTest();
    /* Let the frame-type be IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* Make the MAC address same. */
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipLOCAL_MAC_ADDRESS, ipMAC_ADDRESS_LENGTH_BYTES );

    xSendEventStructToIPTask_IgnoreAndReturn( pdTRUE );

    xResult = xCheckLoopback( pxNetworkBuffer, pdFALSE );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    /* =================================================== */
}

void test_FreeRTOS_PrintARPCache( void )
{
    int x;

    for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        /* Anything except 0. */
        xARPCache[ x ].ulIPAddress = 0xAA;
        /* Anything except 0. */
        xARPCache[ x ].ucAge = 1;
    }

    /* Nothing to actually unit-test here. */
    FreeRTOS_PrintARPCache();
}
