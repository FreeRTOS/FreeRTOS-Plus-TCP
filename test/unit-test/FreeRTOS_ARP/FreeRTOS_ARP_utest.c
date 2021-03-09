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
    uint32_t ulSavedGatewayAddress;

    /* =================================================== */
    ulIPAddress = 0x1234;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 1UL );
    vSetMultiCastIPv4MacAddress_Ignore();
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    /* =================================================== */

    /* =================================================== */
    ulIPAddress = ipBROADCAST_IP_ADDRESS;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( &xBroadcastMACAddress, &xMACAddress, sizeof( xMACAddress ) );
    /* =================================================== */

    /* =================================================== */
    ulIPAddress = xNetworkAddressing.ulBroadcastAddress;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( &xBroadcastMACAddress, &xMACAddress, sizeof( xMACAddress ) );
    /* =================================================== */

    /* =================================================== */
    *ipLOCAL_IP_ADDRESS_POINTER = 0;
    ulIPAddress = 0x1234;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eCantSendPacket, eResult );
    /* =================================================== */

    /* =================================================== */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    ulIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
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
    TEST_ASSERT_EQUAL( eCantSendPacket, eResult );
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
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( &xARPCache[ 1 ].xMACAddress, &xMACAddress, sizeof( xMACAddress ) );
    /* =================================================== */

    /* =================================================== */
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
    TEST_ASSERT_EQUAL( eCantSendPacket, eResult );
    /* =================================================== */

    /* =================================================== */
    ulSavedGatewayAddress = xNetworkAddressing.ulGatewayAddress;
    xNetworkAddressing.ulGatewayAddress = 0;
    ulIPAddress = 0x4321;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    xNetworkAddressing.ulGatewayAddress = ulSavedGatewayAddress;
    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
    /* =================================================== */

    /* =================================================== */
    /* Make both values (IP address and local IP pointer) different. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    /* Get any address on the same netmask. */
    ulIPAddress = ( ( *ipLOCAL_IP_ADDRESS_POINTER ) & xNetworkAddressing.ulNetMask ) + 10;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
    /* =================================================== */
    
    /* =================================================== */
    ulIPAddress = 0;
    /* Make both values (IP address and local IP pointer) different. */
    /* Get any address on the same netmask. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x00000034;
    
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL( eCantSendPacket, eResult );
    /* =================================================== */
}

void test_vARPAgeCache( void )
{
    /* Invalidate the first cache entry. */
    for( int i=0; i< ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[i].ucAge = 0;
    }
    
    uint8_t ucEntryToCheck = 1;
    
    /* =================================================== */
    /* Make second entry invlid but with age > 1. */
    xARPCache[ucEntryToCheck].ucAge = 1;
    xARPCache[ucEntryToCheck].ucValid = pdFALSE;
    /* Set an IP address */
    xARPCache[ucEntryToCheck].ulIPAddress = 0xAAAAAAAA;
    /* The function which calls 'pxGetNetworkBufferWithDescriptor' is 'FreeRTOS_OutputARPRequest'.
     * It doesn't return anything and will be tested separately. */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
    
    /* Let the value returned first time be 100. */
    xTaskGetTickCount_IgnoreAndReturn(100);
    vARPAgeCache();
    /* =================================================== */
    
    /* =================================================== */
    /* Make second entry invlid but with age > 1. */
    xARPCache[ucEntryToCheck].ucAge = 1;
    xARPCache[ucEntryToCheck].ucValid = pdTRUE;
    /* Set an IP address */
    xARPCache[ucEntryToCheck].ulIPAddress = 0xAAAAAAAA;
    /* The function which calls 'pxGetNetworkBufferWithDescriptor' is 'FreeRTOS_OutputARPRequest'.
     * It doesn't return anything and will be tested separately. */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
    
    /* Let the value returned second time be 100. */
    xTaskGetTickCount_IgnoreAndReturn(100);
    vARPAgeCache();
    /* =================================================== */
    
    /* =================================================== */
    /* Make second entry invlid but with age > 1. */
    xARPCache[ucEntryToCheck].ucAge = 100;
    xARPCache[ucEntryToCheck].ucValid = pdTRUE;
    /* Set an IP address */
    xARPCache[ucEntryToCheck].ulIPAddress = 0xAAAAAAAA;
    
    /* This time the pxGetNetworkBuffer will not be called. */
    /* Let the value returned third time as well 100. */
    xTaskGetTickCount_IgnoreAndReturn(100);
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


void vStoreTimeValue( TimeOut_t * const timeout, int32_t callbacks )
{
    timeout->xOverflowCount = 0;
    timeout->xTimeOnEntering = 100;
}

void test_xARPWaitResolution( void)
{
    uint32_t ulIPAddress = 0xAAAAAAAA;
    BaseType_t xResult;
    int i;
    
    /* =================================================== */
    /* Make eARPGetCacheEntry return eARPCacheHit. */
    /* Assertion on calling from IP-task */
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 1UL );
    vSetMultiCastIPv4MacAddress_Ignore();
    xResult = xARPWaitResolution( ulIPAddress,0 );
    TEST_ASSERT_EQUAL(xResult,0);
    /* =================================================== */
    
    /* =================================================== */
    /* Make sure that no address matches the IP address. */
    for( i=0; i< ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[i].ulIPAddress = 0xAAAAAAAA;
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
    
    for( i = 0; i < ipconfigMAX_ARP_RETRANSMISSIONS; i++ )
    {
	    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );    
	    vTaskDelay_Expect( pdMS_TO_TICKS( 250U ) );
	    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
	    xTaskCheckForTimeOut_IgnoreAndReturn(pdFALSE);
    }
    
    xResult = xARPWaitResolution( ulIPAddress,0 );
    TEST_ASSERT_EQUAL(-pdFREERTOS_ERRNO_EADDRNOTAVAIL,xResult);
    /* =================================================== */
}


























































