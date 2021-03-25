/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_task.h"
#include "mock_NetworkBufferManagement.h"

#include "FreeRTOS_ARP.h"

#include "FreeRTOS_ARP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

extern ARPCacheRow_t xARPCache[ ipconfigARP_CACHE_ENTRIES ];

void test_xCheckLoopback_IncorrectFrameType( void )
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
    xResult = xCheckLoopback( pxNetworkBuffer, pdFALSE );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );
    /* =================================================== */
}

void test_xCheckLoopback_IncorrectMACAddress( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    BaseType_t xResult;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( IPPacket_t );

    IPPacket_t * pxIPPacket = ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );

    /* =================================================== */
    /* Let the frame-type be IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* But let the MAC address be different. */
    memset( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, 0xAA, ipMAC_ADDRESS_LENGTH_BYTES );
    /* bReleaseAfterSend parameter doesn't matter here. */
    xResult = xCheckLoopback( pxNetworkBuffer, pdFALSE );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );
    /* =================================================== */
}

void test_xCheckLoopback_HappyCase( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    BaseType_t xResult;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( IPPacket_t );

    IPPacket_t * pxIPPacket = ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );

    /* =================================================== */
    /* Let the frame-type be IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* Make the MAC address same. */
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipLOCAL_MAC_ADDRESS, ipMAC_ADDRESS_LENGTH_BYTES );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( pxNetworkBuffer, pxNetworkBuffer->xDataLength, pxNetworkBuffer );
    xSendEventStructToIPTask_IgnoreAndReturn( pdTRUE );

    xResult = xCheckLoopback( pxNetworkBuffer, pdFALSE );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    /* =================================================== */
}

void test_xCheckLoopback_DuplicationFails( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    BaseType_t xResult;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( IPPacket_t );

    IPPacket_t * pxIPPacket = ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );

    /* =================================================== */
    /* Let the frame-type be IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* Make the MAC address same. */
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipLOCAL_MAC_ADDRESS, ipMAC_ADDRESS_LENGTH_BYTES );
    /* Make buffer duplication fail. */
    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( pxNetworkBuffer, pxNetworkBuffer->xDataLength, NULL );
    xResult = xCheckLoopback( pxNetworkBuffer, pdFALSE );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    /* =================================================== */
}


void test_xCheckLoopback_SendEventToIPTaskFails( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    BaseType_t xResult;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( IPPacket_t );

    IPPacket_t * pxIPPacket = ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );


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
}


void test_eARPProcessPacket_LocalIPisZero( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;

    /* =================================================== */
    /* When the local IP address is 0, we should not process any ARP Packets. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0UL;
    eResult = eARPProcessPacket( &xARPFrame );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_InvalidOperation( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;

    /* =================================================== */
    /* What is some invalid option is sent in the ARP Packet? */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Add invalid operation */
    xARPFrame.xARPHeader.usOperation = ipARP_REQUEST | ipARP_REPLY;
    eResult = eARPProcessPacket( &xARPFrame );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_eARPProcessPacket_Request_DifferentIP( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;

    /* Process an ARP request, but not meant for this node. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REQUEST;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER + 0x11;
    eResult = eARPProcessPacket( &xARPFrame );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_Request_SenderAndTargetDifferent( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;

    /* =================================================== */
    /* Process an ARP request - meant for this node with target and source different. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REQUEST;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress, &( xARPFrame.xARPHeader.ulTargetProtocolAddress ), sizeof( xARPFrame.xARPHeader.ulTargetProtocolAddress ) );
    /* Make sure the the destination and source IP addresses are different. */
    xARPFrame.xARPHeader.ucSenderProtocolAddress[ 0 ]++;
    eResult = eARPProcessPacket( &xARPFrame );
    TEST_ASSERT_EQUAL( eReturnEthernetFrame, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_Request_SenderAndTargetSame( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;

    /* =================================================== */
    /* Process an ARP request - meant for this node with target and source same. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REQUEST;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress, &( xARPFrame.xARPHeader.ulTargetProtocolAddress ), sizeof( xARPFrame.xARPHeader.ulTargetProtocolAddress ) );
    eResult = eARPProcessPacket( &xARPFrame );
    TEST_ASSERT_EQUAL( eReturnEthernetFrame, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_Reply_SenderAndTargetSame( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;

    /* =================================================== */
    /* Process an ARP reply - meant for this node with target and source same. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REPLY;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = 0xAABBCCDD;
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress, &( xARPFrame.xARPHeader.ulTargetProtocolAddress ), sizeof( xARPFrame.xARPHeader.ulTargetProtocolAddress ) );
    eResult = eARPProcessPacket( &xARPFrame );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_Reply_DifferentIP( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;

    /* =================================================== */
    /* Process an ARP reply - not meant for this node. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REPLY;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER + 0x11;
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress, &( xARPFrame.xARPHeader.ulTargetProtocolAddress ), sizeof( xARPFrame.xARPHeader.ulTargetProtocolAddress ) );
    eResult = eARPProcessPacket( &xARPFrame );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_ulARPRemoveCacheEntryByMac_NoMatch( void )
{
    uint32_t ulResult;
    const MACAddress_t xMACAddress = { 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA };
    int i;
    BaseType_t xEntryToCheck;
    uint8_t ucBuffer[ sizeof( xARPCache[ 0 ] ) ];

    /* Catch some asserts. */
    catch_assert( ulARPRemoveCacheEntryByMac( NULL ) );

    /* =================================================== */
    /* Make sure no entry matches. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    }

    ulResult = ulARPRemoveCacheEntryByMac( &xMACAddress );
    TEST_ASSERT_EQUAL( 0, ulResult );
    /* =================================================== */
}

void test_ulARPRemoveCacheEntryByMac_OneMatchingEntry( void )
{
    uint32_t ulResult;
    const MACAddress_t xMACAddress = { 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA };
    int i;
    BaseType_t xEntryToCheck;
    uint8_t ucBuffer[ sizeof( xARPCache[ 0 ] ) ];

    /* =================================================== */
    /* Make sure only one entry matches. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    }

    xEntryToCheck = 1;
    xARPCache[ xEntryToCheck ].ulIPAddress = 0xAABBCCEE;
    memset( xARPCache[ xEntryToCheck ].xMACAddress.ucBytes, 0xAA, sizeof( xMACAddress.ucBytes ) );
    memset( ucBuffer, 0, sizeof( xARPCache[ 0 ] ) );
    ulResult = ulARPRemoveCacheEntryByMac( &xMACAddress );
    TEST_ASSERT_EQUAL( 0xAABBCCEE, ulResult );
    TEST_ASSERT_EQUAL( 0, memcmp( ucBuffer, &xARPCache[ xEntryToCheck ], sizeof( xARPCache[ 0 ] ) ) );
}

void test_vARPRefreshCacheEntry_NULLMAC_NoMatchingEntry( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;

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
}

void test_vARPRefreshCacheEntry_NULLMAC_MatchingEntry( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;

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
}

void test_vARPRefreshCacheEntry_MACWontMatch_IPWillMatch( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = 255;
        xARPCache[ i ].ucValid = pdTRUE;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x34, sizeof( xMACAddress.ucBytes ) );
    }

    xUseEntry = 1;
    xARPCache[ xUseEntry ].ulIPAddress = 0xAABBCCEE;

    ulIPAddress = 0xAABBCCEE;
    memset( xMACAddress.ucBytes, 0x11, ipMAC_ADDRESS_LENGTH_BYTES );
    /* Pass a MAC Address which won't match and an IP address which will match. */
    vARPRefreshCacheEntry( &xMACAddress, ulIPAddress );

    /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
    TEST_ASSERT_EQUAL_MESSAGE( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry ].ucAge, "Test 3" );
    TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry ].ucValid );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xARPCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( xMACAddress.ucBytes ) );
    /* =================================================== */
}

void test_vARPRefreshCacheEntry_MACAndIPWillMatch( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = 255;
        xARPCache[ i ].ucValid = pdFALSE;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x34, sizeof( xMACAddress.ucBytes ) );
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
    TEST_ASSERT_EQUAL_MESSAGE( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry ].ucAge, "Test 4" );
    TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry ].ucValid );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xARPCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( xMACAddress.ucBytes ) );
    /* =================================================== */
}


void test_vARPRefreshCacheEntry_IPOnADifferentSubnet( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = 255;
        xARPCache[ i ].ucValid = pdFALSE;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x34, sizeof( xMACAddress.ucBytes ) );
    }

    xUseEntry = 1;
    xARPCache[ xUseEntry ].ulIPAddress = 0xAABBCCEE;
    /* Set a MAC address which will match */
    memset( xARPCache[ xUseEntry ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    /* Set a local IP address */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCEF;

    /* The IP address being passed should not be on the same subnet. */
    ulIPAddress = 0x00BBCCEE;
    memset( xMACAddress.ucBytes, 0x11, ipMAC_ADDRESS_LENGTH_BYTES );
    /* Pass a MAC Address which will match and an IP address which will match too. */
    vARPRefreshCacheEntry( &xMACAddress, ulIPAddress );

    /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
    TEST_ASSERT_EQUAL_MESSAGE( ipconfigMAX_ARP_AGE, xARPCache[ 0 ].ucAge, "Test 5" );
    TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ 0 ].ucValid );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xARPCache[ 0 ].xMACAddress.ucBytes, sizeof( xMACAddress.ucBytes ) );
    /* =================================================== */
}

void test_vARPRefreshCacheEntry_IPAndMACInDifferentLocations( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = i + 1;
        xARPCache[ i ].ucValid = pdFALSE;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x34, sizeof( xMACAddress.ucBytes ) );
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
    TEST_ASSERT_EQUAL_MESSAGE( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry + 1 ].ucAge, "Test 9" );
    TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry + 1 ].ucValid );

    uint8_t MemoryCompare[ sizeof( ARPCacheRow_t ) ];
    memset( MemoryCompare, 0, sizeof( ARPCacheRow_t ) );
    TEST_ASSERT_EQUAL_MEMORY( MemoryCompare, &xARPCache[ xUseEntry ], sizeof( ARPCacheRow_t ) );
    /* =================================================== */
}

void test_eARPGetCacheEntryByMac_NoMatchingEntries( void )
{
    uint32_t ulIPAddress = 0x12345678, ulEntryToTest;
    eARPLookupResult_t eResult;
    MACAddress_t xMACAddress = { 0x22, 0x22, 0x22, 0x22, 0x22, 0x22 };
    int i;

    /* Hit some asserts */
    catch_assert( eARPGetCacheEntryByMac( NULL, &ulIPAddress ) );
    catch_assert( eARPGetCacheEntryByMac( &xMACAddress, NULL ) );

    /* =================================================== */
    /* Make sure no entry matches. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    }

    eResult = eARPGetCacheEntryByMac( &xMACAddress, &ulIPAddress );
    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
    TEST_ASSERT_EQUAL( 0x12345678, ulIPAddress );
    /* =================================================== */
}

void test_eARPGetCacheEntryByMac_OneMatchingEntry( void )
{
    uint32_t ulIPAddress = 0x12345678, ulEntryToTest;
    eARPLookupResult_t eResult;
    MACAddress_t xMACAddress = { 0x22, 0x22, 0x22, 0x22, 0x22, 0x22 };
    int i;

    /* =================================================== */
    /* Make sure one entry matches. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    }

    ulEntryToTest = 1;
    memset( xARPCache[ ulEntryToTest ].xMACAddress.ucBytes, 0x22, sizeof( xMACAddress.ucBytes ) );
    xARPCache[ ulEntryToTest ].ulIPAddress = 0xAABBCCEE;
    eResult = eARPGetCacheEntryByMac( &xMACAddress, &ulIPAddress );
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    TEST_ASSERT_EQUAL( xARPCache[ ulEntryToTest ].ulIPAddress, ulIPAddress );
    /* =================================================== */
}

void test_eARPGetCacheEntry_IPMatchesBroadcastAddr( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;

    /* =================================================== */
    ulIPAddress = xNetworkAddressing.ulBroadcastAddress;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 3" );
    TEST_ASSERT_EQUAL_MEMORY_MESSAGE( &xBroadcastMACAddress, &xMACAddress, sizeof( xMACAddress ), "Test 3" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_IPMatchesOtherBroadcastAddr( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;

    /* =================================================== */
    ulIPAddress = ipBROADCAST_IP_ADDRESS;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 3" );
    TEST_ASSERT_EQUAL_MEMORY_MESSAGE( &xBroadcastMACAddress, &xMACAddress, sizeof( xMACAddress ), "Test 3" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_LocalIPIsZero( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;

    /* =================================================== */
    *ipLOCAL_IP_ADDRESS_POINTER = 0;
    ulIPAddress = 0x1234;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eCantSendPacket, eResult, "Test 4" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_LocalIPMatchesReceivedIP( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;

    /* =================================================== */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    ulIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 5" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_MatchingInvalidEntry( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;

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
}

void test_eARPGetCacheEntry_MatchingValidEntry( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;

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
}

void test_eARPGetCacheEntry_GatewayAddressZero( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;

    /* =================================================== */
    for( int i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ucValid = ( uint8_t ) pdFALSE;
    }

    ulSavedGatewayAddress = xNetworkAddressing.ulGatewayAddress;
    xNetworkAddressing.ulGatewayAddress = 0;
    ulIPAddress = 0x4321;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    xNetworkAddressing.ulGatewayAddress = ulSavedGatewayAddress;
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheMiss, eResult, "Test 9" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_AddressNotOnLocalAddress( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;

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

void test_eARPGetCacheEntry_NoCacheHit( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;

    /* =================================================== */
    for( int i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0;
        xARPCache[ i ].ucValid = ( uint8_t ) pdTRUE;
    }

    ulSavedGatewayAddress = xNetworkAddressing.ulGatewayAddress;
    xNetworkAddressing.ulGatewayAddress = 0;
    /* Make IP address param == 0 */
    ulIPAddress = 0;

    /* Make both values (IP address and local IP pointer) different
     * and on different net masks. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress );
    xNetworkAddressing.ulGatewayAddress = ulSavedGatewayAddress;
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
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
    /* Make second entry invalid but with age > 1. */
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
    /* Make second entry invalid but with age > 1. */
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
    /* Make second entry invalid but with age > 1. */
    xARPCache[ ucEntryToCheck ].ucAge = 100;
    xARPCache[ ucEntryToCheck ].ucValid = pdTRUE;
    /* Set an IP address */
    xARPCache[ ucEntryToCheck ].ulIPAddress = 0xAAAAAAAA;

    /* This time the pxGetNetworkBuffer will be called. */
    /* Let the value returned third time be 100000. */
    xTaskGetTickCount_IgnoreAndReturn( 100000 );
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
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
    /* =================================================== */

    /* =================================================== */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, &xNetworkBuffer );
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    xSendEventStructToIPTask_IgnoreAndReturn( pdPASS );
    FreeRTOS_OutputARPRequest( ulIPAddress );
    /* =================================================== */
}


void vStoreTimeValue( TimeOut_t * const timeout,
                      int32_t callbacks )
{
    timeout->xOverflowCount = 0;
    timeout->xTimeOnEntering = 100;
}

void test_xARPWaitResolution_PrivateFunctionReturnsHit( void )
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
}

void test_xARPWaitResolution_GNWFailsNoTimeout( void )
{
    uint32_t ulIPAddress = 0xAAAAAAAA;
    BaseType_t xResult;
    int i;

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

    /* Make sure that there are enough stubs for all the repetitive calls. */
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
}

void test_xARPWaitResolution( void )
{
    uint32_t ulIPAddress = 0xAAAAAAAA;
    BaseType_t xResult;
    int i;

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

    /* Make sure that there are enough stubs for all the repetitive calls. */
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

    /* Make sure that there are enough stubs for all the repetitive calls. */
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



void test_FreeRTOS_PrintARPCache( void )
{
    int x;

    for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        /* Anything except 0. */
        xARPCache[ x ].ulIPAddress = 0xAA;
        /* Anything except 0. */
        xARPCache[ x ].ucAge = x;
    }

    /* Nothing to actually unit-test here. */
    FreeRTOS_PrintARPCache();

    for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        /* Anything except 0. */
        xARPCache[ x ].ulIPAddress = 0x00;
        /* Anything except 0. */
        xARPCache[ x ].ucAge = x;
    }

    /* Nothing to actually unit-test here. */
    FreeRTOS_PrintARPCache();
}
