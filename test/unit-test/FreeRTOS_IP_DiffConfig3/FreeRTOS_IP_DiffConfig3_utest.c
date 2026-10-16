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

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_IP_DiffConfig_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_DHCPv6.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_IPv4.h"
#include "mock_FreeRTOS_IPv6.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/*#include "FreeRTOS_IP_stubs.c" */
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer );
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

extern BaseType_t xIPTaskInitialised;
extern BaseType_t xNetworkDownEventPending;
extern BaseType_t xNetworkUp;
extern UBaseType_t uxQueueMinimumSpace;

/* ============================ Unity Fixtures ============================ */

/*! called before each test case */
void setUp( void )
{
    pxNetworkEndPoints = NULL;
    pxNetworkInterfaces = NULL;
    xNetworkDownEventPending = pdFALSE;
}

/*! called after each test case */
void tearDown( void )
{
}

static void prvPrepareIPv4Packet( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                  NetworkEndPoint_t * pxEndPoint,
                                  IPPacket_t * pxIPPacket )
{
    ( void ) memset( pxNetworkBuffer, 0, sizeof( *pxNetworkBuffer ) );
    ( void ) memset( pxEndPoint, 0, sizeof( *pxEndPoint ) );
    ( void ) memset( pxIPPacket, 0, sizeof( *pxIPPacket ) );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) pxIPPacket;
    pxNetworkBuffer->xDataLength = sizeof( *pxIPPacket );
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    pxEndPoint->bits.bEndPointUp = pdTRUE_UNSIGNED;
    pxEndPoint->ipv4_settings.ulIPAddress = 0x01020304U;
    pxEndPoint->ipv4_settings.ulBroadcastAddress = 0x010203FFU;
    ( void ) memset( pxEndPoint->xMACAddress.ucBytes, 0x11, sizeof( MACAddress_t ) );

    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    ( void ) memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes,
                     pxEndPoint->xMACAddress.ucBytes,
                     sizeof( MACAddress_t ) );
    ( void ) memset( pxIPPacket->xEthernetHeader.xSourceAddress.ucBytes, 0x22, sizeof( MACAddress_t ) );
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ipIPV4_VERSION_HEADER_LENGTH_MIN;
    pxIPPacket->xIPHeader.ulDestinationIPAddress = pxEndPoint->ipv4_settings.ulIPAddress;
    pxIPPacket->xIPHeader.ulSourceIPAddress = 0x05060708U;
}

static void prvExpectValidIPv4Source( const IPPacket_t * pxIPPacket )
{
    xBadIPv4Loopback_ExpectAndReturn( &( pxIPPacket->xIPHeader ), pdFALSE );
    xIsIPv4Multicast_ExpectAndReturn( pxIPPacket->xIPHeader.ulSourceIPAddress, pdFALSE );
}

static void prvPrepareIPv6Packet( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                  NetworkEndPoint_t * pxEndPoint,
                                  IPPacket_IPv6_t * pxIPPacket )
{
    ( void ) memset( pxNetworkBuffer, 0, sizeof( *pxNetworkBuffer ) );
    ( void ) memset( pxEndPoint, 0, sizeof( *pxEndPoint ) );
    ( void ) memset( pxIPPacket, 0, sizeof( *pxIPPacket ) );

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) pxIPPacket;
    pxNetworkBuffer->xDataLength = sizeof( *pxIPPacket );
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    pxEndPoint->bits.bIPv6 = pdTRUE_UNSIGNED;
    pxEndPoint->bits.bEndPointUp = pdTRUE_UNSIGNED;
    pxEndPoint->ipv6_settings.xIPAddress.ucBytes[ ipSIZE_OF_IPv6_ADDRESS - 1U ] = 2U;

    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    pxIPPacket->xIPHeader.ucVersionTrafficClass = 0x60U;
    pxIPPacket->xIPHeader.xDestinationAddress = pxEndPoint->ipv6_settings.xIPAddress;
    pxIPPacket->xIPHeader.xSourceAddress.ucBytes[ ipSIZE_OF_IPv6_ADDRESS - 1U ] = 1U;
}

static void prvExpectNoIPv6Loopback( const IPPacket_IPv6_t * pxIPPacket )
{
    xIsIPv6Loopback_ExpectAndReturn( &( pxIPPacket->xIPHeader.xSourceAddress ), pdFALSE );
    xIsIPv6Loopback_ExpectAndReturn( &( pxIPPacket->xIPHeader.xDestinationAddress ), pdFALSE );
}

/* ======================== Stub Callback Functions ========================= */

eFrameProcessingResult_t eApplicationProcessCustomFrameHook( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    ( void ) ( pxNetworkBuffer );

    /* Force hook function to return waiting resultion for unknown Ethernet frame type. */
    return eWaitingResolution;
}

/* ============================== Test Cases ============================== */

/**
 * @brief test_prvProcessIPEventsAndTimers_eDHCPEvent_DHCPv4
 * To validate if prvProcessIPEventsAndTimers() calls vDHCPProcess() while receiving eDHCPEvent.
 */
void test_prvProcessIPEventsAndTimers_eDHCPEvent_DHCPv4( void )
{
    IPStackEvent_t xReceivedEvent;
    uint32_t ulDHCPEvent = 0x1234;
    NetworkEndPoint_t xEndPoints, * pxEndPoints = &xEndPoints;
    BaseType_t xQueueReturn = 100;

    memset( pxEndPoints, 0, sizeof( NetworkEndPoint_t ) );
    pxEndPoints->bits.bWantDHCP = pdTRUE_UNSIGNED;

    xReceivedEvent.eEventType = eDHCPEvent;
    xReceivedEvent.pvData = pxEndPoints;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    vDHCPProcess_Expect( pdFALSE, pxEndPoints );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eDHCPEvent_DHCPv6
 * To validate if prvProcessIPEventsAndTimers() calls vDHCPv6Process() while receiving eDHCPEvent
 * and the endpoint is IPv6.
 */
void test_prvProcessIPEventsAndTimers_eDHCPEvent_DHCPv6( void )
{
    IPStackEvent_t xReceivedEvent;
    uint32_t ulDHCPEvent = 0x1234;
    NetworkEndPoint_t xEndPoints, * pxEndPoints = &xEndPoints;
    BaseType_t xQueueReturn = 100;

    memset( pxEndPoints, 0, sizeof( NetworkEndPoint_t ) );
    pxEndPoints->bits.bWantDHCP = pdTRUE_UNSIGNED;
    pxEndPoints->bits.bIPv6 = pdTRUE_UNSIGNED;

    xReceivedEvent.eEventType = eDHCPEvent;
    xReceivedEvent.pvData = pxEndPoints;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    vDHCPv6Process_Expect( pdFALSE, pxEndPoints );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eDHCPEvent_RA
 * To validate if prvProcessIPEventsAndTimers() calls vRAProcess() while receiving eDHCPEvent
 * and the endpoint is configured for RA.
 */
void test_prvProcessIPEventsAndTimers_eDHCPEvent_RA( void )
{
    IPStackEvent_t xReceivedEvent;
    uint32_t ulDHCPEvent = 0x1234;
    NetworkEndPoint_t xEndPoints, * pxEndPoints = &xEndPoints;
    BaseType_t xQueueReturn = 100;

    memset( pxEndPoints, 0, sizeof( NetworkEndPoint_t ) );
    pxEndPoints->bits.bWantRA = pdTRUE_UNSIGNED;
    pxEndPoints->bits.bIPv6 = pdTRUE_UNSIGNED;

    xReceivedEvent.eEventType = eDHCPEvent;
    xReceivedEvent.pvData = pxEndPoints;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    vRAProcess_Expect( pdFALSE, pxEndPoints );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessEthernetPacket_UnknownFrameType_NeedResolution
 * But we release the network buffer because the frame type is unknown.
 */
void test_prvProcessEthernetPacket_UnknownFrameType_NeedResolution( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ] = { 0 };
    EthernetHeader_t * pxEthernetHeader;
    IPPacket_IPv6_t * pxIPv6Packet;
    IPHeader_IPv6_t * pxIPv6Header;
    struct xNetworkInterface xInterface;
    NetworkEndPoint_t xNetworkEndPoint = { 0 };

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = &xNetworkEndPoint;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxEthernetHeader->usFrameType = 0xFFFF;

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief test_prvProcessEthernetPacket_UnknownFrameType_NeedResolution
 * But we release the network buffer because the frame type is unknown.
 */
void test_prvProcessEthernetPacket_IPv4FrameType_CheckFrameFail( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ] = { 0 };
    EthernetHeader_t * pxEthernetHeader;
    IPPacket_IPv6_t * pxIPv6Packet;
    IPHeader_IPv6_t * pxIPv6Header;
    struct xNetworkInterface xInterface;
    NetworkEndPoint_t xNetworkEndPoint = { 0 };

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = &xNetworkEndPoint;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxEthernetHeader->usFrameType = ipIPv4_FRAME_TYPE;

    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxEthernetHeader->xDestinationAddress, NULL, NULL );
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief Invalid descriptors and truncated Ethernet headers must be rejected.
 */
void test_eConsiderPacketForProcessing_InvalidDescriptor( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer = { 0 };
    NetworkEndPoint_t xEndPoint = { 0 };
    uint8_t ucEthernetBuffer[ sizeof( EthernetHeader_t ) ] = { 0 };

    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( NULL ) );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( ucEthernetBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.xDataLength--;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief ARP and enabled custom Ethernet frames pass the common packet filter.
 */
void test_eConsiderPacketForProcessing_ARPAndCustomFrames( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer = { 0 };
    NetworkEndPoint_t xEndPoint = { 0 };
    EthernetHeader_t xEthernetHeader = { 0 };

    xNetworkBuffer.pucEthernetBuffer = ( uint8_t * ) &xEthernetHeader;
    xNetworkBuffer.xDataLength = sizeof( xEthernetHeader );
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    xEthernetHeader.usFrameType = ipARP_FRAME_TYPE;
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    xEthernetHeader.usFrameType = 0xFFFFU;
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief IPv4 packets require an IPv4 endpoint and a complete, valid header.
 */
void test_eConsiderPacketForProcessing_IPv4HeaderValidation( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_t xIPPacket;

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xNetworkBuffer.xDataLength = sizeof( xIPPacket ) - 1U;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.ucVersionHeaderLength = ipIPV4_VERSION_HEADER_LENGTH_MIN - 1U;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.ucVersionHeaderLength = ipIPV4_VERSION_HEADER_LENGTH_MAX + 1U;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.ucVersionHeaderLength = ipIPV4_VERSION_HEADER_LENGTH_MAX;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief Fragmented IPv4 packets are not supported.
 */
void test_eConsiderPacketForProcessing_IPv4Fragments( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_t xIPPacket;

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.usFragmentOffset = 1U;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.usFragmentOffset = ipFRAGMENT_FLAGS_MORE_FRAGMENTS;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief Invalid IPv4 loopback, Ethernet source, and multicast source addresses are rejected.
 */
void test_eConsiderPacketForProcessing_IPv4SourceValidation( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_t xIPPacket;

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xBadIPv4Loopback_ExpectAndReturn( &( xIPPacket.xIPHeader ), pdTRUE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    ( void ) memcpy( xIPPacket.xEthernetHeader.xSourceAddress.ucBytes,
                     xBroadcastMACAddress.ucBytes,
                     sizeof( MACAddress_t ) );
    xBadIPv4Loopback_ExpectAndReturn( &( xIPPacket.xIPHeader ), pdFALSE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xBadIPv4Loopback_ExpectAndReturn( &( xIPPacket.xIPHeader ), pdFALSE );
    xIsIPv4Multicast_ExpectAndReturn( xIPPacket.xIPHeader.ulSourceIPAddress, pdTRUE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief An up IPv4 endpoint accepts local, broadcast, and multicast destinations.
 */
void test_eConsiderPacketForProcessing_IPv4EndpointUpAcceptsValidDestinations( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_t xIPPacket;

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    prvExpectValidIPv4Source( &xIPPacket );
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.ulDestinationIPAddress = xEndPoint.ipv4_settings.ulBroadcastAddress;
    ( void ) memcpy( xIPPacket.xEthernetHeader.xDestinationAddress.ucBytes,
                     xBroadcastMACAddress.ucBytes,
                     sizeof( MACAddress_t ) );
    prvExpectValidIPv4Source( &xIPPacket );
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.ulDestinationIPAddress = FREERTOS_INADDR_BROADCAST;
    ( void ) memcpy( xIPPacket.xEthernetHeader.xDestinationAddress.ucBytes,
                     xBroadcastMACAddress.ucBytes,
                     sizeof( MACAddress_t ) );
    prvExpectValidIPv4Source( &xIPPacket );
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.ulDestinationIPAddress = 0xE0000001U;
    xIPPacket.xEthernetHeader.xDestinationAddress.ucBytes[ 0 ] = ipMULTICAST_MAC_ADDRESS_IPv4_0;
    xIPPacket.xEthernetHeader.xDestinationAddress.ucBytes[ 1 ] = ipMULTICAST_MAC_ADDRESS_IPv4_1;
    xIPPacket.xEthernetHeader.xDestinationAddress.ucBytes[ 2 ] = ipMULTICAST_MAC_ADDRESS_IPv4_2;
    prvExpectValidIPv4Source( &xIPPacket );
    xIsIPv4Multicast_ExpectAndReturn( xIPPacket.xIPHeader.ulDestinationIPAddress, pdTRUE );
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief An up IPv4 endpoint rejects invalid destination and broadcast combinations.
 */
void test_eConsiderPacketForProcessing_IPv4EndpointUpRejectsInvalidAddresses( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_t xIPPacket;

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.ulDestinationIPAddress = 0x090A0B0CU;
    prvExpectValidIPv4Source( &xIPPacket );
    xIsIPv4Multicast_ExpectAndReturn( xIPPacket.xIPHeader.ulDestinationIPAddress, pdFALSE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.ulSourceIPAddress = xEndPoint.ipv4_settings.ulBroadcastAddress;
    prvExpectValidIPv4Source( &xIPPacket );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.ulSourceIPAddress = FREERTOS_INADDR_BROADCAST;
    prvExpectValidIPv4Source( &xIPPacket );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    ( void ) memcpy( xIPPacket.xEthernetHeader.xDestinationAddress.ucBytes,
                     xBroadcastMACAddress.ucBytes,
                     sizeof( MACAddress_t ) );
    prvExpectValidIPv4Source( &xIPPacket );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief A down IPv4 endpoint accepts only broadcast IP or matching unicast MAC traffic.
 */
void test_eConsiderPacketForProcessing_IPv4EndpointDown( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_t xIPPacket;

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xEndPoint.bits.bEndPointUp = pdFALSE_UNSIGNED;
    ( void ) memcpy( xIPPacket.xEthernetHeader.xDestinationAddress.ucBytes,
                     xBroadcastMACAddress.ucBytes,
                     sizeof( MACAddress_t ) );
    prvExpectValidIPv4Source( &xIPPacket );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xEndPoint.bits.bEndPointUp = pdFALSE_UNSIGNED;
    xIPPacket.xIPHeader.ulDestinationIPAddress = FREERTOS_INADDR_BROADCAST;
    ( void ) memcpy( xIPPacket.xEthernetHeader.xDestinationAddress.ucBytes,
                     xBroadcastMACAddress.ucBytes,
                     sizeof( MACAddress_t ) );
    prvExpectValidIPv4Source( &xIPPacket );
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xEndPoint.bits.bEndPointUp = pdFALSE_UNSIGNED;
    ( void ) memset( xIPPacket.xEthernetHeader.xDestinationAddress.ucBytes, 0x33, sizeof( MACAddress_t ) );
    prvExpectValidIPv4Source( &xIPPacket );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xEndPoint.bits.bEndPointUp = pdFALSE_UNSIGNED;
    prvExpectValidIPv4Source( &xIPPacket );
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief IPv6 packets require an IPv6 endpoint and a complete, version-six header.
 */
void test_eConsiderPacketForProcessing_IPv6HeaderValidation( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_IPv6_t xIPPacket;

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xNetworkBuffer.xDataLength = sizeof( xIPPacket ) - 1U;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.ucVersionTrafficClass = 0x50U;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief Unspecified IPv6 source and destination addresses are rejected.
 */
void test_eConsiderPacketForProcessing_IPv6UnspecifiedAddress( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_IPv6_t xIPPacket;

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    ( void ) memset( &xIPPacket.xIPHeader.xDestinationAddress, 0, sizeof( IPv6_Address_t ) );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    ( void ) memset( &xIPPacket.xIPHeader.xSourceAddress, 0, sizeof( IPv6_Address_t ) );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief IPv6 loopback addresses are not valid on an Ethernet interface.
 */
void test_eConsiderPacketForProcessing_IPv6LoopbackAddress( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_IPv6_t xIPPacket;

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIsIPv6Loopback_ExpectAndReturn( &( xIPPacket.xIPHeader.xSourceAddress ), pdTRUE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIsIPv6Loopback_ExpectAndReturn( &( xIPPacket.xIPHeader.xSourceAddress ), pdFALSE );
    xIsIPv6Loopback_ExpectAndReturn( &( xIPPacket.xIPHeader.xDestinationAddress ), pdTRUE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief IPv6 accepts local, allowed multicast, and pre-configuration traffic.
 */
void test_eConsiderPacketForProcessing_IPv6Destinations( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_IPv6_t xIPPacket;

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    prvExpectNoIPv6Loopback( &xIPPacket );
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.xDestinationAddress.ucBytes[ ipSIZE_OF_IPv6_ADDRESS - 1U ] = 3U;
    prvExpectNoIPv6Loopback( &xIPPacket );
    xIsIPv6AllowedMulticast_ExpectAndReturn( &( xIPPacket.xIPHeader.xDestinationAddress ), pdTRUE );
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.xDestinationAddress.ucBytes[ ipSIZE_OF_IPv6_ADDRESS - 1U ] = 3U;
    xEndPoint.bits.bEndPointUp = pdFALSE_UNSIGNED;
    pxNetworkEndPoints = &xEndPoint;
    prvExpectNoIPv6Loopback( &xIPPacket );
    xIsIPv6AllowedMulticast_ExpectAndReturn( &( xIPPacket.xIPHeader.xDestinationAddress ), pdFALSE );
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    xIPPacket.xIPHeader.xDestinationAddress.ucBytes[ ipSIZE_OF_IPv6_ADDRESS - 1U ] = 3U;
    pxNetworkEndPoints = &xEndPoint;
    prvExpectNoIPv6Loopback( &xIPPacket );
    xIsIPv6AllowedMulticast_ExpectAndReturn( &( xIPPacket.xIPHeader.xDestinationAddress ), pdFALSE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}
