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
#include "mock_FreeRTOS_IPv4_Private.h"
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
 * @brief Validate framing before dispatching IPv4 admission policy.
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
    xIPPacket.xIPHeader.ucVersionHeaderLength = ipIPV4_VERSION_HEADER_LENGTH_MAX;
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief Delegate IPv4 policy and return its decision without host exceptions.
 */
void test_eConsiderPacketForProcessing_IPv4Admission( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_t xIPPacket;

    prvPrepareIPv4Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    eConsiderIPv4PacketForProcessing_ExpectAndReturn( &xIPPacket, &xEndPoint, pdFALSE, eProcessBuffer );
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    eConsiderIPv4PacketForProcessing_ExpectAndReturn( &xIPPacket, &xEndPoint, pdFALSE, eReleaseBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}

/**
 * @brief Validate framing before dispatching IPv6 admission policy.
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
}

/**
 * @brief Delegate IPv6 policy and return its decision without host exceptions.
 */
void test_eConsiderPacketForProcessing_IPv6Admission( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPPacket_IPv6_t xIPPacket;

    prvPrepareIPv6Packet( &xNetworkBuffer, &xEndPoint, &xIPPacket );
    eConsiderIPv6PacketForProcessing_ExpectAndReturn( &xIPPacket.xIPHeader, &xEndPoint, pdFALSE, eProcessBuffer );
    TEST_ASSERT_EQUAL( eProcessBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );

    eConsiderIPv6PacketForProcessing_ExpectAndReturn( &xIPPacket.xIPHeader, &xEndPoint, pdFALSE, eReleaseBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eConsiderPacketForProcessing( &xNetworkBuffer ) );
}
