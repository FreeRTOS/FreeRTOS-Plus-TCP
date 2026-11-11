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

#include "mock_list.h"

#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_task.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_TCP_State_Handling.h"
#include "mock_FreeRTOS_TCP_Reception.h"
#include "mock_FreeRTOS_TCP_Utils.h"
#include "mock_TCP_Transmission_DiffConfig_list_macros.h"

#include "FreeRTOS_TCP_IP.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"
/* The Annexed_TCP copy removes conditional definitions. Use the production
 * defaults so assertions see the same option values as the code under test. */
#include "../../../source/include/FreeRTOSIPConfigDefaults.h"

#include "FreeRTOS_TCP_Transmission_DiffConfig_stubs.c"
#include "FreeRTOS_TCP_Transmission.h"

/* ============================ Test Variables ============================ */

static FreeRTOS_Socket_t xSocket;
static NetworkBufferDescriptor_t xNetworkBuffer;
static uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];
static StreamBuffer_t xStreamBuffer;
static struct xNetworkEndPoint xEndPoint;
static struct xNetworkInterface xInterface;

static const MACAddress_t xTemplateMAC = { { 0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC } };
static const MACAddress_t xCacheMAC = { { 0x21, 0x43, 0x65, 0x87, 0xA9, 0xCB } };


/* ============================ Test Helpers ============================ */

/* Prepares an established socket whose peer advertises the given window. */
static void prvSetUpSocket( uint32_t ulPeerWindowSize )
{
    memset( &xStreamBuffer, 0, sizeof( xStreamBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    xBufferAllocFixedSize = pdFALSE;

    xSocket.u.xTCP.txStream = &xStreamBuffer;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.usMSS = 1000;
    xSocket.u.xTCP.bits.bSendKeepAlive = pdTRUE;
    xSocket.u.xTCP.ucKeepRepCount = 1;
    xStreamBuffer.LENGTH = 2048;
    xSocket.u.xTCP.ulWindowSize = ulPeerWindowSize;
}

/* Returns the TCP flags of the next segment that prvTCPPrepareSend() builds,
 * with 500 bytes ready in the TX window. The argument is the number of bytes
 * queued from the segment start. */
static uint8_t ucPrepareSendFlags( size_t uxQueuedBytes )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    int32_t lBytesSent;
    int32_t lStreamPosition = 100;

    memset( ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    xStreamBuffer.uxHead = ( size_t ) lStreamPosition + uxQueuedBytes;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 500 );
    ulTCPWindowTxGet_ReturnThruPtr_plPosition( &lStreamPosition );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();
    uxStreamBufferDistance_ExpectAndReturn( &xStreamBuffer, 0, ( size_t ) lStreamPosition, 100 );
    uxStreamBufferGet_ExpectAndReturn( &xStreamBuffer, 100,
                                      &ucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER ],
                                      500, pdTRUE, 500 );
    #if ( ipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY == ipconfigENABLE )
        uxStreamBufferDistance_ExpectAndReturn( &xStreamBuffer, ( size_t ) lStreamPosition, xStreamBuffer.uxHead, uxQueuedBytes );
    #endif

    lBytesSent = prvTCPPrepareSend( &xSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 540, lBytesSent );

    return ( ( TCPPacket_t * ) ucEthernetBuffer )->xTCPHeader.ucTCPFlags;
}

/* ============================== Test Cases ============================== */

/**
 * @brief test_prvTCPPrepareSend_PSH_LastSegment
 * To validate if prvTCPPrepareSend() sets PSH on the segment that empties the
 * send queue.
 */
void test_prvTCPPrepareSend_PSH_LastSegment( void )
{
    uint8_t ucFlags;

    prvSetUpSocket( 4000 );
    ucFlags = ucPrepareSendFlags( 500 );

    TEST_ASSERT_EQUAL( tcpTCP_FLAG_PSH, ucFlags & tcpTCP_FLAG_PSH );
}

/**
 * @brief test_prvTCPPrepareSend_PSH_MoreQueued
 * More queued data suppresses PSH only when the option is enabled.
 */
void test_prvTCPPrepareSend_PSH_MoreQueued( void )
{
    uint8_t ucFlags;

    prvSetUpSocket( 4000 );
    ucFlags = ucPrepareSendFlags( 1000 );

    #if ( ipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY == ipconfigENABLE )
        TEST_ASSERT_EQUAL( 0, ucFlags & tcpTCP_FLAG_PSH );
    #else
        TEST_ASSERT_EQUAL( tcpTCP_FLAG_PSH, ucFlags & tcpTCP_FLAG_PSH );
    #endif
}

/* Prepares a connected socket whose header template holds xTemplateMAC, last
 * heard from at tick 100, and sets the expectations that prvTCPReturnPacket()
 * has for any segment. */
static void vPrepareReturnPacket( BaseType_t xWithSocket )
{
    TCPPacket_t * pxTCPPacket = ( TCPPacket_t * ) ucEthernetBuffer;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.pxNetworkInterface = &xInterface;
    xEndPoint.ipv4_settings.ulIPAddress = 0xC0C0C0C0;
    xInterface.pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    xSocket.pxEndPoint = &xEndPoint;
    xSocket.u.xTCP.rxStream = &xStreamBuffer;
    xSocket.u.xTCP.uxRxStreamSize = 1500;
    xSocket.u.xTCP.usMSS = 1000;
    xSocket.u.xTCP.xLastActTime = 100;
    xSocket.u.xTCP.xTCPWindow.xSize.ulRxWindowLength = 500;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    pxTCPPacket->xEthernetHeader.xSourceAddress = xTemplateMAC;
    ( ( TCPPacket_t * ) xSocket.u.xTCP.xPacket.u.ucLastPacket )->xEthernetHeader.xSourceAddress = xTemplateMAC;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    if( xWithSocket != pdFALSE )
    {
        uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
        FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    }
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
}

static TCPPacket_t * pxPrepareReturnPacket( void )
{
    TCPPacket_t * pxTCPPacket = ( TCPPacket_t * ) ucEthernetBuffer;

    memset( &xStreamBuffer, 0, sizeof( xStreamBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    vPrepareReturnPacket( pdTRUE );
    return pxTCPPacket;
}

static void vExpectCacheHit( void )
{
    /* CMock retains this address until the production call consumes it. */
    static struct xNetworkEndPoint * pxEndPoint = &xEndPoint;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eResolutionCacheHit );
    eARPGetCacheEntry_ReturnThruPtr_pxMACAddress( ( MACAddress_t * ) &xCacheMAC );
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
}

/* ============================== Test Cases ============================== */

/**
 * @brief test_prvTCPReturnPacket_SkipARP_ActivePeer
 * To validate if prvTCPReturnPacket() sends to the MAC in the header template
 * without searching the ARP cache while the peer was heard from recently.
 */
void test_prvTCPReturnPacket_SkipARP_ActivePeer( void )
{
    TCPPacket_t * pxTCPPacket = pxPrepareReturnPacket();

    #if ( ipconfigTCP_SKIP_ARP_LOOKUP_MS > 0U )
        xTaskGetTickCount_ExpectAndReturn( 100 + pdMS_TO_TICKS( ipconfigTCP_SKIP_ARP_LOOKUP_MS ) - 1 );
    #else
        vExpectCacheHit();
    #endif

    prvTCPReturnPacket( &xSocket, &xNetworkBuffer, 40, pdFALSE );

    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
    #if ( ipconfigTCP_SKIP_ARP_LOOKUP_MS > 0U )
        TEST_ASSERT_EQUAL_UINT8_ARRAY( xTemplateMAC.ucBytes, pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
    #else
        TEST_ASSERT_EQUAL_UINT8_ARRAY( xCacheMAC.ucBytes, pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
    #endif
}

/**
 * @brief test_prvTCPReturnPacket_SkipARP_QuietPeer
 * To validate if prvTCPReturnPacket() searches the ARP cache once the peer has
 * been quiet, and stores the MAC it finds in the header template.
 */
void test_prvTCPReturnPacket_SkipARP_QuietPeer( void )
{
    TCPPacket_t * pxTCPPacket = pxPrepareReturnPacket();
    struct xNetworkEndPoint * pxEndPoint = &xEndPoint;

    #if ( ipconfigTCP_SKIP_ARP_LOOKUP_MS > 0U )
        xTaskGetTickCount_ExpectAndReturn( 100 + pdMS_TO_TICKS( ipconfigTCP_SKIP_ARP_LOOKUP_MS ) );
    #endif
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eResolutionCacheHit );
    eARPGetCacheEntry_ReturnThruPtr_pxMACAddress( ( MACAddress_t * ) &xCacheMAC );
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );

    prvTCPReturnPacket( &xSocket, &xNetworkBuffer, 40, pdFALSE );

    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( xCacheMAC.ucBytes, pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
    #if ( ipconfigTCP_SKIP_ARP_LOOKUP_MS > 0U )
        TEST_ASSERT_EQUAL_UINT8_ARRAY( xCacheMAC.ucBytes,
                                       ( ( TCPPacket_t * ) xSocket.u.xTCP.xPacket.u.ucLastPacket )->xEthernetHeader.xSourceAddress.ucBytes,
                                       ipMAC_ADDRESS_LENGTH_BYTES );
    #else
        /* With the optimization disabled, a separate outgoing buffer must not
         * update the socket template (the pre-PR behavior). */
        TEST_ASSERT_EQUAL_UINT8_ARRAY( xTemplateMAC.ucBytes,
                                       ( ( TCPPacket_t * ) xSocket.u.xTCP.xPacket.u.ucLastPacket )->xEthernetHeader.xSourceAddress.ucBytes,
                                       ipMAC_ADDRESS_LENGTH_BYTES );
    #endif
}

/* Pass the very same packet through both production functions. A different
 * MAC in the cache makes taking the wrong ARP branch observable. */
static void vCheckPreparedSegment( size_t uxQueuedBytes,
                                   BaseType_t xQuietPeer,
                                   uint8_t ucExpectedPSH )
{
    TCPPacket_t * pxTCPPacket = ( TCPPacket_t * ) ucEthernetBuffer;
    const MACAddress_t * pxExpectedMAC = &xCacheMAC;

    ( void ) ucPrepareSendFlags( uxQueuedBytes );
    vPrepareReturnPacket( pdTRUE );

    #if ( ipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY != ipconfigENABLE )
        ucExpectedPSH = tcpTCP_FLAG_PSH;
    #endif

    #if ( ipconfigTCP_SKIP_ARP_LOOKUP_MS > 0U )
        if( xQuietPeer == pdFALSE )
        {
            xTaskGetTickCount_ExpectAndReturn( 100 );
            pxExpectedMAC = &xTemplateMAC;
        }
        else
        {
            xTaskGetTickCount_ExpectAndReturn( 100 + pdMS_TO_TICKS( ipconfigTCP_SKIP_ARP_LOOKUP_MS ) );
            vExpectCacheHit();
        }
    #else
        ( void ) xQuietPeer;
        vExpectCacheHit();
    #endif

    prvTCPReturnPacket( &xSocket, &xNetworkBuffer, 540, pdFALSE );

    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
    TEST_ASSERT_EQUAL( 540 + ipSIZE_OF_ETH_HEADER, xNetworkBuffer.xDataLength );
    TEST_ASSERT_EQUAL( ucExpectedPSH, pxTCPPacket->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_PSH );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPPacket->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( pxExpectedMAC->ucBytes, pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
}

void test_prvTCPPrepareAndReturn_ActivePeer( void )
{
    prvSetUpSocket( 4000 );
    vCheckPreparedSegment( 1000, pdFALSE, 0 );
    vCheckPreparedSegment( 500, pdFALSE, tcpTCP_FLAG_PSH );
}

void test_prvTCPPrepareAndReturn_QuietPeer( void )
{
    prvSetUpSocket( 4000 );
    vCheckPreparedSegment( 1000, pdTRUE, 0 );
    vCheckPreparedSegment( 500, pdTRUE, tcpTCP_FLAG_PSH );
}

void test_prvTCPPrepareSend_NoPayloadClearsPSH( void )
{
    NetworkBufferDescriptor_t * pxBuffer = &xNetworkBuffer;
    TCPPacket_t * pxTCPPacket = ( TCPPacket_t * ) ucEthernetBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bWinChange = pdTRUE;
    #if ( ipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY == ipconfigENABLE )
        xSocket.u.xTCP.ulUnpushedBytes = 500U;
    #endif
    pxTCPPacket->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_PSH;
    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    TEST_ASSERT_EQUAL( 40, prvTCPPrepareSend( &xSocket, &pxBuffer, 0 ) );
    TEST_ASSERT_EQUAL( 0, pxTCPPacket->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_PSH );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPPacket->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
    #if ( ipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY == ipconfigENABLE )
        TEST_ASSERT_EQUAL_UINT32( 500U, xSocket.u.xTCP.ulUnpushedBytes );
    #endif
}

void test_prvTCPReturnPacket_SkipARP_NoSocket( void )
{
    TCPPacket_t * pxTCPPacket = ( TCPPacket_t * ) ucEthernetBuffer;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );
    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    vPrepareReturnPacket( pdFALSE );
    vExpectCacheHit();

    /* No tick expectation: the NULL socket path must always look up ARP. */
    prvTCPReturnPacket( NULL, &xNetworkBuffer, 40, pdFALSE );
    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( xCacheMAC.ucBytes, pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
}

void test_prvTCPReturnPacket_SkipARP_QuietPeerCacheMiss( void )
{
    TCPPacket_t * pxTCPPacket = pxPrepareReturnPacket();

    #if ( ipconfigTCP_SKIP_ARP_LOOKUP_MS > 0U )
        xTaskGetTickCount_ExpectAndReturn( 101 + pdMS_TO_TICKS( ipconfigTCP_SKIP_ARP_LOOKUP_MS ) );
    #endif
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eResolutionCacheMiss );

    prvTCPReturnPacket( &xSocket, &xNetworkBuffer, 40, pdFALSE );
    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( xTemplateMAC.ucBytes, pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
}

void test_prvTCPReturnPacket_SkipARP_TickWrap( void )
{
    TCPPacket_t * pxTCPPacket = pxPrepareReturnPacket();
    const MACAddress_t * pxExpectedMAC = &xCacheMAC;

    xSocket.u.xTCP.xLastActTime = portMAX_DELAY - 10U;
    #if ( ipconfigTCP_SKIP_ARP_LOOKUP_MS > 0U )
        /* Across wrap, elapsed time is 16 ticks, within the 1000 ms window. */
        xTaskGetTickCount_ExpectAndReturn( 5 );
        pxExpectedMAC = &xTemplateMAC;
    #else
        vExpectCacheHit();
    #endif

    prvTCPReturnPacket( &xSocket, &xNetworkBuffer, 40, pdFALSE );
    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( pxExpectedMAC->ucBytes, pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
}

/**
 * @brief test_prvTCPPrepareSend_PSH_HalfWindow
 * To validate if prvTCPPrepareSend() sets PSH on a segment once more than half
 * of the peer's window has been sent without PSH, while more data stays queued.
 */
void test_prvTCPPrepareSend_PSH_HalfWindow( void )
{
    const uint8_t ucExpected[] = { 0, 0, tcpTCP_FLAG_PSH, 0, 0, tcpTCP_FLAG_PSH };
    size_t uxIndex;

    prvSetUpSocket( 2200 );

    for( uxIndex = 0; uxIndex < sizeof( ucExpected ); uxIndex++ )
    {
        #if ( ipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY == ipconfigENABLE )
            TEST_ASSERT_EQUAL( ucExpected[ uxIndex ], ucPrepareSendFlags( 1000 ) & tcpTCP_FLAG_PSH );
            TEST_ASSERT_EQUAL_UINT32( ( ( uxIndex + 1U ) % 3U ) * 500U, xSocket.u.xTCP.ulUnpushedBytes );
        #else
            TEST_ASSERT_EQUAL( tcpTCP_FLAG_PSH, ucPrepareSendFlags( 1000 ) & tcpTCP_FLAG_PSH );
        #endif
    }
}

/* Equality must not push: the upstream rule is strictly greater than half the
 * window, including integer division for an odd advertised window. */
void test_prvTCPPrepareSend_PSH_HalfWindowBoundary( void )
{
    uint32_t ulWindowSize;
    size_t uxIndex;
    uint8_t ucFlags;

    for( ulWindowSize = 2000U; ulWindowSize <= 2001U; ulWindowSize++ )
    {
        prvSetUpSocket( ulWindowSize );

        for( uxIndex = 0; uxIndex < 3U; uxIndex++ )
        {
            ucFlags = ucPrepareSendFlags( 1000 );
            #if ( ipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY == ipconfigENABLE )
                TEST_ASSERT_EQUAL( ( uxIndex == 2U ) ? tcpTCP_FLAG_PSH : 0, ucFlags & tcpTCP_FLAG_PSH );
                TEST_ASSERT_EQUAL_UINT32( ( ( uxIndex + 1U ) % 3U ) * 500U, xSocket.u.xTCP.ulUnpushedBytes );
            #else
                TEST_ASSERT_EQUAL( tcpTCP_FLAG_PSH, ucFlags & tcpTCP_FLAG_PSH );
            #endif
        }
    }
}

void test_prvTCPPrepareSend_PSH_LastSegmentResetsCount( void )
{
    uint8_t ucFlags;

    prvSetUpSocket( 4000 );
    ( void ) ucPrepareSendFlags( 1000 );
    #if ( ipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY == ipconfigENABLE )
        TEST_ASSERT_EQUAL_UINT32( 500U, xSocket.u.xTCP.ulUnpushedBytes );
    #endif

    ucFlags = ucPrepareSendFlags( 500 );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_PSH, ucFlags & tcpTCP_FLAG_PSH );
    #if ( ipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY == ipconfigENABLE )
        TEST_ASSERT_EQUAL_UINT32( 0U, xSocket.u.xTCP.ulUnpushedBytes );
    #endif

    ucFlags = ucPrepareSendFlags( 1000 );
    #if ( ipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY == ipconfigENABLE )
        TEST_ASSERT_EQUAL( 0, ucFlags & tcpTCP_FLAG_PSH );
        TEST_ASSERT_EQUAL_UINT32( 500U, xSocket.u.xTCP.ulUnpushedBytes );
    #else
        TEST_ASSERT_EQUAL( tcpTCP_FLAG_PSH, ucFlags & tcpTCP_FLAG_PSH );
    #endif
}

/* Reuse the upstream six-segment sequence through both production functions,
 * alternating recent activity and ARP expiry without resetting the socket. */
void test_prvTCPPrepareAndReturn_PSH_HalfWindow( void )
{
    const uint8_t ucExpected[] = { 0, 0, tcpTCP_FLAG_PSH, 0, 0, tcpTCP_FLAG_PSH };
    size_t uxIndex;

    prvSetUpSocket( 2200 );

    for( uxIndex = 0; uxIndex < sizeof( ucExpected ); uxIndex++ )
    {
        vCheckPreparedSegment( 1000, ( uxIndex % 2U ) ? pdTRUE : pdFALSE, ucExpected[ uxIndex ] );
        #if ( ipconfigTCP_PSH_ON_LAST_SEGMENT_ONLY == ipconfigENABLE )
            TEST_ASSERT_EQUAL_UINT32( ( ( uxIndex + 1U ) % 3U ) * 500U, xSocket.u.xTCP.ulUnpushedBytes );
        #endif
    }
}
