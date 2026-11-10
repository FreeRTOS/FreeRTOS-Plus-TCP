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
#include "FreeRTOSIPConfigDefaults.h"

#include "FreeRTOS_TCP_Transmission_DiffConfig_stubs.c"
#include "FreeRTOS_TCP_Transmission.h"

/* ============================ Test Variables ============================ */

static FreeRTOS_Socket_t xSocket;
static NetworkBufferDescriptor_t xNetworkBuffer;
static uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];

static struct xNetworkEndPoint xEndPoint;
static struct xNetworkInterface xInterface;

static const MACAddress_t xTemplateMAC = { { 0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC } };
static const MACAddress_t xCacheMAC = { { 0x21, 0x43, 0x65, 0x87, 0xA9, 0xCB } };

/* ============================ Test Helpers ============================ */

/* Prepares a connected socket whose header template holds xTemplateMAC, last
 * heard from at tick 100, and sets the expectations that prvTCPReturnPacket()
 * has for any segment. */
static TCPPacket_t * pxPrepareReturnPacket( void )
{
    TCPPacket_t * pxTCPPacket = ( TCPPacket_t * ) ucEthernetBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    xEndPoint.pxNetworkInterface = &xInterface;
    xEndPoint.ipv4_settings.ulIPAddress = 0xC0C0C0C0;
    xInterface.pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    xSocket.pxEndPoint = &xEndPoint;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    xSocket.u.xTCP.uxRxStreamSize = 1500;
    xSocket.u.xTCP.usMSS = 1000;
    xSocket.u.xTCP.xLastActTime = 100;
    xSocket.u.xTCP.xTCPWindow.xSize.ulRxWindowLength = 500;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    pxTCPPacket->xEthernetHeader.xSourceAddress = xTemplateMAC;
    ( ( TCPPacket_t * ) xSocket.u.xTCP.xPacket.u.ucLastPacket )->xEthernetHeader.xSourceAddress = xTemplateMAC;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );

    return pxTCPPacket;
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

    xTaskGetTickCount_IgnoreAndReturn( 100 + pdMS_TO_TICKS( ipconfigTCP_SKIP_ARP_LOOKUP_MS ) - 1 );

    prvTCPReturnPacket( &xSocket, &xNetworkBuffer, 40, pdFALSE );

    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( xTemplateMAC.ucBytes, pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
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

    xTaskGetTickCount_IgnoreAndReturn( 100 + pdMS_TO_TICKS( ipconfigTCP_SKIP_ARP_LOOKUP_MS ) );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eResolutionCacheHit );
    eARPGetCacheEntry_ReturnThruPtr_pxMACAddress( ( MACAddress_t * ) &xCacheMAC );
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );

    prvTCPReturnPacket( &xSocket, &xNetworkBuffer, 40, pdFALSE );

    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( xCacheMAC.ucBytes, pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( xCacheMAC.ucBytes,
                                   ( ( TCPPacket_t * ) xSocket.u.xTCP.xPacket.u.ucLastPacket )->xEthernetHeader.xSourceAddress.ucBytes,
                                   ipMAC_ADDRESS_LENGTH_BYTES );
}
