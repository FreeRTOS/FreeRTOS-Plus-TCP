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

#include "mock_task.h"
#include "mock_list.h"

#include "FreeRTOSIPConfig.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_FreeRTOS_UDP_IPv6_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_ND.h"
#include "mock_FreeRTOS_IP_Utils.h"

#include "FreeRTOS_DNS_Globals.h"
#include "FreeRTOS_UDP_IP.h"

#include "FreeRTOS_UDP_IPv6_stubs.c"
#include "catch_assert.h"

/* ===========================  EXTERN VARIABLES  =========================== */

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
}

/*! called after each test case */
void tearDown( void )
{
}

/* ======================== Stub Callback Functions ========================= */

void UDPReceiveHandlerChecker( Socket_t xSocket,
                                                  void * pData,
                                                  size_t xLength,
                                                  const struct freertos_sockaddr * pxFrom,
                                                  const struct freertos_sockaddr * pxDest )
{
    uint8_t * pucData = ( uint8_t * ) pData;
    UDPPacket_IPv6_t * pxUDPv6Packet = pucData - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_UDP_HEADER );

    TEST_ASSERT_EQUAL_MEMORY( pxUDPv6Packet->xIPHeader.xSourceAddress.ucBytes, pxFrom->sin_address.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( pxUDPv6Packet->xIPHeader.xDestinationAddress.ucBytes, pxDest->sin_address.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( pxUDPv6Packet->xUDPHeader.usSourcePort, pxFrom->sin_port );
    TEST_ASSERT_EQUAL( pxUDPv6Packet->xUDPHeader.usDestinationPort, pxDest->sin_port );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, pxFrom->sin_family );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, pxDest->sin_family );
    TEST_ASSERT_EQUAL( sizeof( struct freertos_sockaddr ), pxFrom->sin_len );
    TEST_ASSERT_EQUAL( sizeof( struct freertos_sockaddr ), pxDest->sin_len );
    TEST_ASSERT_EQUAL( pxUDPv6Packet->xIPHeader.usPayloadLength - ipSIZE_OF_UDP_HEADER, xLength );
}

BaseType_t xStubUDPReceiveHandler_Pass( Socket_t xSocket,
                                                  void * pData,
                                                  size_t xLength,
                                                  const struct freertos_sockaddr * pxFrom,
                                                  const struct freertos_sockaddr * pxDest )
{
    UDPReceiveHandlerChecker( xSocket, pData, xLength, pxFrom, pxDest );
    return 0;
}

BaseType_t xStubUDPReceiveHandler_Fail( Socket_t xSocket,
                                                  void * pData,
                                                  size_t xLength,
                                                  const struct freertos_sockaddr * pxFrom,
                                                  const struct freertos_sockaddr * pxDest )
{
    UDPReceiveHandlerChecker( xSocket, pData, xLength, pxFrom, pxDest );
    return -1;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_NullInput
 * Trigger assertion when input network buffer pointer is NULL.
 */
void test_xProcessReceivedUDPPacket_IPv6_NullInput()
{
    BaseType_t xIsWaitingForARPResolution;
    catch_assert( xProcessReceivedUDPPacket_IPv6( NULL, 0, &xIsWaitingForARPResolution ) );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_NullBufferPointer
 * Trigger assertion when input buffer pointer in network buffer is NULL.
 */
void test_xProcessReceivedUDPPacket_IPv6_NullBufferPointer()
{
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    catch_assert( xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, 0, &xIsWaitingForARPResolution ) );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_ZeroChecksum
 * Return fail due to zero checksum.
 */
void test_xProcessReceivedUDPPacket_IPv6_ZeroChecksum()
{
    BaseType_t xReturn;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0U;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_DNSReplyPass
 * To validate the scenario that receives DNS reply packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_DNSReplyPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipDNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_DNSReplyFail
 * To validate the scenario that receives DNS reply packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_DNSReplyFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipDNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_LLMNRRequestPass
 * To validate the scenario that receives LLMNR request packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_LLMNRRequestPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipLLMNR_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_LLMNRRequestFail
 * To validate the scenario that receives LLMNR request packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_LLMNRRequestFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipLLMNR_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_LLMNRReplyPass
 * To validate the scenario that receives LLMNR reply packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_LLMNRReplyPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipLLMNR_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_LLMNRReplyFail
 * To validate the scenario that receives LLMNR reply packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_LLMNRReplyFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipLLMNR_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_NBNSRequestPass
 * To validate the scenario that receives NBNS request packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_NBNSRequestPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipNBNS_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_NBNSRequestFail
 * To validate the scenario that receives NBNS request packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_NBNSRequestFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipNBNS_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_NBNSReplyPass
 * To validate the scenario that receives NBNS Reply packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_NBNSReplyPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipNBNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_NBNSReplyFail
 * To validate the scenario that receives NBNS Reply packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_NBNSReplyFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipNBNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_NoSocket
 * To validate the scenario that no one is waiting for the packet.
 */
void test_xProcessReceivedUDPPacket_IPv6_NoSocket()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_SocketNeedND
 * To validate the flow that socket needs neighbor discovery.
 */
void test_xProcessReceivedUDPPacket_IPv6_SocketNeedND()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xIsWaitingForARPResolution );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_SocketRecvHandlerFail
 * To validate the flow that socket receive handler returns fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_SocketRecvHandlerFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = xStubUDPReceiveHandler_Fail;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_UDPListBufferFull
 * To validate the flow that list of the socket is full and return fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_UDPListBufferFull()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = xStubUDPReceiveHandler_Pass;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    // listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket.u.xUDP.xWaitingPacketsList ), xSocket.u.xUDP.uxMaxPackets );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = xSocket.u.xUDP.uxMaxPackets;

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_Pass
 * To validate the flow that all flows (list/event group/select/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_Pass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE, pdPASS );
    
    xSocket.pxSocketSet = &xSocketSet;
    xSocket.xSelectBits |= eSELECT_READ;
    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );

    /* xSemaphoreGive is defined as xQueueGenericSend */
    xSocket.pxUserSemaphore = &xSocketSem;
    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdTRUE );
    xSendDHCPEvent_ExpectAndReturn( xNetworkBuffer.pxEndPoint, pdPASS );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_PassNoEventGroup
 * To validate the flow that all flows except for event group (list/select/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_PassNoEventGroup()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = NULL;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );
    
    xSocket.pxSocketSet = &xSocketSet;
    xSocket.xSelectBits |= eSELECT_READ;
    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );

    /* xSemaphoreGive is defined as xQueueGenericSend */
    xSocket.pxUserSemaphore = &xSocketSem;
    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdTRUE );
    xSendDHCPEvent_ExpectAndReturn( xNetworkBuffer.pxEndPoint, pdPASS );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_PassNoSelectBit
 * To validate the flow that all flows except for select bit (list/event group/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_PassNoSelectBit()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE, pdPASS );
    
    xSocket.pxSocketSet = &xSocketSet;

    /* xSemaphoreGive is defined as xQueueGenericSend */
    xSocket.pxUserSemaphore = &xSocketSem;
    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdTRUE );
    xSendDHCPEvent_ExpectAndReturn( xNetworkBuffer.pxEndPoint, pdPASS );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_PassNoSelectSet
 * To validate the flow that all flows except for select set (list/event group/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_PassNoSelectSet()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE, pdPASS );

    /* xSemaphoreGive is defined as xQueueGenericSend */
    xSocket.pxUserSemaphore = &xSocketSem;
    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdTRUE );
    xSendDHCPEvent_ExpectAndReturn( xNetworkBuffer.pxEndPoint, pdPASS );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_PassNoSem
 * To validate the flow that all flows except for sem (list/event group/select/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_PassNoSem()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE, pdPASS );
    
    xSocket.pxSocketSet = &xSocketSet;
    xSocket.xSelectBits |= eSELECT_READ;
    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdTRUE );
    xSendDHCPEvent_ExpectAndReturn( xNetworkBuffer.pxEndPoint, pdPASS );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_xProcessReceivedUDPPacket_IPv6_PassNoDHCP
 * To validate the flow that all flows except for DHCP (list/event group/select/queue) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_PassNoDHCP()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE, pdPASS );
    
    xSocket.pxSocketSet = &xSocketSet;
    xSocket.xSelectBits |= eSELECT_READ;
    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );

    /* xSemaphoreGive is defined as xQueueGenericSend */
    xSocket.pxUserSemaphore = &xSocketSem;
    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdFALSE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}
