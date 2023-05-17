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
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_UDP_IPv6_list_macros.h"
#include "mock_FreeRTOS_DNS.h"

#include "FreeRTOS_DNS_Globals.h"
#include "FreeRTOS_UDP_IP.h"

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
