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

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_TCP_Transmission.h"
#include "mock_FreeRTOS_TCP_Utils.h"
#include "mock_FreeRTOS_TCP_IP.h"
#include "mock_TCP_State_Handling_IPV4_list_macros.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* ===========================  EXTERN VARIABLES  =========================== */

FreeRTOS_Socket_t xSocket, * pxSocket;
NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;
uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ] =
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x08, 0x00, 0x45, 0x00,
    0x00, 0x34, 0x15, 0xc2, 0x40, 0x00, 0x40, 0x06, 0xa8, 0x8e, 0xc0, 0xa8, 0x00, 0x08, 0xac, 0xd9,
    0x0e, 0xea, 0xea, 0xfe, 0x01, 0xbb, 0x8b, 0xaf, 0x8a, 0x24, 0xdc, 0x96, 0x95, 0x7a, 0x80, 0x10,
    0x01, 0xf5, 0x7c, 0x9a, 0x00, 0x00, 0x01, 0x01, 0x08, 0x0a, 0xb8, 0x53, 0x57, 0x27, 0xb2, 0xce,
    0xc3, 0x17
};

uint8_t EthernetBuffer_Fin[ ipconfigNETWORK_MTU ] =
{
    0x8c, 0xdc, 0xd4, 0x4a, 0xea, 0x02, 0xa0, 0x40, 0xa0, 0x3a, 0x21, 0xea, 0x08, 0x00, 0x45, 0x20,
    0x00, 0x28, 0x51, 0x4a, 0x40, 0x00, 0xcf, 0x06, 0x14, 0x7b, 0xd1, 0x36, 0xb4, 0x03, 0xc0, 0xa8,
    0x00, 0x08, 0x01, 0xbb, 0xe9, 0xcc, 0xce, 0x19, 0x42, 0xb1, 0x6c, 0x98, 0x52, 0xe7, 0x50, 0x11,
    0x01, 0xb8, 0xac, 0x5e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};

uint8_t EthernetBuffer[ ipconfigNETWORK_MTU ] =
{
    0x8c, 0xdc, 0xd4, 0x4a, 0xea, 0x02, 0xa0, 0x40, 0xa0, 0x3a, 0x21, 0xea, 0x08, 0x00, 0x45, 0x20,
    0x00, 0x5b, 0xd2, 0xe9, 0x00, 0x00, 0x39, 0x06, 0x32, 0x47, 0xac, 0xd9, 0x0e, 0xc3, 0xc0, 0xa8,
    0x00, 0x08, 0x01, 0xbb, 0xdc, 0x44, 0xe2, 0x34, 0xd4, 0x84, 0xa7, 0xa9, 0xc1, 0xd8, 0x80, 0x18,
    0x01, 0x15, 0x2c, 0xed, 0x00, 0x00, 0x01, 0x01, 0x08, 0x0a, 0x7c, 0x17, 0x05, 0xb6, 0x9e, 0x62,
    0x6f, 0x27, 0x17, 0x03, 0x03, 0x00, 0x22, 0x1c, 0xeb, 0x68, 0x29, 0xea, 0x20, 0x2d, 0xb2, 0x6f,
    0x97, 0xdf, 0x26, 0xf5, 0x70, 0x9c, 0x09, 0xe0, 0x0d, 0xda, 0xf5, 0xf9, 0xd5, 0x37, 0x92, 0x4f,
    0x81, 0xe7, 0x65, 0x1e, 0xb1, 0x77, 0xcc, 0x72, 0x11
};

extern FreeRTOS_Socket_t * prvHandleListen_IPV4( FreeRTOS_Socket_t * pxSocket,
                                                 NetworkBufferDescriptor_t * pxNetworkBuffer );

/* ==============================  Test Cases  ============================== */

/**
 * @brief The packet IP address is not for endpoint.
 */
void test_prvHandleListen_IPV4_NotForMe( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    struct xNetworkEndPoint xEndPoint = { 0 };
    TCPPacket_t * pxTCPPacket;

    xEndPoint.ipv4_settings.ulIPAddress = 0x0700a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;

    pxTCPPacket = ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x12345678;

    pxSocket = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxSocket );
}

/**
 * @brief Flag of reuse socket is enabled.
 */
void test_prvHandleListen_IPV4_ReuseSocket( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdTRUE;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgs();
    vTCPStateChange_Ignore();

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxSocket, pxReturn );
    TEST_ASSERT_EQUAL( 1000, pxReturn->u.xTCP.xTCPWindow.ulOurSequenceNumber );
}

/**
 * @brief Number of child socket is beyond limitation.
 */
void test_prvHandleListen_IPV4_NewSocketExceedLimit( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 10;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Happy path.
 */
void test_prvHandleListen_IPV4_NewSocketGood( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( &MockReturnSocket );
    prvTCPSocketCopy_ExpectAndReturn( &MockReturnSocket, pxSocket, pdTRUE );
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgs();
    vTCPStateChange_ExpectAnyArgs();

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( &MockReturnSocket, pxReturn );
    TEST_ASSERT_EQUAL( 1000, pxReturn->u.xTCP.xTCPWindow.ulOurSequenceNumber );
}

/**
 * @brief Got NULL return when creating socket.
 */
void test_prvHandleListen_IPV4_NewSocketNULLSocket( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( NULL );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Fail to create socket.
 */
void test_prvHandleListen_IPV4_NewSocketInvalidSocket( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( FREERTOS_INVALID_SOCKET );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Failure happens in copy step.
 */
void test_prvHandleListen_IPV4_NewSocketSocketCopyFailure( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( &MockReturnSocket );
    prvTCPSocketCopy_ExpectAndReturn( &MockReturnSocket, pxSocket, pdFALSE );

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief The socket handler is NULL.
 */
void test_prvHandleListen_IPV4_NullSocket( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;

    pxReturn = prvHandleListen_IPV4( NULL, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief The network buffer pointer is NULL.
 */
void test_prvHandleListen_IPV4_NullNetworkBuffer( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;

    pxSocket = &xSocket;

    pxReturn = prvHandleListen_IPV4( pxSocket, NULL );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief The endpoint in network buffer is NULL.
 */
void test_prvHandleListen_IPV4_NullEndpoint( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}
