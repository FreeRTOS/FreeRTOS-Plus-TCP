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

#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_TCP_Transmission.h"
#include "mock_FreeRTOS_TCP_Reception.h"
#include "mock_TCP_State_Handling_list_macros.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_TCP_State_Handling.h"

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

extern BaseType_t prvTCPHandleFin( FreeRTOS_Socket_t * pxSocket,
                                   const NetworkBufferDescriptor_t * pxNetworkBuffer );

extern BaseType_t prvHandleSynReceived( FreeRTOS_Socket_t * pxSocket,
                                        const NetworkBufferDescriptor_t * pxNetworkBuffer,
                                        uint32_t ulReceiveLength,
                                        UBaseType_t uxOptionsLength );

extern BaseType_t prvHandleEstablished( FreeRTOS_Socket_t * pxSocket,
                                        NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                                        uint32_t ulReceiveLength,
                                        UBaseType_t uxOptionsLength );

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    pxSocket = NULL;
    pxNetworkBuffer = NULL;
}

/* ======================== Stub Callback Functions ========================= */

static uint32_t ulCalled = 0;
static void xLocalFunctionPointer( Socket_t xSocket,
                                   size_t xLength )
{
    ulCalled++;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief Check if socket is active in different states.
 */
void test_prvTCPSocketIsActive( void )
{
    BaseType_t xResult;

    /* Setup TCP option for tests */
    eIPTCPState_t Status;

    Status = eCLOSED;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );

    Status = eCLOSE_WAIT;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );

    Status = eFIN_WAIT_2;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );

    Status = eCLOSING;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );

    Status = eTIME_WAIT;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );

    Status = eTCP_LISTEN;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );

    Status = eCONNECT_SYN;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );

    Status = eSYN_FIRST;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );

    Status = eSYN_RECEIVED;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );

    Status = eESTABLISHED;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );

    Status = eFIN_WAIT_1;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );

    Status = eLAST_ACK;
    xResult = prvTCPSocketIsActive( Status );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

#if ( ipconfigTCP_HANG_PROTECTION == 1 )

/**
 * @brief No need to check timeout in some states.
 */
    void test_prvTCPStatusAgeCheck_NoChecksNeeded( void )
    {
        BaseType_t xResult = pdTRUE;

        pxSocket = &xSocket;

        pxSocket->u.xTCP.eTCPState = eESTABLISHED;
        xResult = prvTCPStatusAgeCheck( pxSocket );
        TEST_ASSERT_EQUAL( pdFALSE, xResult );

        pxSocket->u.xTCP.eTCPState = eCLOSED;
        xResult = prvTCPStatusAgeCheck( pxSocket );
        TEST_ASSERT_EQUAL( pdFALSE, xResult );

        pxSocket->u.xTCP.eTCPState = eTCP_LISTEN;
        xResult = prvTCPStatusAgeCheck( pxSocket );
        TEST_ASSERT_EQUAL( pdFALSE, xResult );

        pxSocket->u.xTCP.eTCPState = eCLOSE_WAIT;
        xResult = prvTCPStatusAgeCheck( pxSocket );
        TEST_ASSERT_EQUAL( pdFALSE, xResult );
    }

/**
 * @brief Keep waiting when timeout is not triggered.
 */
    void test_prvTCPStatusAgeCheck_ChecksDoneAgeLEProtectiontime( void )
    {
        BaseType_t xResult = pdTRUE;

        pxSocket = &xSocket;

        pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
        pxSocket->u.xTCP.xLastAliveTime = 1000;

        xTaskGetTickCount_ExpectAndReturn( 2000 );
        xResult = prvTCPStatusAgeCheck( pxSocket );
        TEST_ASSERT_EQUAL( pdTRUE, xResult );
    }

/**
 * @brief Start close procedure when waiting SYN/ACK timeout.
 */
    void test_prvTCPStatusAgeCheck_ChecksDoneAgeGTProtectiontime( void )
    {
        BaseType_t xResult = pdTRUE;

        pxSocket = &xSocket;

        pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
        pxSocket->u.xTCP.xLastAliveTime = 1000;

        xTaskGetTickCount_ExpectAndReturn( 32000 );
        vTCPStateChange_ExpectAnyArgs();
        xResult = prvTCPStatusAgeCheck( pxSocket );
        TEST_ASSERT_EQUAL( pdTRUE, xResult );
    }

/**
 * @brief Start close procedure when waiting SYN/ACK timeout.
 * And the pass queue is true.
 */
    void test_prvTCPStatusAgeCheck_ChecksDonePassQueueBitTrue( void )
    {
        BaseType_t xResult = pdTRUE;

        pxSocket = &xSocket;

        pxSocket->u.xTCP.eTCPState = eSYN_FIRST;
        pxSocket->u.xTCP.xLastAliveTime = 1000;
        pxSocket->u.xTCP.bits.bPassQueued = pdTRUE;

        xTaskGetTickCount_ExpectAndReturn( 32000 );
        vTCPStateChange_ExpectAnyArgs();
        xResult = prvTCPStatusAgeCheck( pxSocket );
        TEST_ASSERT_EQUAL( -1, xResult );
    }

#endif /* if ( ipconfigTCP_HANG_PROTECTION == 1 ) */

/**
 * @brief Receive FIN packet when FIN sent/ack/recv/last are all not true.
 */
void test_prvTCPHandleFin_FIN_BitsAllFalse( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    uint32_t ulAckNr = FreeRTOS_ntohl( pxTCPHeader->ulAckNr );

    pxTCPHeader->ucTCPFlags = 0;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxTCPWindow->tx.ulCurrentSequenceNumber = 2000;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE;
    pxTCPHeader->ulAckNr = 2000;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    vTCPStateChange_ExpectAnyArgs();
    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    xSendLength = prvTCPHandleFin( pxSocket, ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 40, xSendLength );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->tx.ulFINSequenceNumber );
}

/**
 * @brief Receive FIN packet when FIN recv is not true.
 */
void test_prvTCPHandleFin_FIN_FINSentFINACKNoFINRecv( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    uint32_t ulAckNr = FreeRTOS_ntohl( pxTCPHeader->ulAckNr );

    pxTCPHeader->ucTCPFlags |= tcpTCP_FLAG_FIN;
    pxTCPHeader->ulAckNr = FreeRTOS_htonl( 2001 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxTCPWindow->tx.ulCurrentSequenceNumber = 2000;
    pxTCPWindow->tx.ulFINSequenceNumber = 2000;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAcked = pdTRUE;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    xSendLength = prvTCPHandleFin( pxSocket, ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 0, xSendLength );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->tx.ulFINSequenceNumber );
}

/**
 * @brief Receive FIN packet when FIN last is not true.
 */
void test_prvTCPHandleFin_FIN_FINRecvFINSentFINACKFINNotLast( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    uint32_t ulAckNr = FreeRTOS_ntohl( pxTCPHeader->ulAckNr );

    pxTCPHeader->ucTCPFlags |= tcpTCP_FLAG_FIN;
    pxTCPHeader->ulAckNr = FreeRTOS_htonl( 2001 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxTCPWindow->tx.ulCurrentSequenceNumber = 2000;
    pxTCPWindow->tx.ulFINSequenceNumber = 2000;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAcked = pdTRUE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    vTCPStateChange_ExpectAnyArgs();
    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    xSendLength = prvTCPHandleFin( pxSocket, ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 40, xSendLength );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->tx.ulFINSequenceNumber );
}

/**
 * @brief Receive FIN packet when FIN sent/ack/recv/last are all true.
 */
void test_prvTCPHandleFin_FIN_FINRecvFINSentFINACKFINLast( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    uint32_t ulAckNr = FreeRTOS_ntohl( pxTCPHeader->ulAckNr );

    pxTCPHeader->ucTCPFlags |= tcpTCP_FLAG_FIN;
    pxTCPHeader->ulAckNr = 2001;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxTCPWindow->tx.ulCurrentSequenceNumber = 2000;
    pxTCPWindow->tx.ulFINSequenceNumber = 2000;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAcked = pdTRUE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxSocket->u.xTCP.bits.bFinLast = pdTRUE;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvTCPHandleFin( pxSocket, ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 0, xSendLength );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->tx.ulFINSequenceNumber );
}

/**
 * @brief Receive SYN packet when waiting for it.
 */
void test_prvHandleSynReceived_ExpSYNStateConnectSyn( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_SYN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = 0;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    vTCPWindowInit_ExpectAnyArgs();
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( ( void * ) 0x1234 );
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleSynReceived( pxSocket,
                                        ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/**
 * @brief Receive SYN IPv6 packet when waiting for it.
 */
void test_prvHandleSynReceived_ExpSYNStateConnectSynIPv6( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->bits.bIsIPv6 = pdTRUE_UNSIGNED;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_SYN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = 0;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    vTCPWindowInit_ExpectAnyArgs();
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( ( void * ) 0x1234 );
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleSynReceived( pxSocket,
                                        ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/**
 * @brief Trigger close procedure when expect SYN packet but receive packet without SYN.
 */
void test_prvHandleSynReceived_NotSYNStateConnectSyn( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->ulAckNr = 1;
    pxTCPHeader->ulSequenceNumber = 0;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleSynReceived( pxSocket,
                                        ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/**
 * @brief Trigger close procedure when not expect SYN packet but receive one.
 */
void test_prvHandleSynReceived_NotExpSYNStateSynreceived( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eSYN_RECEIVED;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_SYN;
    pxTCPHeader->ulAckNr = 1;
    pxTCPHeader->ulSequenceNumber = 0;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleSynReceived( pxSocket,
                                        ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/**
 * @brief Handle an ACK packet.
 */
void test_prvHandleSynReceived_ExpACKStateSynreceivedZeroData( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eSYN_RECEIVED;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = 0;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( ( void * ) 0x1234 );
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleSynReceived( pxSocket,
                                        ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/**
 * @brief Handle an ACK packet with window scaling enabled.
 */
void test_prvHandleSynReceived_ExpACKStateSynreceivedNonZeroDataWinScaling( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eSYN_RECEIVED;
    pxSocket->u.xTCP.bits.bWinScaling = pdTRUE;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = 0;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( ( void * ) 0x1234 );
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleSynReceived( pxSocket,
                                        ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer,
                                        20,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/**
 * @brief Handle a packet without ACK flag.
 */
void test_prvHandleEstablished_NoACK( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;

    pxTCPHeader->ucTCPFlags = 0;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        1000,
                                        0 );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/**
 * @brief Happy path to handle ACK packet.
 */
void test_prvHandleEstablished_ACKHappy( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 1000 );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 1000 );
    prvTCPAddTxData_ExpectAnyArgs();
    prvTCPPrepareSend_ExpectAnyArgsAndReturn( 1040 );

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        1000,
                                        0 );
    TEST_ASSERT_EQUAL( 1040, xSendLength );
    TEST_ASSERT_EQUAL( 1, ulCalled );
}

/**
 * @brief Receive packet with NULL TX stream.
 */
void test_prvHandleEstablished_ACKNullTXRecvZero( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 1000 );
    prvTCPPrepareSend_ExpectAnyArgsAndReturn( 40 );

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
    TEST_ASSERT_EQUAL( 0, ulCalled );
}

/**
 * @brief Return basic header size and option length to send ACK back when option length is not zero.
 */
void test_prvHandleEstablished_ACKWinZeroRecvZero_HasOption( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    prvTCPAddTxData_ExpectAnyArgs();

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        1000,
                                        12 );
    TEST_ASSERT_EQUAL( 52, xSendLength );
    TEST_ASSERT_EQUAL( 0, ulCalled );
}

/**
 * @brief No buffer available to send, return basic header size to send ACK back.
 */
void test_prvHandleEstablished_ACKBufferZeroPrepFalse( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 1000 );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 0 );
    prvTCPAddTxData_ExpectAnyArgs();
    prvTCPPrepareSend_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        1000,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
    TEST_ASSERT_EQUAL( 0, ulCalled );
}

/**
 * @brief Happy path to send packet back with select bit when receiving TCP packet with ACK.
 * But no callback registered.
 */
void test_prvHandleEstablished_ACKHappySelectNoHandler( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxSocket->xSelectBits = eSELECT_WRITE;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 1000 );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 1000 );
    prvTCPAddTxData_ExpectAnyArgs();
    prvTCPPrepareSend_ExpectAnyArgsAndReturn( 1040 );

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        1000,
                                        0 );
    TEST_ASSERT_EQUAL( 1040, xSendLength );
}

/**
 * @brief Trigger closing flow when first receiving TCP packet with FIN/ACK.
 */
void test_prvHandleEstablished_FINNotSentRXComplete( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2501;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    prvTCPAddTxData_ExpectAnyArgs();
    xTCPWindowRxEmpty_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdTRUE );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/**
 * @brief Data left for receiving when receiving TCP packet with FIN/ACK.
 */
void test_prvHandleEstablished_FINNotSentRXNotComplete( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2501;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    prvTCPAddTxData_ExpectAnyArgs();
    xTCPWindowRxEmpty_ExpectAnyArgsAndReturn( pdFALSE );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdTRUE );
    prvTCPPrepareSend_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/**
 * @brief Data left for sending when receiving TCP packet with FIN/ACK.
 */
void test_prvHandleEstablished_FINNotSentTXWinNotComplete( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2501;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    prvTCPAddTxData_ExpectAnyArgs();
    xTCPWindowRxEmpty_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdFALSE );
    prvTCPPrepareSend_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/**
 * @brief RX sequence doesn't match when receiving TCP packet with FIN/ACK.
 */
void test_prvHandleEstablished_FINNotSentDataLeft( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2200;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    prvTCPAddTxData_ExpectAnyArgs();
    xTCPWindowRxEmpty_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdTRUE );
    prvTCPPrepareSend_ExpectAnyArgsAndReturn( 40 );

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        1000,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/**
 * @brief Fin sent bit was set before receiving an ACK packet.
 */
void test_prvHandleEstablished_FINSentACKPacket( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2200;
    pxTCPWindow->tx.ulCurrentSequenceNumber = 1999;
    pxTCPWindow->tx.ulFINSequenceNumber = 2000;

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    prvTCPPrepareSend_ExpectAnyArgsAndReturn( 40 );

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        1000,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->tx.ulCurrentSequenceNumber );
}

/**
 * @brief Need to release resources when receiving TCP packet with FIN/ACK.
 */
void test_prvHandleEstablished_FINSent( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2501;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    prvTCPAddTxData_ExpectAnyArgs();
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/**
 * @brief FIN was accepted before receiving an ACK packet.
 */
void test_prvHandleEstablished_FINAccept( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdTRUE;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2501;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    xTCPWindowRxEmpty_ExpectAnyArgsAndReturn( pdFALSE );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdFALSE );
    prvTCPPrepareSend_ExpectAnyArgsAndReturn( 40 );

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        1000,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/**
 * @brief Get TCP packet with ACK when the state of socket is eCLOSED.
 * To simulate malloc fail case.
 */
void test_prvTCPHandleState_ClosedMallocFailure( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxSocket->u.xTCP.eTCPState = eCLOSED;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1500;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 1000 );
    prvStoreRxData_ExpectAnyArgsAndReturn( -1 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( -1, xSendLength );
}

/**
 * @brief Get TCP packet with ACK when the state of socket is eCLOSED.
 */
void test_prvTCPHandleState_Closed( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxSocket->u.xTCP.eTCPState = eCLOSED;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1500;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 1000 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 1000 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/**
 * @brief Get TCP packet with ACK when the state of socket is eTCP_LISTEN.
 */
void test_prvTCPHandleState_TCPListen( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eTCP_LISTEN;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1500;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 1000 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 1000 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/**
 * @brief Get TCP packet with no flag when the state of socket is eSYN_FIRST.
 */
void test_prvTCPHandleState_SYNFirst( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eSYN_FIRST;
    pxTCPHeader->ucTCPFlags = 0;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1500;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 1000 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 1000 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );
    prvSetSynAckOptions_ExpectAnyArgsAndReturn( 0 );
    vTCPStateChange_ExpectAnyArgs();
    prvSendData_ExpectAnyArgsAndReturn( 1040 );


    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1001, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( ( uint8_t ) tcpTCP_FLAG_SYN | ( uint8_t ) tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( 1040, xSendLength );
}

/**
 * @brief Get TCP packet with ACK when the state of socket is eCONNECT_SYN.
 */
void test_prvTCPHandleState_ConnectSyn( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1500;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 1000 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 1000 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );
    vTCPStateChange_ExpectAnyArgs();
    prvSendData_ExpectAnyArgsAndReturn( 60 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 60, xSendLength );
}

/**
 * @brief Get TCP packet with SYN when the state of socket is eSYN_RECEIVED.
 */
void test_prvTCPHandleState_SynReceived( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eSYN_RECEIVED;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_SYN;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1500;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 1000 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 1000 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );
    vTCPStateChange_ExpectAnyArgs();
    vTCPStateChange_ExpectAnyArgs();
    prvSendData_ExpectAnyArgsAndReturn( 60 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 60, xSendLength );
}

/**
 * @brief Get TCP packet with ACK when the state of socket is eSYN_RECEIVED.
 */
void test_prvTCPHandleState_SynReceivedFlagNotSyn( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eSYN_RECEIVED;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1500;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 1000 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 1000 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( "" );
    vTCPStateChange_ExpectAnyArgs();
    prvSendData_ExpectAnyArgsAndReturn( 60 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 60, xSendLength );
}

/**
 * @brief Get TCP packet with ACK when the state of socket is eESTABLISHED.
 */
void test_prvTCPHandleState_Established_DataAck( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1500;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 1000 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 1000 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 1500 );
    prvTCPPrepareSend_ExpectAnyArgsAndReturn( 1000 );
    prvSendData_ExpectAnyArgsAndReturn( 1000 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 1000, xSendLength );
}

/**
 * @brief Get TCP packet with FIN when the state of socket is eESTABLISHED.
 */
void test_prvTCPHandleState_Established_FirstFinFromPeer( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 1500 );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 1000 );
    prvTCPAddTxData_ExpectAnyArgs();
    xTCPWindowRxEmpty_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdTRUE );
    vTCPStateChange_ExpectAnyArgs();
    prvSendData_ExpectAnyArgsAndReturn( 40 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( 1, ulCalled );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/**
 * @brief Get TCP packet when the state of socket is eLAST_ACK.
 */
void test_prvTCPHandleState_LastAck( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxSocket->u.xTCP.eTCPState = eLAST_ACK;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAcked = pdTRUE;
    pxSocket->u.xTCP.bits.bFinLast = pdTRUE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/**
 * @brief Get TCP packet with FIN flag when the state of socket is eFIN_WAIT_1.
 */
void test_prvTCPHandleState_FinWait1_FinFromPeer( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = eFIN_WAIT_1;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );
    vTCPStateChange_ExpectAnyArgs();
    prvSendData_ExpectAnyArgsAndReturn( 40 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulCalled );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/**
 * @brief Get TCP packet when the state of socket is eCLOSE_WAIT.
 */
void test_prvTCPHandleState_CloseWait( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = eCLOSE_WAIT;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->rx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/**
 * @brief Get TCP packet when the state of socket is eCLOSING.
 */
void test_prvTCPHandleState_ClosingKeepAlive( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = eCLOSING;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->rx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/**
 * @brief Get TCP packet when the state of socket is eTIME_WAIT.
 */
void test_prvTCPHandleState_TimeWait( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = eTIME_WAIT;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdTRUE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->rx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/**
 * @brief Get TCP packet when the state of socket is unknown.
 */
void test_prvTCPHandleState_StateUnknown( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = 12;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdTRUE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->rx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/**
 * @brief Call prvHandleListen with IPv4 packet.
 */
void test_prvHandleListen_IPv4Packet( void )
{
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    prvHandleListen_IPV4_ExpectAndReturn( pxSocket, pxNetworkBuffer, NULL );

    pxSocket = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxSocket );
}

/**
 * @brief Call prvHandleListen with IPv6 packet.
 */
void test_prvHandleListen_IPv6Packet( void )
{
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv6_HEADER );
    prvHandleListen_IPV6_ExpectAndReturn( pxSocket, pxNetworkBuffer, NULL );

    pxSocket = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxSocket );
}

/**
 * @brief Call prvHandleListen with unknown IP type packet.
 */
void test_prvHandleListen_UnknownIPType( void )
{
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER + 1 );

    pxSocket = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxSocket );
}

/**
 * @brief Socket handler has NULL socket set pointer.
 */
void test_prvTCPSocketCopy_NullSocketSet( void )
{
    BaseType_t Result = pdFALSE;

    FreeRTOS_Socket_t MockReturnSocket;

    pxSocket = &xSocket;

    pxSocket->usLocalPort = 22;
    pxSocket->u.xTCP.uxTxWinSize = 0x123456;
    pxSocket->pxSocketSet = NULL;
    pxSocket->xSelectBits = eSELECT_READ;

    vSocketBind_ExpectAnyArgsAndReturn( 0 );

    Result = prvTCPSocketCopy( &MockReturnSocket, pxSocket );
    TEST_ASSERT_EQUAL( pdTRUE, Result );
    TEST_ASSERT_NOT_EQUAL( pxSocket->usLocalPort, MockReturnSocket.usLocalPort );
    TEST_ASSERT_EQUAL( pxSocket->u.xTCP.uxTxWinSize, MockReturnSocket.u.xTCP.uxTxWinSize );
    TEST_ASSERT_NOT_EQUAL( ( pxSocket->xSelectBits | eSELECT_READ | eSELECT_EXCEPT ), MockReturnSocket.xSelectBits );
}

/**
 * @brief Get fail return in bind function.
 */
void test_prvTCPSocketCopy_BindError( void )
{
    BaseType_t Result = pdFALSE;

    FreeRTOS_Socket_t MockReturnSocket;

    pxSocket = &xSocket;

    pxSocket->usLocalPort = 22;
    pxSocket->u.xTCP.uxTxWinSize = 0x123456;
    pxSocket->pxSocketSet = ( struct xSOCKET_SET * ) 0x1111111;
    pxSocket->xSelectBits = eSELECT_READ;

    vSocketBind_ExpectAnyArgsAndReturn( 1 );
    vSocketClose_ExpectAnyArgsAndReturn( NULL );

    Result = prvTCPSocketCopy( &MockReturnSocket, pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, Result );
    TEST_ASSERT_NOT_EQUAL( pxSocket->usLocalPort, MockReturnSocket.usLocalPort );
    TEST_ASSERT_EQUAL( pxSocket->u.xTCP.uxTxWinSize, MockReturnSocket.u.xTCP.uxTxWinSize );
    TEST_ASSERT_EQUAL( ( pxSocket->xSelectBits | eSELECT_READ | eSELECT_EXCEPT ), MockReturnSocket.xSelectBits );
}

/**
 * @brief Test for FreeRTOS_GetTCPStateName function.
 */
void test_FreeRTOS_GetTCPStateName( void )
{
    const char * ReturnStateName;

    ReturnStateName = FreeRTOS_GetTCPStateName( 0 );

    TEST_ASSERT_EQUAL_STRING( "eCLOSED", ReturnStateName );
}

/**
 * @brief Negative index as input.
 */
void test_FreeRTOS_GetTCPStateName_NegativeIndex( void )
{
    const char * ReturnStateName;

    ReturnStateName = FreeRTOS_GetTCPStateName( -1 );

    TEST_ASSERT_EQUAL_STRING( "eUNKNOWN", ReturnStateName );
}

/**
 * @brief Input with index greater than maximum.
 */
void test_FreeRTOS_GetTCPStateName_GreaterIndex( void )
{
    const char * ReturnStateName;

    ReturnStateName = FreeRTOS_GetTCPStateName( 30 );

    TEST_ASSERT_EQUAL_STRING( "eUNKNOWN", ReturnStateName );
}
