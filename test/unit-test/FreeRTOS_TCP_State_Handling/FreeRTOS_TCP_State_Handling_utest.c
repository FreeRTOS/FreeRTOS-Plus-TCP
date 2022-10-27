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

/*#include "mock_task.h" */
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
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
#include "mock_FreeRTOS_TCP_Transmission.h"
#include "mock_FreeRTOS_TCP_Reception.h"
#include "mock_FreeRTOS_TCP_Utils.h"

#include "FreeRTOS_TCP_IP.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_TCP_State_Handling_stubs.c"
#include "FreeRTOS_TCP_State_Handling.h"


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

/* Test for prvTCPSocketIsActive function. */
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
/* test for prvTCPStatusAgeCheck function */
    void test_prvTCPStatusAgeCheck_No_Checks_Needed( void )
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

/* test for prvTCPStatusAgeCheck function */
    void test_prvTCPStatusAgeCheck_Checks_Done_Age_LE_Protectiontime( void )
    {
        BaseType_t xResult = pdTRUE;

        pxSocket = &xSocket;

        pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
        pxSocket->u.xTCP.xLastAliveTime = 1000;

        xTaskGetTickCount_ExpectAndReturn( 2000 );
        xResult = prvTCPStatusAgeCheck( pxSocket );
        TEST_ASSERT_EQUAL( pdTRUE, xResult );
    }

/* test for prvTCPStatusAgeCheck function */
    void test_prvTCPStatusAgeCheck_Checks_Done_Age_GT_Protectiontime( void )
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

/* test for prvTCPStatusAgeCheck function */
    void test_prvTCPStatusAgeCheck_Checks_Done_PassQueueBit_True( void )
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

/* test for prvTCPHandleFin function */

void test_prvTCPHandleFin_Recv_No_FIN_Not_Sent_FINACK_Not_Sent( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    uint32_t ulAckNr = FreeRTOS_ntohl( pxTCPHeader->ulAckNr );

    pxTCPHeader->ucTCPFlags = 0;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxTCPWindow->tx.ulCurrentSequenceNumber = 2000;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE;
    pxTCPHeader->ulAckNr = 2000;

    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvTCPHandleFin( pxSocket, ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 40, xSendLength );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->tx.ulFINSequenceNumber );
}
/* test for prvTCPHandleFin function */
void test_prvTCPHandleFin_Recv_FIN_FIN_Sent_FINACK_Sent_Recv_No_FIN( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
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

    xSendLength = prvTCPHandleFin( pxSocket, ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 0, xSendLength );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->tx.ulFINSequenceNumber );
}

/* test for prvTCPHandleFin function */
void test_prvTCPHandleFin_Recv_FIN_FIN_Sent_FINACK_Sent_Recv_FIN_Not_Last( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
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

    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvTCPHandleFin( pxSocket, ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 40, xSendLength );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->tx.ulFINSequenceNumber );
}

/* test for prvTCPHandleFin function */
void test_prvTCPHandleFin_Recv_FIN_FIN_Sent_FINACK_Sent_Recv_FIN_Last( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
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

    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvTCPHandleFin( pxSocket, ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 0, xSendLength );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->tx.ulFINSequenceNumber );
}

/* test for prvHandleSynReceived function */
void test_prvHandleSynReceived_Exp_SYN_State_ConnectSyn( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_SYN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = 0;

    vTCPWindowInit_ExpectAnyArgs();
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleSynReceived( pxSocket,
                                        ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/* test for prvHandleSynReceived function */
void test_prvHandleSynReceived_Not_Exp_SYN_State_ConnectSyn( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->ulAckNr = 1;
    pxTCPHeader->ulSequenceNumber = 0;

    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleSynReceived( pxSocket,
                                        ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/* test for prvHandleSynReceived function */
void test_prvHandleSynReceived_Not_Exp_SYN_State_Synreceived( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eSYN_RECEIVED;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_SYN;
    pxTCPHeader->ulAckNr = 1;
    pxTCPHeader->ulSequenceNumber = 0;

    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleSynReceived( pxSocket,
                                        ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

/* test for prvHandleSynReceived function */
void test_prvHandleSynReceived_Exp_ACK_State_Synreceived_Zero_Data( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eSYN_RECEIVED;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = 0;

    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleSynReceived( pxSocket,
                                        ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}


/* test for prvHandleSynReceived function */
void test_prvHandleSynReceived_Exp_ACK_State_Synreceived_Non_Zero_Data_WinScaling( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eSYN_RECEIVED;
    pxSocket->u.xTCP.bits.bWinScaling = pdTRUE;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = 0;

    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleSynReceived( pxSocket,
                                        ( const NetworkBufferDescriptor_t * ) pxNetworkBuffer,
                                        20,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
}

static uint32_t ulCalled = 0;
static void xLocalFunctionPointer( Socket_t xSocket,
                                   size_t xLength )
{
    ulCalled++;
}

/* test for prvHandleEstablished function */
void test_prvHandleEstablished_No_ACK( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;

    pxTCPHeader->ucTCPFlags = 0;

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        1000,
                                        0 );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/* test for prvHandleEstablished function */
void test_prvHandleEstablished_ACK_Happy( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;


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

/* test for prvHandleEstablished function */
void test_prvHandleEstablished_ACK_Null_TX_Recv_Zero( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;


    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 1000 );
    prvTCPPrepareSend_ExpectAnyArgsAndReturn( 40 );

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 40, xSendLength );
    TEST_ASSERT_EQUAL( 0, ulCalled );
}

/* test for prvHandleEstablished function */
void test_prvHandleEstablished_ACK_Win_Zero_Recv_Zero_Has_Option( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;


    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    prvTCPAddTxData_ExpectAnyArgs();

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        1000,
                                        12 );
    TEST_ASSERT_EQUAL( 52, xSendLength );
    TEST_ASSERT_EQUAL( 0, ulCalled );
}

/* test for prvHandleEstablished function */
void test_prvHandleEstablished_ACK_Buffer_Zero_Prep_False( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;


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

/* test for prvHandleEstablished function */
void test_prvHandleEstablished_ACK_Happy_Select_Write_No_Handler( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxSocket->xSelectBits = eSELECT_WRITE;



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

uint8_t EthernetBuffer_Fin[ ipconfigNETWORK_MTU ] =
{
    0x8c, 0xdc, 0xd4, 0x4a, 0xea, 0x02, 0xa0, 0x40, 0xa0, 0x3a, 0x21, 0xea, 0x08, 0x00, 0x45, 0x20,
    0x00, 0x28, 0x51, 0x4a, 0x40, 0x00, 0xcf, 0x06, 0x14, 0x7b, 0xd1, 0x36, 0xb4, 0x03, 0xc0, 0xa8,
    0x00, 0x08, 0x01, 0xbb, 0xe9, 0xcc, 0xce, 0x19, 0x42, 0xb1, 0x6c, 0x98, 0x52, 0xe7, 0x50, 0x11,
    0x01, 0xb8, 0xac, 0x5e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};

/* test for prvHandleEstablished function */
void test_prvHandleEstablished_FIN_NotSent_RX_Complete( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2501;

    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    prvTCPAddTxData_ExpectAnyArgs();
    xTCPWindowRxEmpty_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdTRUE );
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/* test for prvHandleEstablished function */
void test_prvHandleEstablished_FIN_NotSent_RX_Not_Complete( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2501;

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

/* test for prvHandleEstablished function */
void test_prvHandleEstablished_FIN_NotSent_TX_Win_Not_Complete( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2501;

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

/* test for prvHandleEstablished function */
void test_prvHandleEstablished_FIN_NotSent_Data_Left( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2200;

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

/* test for prvHandleEstablished function */
void test_prvHandleEstablished_FIN_Sent( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_Fin;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN | tcpTCP_FLAG_ACK;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1500 );
    pxTCPHeader->usWindow = 1000;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.pxHandleSent = NULL;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 2501;

    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    prvTCPAddTxData_ExpectAnyArgs();
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvHandleEstablished( pxSocket,
                                        &pxNetworkBuffer,
                                        0,
                                        0 );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

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

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Closed_malloc_failure( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
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

    prvCheckRxData_ExpectAnyArgsAndReturn( 1000 );
    prvStoreRxData_ExpectAnyArgsAndReturn( -1 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( -1, xSendLength );
}

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Closed( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
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

    prvCheckRxData_ExpectAnyArgsAndReturn( 1000 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 1000 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_TCP_Listen( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
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

    prvCheckRxData_ExpectAnyArgsAndReturn( 1000 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 1000 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 2000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_SYN_First( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
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

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Connect_Syn( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
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

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Syn_Received( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
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

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Syn_Received_Flag_Not_Syn( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
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
/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Established_Data_Ack( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
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

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Established_First_Fin_From_Peer( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

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

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Last_Ack( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxSocket->u.xTCP.eTCPState = eLAST_ACK;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAcked = pdTRUE;
    pxSocket->u.xTCP.bits.bFinLast = pdTRUE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );
    vTCPStateChange_ExpectAnyArgs();

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Fin_Wait_1_Fin_From_Peer( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    ulCalled = 0;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = eFIN_WAIT_1;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE;
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

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

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Close_Wait( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = eCLOSE_WAIT;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Closing_Keep_Alive( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = eCLOSING;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_Time_Wait( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = eTIME_WAIT;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdTRUE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/* test for prvTCPHandleState function */
void test_prvTCPHandleState_State_Unknown( void )
{
    BaseType_t xSendLength = 0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.eTCPState = 12;
    pxSocket->u.xTCP.txStream = 0x12345678;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.bits.bFinAccepted = pdTRUE;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE;
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1001;
    pxTCPWindow->rx.ulHighestSequenceNumber = 1000;

    prvCheckRxData_ExpectAnyArgsAndReturn( 0 );
    prvStoreRxData_ExpectAnyArgsAndReturn( 0 );
    prvSetOptions_ExpectAnyArgsAndReturn( 0 );

    xSendLength = prvTCPHandleState( pxSocket, &pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( 1000, pxTCPWindow->rx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( 0, xSendLength );
}

/* test for prvHandleListen function */
void test_prvHandleListen_Not_For_Me( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    const TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    xDefaultPartUDPPacketHeader.ulWords[ 20 / sizeof( uint32_t ) ] = 0x0700a8c0;

    pxSocket = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxSocket );
}

/* test for prvHandleListen function */
void test_prvHandleListen_Reuse_Socket( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    const TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    xDefaultPartUDPPacketHeader.ulWords[ 20 / sizeof( uint32_t ) ] = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdTRUE;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgs();
    vTCPStateChange_ExpectAnyArgs();

    pxReturn = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxSocket, pxReturn );
    TEST_ASSERT_EQUAL( 1000, pxReturn->u.xTCP.xTCPWindow.ulOurSequenceNumber );
}

/* test for prvHandleListen function */
void test_prvHandleListen_New_Socket_Exceed_Limit( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    const TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    xDefaultPartUDPPacketHeader.ulWords[ 20 / sizeof( uint32_t ) ] = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 10;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/* test for prvHandleListen function */
void test_prvHandleListen_New_Socket_Good( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    const TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    xDefaultPartUDPPacketHeader.ulWords[ 20 / sizeof( uint32_t ) ] = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( &MockReturnSocket );
    vSocketBind_ExpectAnyArgsAndReturn( 0 );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgs();
    vTCPStateChange_ExpectAnyArgs();

    pxReturn = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( &MockReturnSocket, pxReturn );
    TEST_ASSERT_EQUAL( 1000, pxReturn->u.xTCP.xTCPWindow.ulOurSequenceNumber );
}

/* test for prvHandleListen function */
void test_prvHandleListen_New_Socket_NULL_Socket( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    const TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    xDefaultPartUDPPacketHeader.ulWords[ 20 / sizeof( uint32_t ) ] = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( NULL );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/* test for prvHandleListen function */
void test_prvHandleListen_New_Socket_Invalid_Socket( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    const TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    xDefaultPartUDPPacketHeader.ulWords[ 20 / sizeof( uint32_t ) ] = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( FREERTOS_INVALID_SOCKET );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/* test for prvHandleListen function */
void test_prvHandleListen_New_Socket_Socket_Copy_Failure( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    const TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    xDefaultPartUDPPacketHeader.ulWords[ 20 / sizeof( uint32_t ) ] = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( &MockReturnSocket );
    vSocketBind_ExpectAnyArgsAndReturn( 1 );
    vSocketClose_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/* test for prvTCPSocketCopy function */
void test_prvTCPSocketCopy_NULL_SocketSet( void )
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

/* test for prvTCPSocketCopy function */
void test_prvTCPSocketCopy_Bind_Error( void )
{
    BaseType_t Result = pdFALSE;

    FreeRTOS_Socket_t MockReturnSocket;

    pxSocket = &xSocket;

    pxSocket->usLocalPort = 22;
    pxSocket->u.xTCP.uxTxWinSize = 0x123456;
    pxSocket->pxSocketSet = 0x1111111;
    pxSocket->xSelectBits = eSELECT_READ;

    vSocketBind_ExpectAnyArgsAndReturn( 1 );
    vSocketClose_ExpectAnyArgsAndReturn( pdTRUE );

    Result = prvTCPSocketCopy( &MockReturnSocket, pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, Result );
    TEST_ASSERT_NOT_EQUAL( pxSocket->usLocalPort, MockReturnSocket.usLocalPort );
    TEST_ASSERT_EQUAL( pxSocket->u.xTCP.uxTxWinSize, MockReturnSocket.u.xTCP.uxTxWinSize );
    TEST_ASSERT_EQUAL( ( pxSocket->xSelectBits | eSELECT_READ | eSELECT_EXCEPT ), MockReturnSocket.xSelectBits );
}

/* test for FreeRTOS_GetTCPStateName function */
void test_FreeRTOS_GetTCPStateName( void )
{
    char * ReturnStateName;

    ReturnStateName = FreeRTOS_GetTCPStateName( 0 );

    TEST_ASSERT_EQUAL_STRING( "eCLOSED", ReturnStateName );
}

/* test for FreeRTOS_GetTCPStateName function */
void test_FreeRTOS_GetTCPStateName_Invalid_Index( void )
{
    char * ReturnStateName;

    ReturnStateName = FreeRTOS_GetTCPStateName( -1 );

    TEST_ASSERT_EQUAL_STRING( "eUNKNOWN", ReturnStateName );
}

/* test for FreeRTOS_GetTCPStateName function */
void test_FreeRTOS_GetTCPStateName_Wrong_Index( void )
{
    char * ReturnStateName;

    ReturnStateName = FreeRTOS_GetTCPStateName( 30 );

    TEST_ASSERT_EQUAL_STRING( "eUNKNOWN", ReturnStateName );
}
