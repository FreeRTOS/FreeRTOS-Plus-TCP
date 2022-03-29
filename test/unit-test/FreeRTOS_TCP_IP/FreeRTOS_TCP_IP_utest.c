/*
 * FreeRTOS+TCP V2.3.4
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
#include "mock_TCP_IP_list_macros.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_queue.h"
#include "mock_task.h"
#include "mock_event_groups.h"
#include "mock_list.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_TCP_State_Handling.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_TCP_Transmission.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_TCP_IP_stubs.c"
#include "FreeRTOS_TCP_IP.h"

FreeRTOS_Socket_t xSocket, * pxSocket;
NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;

extern BaseType_t xTCPWindowLoggingLevel;

uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ] =
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x08, 0x00, 0x45, 0x00,
    0x00, 0x34, 0x15, 0xc2, 0x40, 0x00, 0x40, 0x06, 0xa8, 0x8e, 0xc0, 0xa8, 0x00, 0x08, 0xac, 0xd9,
    0x0e, 0xea, 0xea, 0xfe, 0x01, 0xbb, 0x8b, 0xaf, 0x8a, 0x24, 0xdc, 0x96, 0x95, 0x7a, 0x80, 0x10,
    0x01, 0xf5, 0x7c, 0x9a, 0x00, 0x00, 0x01, 0x01, 0x08, 0x0a, 0xb8, 0x53, 0x57, 0x27, 0xb2, 0xce,
    0xc3, 0x17
};

/* test vSocketCloseNextTime function */
void test_vSocketCloseNextTime_Null_Socket( void )
{
    vSocketCloseNextTime( NULL );
}

/* test vSocketCloseNextTime function */
void test_vSocketCloseNextTime_Not_Close_Socket( void )
{
    memset( &xSocket, 0, sizeof( xSocket ) );

    vSocketCloseNextTime( &xSocket );
}

/* test vSocketCloseNextTime function */
void test_vSocketCloseNextTime_Not_Close_Same_Socket( void )
{
    memset( &xSocket, 0, sizeof( xSocket ) );

    vSocketCloseNextTime( &xSocket );
}


/* test vSocketCloseNextTime function */
void test_vSocketCloseNextTime_Close_Previous_Socket( void )
{
    FreeRTOS_Socket_t NewSocket;
    vSocketClose_ExpectAnyArgsAndReturn(NULL);
    vSocketCloseNextTime(&NewSocket);
}

/* test xTCPSocketCheck function */
void test_xTCPSocketCheck_AllInputsZero1( void )
{
    BaseType_t xReturn, xToReturn = 0xAABBCCDD;
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &xDelayReturn );

    prvTCPStatusAgeCheck_ExpectAnyArgsAndReturn( xToReturn );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
}

/* test xTCPSocketCheck function */
void test_xTCPSocketCheck_StateEstablished( void )
{
    BaseType_t xReturn, xToReturn = 0xAABBCCDD;
    FreeRTOS_Socket_t xSocket;
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    prvTCPSendPacket_ExpectAndReturn( &xSocket, 0 );

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &xDelayReturn );

    prvTCPStatusAgeCheck_ExpectAnyArgsAndReturn( xToReturn );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
}

/* test xTCPSocketCheck function */
void test_xTCPSocketCheck_StateEstablished_TxStreamNonNull( void )
{
    BaseType_t xReturn, xToReturn = 0xAABBCCDD;
    FreeRTOS_Socket_t xSocket;
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;

    prvTCPAddTxData_Expect( &xSocket );

    prvTCPSendPacket_ExpectAndReturn( &xSocket, 0 );

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &xDelayReturn );

    prvTCPStatusAgeCheck_ExpectAnyArgsAndReturn( xToReturn );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
}

/* test xTCPSocketCheck function */
void test_xTCPSocketCheck_StateEstablished_TxStreamNonNull1( void )
{
    BaseType_t xReturn, xToReturn = 0xAABBCCDD;
    FreeRTOS_Socket_t xSocket;
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;
    xSocket.u.xTCP.pxAckMessage = ( void * ) &xSocket;

    prvTCPAddTxData_Expect( &xSocket );

    prvTCPReturnPacket_Expect( &xSocket, xSocket.u.xTCP.pxAckMessage, ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER, ipconfigZERO_COPY_TX_DRIVER );

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &xDelayReturn );

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    prvTCPSendPacket_ExpectAndReturn( &xSocket, 0 );

    prvTCPStatusAgeCheck_ExpectAndReturn( &xSocket, xToReturn );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 1U, xSocket.u.xTCP.usTimeout );
}

/* @brief Test xTCPSocketCheck function when the stream is non-NULL and the
 *        time out is non-zero. */
void test_xTCPSocketCheck_StateEstablished_TxStreamNonNull1_NonZeroTimeout( void )
{
    BaseType_t xReturn, xToReturn = 0;
    FreeRTOS_Socket_t xSocket;
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;
    xSocket.u.xTCP.pxAckMessage = ( void * ) &xSocket;
    xSocket.u.xTCP.usTimeout = 100;

    prvTCPAddTxData_Expect( &xSocket );

    prvTCPReturnPacket_Expect( &xSocket, xSocket.u.xTCP.pxAckMessage, ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER, ipconfigZERO_COPY_TX_DRIVER );

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 100U, xSocket.u.xTCP.usTimeout );
}

/* @brief Test xTCPSocketCheck function when the stream is non-NULL and the
 *        time out is non-zero. The port number cannot be allowed to issue log
 *        messages. */
void test_xTCPSocketCheck_StateEstablished_TxStreamNonNull1_NonZeroTimeout_NoLogPort( void )
{
    BaseType_t xReturn, xToReturn = 0, xBackup;
    FreeRTOS_Socket_t xSocket;
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;
    xSocket.u.xTCP.pxAckMessage = ( void * ) &xSocket;
    xSocket.u.xTCP.usTimeout = 100;
    xSocket.usLocalPort = 23U;

    xBackup = xTCPWindowLoggingLevel;
    xTCPWindowLoggingLevel = 2;

    prvTCPAddTxData_Expect( &xSocket );

    prvTCPReturnPacket_Expect( &xSocket, xSocket.u.xTCP.pxAckMessage, ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER, ipconfigZERO_COPY_TX_DRIVER );

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 100U, xSocket.u.xTCP.usTimeout );

    xTCPWindowLoggingLevel = xBackup;
}

/* @brief Test xTCPSocketCheck function when the stream is non-NULL and the
 *        time out is non-zero. The port number cannot be allowed to issue log
 *        messages. */
void test_xTCPSocketCheck_StateCLOSED_TxStreamNonNull1_NonZeroTimeout( void )
{
    BaseType_t xReturn, xToReturn = 0;
    FreeRTOS_Socket_t xSocket;
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eCLOSED;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;
    xSocket.u.xTCP.pxAckMessage = ( void * ) &xSocket;
    xSocket.u.xTCP.usTimeout = 100;
    xSocket.usLocalPort = 23U;

    xTCPWindowLoggingLevel = 2;

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 100U, xSocket.u.xTCP.usTimeout );

    xTCPWindowLoggingLevel = 1;
}

/* @brief Test xTCPSocketCheck function when the stream is non-NULL and the
 *        time out is non-zero. Additionally, the user has requested to shutdown
 *        the socket. */
void test_xTCPSocketCheck_StateeCONNECT_SYN_TxStreamNonNull_UserShutdown( void )
{
    BaseType_t xReturn, xToReturn = 0;
    FreeRTOS_Socket_t xSocket;
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eCONNECT_SYN;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;
    xSocket.u.xTCP.pxAckMessage = ( void * ) &xSocket;
    xSocket.u.xTCP.usTimeout = 100;
    xSocket.u.xTCP.bits.bUserShutdown = pdTRUE_UNSIGNED;

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    prvTCPSendPacket_ExpectAndReturn( &xSocket, 0 );

    prvTCPStatusAgeCheck_ExpectAndReturn( &xSocket, xToReturn );

//     xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    /* ARP phase. Check every half second. */
    TEST_ASSERT_EQUAL( 500U, xSocket.u.xTCP.usTimeout );
}

/* @brief Test prvTCPTouchSocket function. */
void test_prvTCPTouchSocket( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0xAA, sizeof( xSocket ) );

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );

    prvTCPTouchSocket( &xSocket );

    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/* test xProcessReceivedTCPPacket function */
void test_xProcessReceivedTCPPacket_Null_Descriptor(void)
{
    BaseType_t Return = pdFALSE;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    
    pxNetworkBuffer->xDataLength = 40;

    catch_assert(xProcessReceivedTCPPacket(NULL));
}

/* test xProcessReceivedTCPPacket function */
void test_xProcessReceivedTCPPacket_Null_Buffer(void)
{
    BaseType_t Return = pdFALSE;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = NULL;
    
    pxNetworkBuffer->xDataLength = 40;

    catch_assert(xProcessReceivedTCPPacket(pxNetworkBuffer));
}

/* test xProcessReceivedTCPPacket function */
void test_xProcessReceivedTCPPacket_Minimal_Data_Length(void)
{
    BaseType_t Return = pdFALSE;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    
    pxNetworkBuffer->xDataLength = 40;

    Return = xProcessReceivedTCPPacket(pxNetworkBuffer);
    TEST_ASSERT_EQUAL(pdFALSE, Return);
}

/* test xProcessReceivedTCPPacket function */
void test_xProcessReceivedTCPPacket_No_Socket(void)
{
    BaseType_t Return = pdFALSE;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( const ProtocolHeaders_t * )&( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    
    pxNetworkBuffer->xDataLength = 100;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_ACK;

    pxTCPSocketLookup_ExpectAnyArgsAndReturn(NULL);

    Return = xProcessReceivedTCPPacket(pxNetworkBuffer);
    TEST_ASSERT_EQUAL(pdFALSE, Return);
}

/* test xProcessReceivedTCPPacket function */
void test_xProcessReceivedTCPPacket_No_Active_Socket(void)
{
    BaseType_t Return = pdFALSE;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( const ProtocolHeaders_t * )&( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    
    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.ucTCPState = eCLOSE_WAIT;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    pxTCPSocketLookup_ExpectAnyArgsAndReturn(pxSocket);
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn(pdFALSE);

    Return = xProcessReceivedTCPPacket(pxNetworkBuffer);
    TEST_ASSERT_EQUAL(pdFALSE, Return);
}

/* test xProcessReceivedTCPPacket function */
void test_xProcessReceivedTCPPacket_No_Active_Socket_Send_Reset(void)
{
    BaseType_t Return = pdFALSE;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( const ProtocolHeaders_t * )&( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    
    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.ucTCPState = eCLOSE_WAIT;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;

    pxTCPSocketLookup_ExpectAnyArgsAndReturn(pxSocket);
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn(pdFALSE);
    prvTCPSendReset_ExpectAnyArgsAndReturn(pdTRUE);

    Return = xProcessReceivedTCPPacket(pxNetworkBuffer);
    TEST_ASSERT_EQUAL(pdFALSE, Return);
}

/* test xProcessReceivedTCPPacket function */
void test_xProcessReceivedTCPPacket_Listen_State_Not_Syn_No_Rst(void)
{
    BaseType_t Return = pdFALSE;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( const ProtocolHeaders_t * )&( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    
    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.ucTCPState = eTCP_LISTEN;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    pxTCPSocketLookup_ExpectAnyArgsAndReturn(pxSocket);
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn(pdTRUE);
    
    Return = xProcessReceivedTCPPacket(pxNetworkBuffer);
    TEST_ASSERT_EQUAL(pdFALSE, Return);
}

/* test xProcessReceivedTCPPacket function */
void test_xProcessReceivedTCPPacket_Listen_State_Not_Syn_Rst(void)
{
    BaseType_t Return = pdFALSE;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( const ProtocolHeaders_t * )&( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    
    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.ucTCPState = eTCP_LISTEN;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_ACK;

    pxTCPSocketLookup_ExpectAnyArgsAndReturn(pxSocket);
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn(pdTRUE);
    prvTCPSendReset_ExpectAnyArgsAndReturn(pdTRUE);

    Return = xProcessReceivedTCPPacket(pxNetworkBuffer);
    TEST_ASSERT_EQUAL(pdFALSE, Return);
}


/* test xTCPCheckNewClient function */
void test_xTCPCheckNewClient_Empty_List(void)
{
    BaseType_t Return = pdFALSE;
    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    MiniListItem_t EndItem;

    pSocketList->xListEnd = EndItem;
    pSocketList->xListEnd.pxNext = (ListItem_t *) &(pSocketList->xListEnd);
    pSocketList->xListEnd.pxPrevious = (ListItem_t *) &(pSocketList->xListEnd);
    pSocketList->uxNumberOfItems = 0;
    pSocketList->pxIndex = (ListItem_t *) &(pSocketList->xListEnd);

    pxSocket->usLocalPort = 40000;
    Return = xTCPCheckNewClient(pxSocket);
    TEST_ASSERT_EQUAL(pdFALSE, Return);
}

/* test xTCPCheckNewClient function */
// void test_xTCPCheckNewClient_Not_Found(void)
// {
//     BaseType_t Return = pdFALSE;
//     pxSocket = &xSocket;
//     List_t * pSocketList = &xBoundTCPSocketsList;
//     MiniListItem_t EndItem;

//     pSocketList->xListEnd = EndItem;
//     pSocketList->xListEnd.pxNext = (ListItem_t *) &(pSocketList->xListEnd);
//     pSocketList->xListEnd.pxPrevious = (ListItem_t *) &(pSocketList->xListEnd);
//     pSocketList->uxNumberOfItems = 0;
//     pSocketList->pxIndex = (ListItem_t *) &(pSocketList->xListEnd);

//     vListInitialiseItem( &( pxSocket->xBoundSocketListItem ) );
//     pxSocket->xBoundSocketListItem.pxContainer = &( xBoundTCPSocketsList );
//     vListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );
//     //vListInsertEnd( pSocketList, &( pxSocket->xBoundSocketListItem ) );
//     pxSocket->usLocalPort = 40000;
//     Return = xTCPCheckNewClient(pxSocket);
//     TEST_ASSERT_EQUAL(pdFALSE, Return);
// }
