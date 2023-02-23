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
#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_TCP_State_Handling.h"
#include "mock_FreeRTOS_TCP_Reception.h"
#include "mock_FreeRTOS_TCP_Utils.h"
#include "mock_FreeRTOS_TCP_WIN.h"

#include "FreeRTOS_TCP_IP.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"
#include "FreeRTOSIPConfigDefaults.h"

#include "FreeRTOS_TCP_Transmission_stubs.c"
#include "FreeRTOS_TCP_Transmission.h"



BaseType_t prvCheckOptions( FreeRTOS_Socket_t * pxSocket,
                            const NetworkBufferDescriptor_t * pxNetworkBuffer );
BaseType_t prvTCPSendReset( NetworkBufferDescriptor_t * pxNetworkBuffer );

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


/* test for prvTCPMakeSurePrepared function */
void test_prvTCPMakeSurePrepared_Not_Ready( void )
{
    BaseType_t xResult = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    prvSocketSetMSS_ExpectAnyArgs();
    vTCPWindowCreate_ExpectAnyArgs();

    xResult = prvTCPMakeSurePrepared( pxSocket );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

/* test for prvTCPMakeSurePrepared function */
void test_prvTCPMakeSurePrepared_Not_Ready_Error_Connect( void )
{
    BaseType_t xResult = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );
    FreeRTOS_OutputARPRequest_ExpectAnyArgs();

    xResult = prvTCPMakeSurePrepared( pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/* test for prvTCPMakeSurePrepared function */
void test_prvTCPMakeSurePrepared_Ready( void )
{
    BaseType_t xResult = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;

    xResult = prvTCPMakeSurePrepared( pxSocket );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

/* test for prvTCPSendPacket function */
void test_prvTCPSendPacket_Syn_State( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.ucRepCount = 1;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;

    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 1000 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1234 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2345 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    BytesSent = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( 52, BytesSent );
}

/* test for prvTCPSendPacket function */
void test_prvTCPSendPacket_Syn_State_Rep_Count_GT_3( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.ucRepCount = 3;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;

    vTCPStateChange_ExpectAnyArgs();

    BytesSent = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test for prvTCPSendPacket function */
void test_prvTCPSendPacket_Syn_State_Not_Prepared( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.ucRepCount = 1;
    pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );
    FreeRTOS_OutputARPRequest_ExpectAnyArgs();

    BytesSent = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test for prvTCPSendPacket function */
void test_prvTCPSendPacket_Other_State_Zero_To_Send( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.ucRepCount = 1;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;
    pxSocket->u.xTCP.xLastAliveTime = 1000;

    xTaskGetTickCount_ExpectAndReturn( 2000 );

    BytesSent = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test for prvTCPSendPacket function */
void test_prvTCPSendPacket_Other_State_Something_To_Send( void )
{
    int32_t BytesSent = 0;
    UBaseType_t RepeatCount = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = 1000;

    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    StreamBuffer_t TxStream;

    pxSocket->u.xTCP.eTCPState = eSYN_RECEIVED;
    pxSocket->u.xTCP.ucRepCount = 1;
    pxSocket->u.xTCP.xLastAliveTime = 1000;
    pxSocket->u.xTCP.txStream = &TxStream;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE;
    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE;
    pxSocket->u.xTCP.ucKeepRepCount = 0;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;
    pxSocket->u.xTCP.ucRepCount = 0;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 20 );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &NewNetworkBuffer );
    /*vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs(); */
    uxStreamBufferDistance_ExpectAnyArgsAndReturn( 500 );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 20 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 1000 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1234 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2345 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    for( RepeatCount = 1; RepeatCount < SEND_REPEATED_COUNT; RepeatCount++ )
    {
        ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 20 ); /* data length may sent */
        uxStreamBufferDistance_ExpectAnyArgsAndReturn( 500 );
        uxStreamBufferGet_ExpectAnyArgsAndReturn( 20 );
        FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 1000 );
        usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1234 );
        usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2345 );
        eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
        xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );
    }

    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    BytesSent = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( 480, BytesSent );
}

/* test for prvTCPSendRepeated function */
void test_prvTCPSendRepeated_Zero_To_Send( void )
{
    int32_t BytesSent = 0;
    UBaseType_t RepeatCount = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    xBufferAllocFixedSize = pdFALSE;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 0 );

    BytesSent = prvTCPSendRepeated( pxSocket, &pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test for prvTCPSendRepeated function */
void test_prvTCPSendRepeated_Repeat_8( void )
{
    int32_t BytesSent = 0;
    UBaseType_t RepeatCount = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = 1000;

    StreamBuffer_t StreamBuffer;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) &StreamBuffer;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdTRUE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE;
    pxSocket->u.xTCP.ucKeepRepCount = 1;
    pxSocket->u.xTCP.ucRepCount = 1;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;

    for( RepeatCount = 0; RepeatCount < SEND_REPEATED_COUNT; RepeatCount++ )
    {
        ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 20 ); /* data length may sent */
        uxStreamBufferDistance_ExpectAnyArgsAndReturn( 500 );
        uxStreamBufferGet_ExpectAnyArgsAndReturn( 20 );
        FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 1000 );
        usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1234 );
        usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2345 );
        eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
        xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );
    }

    BytesSent = prvTCPSendRepeated( pxSocket, &pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 480, BytesSent );
}

/* test for prvTCPReturnPacket function */
void test_prvTCPReturnPacket_Null_Buffer_Null_Rx_Stream_KL( void )
{
    pxSocket = &xSocket;
    pxNetworkBuffer = NULL;

    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    memcpy( pxSocket->u.xTCP.xPacket.u.ucLastPacket,
            ucEthernetBuffer,
            sizeof( pxSocket->u.xTCP.xPacket.u.ucLastPacket ) );
    pxSocket->u.xTCP.rxStream = NULL;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 0;

    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    prvTCPReturnPacket( pxSocket, pxNetworkBuffer, 40, pdFALSE );
    TEST_ASSERT_EQUAL( 1000, pxSocket->u.xTCP.ulHighestRxAllowed );
}

/* test for prvTCPReturnPacket function */
void test_prvTCPReturnPacket_Null_Socket( void )
{
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    IPHeader_t * pxIPHeader = &pxTCPPacket->xIPHeader;

    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    uint32_t OldSourceAddress = pxIPHeader->ulSourceIPAddress;
    uint32_t OldDestinationAddress = pxIPHeader->ulDestinationIPAddress;
    uint32_t RxSequenceNumber = pxTCPPacket->xTCPHeader.ulSequenceNumber;
    uint32_t OurSequenceNumber = pxTCPPacket->xTCPHeader.ulAckNr;

    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    prvTCPReturnPacket( NULL, pxNetworkBuffer, 40, pdFALSE );

    /* with ReleaseAfterSend set to FALSE, IP address not flipped */
    TEST_ASSERT_EQUAL( OldSourceAddress, pxIPHeader->ulSourceIPAddress );
    TEST_ASSERT_EQUAL( RxSequenceNumber, pxTCPPacket->xTCPHeader.ulAckNr );
}

/* test for prvTCPReturnPacket function */
void test_prvTCPReturnPacket_Null_Socket_Relase_True( void )
{
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    IPHeader_t * pxIPHeader = &pxTCPPacket->xIPHeader;

    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    uint32_t OldSourceAddress = pxIPHeader->ulSourceIPAddress;
    uint32_t OldDestinationAddress = pxIPHeader->ulDestinationIPAddress;
    uint32_t RxSequenceNumber = pxTCPPacket->xTCPHeader.ulSequenceNumber;
    uint32_t OurSequenceNumber = pxTCPPacket->xTCPHeader.ulAckNr;

    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    prvTCPReturnPacket( NULL, pxNetworkBuffer, 40, pdTRUE );

    /* with ReleaseAfterSend set to TRUE, IP address flipped */
    TEST_ASSERT_EQUAL( OldDestinationAddress, pxIPHeader->ulSourceIPAddress );
    TEST_ASSERT_EQUAL( RxSequenceNumber, pxTCPPacket->xTCPHeader.ulAckNr );
}

/* test for prvTCPReturnPacket function */
void test_prvTCPReturnPacket_No_KL( void )
{
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    prvTCPReturnPacket( pxSocket, pxNetworkBuffer, 40, pdFALSE );
    TEST_ASSERT_EQUAL( 1050, pxSocket->u.xTCP.ulHighestRxAllowed );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 100 ), pxTCPPacket->xTCPHeader.ulSequenceNumber );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 50 ), pxTCPPacket->xTCPHeader.ulAckNr );
}

/* test for prvTCPReturnPacket function */
void test_prvTCPReturnPacket_No_KL_LocalIP( void )
{
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    MACAddress_t NewSourceMacAddr = { { 0x11, 0x22, 0x33, 0x44, 0x55, 0x66 } };

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;
    *ipLOCAL_IP_ADDRESS_POINTER = 0xC0C0C0C0;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    prvTCPReturnPacket( pxSocket, pxNetworkBuffer, 40, pdTRUE );
    TEST_ASSERT_EQUAL( 1050, pxSocket->u.xTCP.ulHighestRxAllowed );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 100 ), pxTCPPacket->xTCPHeader.ulSequenceNumber );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 50 ), pxTCPPacket->xTCPHeader.ulAckNr );
    TEST_ASSERT_EQUAL( 0xC0C0C0C0, pxTCPPacket->xIPHeader.ulSourceIPAddress );
    TEST_ASSERT_EQUAL_INT8_ARRAY( NewSourceMacAddr.ucBytes,
                                  pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes,
                                  6 );
    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
}


/* test for prvTCPReturnPacket function */
void test_prvTCPReturnPacket_No_KL_LocalIP_GT_Eth_Packet_Length( void )
{
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    MACAddress_t NewSourceMacAddr = { { 0x11, 0x22, 0x33, 0x44, 0x55, 0x66 } };

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;
    *ipLOCAL_IP_ADDRESS_POINTER = 0xC0C0C0C0;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    prvTCPReturnPacket( pxSocket, pxNetworkBuffer, 1000, pdTRUE );
    TEST_ASSERT_EQUAL( 1050, pxSocket->u.xTCP.ulHighestRxAllowed );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 100 ), pxTCPPacket->xTCPHeader.ulSequenceNumber );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 50 ), pxTCPPacket->xTCPHeader.ulAckNr );
    TEST_ASSERT_EQUAL( 0xC0C0C0C0, pxTCPPacket->xIPHeader.ulSourceIPAddress );
    TEST_ASSERT_EQUAL_INT8_ARRAY( NewSourceMacAddr.ucBytes,
                                  pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes,
                                  6 );
    TEST_ASSERT_EQUAL( 1000 + ipSIZE_OF_ETH_HEADER, pxNetworkBuffer->xDataLength );
}

/* test for prvTCPReturnPacket function */
void test_prvTCPReturnPacket_No_KL_LocalIP_ARP_Not_Hit( void )
{
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    MACAddress_t NewDestMacAddr = { { 0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC } };

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;
    pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes[ 0 ] = 0x12;
    pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes[ 1 ] = 0x34;
    pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes[ 2 ] = 0x56;
    pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes[ 3 ] = 0x78;
    pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes[ 4 ] = 0x9A;
    pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes[ 5 ] = 0xBC;
    *ipLOCAL_IP_ADDRESS_POINTER = 0xC0C0C0C0;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    prvTCPReturnPacket( pxSocket, pxNetworkBuffer, 40, pdTRUE );
    TEST_ASSERT_EQUAL( 1050, pxSocket->u.xTCP.ulHighestRxAllowed );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 100 ), pxTCPPacket->xTCPHeader.ulSequenceNumber );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 50 ), pxTCPPacket->xTCPHeader.ulAckNr );
    TEST_ASSERT_EQUAL( 0xC0C0C0C0, pxTCPPacket->xIPHeader.ulSourceIPAddress );
    TEST_ASSERT_EQUAL_INT8_ARRAY( NewDestMacAddr.ucBytes,
                                  pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes,
                                  6 );
}

/* test for prvTCPReturnPacket function */
void test_prvTCPReturnPacket_No_KL_Fin_Suppress_Rx_Stop( void )
{
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );


    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdTRUE;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPWindow->rx.ulFINSequenceNumber = 150;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;
    pxTCPPacket->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_FIN;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    prvTCPReturnPacket( pxSocket, pxNetworkBuffer, 40, pdFALSE );
    TEST_ASSERT_EQUAL( 1050, pxSocket->u.xTCP.ulHighestRxAllowed );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 100 ), pxTCPPacket->xTCPHeader.ulSequenceNumber );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 50 ), pxTCPPacket->xTCPHeader.ulAckNr );
    TEST_ASSERT_EQUAL( 0, pxTCPPacket->xTCPHeader.ucTCPFlags );
}

/* test for prvTCPReturnPacket function */
void test_prvTCPReturnPacket_No_KL_Fin_Not_Suppress_Low_Water( void )
{
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );


    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdTRUE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxTCPWindow->ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPWindow->tx.ulFINSequenceNumber = 100;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;
    pxTCPPacket->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_FIN;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    prvTCPReturnPacket( pxSocket, pxNetworkBuffer, 40, pdFALSE );
    TEST_ASSERT_EQUAL( 1050, pxSocket->u.xTCP.ulHighestRxAllowed );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 100 ), pxTCPPacket->xTCPHeader.ulSequenceNumber );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 50 ), pxTCPPacket->xTCPHeader.ulAckNr );
    TEST_ASSERT_EQUAL( 1, pxTCPPacket->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_FIN );
}

/* test for prvTCPReturnPacket function */
void test_prvTCPReturnPacket_No_KL_Fin_Not_Suppress_Big_Win( void )
{
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );


    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPWindow->rx.ulFINSequenceNumber = 100;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;
    pxTCPPacket->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_FIN;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 0x10000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 0x10000 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    prvTCPReturnPacket( pxSocket, pxNetworkBuffer, 40, pdFALSE );
    TEST_ASSERT_EQUAL( 0x10032, pxSocket->u.xTCP.ulHighestRxAllowed );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 100 ), pxTCPPacket->xTCPHeader.ulSequenceNumber );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 50 ), pxTCPPacket->xTCPHeader.ulAckNr );
    TEST_ASSERT_NOT_EQUAL( 0, pxTCPPacket->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_FIN );
}

/* test for prvTCPPrepareConnect function */
void test_prvTCPPrepareConnect_Ready( void )
{
    BaseType_t Return = pdFALSE;

    pxSocket = &xSocket;

    pxSocket->u.xTCP.ucRepCount = 0;
    pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 0x11111111 );
    prvSocketSetMSS_ExpectAnyArgs();
    vTCPWindowCreate_ExpectAnyArgs();

    Return = prvTCPPrepareConnect( pxSocket );
    TEST_ASSERT_EQUAL( pdTRUE, Return );
    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bConnPrepared );
    TEST_ASSERT_EQUAL( 0, pxSocket->u.xTCP.ucRepCount );
}

/* test for prvTCPPrepareConnect function */
void test_prvTCPPrepareConnect_No_Arp_Entry( void )
{
    BaseType_t Return = pdFALSE;

    pxSocket = &xSocket;

    pxSocket->u.xTCP.ucRepCount = 0;
    pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );
    FreeRTOS_OutputARPRequest_ExpectAnyArgs();

    Return = prvTCPPrepareConnect( pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bConnPrepared );
    TEST_ASSERT_EQUAL( 1, pxSocket->u.xTCP.ucRepCount );
}

/* test for prvTCPPrepareConnect function */
void test_prvTCPPrepareConnect_Zero_SequenceNum( void )
{
    BaseType_t Return = pdFALSE;

    pxSocket = &xSocket;

    pxSocket->u.xTCP.ucRepCount = 0;
    pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 0 );

    Return = prvTCPPrepareConnect( pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bConnPrepared );
}

/* test for prvWinScaleFactor function */
void test_prvWinScaleFactor( void )
{
    uint8_t Factor = 0;

    pxSocket = &xSocket;

    pxSocket->u.xTCP.uxRxWinSize = 1;
    pxSocket->u.xTCP.usMSS = 1500;

    Factor = prvWinScaleFactor( pxSocket );
    TEST_ASSERT_EQUAL( 0, Factor );
}

/* test for prvWinScaleFactor function */
void test_prvWinScaleFactor_Big_Win( void )
{
    uint8_t Factor = 0;

    pxSocket = &xSocket;

    pxSocket->u.xTCP.uxRxWinSize = 5;
    pxSocket->u.xTCP.usMSS = 15000;

    Factor = prvWinScaleFactor( pxSocket );
    TEST_ASSERT_EQUAL( 1, Factor );
}

/* test for prvSetAynAckOptions function */
void test_prvSetSynAckOptions( void )
{
    UBaseType_t ReturnOptionLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    ReturnOptionLength = prvSetSynAckOptions( pxSocket, pxTCPHeader );
    TEST_ASSERT_EQUAL( 12, ReturnOptionLength );
}

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_Fixed_Size_With_Buffer( void )
{
    NetworkBufferDescriptor_t * pReturn;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    xBufferAllocFixedSize = pdTRUE;

    pReturn = prvTCPBufferResize( pxSocket, pxNetworkBuffer, 500, 0 );
    TEST_ASSERT_EQUAL_PTR( pxNetworkBuffer, pReturn );
    TEST_ASSERT_EQUAL( 554, pReturn->xDataLength );
}

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_Fixed_Size_Without_Buffer( void )
{
    NetworkBufferDescriptor_t * pReturn;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    xBufferAllocFixedSize = pdTRUE;

    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &NewNetworkBuffer );
    pReturn = prvTCPBufferResize( pxSocket, NULL, 500, 0 );
    TEST_ASSERT_EQUAL_PTR( &NewNetworkBuffer, pReturn );
    TEST_ASSERT_EQUAL( ipconfigNETWORK_MTU + 22U, pReturn->xDataLength );
}

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_Without_Buffer( void )
{
    NetworkBufferDescriptor_t * pReturn;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    xBufferAllocFixedSize = pdFALSE;
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &NewNetworkBuffer );

    pReturn = prvTCPBufferResize( pxSocket, NULL, 500, 0 );
    TEST_ASSERT_EQUAL_PTR( &NewNetworkBuffer, pReturn );
    TEST_ASSERT_EQUAL( 554, pReturn->xDataLength );
}

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_Without_Buffer_Null_New_Buffer( void )
{
    NetworkBufferDescriptor_t * pReturn;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    xBufferAllocFixedSize = pdFALSE;
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    pReturn = prvTCPBufferResize( pxSocket, NULL, 500, 0 );
    TEST_ASSERT_EQUAL_PTR( NULL, pReturn );
}

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_With_Buffer_LT_Needed_GT_Last_Packet( void )
{
    NetworkBufferDescriptor_t * pReturn;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = 500;

    xBufferAllocFixedSize = pdFALSE;
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &NewNetworkBuffer );
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    pReturn = prvTCPBufferResize( pxSocket, pxNetworkBuffer, 500, 0 );
    TEST_ASSERT_EQUAL_PTR( &NewNetworkBuffer, pReturn );
    TEST_ASSERT_EQUAL( 554, pReturn->xDataLength );
}

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_With_Buffer_LT_Needed_LT_Last_Packet( void )
{
    NetworkBufferDescriptor_t * pReturn;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = 10;

    xBufferAllocFixedSize = pdFALSE;
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &NewNetworkBuffer );
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    pReturn = prvTCPBufferResize( pxSocket, pxNetworkBuffer, 10, 0 );
    TEST_ASSERT_EQUAL_PTR( &NewNetworkBuffer, pReturn );
    TEST_ASSERT_EQUAL( 70, pReturn->xDataLength );
}

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_With_Buffer_GT_Needed( void )
{
    NetworkBufferDescriptor_t * pReturn;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    xBufferAllocFixedSize = pdFALSE;
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    pxNetworkBuffer->xDataLength = 200;

    pReturn = prvTCPBufferResize( pxSocket, pxNetworkBuffer, 10, 0 );
    TEST_ASSERT_EQUAL_PTR( pxNetworkBuffer, pReturn );
    TEST_ASSERT_EQUAL( 64, pReturn->xDataLength );
}


/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Syn_Zero_Data( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    xBufferAllocFixedSize = pdFALSE;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 0 );

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Syn_Zero_Data_Win_Change( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];

    xBufferAllocFixedSize = pdFALSE;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdTRUE;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 0 );

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 40, BytesSent );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Syn_Zero_Data_Keep_Alive( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];

    xBufferAllocFixedSize = pdFALSE;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 0 );

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 40, BytesSent );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Established_Zero_Data_KLCount1_Age_GT_Max( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];

    xBufferAllocFixedSize = pdFALSE;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE;
    pxSocket->u.xTCP.ucKeepRepCount = 1;
    pxSocket->u.xTCP.xLastAliveTime = 1000;

    xTaskGetTickCount_ExpectAndReturn( 5000 );
    xTaskGetTickCount_ExpectAndReturn( 6000 );

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 40, BytesSent );
    TEST_ASSERT_EQUAL( 2, pxSocket->u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( 6000, pxSocket->u.xTCP.xLastAliveTime );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Established_Null_Buffer_Zero_Data_KLCount0_Age_LT_Max( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = NULL;

    xBufferAllocFixedSize = pdFALSE;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE;
    pxSocket->u.xTCP.ucKeepRepCount = 0;
    pxSocket->u.xTCP.xLastAliveTime = 1000;

    xTaskGetTickCount_ExpectAndReturn( 5000 );

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 40, BytesSent );
    TEST_ASSERT_EQUAL( 0, pxSocket->u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( 1000, pxSocket->u.xTCP.xLastAliveTime );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Established_Null_Buffer_Zero_Data_KLCount1_Age_GT_Max( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = NULL;

    xBufferAllocFixedSize = pdFALSE;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE;
    pxSocket->u.xTCP.ucKeepRepCount = 1;
    pxSocket->u.xTCP.xLastAliveTime = 1000;

    xTaskGetTickCount_ExpectAndReturn( 5000 );
    xTaskGetTickCount_ExpectAndReturn( 6000 );

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 40, BytesSent );
    TEST_ASSERT_EQUAL( 2, pxSocket->u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( 6000, pxSocket->u.xTCP.xLastAliveTime );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Established_Zero_Data_KLCount1_Age_GT_Max_Win_Change( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];

    xBufferAllocFixedSize = pdFALSE;
    pxSocket->u.xTCP.txStream = NULL;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdTRUE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE;
    pxSocket->u.xTCP.ucKeepRepCount = 1;
    pxSocket->u.xTCP.xLastAliveTime = 1000;

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 40, BytesSent );
    TEST_ASSERT_EQUAL( 1, pxSocket->u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( 1000, pxSocket->u.xTCP.xLastAliveTime );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Established_Non_Zero_Data_No_Buffer( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ReturnEthernetBuffer;

    StreamBuffer_t StreamBuffer;

    xBufferAllocFixedSize = pdFALSE;
    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) &StreamBuffer;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE;
    pxSocket->u.xTCP.ucKeepRepCount = 1;


    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 500 ); /* data length may sent */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( -1, BytesSent );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Established_Non_Zero_Data_MSS_0_KLCount4( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    xBufferAllocFixedSize = pdFALSE;
    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ReturnEthernetBuffer;

    StreamBuffer_t StreamBuffer;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) &StreamBuffer;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usMSS = 0;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE;
    pxSocket->u.xTCP.ucKeepRepCount = 4;
    pxSocket->u.xTCP.xLastAliveTime = 1000;

    vTCPStateChange_ExpectAnyArgs();

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( -1, BytesSent );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Established_Non_Zero_Data_Not_Close_Not_ShutDown_KLcount1( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    xBufferAllocFixedSize = pdFALSE;
    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ReturnEthernetBuffer;

    StreamBuffer_t StreamBuffer;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) &StreamBuffer;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE;
    pxSocket->u.xTCP.ucKeepRepCount = 1;


    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 500 ); /* data length may sent */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();
    uxStreamBufferDistance_IgnoreAndReturn( 500 );
    uxStreamBufferGet_IgnoreAndReturn( 20 );

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 540, BytesSent );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Established_Non_Zero_Data_Req_Close_Req_ShutDown_Tx_Done_KLcount1( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ReturnEthernetBuffer;

    StreamBuffer_t StreamBuffer;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) &StreamBuffer;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bCloseRequested = pdTRUE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdTRUE;
    pxSocket->u.xTCP.ucKeepRepCount = 1;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 500 ); /* data length may sent */
    uxStreamBufferDistance_ExpectAnyArgsAndReturn( 500 );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 20 );
    uxStreamBufferDistance_ExpectAnyArgsAndReturn( 20 );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdTRUE );
    vTCPStateChange_ExpectAnyArgs();

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 540, BytesSent );
    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bFinSent );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Established_Non_Zero_Data_Req_Close_Req_ShutDown_Tx_Not_Done_KLcount1( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ReturnEthernetBuffer;

    StreamBuffer_t StreamBuffer;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) &StreamBuffer;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bCloseRequested = pdTRUE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdTRUE;
    pxSocket->u.xTCP.ucKeepRepCount = 1;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 500 ); /* data length may sent */
    uxStreamBufferDistance_ExpectAnyArgsAndReturn( 500 );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 20 );
    uxStreamBufferDistance_ExpectAnyArgsAndReturn( 20 );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdFALSE );

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 540, BytesSent );
    TEST_ASSERT_EQUAL( pdTRUE, pxSocket->u.xTCP.bits.bFinSent );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Established_Non_Zero_Data_Req_Close_Req_ShutDown_Tx_Not_Done_Not_Last_Packet_KLcount1( void )
{
    int32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ReturnEthernetBuffer;

    StreamBuffer_t StreamBuffer;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) &StreamBuffer;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bCloseRequested = pdTRUE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdTRUE;
    pxSocket->u.xTCP.ucKeepRepCount = 1;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;


    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 500 ); /* data length may sent */
    uxStreamBufferDistance_ExpectAnyArgsAndReturn( 500 );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 200 );
    uxStreamBufferDistance_ExpectAnyArgsAndReturn( 20 );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdFALSE );

    BytesSent = prvTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    TEST_ASSERT_EQUAL( 540, BytesSent );
    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bFinSent );
}

/* test prvTCPAddTxData function */
void test_prvTCPAddTxData_Zero_Data( void )
{
    pxSocket = &xSocket;
    StreamBuffer_t TxStream;
    pxSocket->u.xTCP.txStream = &TxStream;

    uxStreamBufferMidSpace_ExpectAndReturn( pxSocket->u.xTCP.txStream, 0 );

    prvTCPAddTxData( pxSocket );
}

/* test prvTCPAddTxData function */
void test_prvTCPAddTxData_Zero_Win( void )
{
    pxSocket = &xSocket;
    StreamBuffer_t TxStream;
    pxSocket->u.xTCP.txStream = &TxStream;

    uxStreamBufferMidSpace_ExpectAndReturn( pxSocket->u.xTCP.txStream, 300 );
    lTCPWindowTxAdd_ExpectAnyArgsAndReturn( 0 );

    prvTCPAddTxData( pxSocket );
}

/* test prvTCPAddTxData function */
void test_prvTCPAddTxData_Normal( void )
{
    pxSocket = &xSocket;
    StreamBuffer_t TxStream;
    pxSocket->u.xTCP.txStream = &TxStream;

    uxStreamBufferMidSpace_ExpectAndReturn( pxSocket->u.xTCP.txStream, 300 );
    lTCPWindowTxAdd_ExpectAnyArgsAndReturn( 100 );
    vStreamBufferMoveMid_ExpectAnyArgs();

    prvTCPAddTxData( pxSocket );
}

/*test prvSetOptions function */
void test_prvSetOptions_Zero_Option_Syn_State_No_MSS_Change( void )
{
    uint32_t OptionLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.bits.bMssChange = pdFALSE;

    pxTCPWindow->ucOptionLength = 0;
    pxTCPHeader->ucTCPOffset = 0x50;

    OptionLength = prvSetOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 0, OptionLength );
    TEST_ASSERT_EQUAL( 0x50, pxTCPHeader->ucTCPOffset );
}

/*test prvSetOptions function */
void test_prvSetOptions_Zero_Option_Syn_State_MSS_Change( void )
{
    uint32_t OptionLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.bits.bMssChange = pdTRUE;

    pxTCPWindow->ucOptionLength = 0;
    pxTCPHeader->ucTCPOffset = 0x50;

    OptionLength = prvSetOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 0, OptionLength );
    TEST_ASSERT_EQUAL( 0x50, pxTCPHeader->ucTCPOffset );
}

/*test prvSetOptions function */
void test_prvSetOptions_Zero_Option_Establish_State_No_MSS_Change( void )
{
    uint32_t OptionLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.bits.bMssChange = pdFALSE;
    pxTCPWindow->ucOptionLength = 0;
    pxTCPHeader->ucTCPOffset = 0x50;

    OptionLength = prvSetOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 0, OptionLength );
    TEST_ASSERT_EQUAL( 0x50, pxTCPHeader->ucTCPOffset );
}

/*test prvSetOptions function */
void test_prvSetOptions_Zero_Option_Establish_State_MSS_Change( void )
{
    uint32_t OptionLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.bits.bMssChange = pdTRUE;
    pxTCPWindow->ucOptionLength = 0;
    pxTCPHeader->ucTCPOffset = 0x50;

    OptionLength = prvSetOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 4, OptionLength );
    TEST_ASSERT_EQUAL( 0x60, pxTCPHeader->ucTCPOffset );
}

/* test prvSetOptions function */
void test_prvSetOptions_Establish_State_MSS_Change( void )
{
    uint32_t OptionLength = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.bits.bMssChange = pdTRUE;
    pxTCPWindow->ucOptionLength = 12;
    pxTCPHeader->ucTCPOffset = 0x50;

    OptionLength = prvSetOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( 12, OptionLength );
    TEST_ASSERT_EQUAL( 0x80, pxTCPHeader->ucTCPOffset );
}

/* test prvSendData function */
void test_prvSendData_Zero_Sent( void )
{
    uint32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.ulHighestRxAllowed = 5000;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxSocket->u.xTCP.usMSS = 1500;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxSocket->u.xTCP.pxAckMessage = NULL;

    BytesSent = prvSendData( pxSocket, &pxNetworkBuffer, 1500, 40 );
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test prvSendData function */
void test_prvSendData_Zero_Sent_AckMsg_Not_Null_Small_Length( void )
{
    uint32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    NetworkBufferDescriptor_t AckMessage;

    pxSocket->u.xTCP.ulHighestRxAllowed = 5000;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxSocket->u.xTCP.usMSS = 1500;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxSocket->u.xTCP.pxAckMessage = &AckMessage;

    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    BytesSent = prvSendData( pxSocket, &pxNetworkBuffer, 100, 40 );
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test prvSendData function */
void test_prvSendData_Zero_Sent_AckMsg_Not_Null_Same_NetBuffer_Log( void )
{
    uint32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxSocket->u.xTCP.ulHighestRxAllowed = 5000;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxSocket->u.xTCP.usMSS = 1500;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    pxSocket->u.xTCP.pxAckMessage = pxNetworkBuffer;
    xTCPWindowLoggingLevel = 2;

    BytesSent = prvSendData( pxSocket, &pxNetworkBuffer, 100, 40 );
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test prvSendData function */
void test_prvSendData_AckMsg_Not_Null_Small_Length( void )
{
    uint32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    NetworkBufferDescriptor_t AckMessage;

    pxSocket->u.xTCP.ulHighestRxAllowed = 5000;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxSocket->u.xTCP.usMSS = 1500;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxTCPHeader->ucTCPFlags = 0;
    pxSocket->u.xTCP.pxAckMessage = &AckMessage;

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;

    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();
    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    BytesSent = prvSendData( pxSocket, &pxNetworkBuffer, 100, 40 );
    TEST_ASSERT_EQUAL( 40, BytesSent );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxAckMessage );
}

/* test prvSendData function */
void test_prvSendData_AckMsg_Not_Null_Same_NetBuffer_Syn_State( void )
{
    uint32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxSocket->u.xTCP.ulHighestRxAllowed = 5000;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxSocket->u.xTCP.usMSS = 1500;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxTCPHeader->ucTCPFlags = 0;
    pxSocket->u.xTCP.pxAckMessage = pxNetworkBuffer;

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    BytesSent = prvSendData( pxSocket, &pxNetworkBuffer, 100, 40 );
    TEST_ASSERT_EQUAL( 40, BytesSent );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxAckMessage );
}

/* test prvSendData function */
void test_prvSendData_AckMsg_Not_Null_Same_NetBuffer_Syn_State_Data_To_Send( void )
{
    uint32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxSocket->u.xTCP.ulHighestRxAllowed = 5000;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxSocket->u.xTCP.usMSS = 1500;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxTCPHeader->ucTCPFlags = 0;
    pxSocket->u.xTCP.pxAckMessage = pxNetworkBuffer;

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    BytesSent = prvSendData( pxSocket, &pxNetworkBuffer, 100, 50 );
    TEST_ASSERT_EQUAL( 50, BytesSent );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxAckMessage );
}

/* test prvSendData function */
void test_prvSendData_AckMsg_Null_Syn_State_Data_To_Send( void )
{
    uint32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxSocket->u.xTCP.ulHighestRxAllowed = 5000;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxSocket->u.xTCP.usMSS = 1500;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxTCPHeader->ucTCPFlags = 0;
    pxSocket->u.xTCP.pxAckMessage = NULL;

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    BytesSent = prvSendData( pxSocket, &pxNetworkBuffer, 100, 50 );
    TEST_ASSERT_EQUAL( 50, BytesSent );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxAckMessage );
}

/* test prvSendData function */
void test_prvSendData_AckMsg_Null_Syn_State_Data_To_Send_Log( void )
{
    uint32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxSocket->u.xTCP.ulHighestRxAllowed = 1500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxSocket->u.xTCP.usMSS = 1500;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxTCPHeader->ucTCPFlags = 0;
    pxSocket->u.xTCP.pxAckMessage = NULL;
    xTCPWindowLoggingLevel = 2;

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    BytesSent = prvSendData( pxSocket, &pxNetworkBuffer, 100, 50 );
    TEST_ASSERT_EQUAL( 50, BytesSent );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxAckMessage );
}

/* test prvSendData function */
void test_prvSendData_AckMsg_Null_Syn_State_Data_To_Send_Rcv_Zero( void )
{
    uint32_t BytesSent = 0;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeader->xTCPHeader;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxSocket->u.xTCP.ulHighestRxAllowed = 1500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 1000;
    pxSocket->u.xTCP.usMSS = 1500;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxTCPHeader->ucTCPFlags = 0;
    pxSocket->u.xTCP.pxAckMessage = NULL;
    xTCPWindowLoggingLevel = 1;

    pxSocket->u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket->u.xTCP.uxRxStreamSize = 1500;
    pxSocket->u.xTCP.bits.bLowWater = pdFALSE;
    pxSocket->u.xTCP.bits.bRxStopped = pdFALSE;
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 100;
    pxTCPWindow->xSize.ulRxWindowLength = 500;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 50;
    pxTCPPacket->xTCPHeader.ulAckNr = 0;

    uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 500 );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    BytesSent = prvSendData( pxSocket, &pxNetworkBuffer, 0, 50 );
    TEST_ASSERT_EQUAL( 50, BytesSent );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxAckMessage );
}

/* test prvTCPSendSpecialPacketHelper function */
void test_prvTCPSendSpecialPacketHelper( void )
{
    BaseType_t Return = pdTRUE;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxTCPPacket->xTCPHeader.ucTCPFlags = 0;
    pxTCPPacket->xTCPHeader.ucTCPOffset = 0;

    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    Return = prvTCPSendSpecialPacketHelper( pxNetworkBuffer, tcpTCP_FLAG_ACK );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPPacket->xTCPHeader.ucTCPFlags );
    TEST_ASSERT_EQUAL( 0x50, pxTCPPacket->xTCPHeader.ucTCPOffset );
}

/* test prvTCPSendSpecialPacketHelper function */
void test_prvTCPSendSpecialPacketHelper_flagSYN( void )
{
    BaseType_t Return = pdTRUE;
    const uint32_t ulSequenceNumber = 0xABC12300;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxTCPPacket->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;
    pxTCPPacket->xTCPHeader.ucTCPOffset = 0;
    pxTCPPacket->xTCPHeader.ulSequenceNumber = FreeRTOS_htonl( ulSequenceNumber );

    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    Return = prvTCPSendSpecialPacketHelper( pxNetworkBuffer, tcpTCP_FLAG_ACK );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPPacket->xTCPHeader.ucTCPFlags );
    TEST_ASSERT_EQUAL( 0x50, pxTCPPacket->xTCPHeader.ucTCPOffset );
    TEST_ASSERT_EQUAL( ulSequenceNumber + 1, FreeRTOS_ntohl( pxTCPPacket->xTCPHeader.ulAckNr ) );
}

/* test prvTCPSendChallengeAck function */
void test_prvTCPSendChallengeAck( void )
{
    BaseType_t Return = pdTRUE;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxTCPPacket->xTCPHeader.ucTCPFlags = 0;
    pxTCPPacket->xTCPHeader.ucTCPOffset = 0;

    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    Return = prvTCPSendChallengeAck( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPPacket->xTCPHeader.ucTCPFlags );
    TEST_ASSERT_EQUAL( 0x50, pxTCPPacket->xTCPHeader.ucTCPOffset );
}

/* test prvTCPSendReset function */
void test_prvTCPSendReset( void )
{
    BaseType_t Return = pdTRUE;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    TCPPacket_t * pxTCPPacket = ( ( const TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxTCPPacket->xTCPHeader.ucTCPFlags = 0;
    pxTCPPacket->xTCPHeader.ucTCPOffset = 0;

    usGenerateChecksum_ExpectAnyArgsAndReturn( 0x1111 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 0x2222 );
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn( pdTRUE );

    Return = prvTCPSendReset( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK | tcpTCP_FLAG_RST, pxTCPPacket->xTCPHeader.ucTCPFlags );
    TEST_ASSERT_EQUAL( 0x50, pxTCPPacket->xTCPHeader.ucTCPOffset );
}
