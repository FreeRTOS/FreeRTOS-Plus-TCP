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


uint8_t ucTCPOptions_good_MSS_WSF[ ipSIZE_TCP_OPTIONS ] =
{
    0x02, 0x04, 0x12, 0x34, /* MSS */
    0x01,                   /* noop */
    0x03, 0x03, 0x10,       /* WSF */
    0x01,                   /* noop */
    0x04, 0x02,             /* SACKP */
    0x00                    /* EOL */
};

uint8_t ucTCPOptions_bad_MSS_WSF[ ipSIZE_TCP_OPTIONS ] =
{
    0x02, 0x04, 0x12, 0x34, /* MSS */
    0x01,                   /* noop */
    0x03, 0x03, 0x10,       /* WSF */
    0x01,                   /* noop */
    0x08, 0x0a, 0x01        /* bad TS */
};

uint8_t ucTCPOptions_good_MSS_WSF_woEND[ ipSIZE_TCP_OPTIONS ] =
{
    0x02, 0x04, 0x12, 0x34, /* MSS */
    0x01,                   /* noop */
    0x03, 0x03, 0x10,       /* WSF */
    0x01,                   /* noop */
    0x04, 0x02,             /* SACKP */
    0x01                    /* noop */
};

uint8_t ucTCPOptions_good_SACK[ ipSIZE_TCP_OPTIONS ] =
{
    0x05, 0x0A, 0x10, 0x00, 0x05, 0x00, 0x11, 0x11, 0x22, 0x22,
    0x00,
    0x00
};

uint8_t ucTCPOptions_good_TS[ ipSIZE_TCP_OPTIONS ] =
{
    0x08, 0x0A, 0x12, 0x34, 0x56, 0x78, 0x11, 0x22, 0x33, 0x44,
    0x00,
    0x00
};



/* test for prvTCPMakeSurePrepared function */
void test_prvTCPMakeSurePrepared_Not_Ready(void)
{
    BaseType_t xResult = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    
    pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;
    
    eARPGetCacheEntry_ExpectAnyArgsAndReturn(eARPCacheHit);
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn(1000);
    prvSocketSetMSS_ExpectAnyArgs();
    vTCPWindowCreate_ExpectAnyArgs();
    
    xResult = prvTCPMakeSurePrepared(pxSocket);
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

/* test for prvTCPMakeSurePrepared function */
void test_prvTCPMakeSurePrepared_Not_Ready_Error_Connect(void)
{
    BaseType_t xResult = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    
    pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;
    
    eARPGetCacheEntry_ExpectAnyArgsAndReturn(eARPCacheMiss);
    FreeRTOS_OutputARPRequest_ExpectAnyArgs();

    xResult = prvTCPMakeSurePrepared(pxSocket);
    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/* test for prvTCPMakeSurePrepared function */
void test_prvTCPMakeSurePrepared_Ready(void)
{
    BaseType_t xResult = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;
    
    xResult = prvTCPMakeSurePrepared(pxSocket);
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

/* test for prvTCPSendPacket function */
void test_prvTCPSendPacket_Syn_State(void)
{
    int32_t BytesSent = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.ucRepCount = 1;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;

    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn(1000);
    usGenerateChecksum_ExpectAnyArgsAndReturn(0x1234);
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn(0x2345);
    eARPGetCacheEntry_ExpectAnyArgsAndReturn(eARPCacheHit);
    xNetworkInterfaceOutput_ExpectAnyArgsAndReturn(pdTRUE);

    BytesSent = prvTCPSendPacket(pxSocket);
    TEST_ASSERT_EQUAL( 52, BytesSent );
}

/* test for prvTCPSendPacket function */
void test_prvTCPSendPacket_Syn_State_Rep_Count_GT_3(void)
{
    int32_t BytesSent = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.ucRepCount = 3;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;

    vTCPStateChange_ExpectAnyArgs();

    BytesSent = prvTCPSendPacket(pxSocket);
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test for prvTCPSendPacket function */
void test_prvTCPSendPacket_Syn_State_Not_Prepared(void)
{
    int32_t BytesSent = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.ucRepCount = 1;
    pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn(eARPCacheMiss);
    FreeRTOS_OutputARPRequest_ExpectAnyArgs();

    BytesSent = prvTCPSendPacket(pxSocket);
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test for prvTCPSendPacket function */
void test_prvTCPSendPacket_Other_State_Zero_To_Send(void)
{
    int32_t BytesSent = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    pxSocket->u.xTCP.ucRepCount = 1;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;
    pxSocket->u.xTCP.xLastAliveTime = 1000;

    xTaskGetTickCount_ExpectAndReturn(2000);

    BytesSent = prvTCPSendPacket(pxSocket);
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test for prvTCPSendPacket function */
// void test_prvTCPSendPacket_Other_State_Something_To_Send(void)
// {
//     int32_t BytesSent = 0;
//     pxSocket = &xSocket;
//     pxNetworkBuffer = &xNetworkBuffer;
//     pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

//     uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];


//     pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
//     pxSocket->u.xTCP.ucRepCount = 1;
//     pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;
//     pxSocket->u.xTCP.xLastAliveTime = 1000;
//     pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x12345678;
//     pxSocket->u.xTCP.usMSS = 1000;

//     ulTCPWindowTxGet_ExpectAnyArgsAndReturn(52);
//     pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&ReturnEthernetBuffer);
//     vReleaseNetworkBuffer_ExpectAnyArgs();
//     xTaskGetTickCount_ExpectAndReturn(2000);
//     FreeRTOS_min_uint32_ExpectAnyArgsAndReturn(1000);
//     usGenerateChecksum_ExpectAnyArgsAndReturn(0x1234);
//     usGenerateProtocolChecksum_ExpectAnyArgsAndReturn(0x2345);
//     eARPGetCacheEntry_ExpectAnyArgsAndReturn(eARPCacheHit);
//     xNetworkInterfaceOutput_ExpectAnyArgsAndReturn(pdTRUE);

//     BytesSent = prvTCPSendPacket(pxSocket);
//     TEST_ASSERT_EQUAL( 0, BytesSent );
// }

/* test for prvTCPSendRepeated function */
void test_prvTCPSendRepeated(void)
{
    int32_t BytesSent = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];


}

// /* test for prvTCPBufferResize function */
// void test_prvTCPBufferResize_Fixed_Size_With_Buffer(void)
// {
//     NetworkBufferDescriptor_t * pReturn;
//     pxSocket = &xSocket;
//     pxNetworkBuffer = &xNetworkBuffer;
//     pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

//     pReturn = prvTCPBufferResize(pxSocket, pxNetworkBuffer, 500, 0);
//     TEST_ASSERT_EQUAL_PTR( pxNetworkBuffer, pReturn );
//     TEST_ASSERT_EQUAL(554, pReturn->xDataLength);
// }

// /* test for prvTCPBufferResize function */
// void test_prvTCPBufferResize_Fixed_Size_Without_Buffer(void)
// {
//     NetworkBufferDescriptor_t * pReturn;
//     pxSocket = &xSocket;
//     pxNetworkBuffer = &xNetworkBuffer;
//     pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

//     NetworkBufferDescriptor_t NewNetworkBuffer;
//     NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

//     pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&NewNetworkBuffer);
//     pReturn = prvTCPBufferResize(pxSocket, NULL, 500, 0);
//     TEST_ASSERT_EQUAL_PTR( &NewNetworkBuffer, pReturn );
//     TEST_ASSERT_EQUAL(1222, pReturn->xDataLength);
// }

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_Without_Buffer(void)
{
    NetworkBufferDescriptor_t * pReturn;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&NewNetworkBuffer);

    pReturn = prvTCPBufferResize(pxSocket, NULL, 500, 0);
    TEST_ASSERT_EQUAL_PTR( &NewNetworkBuffer, pReturn );
    TEST_ASSERT_EQUAL(554, pReturn->xDataLength);
}

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_Without_Buffer_Null_New_Buffer(void)
{
    NetworkBufferDescriptor_t * pReturn;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(NULL);

    pReturn = prvTCPBufferResize(pxSocket, NULL, 500, 0);
    TEST_ASSERT_EQUAL_PTR( NULL, pReturn );
}

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_With_Buffer_LT_Needed_GT_Last_Packet(void)
{
    NetworkBufferDescriptor_t * pReturn;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&NewNetworkBuffer);
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    pReturn = prvTCPBufferResize(pxSocket, pxNetworkBuffer, 500, 0);
    TEST_ASSERT_EQUAL_PTR( &NewNetworkBuffer, pReturn );
    TEST_ASSERT_EQUAL(554, pReturn->xDataLength);
}

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_With_Buffer_LT_Needed_LT_Last_Packet(void)
{
    NetworkBufferDescriptor_t * pReturn;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&NewNetworkBuffer);
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    pReturn = prvTCPBufferResize(pxSocket, pxNetworkBuffer, 10, 0);
    TEST_ASSERT_EQUAL_PTR( &NewNetworkBuffer, pReturn );
    TEST_ASSERT_EQUAL(70, pReturn->xDataLength);
}

/* test for prvTCPBufferResize function */
void test_prvTCPBufferResize_With_Buffer_GT_Needed(void)
{
    NetworkBufferDescriptor_t * pReturn;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;

    pxNetworkBuffer->xDataLength = 200;

    pReturn = prvTCPBufferResize(pxSocket, pxNetworkBuffer, 10, 0);
    TEST_ASSERT_EQUAL_PTR( pxNetworkBuffer, pReturn );
    TEST_ASSERT_EQUAL(64, pReturn->xDataLength);
}


/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Syn_Zero_Data(void)
{
    int32_t BytesSent = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];

    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x12345678;
    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.usMSS = 1000;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn(0); 


    BytesSent = prvTCPPrepareSend(pxSocket, &pxNetworkBuffer, 0);
    TEST_ASSERT_EQUAL( 0, BytesSent );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Syn_Zero_Data_Win_Change(void)
{
    int32_t BytesSent = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];

    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x12345678;
    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdTRUE;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn(0); 

    BytesSent = prvTCPPrepareSend(pxSocket, &pxNetworkBuffer, 0);
    TEST_ASSERT_EQUAL( 40, BytesSent );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Syn_Zero_Data_Keep_Alive(void)
{
    int32_t BytesSent = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];

    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x12345678;
    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn(0); 

    BytesSent = prvTCPPrepareSend(pxSocket, &pxNetworkBuffer, 0);
    TEST_ASSERT_EQUAL( 40, BytesSent );
}

/* test for prvTCPPrepareSend function */
void test_prvTCPPrepareSend_State_Established_Non_Zero_Data_Not_Close_Not_ShutDown_KLcount1(void)
{
    int32_t BytesSent = 0;
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    uint8_t ReturnEthernetBuffer[ ipconfigNETWORK_MTU ];
    NetworkBufferDescriptor_t NewNetworkBuffer;
    NewNetworkBuffer.pucEthernetBuffer = ReturnEthernetBuffer;

    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x12345678;
    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.usMSS = 1000;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE;
    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE;
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE;
    pxSocket->u.xTCP.ucKeepRepCount = 1;


    ulTCPWindowTxGet_ExpectAnyArgsAndReturn(500); 
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(pxNetworkBuffer);
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();
    uxStreamBufferDistance_ExpectAnyArgsAndReturn(500);
    uxStreamBufferGet_ExpectAnyArgsAndReturn(20);

    BytesSent = prvTCPPrepareSend(pxSocket, &pxNetworkBuffer, 0);
    TEST_ASSERT_EQUAL( 40, BytesSent );
}