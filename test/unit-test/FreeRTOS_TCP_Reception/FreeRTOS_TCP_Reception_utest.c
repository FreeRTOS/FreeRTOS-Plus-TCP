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

//#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_IP_Timers.h"
//#include "mock_FreeRTOS_TCP_IP.h"
//#include "mock_FreeRTOS_ICMP.h"
//#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
//#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_UDP_IP.h"

#include "FreeRTOS_TCP_IP.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_TCP_Reception_stubs.c"



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
    0x02, 0x04, 0x12, 0x34,     /* MSS */
    0x01,  /* noop */
    0x03, 0x03, 0x10,  /* WSF */
    0x01, /* noop */
    0x04, 0x02,  /* SACKP */
    0x00        /* EOL */
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

/* Test for prvCheckOptions function. */
void test_prvCheckOptions_MSS_WSF( void )
{
    BaseType_t xReturn;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer );

    ProtocolHeaders_t *pxProtocolHeader = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                              &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    memcpy( (void*)pxTCPHeader->ucOptdata, (void*)ucTCPOptions_good_MSS_WSF, sizeof(ucTCPOptions_good_MSS_WSF));
    
    
    xReturn = prvCheckOptions( pxSocket, pxNetworkBuffer);
    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/* Test for prvSingleStepTCPHeaderOptions function. */
void test_prvSingleStepTCPHeaderOptions_SACK( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer );

    ProtocolHeaders_t *pxProtocolHeader = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                              &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    uint8_t ucTCPOptions_good_SACK[ ipSIZE_TCP_OPTIONS ] = 
    {
        0x05, 0x0A, 0x10, 0x00, 0x05, 0x00, 0x11, 0x11, 0x22, 0x22
    };
    memcpy( (void*)pxTCPHeader->ucOptdata, (void*)ucTCPOptions_good_SACK, sizeof(ucTCPOptions_good_SACK));
    
    
    result = prvSingleStepTCPHeaderOptions( 
        pxTCPHeader->ucOptdata,
        10,
        pxSocket, 
        pdTRUE);

    TEST_ASSERT_EQUAL( 10, result );
}

/* Test for prvSingleStepTCPHeaderOptions function. */
void test_prvSingleStepTCPHeaderOptions_TS( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer );

    ProtocolHeaders_t *pxProtocolHeader = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                              &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    uint8_t ucTCPOptions_good_SACK[ ipSIZE_TCP_OPTIONS ] = 
    {
        0x08, 0x0A, 0x10, 0x00, 0x05, 0x00, 0x11, 0x11, 0x22, 0x22
    };
    memcpy( (void*)pxTCPHeader->ucOptdata, (void*)ucTCPOptions_good_SACK, sizeof(ucTCPOptions_good_SACK));
    
    
    result = prvSingleStepTCPHeaderOptions( 
        pxTCPHeader->ucOptdata,
        10,
        pxSocket, 
        pdTRUE);

    TEST_ASSERT_EQUAL( 10, result );
}

/* Test for prvSingleStepTCPHeaderOptions function. */
void test_prvSingleStepTCPHeaderOptions_END_NOOP( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer );

    ProtocolHeaders_t *pxProtocolHeader = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                              &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    uint8_t ucTCPOptions = 0x00;
    memcpy( (void*)pxTCPHeader->ucOptdata, (void*)&ucTCPOptions, sizeof(ucTCPOptions));
    
    
    result = prvSingleStepTCPHeaderOptions( 
        pxTCPHeader->ucOptdata,
        1,
        pxSocket, 
        pdTRUE);

    TEST_ASSERT_EQUAL( 0, result );

    ucTCPOptions = 0x01;
    memcpy( (void*)pxTCPHeader->ucOptdata, (void*)&ucTCPOptions, sizeof(ucTCPOptions));
    
    
    result = prvSingleStepTCPHeaderOptions( 
        pxTCPHeader->ucOptdata,
        1,
        pxSocket, 
        pdTRUE);

    TEST_ASSERT_EQUAL( 1, result );
}


/* Test for prvCheckRxData function. */
void test_prvCheckRxData( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    //memset(pxNetworkBuffer->pucEthernetBuffer, 0, sizeof(ucEthernetBuffer));
    // memcpy(pxNetworkBuffer->pucEthernetBuffer, ucEthernetBuffer, sizeof(ucEthernetBuffer));
    uint8_t EthernetBuffer[ ipconfigNETWORK_MTU ] =
    {
        0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x08, 0x00, 0x45, 0x00,
        0x00, 0x34, 0x15, 0xc2, 0x40, 0x00, 0x40, 0x06, 0xa8, 0x8e, 0xc0, 0xa8, 0x00, 0x08, 0xac, 0xd9,
        0x0e, 0xea, 0xea, 0xfe, 0x01, 0xbb, 0x8b, 0xaf, 0x8a, 0x24, 0xdc, 0x96, 0x95, 0x7a, 0x80, 0x10,
        0x01, 0xf5, 0x7c, 0x9a, 0x00, 0x00, 0x01, 0x01, 0x08, 0x0a, 0xb8, 0x53, 0x57, 0x27, 0xb2, 0xce,
        0xc3, 0x17                                       
    };

    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    uint8_t * pData;
        
    result = prvCheckRxData( pxNetworkBuffer, &pData);

    TEST_ASSERT_EQUAL( 0, result );
}
