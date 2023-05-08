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

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_Sockets_IPv6_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_portable.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"

#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IPv6_Sockets.h"

#include "FreeRTOS_Sockets_IPv6_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* The maximum segment size used by TCP, it is the maximum size of
 * the TCP payload per packet.
 * For IPv4: when MTU equals 1500, the MSS equals 1460.
 * It is recommended to use the default value defined here.
 *
 * In FreeRTOS_TCP_IP.c, there is a local macro called 'tcpREDUCED_MSS_THROUGH_INTERNET'.
 * When a TCP connection is made outside the local network, the MSS
 * will be reduced to 'tcpREDUCED_MSS_THROUGH_INTERNET' before the connection
 * is made.
 */
#ifndef ipconfigTCP_MSS
    #define ipconfigTCP_MSS    ( ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER ) )
#endif

static const IPv6_Address_t xSampleAddress_IPv6 = { .ucBytes = {0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x70, 0x08 } };
static const IPv6_Address_t xSampleAddress_IPv6_2 = { .ucBytes = {0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x74, 0x08 } };
static const IPv6_Address_t xSampleAddress_IPv6_3 = { .ucBytes = {0xfe, 0x80, 0, 0, 0, 0xde, 0, 0, 0, 0, 0, 0, 0, 0, 0x70, 0x08 } };
static const IPv6_Address_t xSampleAddress_IPv6_4 = { .ucBytes = {0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0, 0, 0, 0x74, 0x08 } };
static const IPv6_Address_t xSampleAddress_IPv6_5 = { .ucBytes = {0xfe, 0x80, 0, 0xde, 0, 0xde, 0, 0xde, 0, 0xde, 0xff, 0, 0xde, 0, 0x74, 0x08 } };
static const IPv6_Address_t xSampleAddress_IPv6_6 = { .ucBytes = {0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 } };

/* IPv6 address pointer passed but socket is not an IPv6 socket */
void test_pxTCPSocketLookup_IPv6_NotIPv6Socket_NonNULLIPv6Address( void )
{
    FreeRTOS_Socket_t xSocket;
    IPv6_Address_t xAddress_IPv6;
    FreeRTOS_Socket_t * pxRetSocket;

    xSocket.bits.bIsIPv6 = pdFALSE_UNSIGNED;

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, &xAddress_IPv6, 0xABCD1234 );

    TEST_ASSERT_EQUAL( NULL, pxRetSocket );

}

/* NULL IPv6 address pointer passed and socket is not an IPv6 socket */
void test_pxTCPSocketLookup_IPv6_NotIPv6Socket_NULLIPv6Address( void )
{
    FreeRTOS_Socket_t xSocket;
    IPv6_Address_t xAddress_IPv6;
    FreeRTOS_Socket_t * pxRetSocket;

    xSocket.bits.bIsIPv6 = pdFALSE_UNSIGNED;

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, NULL, 0xABCD1234 );

    TEST_ASSERT_EQUAL( NULL, pxRetSocket );

}

/* NULL IPv6 address pointer passed and socket is not an IPv6 socket, but a matching IPv4 address is passed */
void test_pxTCPSocketLookup_IPv6_NotIPv6Socket_NULLIPv6Address_MatchingIPv4Address( void )
{
    FreeRTOS_Socket_t xSocket, * pxRetSocket = NULL;
    IPv6_Address_t xAddress_IPv6;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.bits.bIsIPv6 = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = 0xABCD1234;

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, NULL, 0xABCD1234 );

    TEST_ASSERT_EQUAL( &xSocket, pxRetSocket );

}

/* NULL IPv6 address pointer passed and socket is not an IPv6 socket, but a non matching IPv4 address is passed */
void test_pxTCPSocketLookup_IPv6_NotIPv6Socket_NULLIPv6Address_NonMatchingIPv4Address( void )
{
    FreeRTOS_Socket_t xSocket, * pxRetSocket = NULL;
    IPv6_Address_t xAddress_IPv6;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.bits.bIsIPv6 = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = 0xDBCD1235;

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, NULL, 0xABCD1234 );

    TEST_ASSERT_EQUAL( NULL, pxRetSocket );

}

/* NULL IPv6 address pointer passed and socket is an IPv6 socket */
void test_pxTCPSocketLookup_IPv6_IPv6Socket_NULLIPv6Address( void )
{
    FreeRTOS_Socket_t xSocket;
    IPv6_Address_t xAddress_IPv6;
    FreeRTOS_Socket_t * pxRetSocket;

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, NULL, 0xABCD1234 );

    TEST_ASSERT_EQUAL( NULL, pxRetSocket );

}

/* Valid IPv6 address pointer passed and socket is an IPv6 socket, but the IPv6 addresses match */
void test_pxTCPSocketLookup_IPv6_IPv6Socket_NonNULLIPv6Address__MatchingIPv6Address( void )
{
    FreeRTOS_Socket_t xSocket;
    IPv6_Address_t xAddress_IPv6;
    FreeRTOS_Socket_t * pxRetSocket;

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;
    memcpy(&xAddress_IPv6, &xSampleAddress_IPv6, sizeof(IPv6_Address_t));
    memcpy(xSocket.u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, &xSampleAddress_IPv6, sizeof(IPv6_Address_t));

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, &xAddress_IPv6, 0xABCD1234 );

    TEST_ASSERT_EQUAL( &xSocket, pxRetSocket );

}

/* Valid IPv6 address pointer passed and socket is an IPv6 socket, but the IPv6 addresses doesn't match */
void test_pxTCPSocketLookup_IPv6_IPv6Socket_NonNULLIPv6Address__NonMatchingIPv6Address( void )
{
    FreeRTOS_Socket_t xSocket;
    IPv6_Address_t xAddress_IPv6;
    FreeRTOS_Socket_t * pxRetSocket;

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;
    memcpy(&xAddress_IPv6, &xSampleAddress_IPv6, sizeof(IPv6_Address_t));
    memcpy(xSocket.u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, &xSampleAddress_IPv6_2, sizeof(IPv6_Address_t));

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, &xAddress_IPv6, 0xABCD1234 );

    TEST_ASSERT_EQUAL( NULL, pxRetSocket );

}

/* Catch configASSERT in case NULL pxDestinationAddress is passed */
void test_xSend_UDP_Update_IPv6_NullDestinationAddr( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;

    catch_assert( xSend_UDP_Update_IPv6(&xNetworkBuffer, NULL) );

}

/* Valid network buffer and destination addresses are passed and the output is compared */
void test_xSend_UDP_Update_IPv6( void )
{

    struct freertos_sockaddr xDestinationAddress;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPPacket_IPv6;
    void *pvReturn;

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) xNetworkBuffer.pucEthernetBuffer );

    ( void ) memcpy( xDestinationAddress.sin_address.xIP_IPv6.ucBytes, xSampleAddress_IPv6.ucBytes, sizeof(IPv6_Address_t) );

    pvReturn = xSend_UDP_Update_IPv6(&xNetworkBuffer, &xDestinationAddress);

    TEST_ASSERT_EQUAL_MEMORY(pxUDPPacket_IPv6->xIPHeader.xDestinationAddress.ucBytes, xDestinationAddress.sin_address.xIP_IPv6.ucBytes,sizeof(IPv6_Address_t));
    TEST_ASSERT_EQUAL_MEMORY(xNetworkBuffer.xIPAddress.xIP_IPv6.ucBytes, xDestinationAddress.sin_address.xIP_IPv6.ucBytes,sizeof(IPv6_Address_t));
    TEST_ASSERT_EQUAL(pxUDPPacket_IPv6->xEthernetHeader.usFrameType, ipIPv6_FRAME_TYPE);
    TEST_ASSERT_EQUAL( NULL, pvReturn );

}

/* Test for invalid IP frame type */
void test_xRecv_Update_IPv6_InvalidFrame( void )
{

    struct freertos_sockaddr xSourceAddress;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPPacket_IPv6;
    void *pvReturn;
    size_t xRetVal;

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) xNetworkBuffer.pucEthernetBuffer );

    pxUDPPacket_IPv6->xEthernetHeader.usFrameType = 0xCAFE;

    xRetVal = xRecv_Update_IPv6(&xNetworkBuffer, &xSourceAddress);

    TEST_ASSERT_EQUAL( 0, xRetVal );

}

/* NULL source address pointer */
void test_xRecv_Update_IPv6_InvalidFrame_NullSourceAddress( void )
{

    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPPacket_IPv6;
    void *pvReturn;
    size_t xRetVal;

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) xNetworkBuffer.pucEthernetBuffer );

    pxUDPPacket_IPv6->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    xRetVal = xRecv_Update_IPv6(&xNetworkBuffer, NULL);

    TEST_ASSERT_EQUAL( ipUDP_PAYLOAD_OFFSET_IPv6, xRetVal );
    
}

/* Test for invalid IP frame type */
void test_xRecv_Update_IPv6_InvalidFrame_ValidSourceAddress( void )
{

    struct freertos_sockaddr xSourceAddress;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPPacket_IPv6;
    void *pvReturn;
    size_t xRetVal;

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) xNetworkBuffer.pucEthernetBuffer );

    ( void ) memcpy( pxUDPPacket_IPv6->xIPHeader.xSourceAddress.ucBytes, xSampleAddress_IPv6.ucBytes, sizeof(IPv6_Address_t) );
    xNetworkBuffer.usPort = 1234;

    pxUDPPacket_IPv6->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    xRetVal = xRecv_Update_IPv6(&xNetworkBuffer, &xSourceAddress);

    TEST_ASSERT_EQUAL( ipUDP_PAYLOAD_OFFSET_IPv6, xRetVal );
    TEST_ASSERT_EQUAL_MEMORY(xSourceAddress.sin_address.xIP_IPv6.ucBytes, xSampleAddress_IPv6.ucBytes, sizeof(IPv6_Address_t));
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, xSourceAddress.sin_family );
    TEST_ASSERT_EQUAL( 1234, xSourceAddress.sin_port );

}

void test_cHexToChar_LessThanEqNine( void )
{

    char cRetVal;

    cRetVal = cHexToChar(8);

    TEST_ASSERT_EQUAL( '8', cRetVal );

}

void test_cHexToChar_GreaterThanNine( void )
{

    char cRetVal;

    cRetVal = cHexToChar(10);

    TEST_ASSERT_EQUAL( 'a', cRetVal );

}

void test_cHexToChar_GreaterThanFifteen( void )
{

    char cRetVal;

    catch_assert(cHexToChar(16));

}

void test_uxHexPrintShort( void )
{
    char cBuffer[5] = {'\0'};
    size_t xCBuffLen;
    char *pcExpOp = "cafe";

    xCBuffLen = uxHexPrintShort(cBuffer, 5, 0xCAFE);

    TEST_ASSERT_EQUAL( 4, xCBuffLen );
    TEST_ASSERT_EQUAL_MEMORY(pcExpOp,cBuffer, xCBuffLen);

}


void test_uxHexPrintShort_LongerBuffer( void )
{
    char cBuffer[7] = {'\0'};
    size_t xCBuffLen;
    char *pcExpOp = "cafe";

    xCBuffLen = uxHexPrintShort(cBuffer, 7, 0xCAFE);

    TEST_ASSERT_EQUAL( 4, xCBuffLen );
    TEST_ASSERT_EQUAL_MEMORY(pcExpOp,cBuffer, xCBuffLen);

}

void test_uxHexPrintShort_OneByteInput( void )
{
    char cBuffer[5] = {'\0'};
    size_t xCBuffLen;
    char *pcExpOp = "cafe";

    xCBuffLen = uxHexPrintShort(cBuffer, 5, 0xCA);

    TEST_ASSERT_EQUAL( 2, xCBuffLen );
    TEST_ASSERT_EQUAL_MEMORY(pcExpOp,cBuffer, xCBuffLen);

}

void test_uxHexPrintShort_OneByteAndNibbleInput( void )
{
    char cBuffer[5] = {'\0'};
    size_t xCBuffLen;
    char *pcExpOp = "cafe";

    xCBuffLen = uxHexPrintShort(cBuffer, 5, 0xCAF);

    TEST_ASSERT_EQUAL( 3, xCBuffLen );
    TEST_ASSERT_EQUAL_MEMORY(pcExpOp,cBuffer, xCBuffLen);

}

void test_uxHexPrintShort_NibbleInput( void )
{
    char cBuffer[5] = {'\0'};
    size_t xCBuffLen;
    char *pcExpOp = "cafe";

    xCBuffLen = uxHexPrintShort(cBuffer, 5, 0xC);

    TEST_ASSERT_EQUAL( 1, xCBuffLen );
    TEST_ASSERT_EQUAL_MEMORY(pcExpOp,cBuffer, xCBuffLen);

}

void test_prv_ntop6_search_zeros( void )
{
    struct sNTOP6_Set xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = xSampleAddress_IPv6.ucBytes;

    prv_ntop6_search_zeros( &( xSet ) );

    TEST_ASSERT_EQUAL( 6, xSet.xZeroLength );
    TEST_ASSERT_EQUAL( 1, xSet.xZeroStart );
    
}

void test_prv_ntop6_search_zeros_2( void )
{
    struct sNTOP6_Set xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = xSampleAddress_IPv6_3.ucBytes;

    prv_ntop6_search_zeros( &( xSet ) );

    TEST_ASSERT_EQUAL( 4, xSet.xZeroLength );
    TEST_ASSERT_EQUAL( 3, xSet.xZeroStart );
    
}

void test_prv_ntop6_search_zeros_3( void )
{
    struct sNTOP6_Set xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = xSampleAddress_IPv6_4.ucBytes;

    prv_ntop6_search_zeros( &( xSet ) );

    TEST_ASSERT_EQUAL( 4, xSet.xZeroLength );
    TEST_ASSERT_EQUAL( 1, xSet.xZeroStart );
    
}

void test_prv_ntop6_search_zeros_4( void )
{
    struct sNTOP6_Set xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = xSampleAddress_IPv6_6.ucBytes;

    prv_ntop6_search_zeros( &( xSet ) );

    TEST_ASSERT_EQUAL( 7, xSet.xZeroLength );
    TEST_ASSERT_EQUAL( 1, xSet.xZeroStart );
    
}

void test_prv_ntop6_search_zeros_NoZeroes( void )
{
    struct sNTOP6_Set xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = xSampleAddress_IPv6_5.ucBytes;

    prv_ntop6_search_zeros( &( xSet ) );

    TEST_ASSERT_EQUAL( 0, xSet.xZeroLength );
    TEST_ASSERT_EQUAL( -1, xSet.xZeroStart );
    
}

void test_prv_ntop6_write_zeros( void )
{
    struct sNTOP6_Set xSet;
    char cDestination[41] = {'\0'};

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = xSampleAddress_IPv6.ucBytes;
    xSet.xZeroLength = 6;
    xSet.xZeroStart = 1;
    xSet.xIndex = xSet.xZeroStart;
    xSet.uxTargetIndex = xSet.xZeroStart * 5; /* Assuming all the previous shorts have 4 chars + 1 colon */

    prv_ntop6_write_zeros( cDestination, 40, &( xSet ) );

    TEST_ASSERT_EQUAL_MEMORY(&cDestination[xSet.xZeroStart * 5], ":", 1);

}

void test_prv_ntop6_write_zeros_AddressEndsInZeroes( void )
{
    struct sNTOP6_Set xSet;
    char cDestination[41] = {'\0'};

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = xSampleAddress_IPv6.ucBytes;
    xSet.xZeroLength = 7;
    xSet.xZeroStart = 1;
    xSet.xIndex = xSet.xZeroStart;
    xSet.uxTargetIndex = xSet.xZeroStart * 5; /* Assuming all the previous shorts have 4 chars + 1 colon */

    prv_ntop6_write_zeros( cDestination, 40, &( xSet ) );

    TEST_ASSERT_EQUAL_MEMORY(&cDestination[xSet.xZeroStart * 5], "::", 2);

}