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
#include "mock_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_DNS.h"

#include "FreeRTOS_UDP_IP.h"

#include "FreeRTOS_UDP_IP_stubs.c"
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


extern NetworkInterface_t xInterfaces[ 1 ];

static uint32_t ulFunctionCalled = 0;
static BaseType_t xFunctionReturn;
static BaseType_t xLocalHandler( Socket_t pxSocket,
                                 void * pvData,
                                 size_t xLength,
                                 const struct freertos_sockaddr * pxFrom,
                                 const struct freertos_sockaddr * pxTo )
{
    TEST_ASSERT( pxSocket != NULL );
    TEST_ASSERT( pvData != NULL );
    TEST_ASSERT( pxFrom != NULL );
    TEST_ASSERT( pxTo != NULL );

    ulFunctionCalled++;

    return xFunctionReturn;
}


static void vConfigureInterfaceAndEndpoints( NetworkBufferDescriptor_t * xLocalNetworkBuffer,
                                             struct xNetworkEndPoint * xEndPoint,
                                             struct xNetworkInterface * xInterface )
{
    xEndPoint->pxNetworkInterface = xInterface;
    xEndPoint->pxNext = NULL;
    xLocalNetworkBuffer->pxEndPoint = xEndPoint;
    xInterface->pxEndPoint = xEndPoint;
    xInterface->pxNext = NULL;
}

/*
 * @brief Test what happens if the packet cannot be sent due to
 *        the address not being resolved.
 */
void test_vProcessGeneratedUDPPacket_CantSendPacket( void )
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eCantSendPacket );

    /* Expect the buffer to be released in this case. */
    vReleaseNetworkBufferAndDescriptor_Expect( &xLocalNetworkBuffer );

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );

    /* Nothing to assert on since there was no modification. */
}

BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
}


/*
 * @brief Test what if there is a cache miss and the packet is smaller
 *        than the minimum number of bytes required in the packet.
 */
void test_vProcessGeneratedUDPPacket_CacheMiss_PacketSmaller( void )
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    UDPPacket_t * pxUDPPacket;
    uint32_t ulIPAddr = 0x1234ABCD, ulLocalIPAddress = 0xAABBCCDD;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    vConfigureInterfaceAndEndpoints( &xLocalNetworkBuffer, &xEndPoint, &xInterface );

    xLocalNetworkBuffer.xIPAddress.ulIP_IPv4 = ulIPAddr;
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t * ) pucLocalEthernetBuffer;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );
    eARPGetCacheEntry_ReturnMemThruPtr_pulIPAddress( &ulLocalIPAddress, sizeof( ulLocalIPAddress ) );
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &xEndPoint );

    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( &xEndPoint );

    vARPRefreshCacheEntry_Ignore();
    vARPGenerateRequestPacket_Expect( &xLocalNetworkBuffer );

    /* Make sure that the packet is smaller than minimum packet length. */
    xLocalNetworkBuffer.xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES - 2;
    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );

    TEST_ASSERT_EQUAL( ulLocalIPAddress, xLocalNetworkBuffer.xIPAddress.ulIP_IPv4 );
}

/*
 * @brief Test when there is a cache miss, but the packet is of
 *        appropriate size.
 */
void test_vProcessGeneratedUDPPacket_CacheMiss_PacketNotSmaller( void )
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    UDPPacket_t * pxUDPPacket;
    uint32_t ulIPAddr = 0x1234ABCD, ulLocalIPAddress = 0xAABBCCDD;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    vConfigureInterfaceAndEndpoints( &xLocalNetworkBuffer, &xEndPoint, &xInterface );

    pxUDPPacket = ( UDPPacket_t * ) pucLocalEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.xDataLength = sizeof( UDPPacket_t );


    /* / * Cleanup the ethernet buffer. * / */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    /* / * Map the UDP packet onto the start of the frame. * / */

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );
    eARPGetCacheEntry_ReturnMemThruPtr_pulIPAddress( &ulLocalIPAddress, sizeof( ulLocalIPAddress ) );

    vARPRefreshCacheEntry_Expect( NULL, ulLocalIPAddress, NULL );

    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( &xEndPoint );

    vARPGenerateRequestPacket_Expect( &xLocalNetworkBuffer );

    xLocalNetworkBuffer.xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES + 2;
    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );

    TEST_ASSERT_EQUAL( ulLocalIPAddress, xLocalNetworkBuffer.xIPAddress.ulIP_IPv4 );
}

/*
 * @brief Test when ARP cache returned an unknown value.
 */
void test_vProcessGeneratedUDPPacket_UnknownARPReturn( void )
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    UDPPacket_t * pxUDPPacket;
    uint32_t ulIPAddr = 0x1234ABCD;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    xLocalNetworkBuffer.xIPAddress.ulIP_IPv4 = ulIPAddr;
    xLocalNetworkBuffer.usPort = ipPACKET_CONTAINS_ICMP_DATA;

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t * ) pucLocalEthernetBuffer;

    /* Return an unknown value. */
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eCantSendPacket + 1 );

    vReleaseNetworkBufferAndDescriptor_Expect( &xLocalNetworkBuffer );

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );

    /* Nothing to assert on since there was no modification. */
}

/*
 * @brief Test when there is a cache hit but the packet does not have
 *        ICMP data.
 */
void test_vProcessGeneratedUDPPacket_CacheHit_NoICMP( void )
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    UDPPacket_t * pxUDPPacket;
    uint32_t ulIPAddr = 0x1234ABCD;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    xEndPoint.pxNetworkInterface = &xInterface;
    xEndPoint.pxNext = NULL;
    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xInterface.pxEndPoint = &xEndPoint;
    xInterface.pxNext = NULL;
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    xLocalNetworkBuffer.xIPAddress.ulIP_IPv4 = ulIPAddr;
    /* Not ICMP data. */
    xLocalNetworkBuffer.usPort = ipPACKET_CONTAINS_ICMP_DATA + 1;
    xLocalNetworkBuffer.usBoundPort = 0x1023;
    xLocalNetworkBuffer.xDataLength = sizeof( UDPPacket_t );

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t * ) pucLocalEthernetBuffer;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usGenerateChecksum_ExpectAndReturn( 0U, NULL, ipSIZE_OF_IPv4_HEADER, 0 );
    usGenerateChecksum_IgnoreArg_pucNextData();

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );

    TEST_ASSERT_EQUAL( xLocalNetworkBuffer.usPort, pxUDPPacket->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL( xLocalNetworkBuffer.usBoundPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( 0, pxUDPPacket->xUDPHeader.usChecksum );
}

/*
 * @brief Test cache hit when the packet is ICMP packet and has an LLMNR
 *        IP address with a UDP socket option.
 */
void test_vProcessGeneratedUDPPacket_CacheHit_ICMPPacket_LLMNR_UDPChkSumOption( void )
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    UDPPacket_t * pxUDPPacket;
    uint32_t ulIPAddr = ipLLMNR_IP_ADDR;
    uint8_t ucSocketOptions = FREERTOS_SO_UDPCKSUM_OUT;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    xEndPoint.pxNetworkInterface = &xInterface;
    xEndPoint.pxNext = NULL;
    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xInterface.pxEndPoint = &xEndPoint;
    xInterface.pxNext = NULL;

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] = ucSocketOptions;

    xLocalNetworkBuffer.xIPAddress.ulIP_IPv4 = ulIPAddr;
    xLocalNetworkBuffer.usPort = ipPACKET_CONTAINS_ICMP_DATA;
    xLocalNetworkBuffer.usBoundPort = 0x1023;
    xLocalNetworkBuffer.xDataLength = sizeof( UDPPacket_t );

    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t * ) pucLocalEthernetBuffer;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    usGenerateChecksum_ExpectAndReturn( 0U, NULL, ipSIZE_OF_IPv4_HEADER, 0 );
    usGenerateChecksum_IgnoreArg_pucNextData();

    usGenerateProtocolChecksum_ExpectAndReturn( pucLocalEthernetBuffer, xLocalNetworkBuffer.xDataLength, pdTRUE, 0 );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );

    TEST_ASSERT_EQUAL( xLocalNetworkBuffer.usPort, pxUDPPacket->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL( ipPROTOCOL_ICMP, pxUDPPacket->xIPHeader.ucProtocol );
    TEST_ASSERT_EQUAL( 0, pxUDPPacket->xUDPHeader.usChecksum );
}

/*
 * @brief Test the asserts in the function.
 */
void test_xProcessReceivedUDPPacket_catchAsserts( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    BaseType_t xIsWaitingARPResolution = pdFALSE;

    catch_assert( xProcessReceivedUDPPacket( NULL, 0, &xIsWaitingARPResolution ) );

    xLocalNetworkBuffer.pucEthernetBuffer = NULL;
    catch_assert( xProcessReceivedUDPPacket( &xLocalNetworkBuffer, 0, &xIsWaitingARPResolution ) );
}

/*
 * @brief Test when there is no listening socket and the packet is not
 *        for this node.
 */
void test_xProcessReceivedUDPPacket_NoListeningSocket_NotForThisNode( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = 0;
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    UDPPacket_t * pxUDPPacket;

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    pxUDPPacket = ( ( const UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer );
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    /* No socket found. */
    pxUDPSocketLookup_ExpectAndReturn( usPort, NULL );

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when there is no listening socket but the packet seems like
 *        a late DNS response.
 */
void test_xProcessReceivedUDPPacket_NoListeningSocket_DelayedDNSResponse( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = 0;
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    vConfigureInterfaceAndEndpoints( &xLocalNetworkBuffer, &xEndPoint, &xInterface );

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    pxUDPPacket = ( ( const UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer );
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    /* Packet coming from a DNS port. */
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( ipDNS_PORT );

    /* No socket found. */
    pxUDPSocketLookup_ExpectAndReturn( usPort, NULL );

    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xLocalNetworkBuffer, pdPASS );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when there is no listening socket but the packet seems like an
 *        LLMNR response.
 */
void test_xProcessReceivedUDPPacket_NoListeningSocket_LLMNRResponse( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipLLMNR_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    vConfigureInterfaceAndEndpoints( &xLocalNetworkBuffer, &xEndPoint, &xInterface );

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( ( const UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer );
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* LLMNR port. */
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_ntohs( ipLLMNR_PORT );

    /* No socket found. */
    pxUDPSocketLookup_ExpectAndReturn( usPort, NULL );

    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xLocalNetworkBuffer, pdPASS );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when there is no listening socket but the packet is for LLMNR and the
 *        source and destination sockets are mismatching.
 */
void test_xProcessReceivedUDPPacket_NoListeningSocket_LLMNRResponse_MismatchingPorts( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipLLMNR_PORT + 1 );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    vConfigureInterfaceAndEndpoints( &xLocalNetworkBuffer, &xEndPoint, &xInterface );

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_ntohs( ipLLMNR_PORT );

    pxUDPSocketLookup_ExpectAndReturn( usPort, NULL );

    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xLocalNetworkBuffer, pdPASS );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when there is no listening socket and this is an NBNS response.
 */
void test_xProcessReceivedUDPPacket_NoListeningSocket_NBNSResponse( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    vConfigureInterfaceAndEndpoints( &xLocalNetworkBuffer, &xEndPoint, &xInterface );

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_ntohs( ipNBNS_PORT );

    pxUDPSocketLookup_ExpectAndReturn( usPort, NULL );

    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );
    ulNBNSHandlePacket_ExpectAndReturn( &xLocalNetworkBuffer, pdPASS );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when there is no listening socket and this is an NBNS packet but the source
 *        and destination ports mismatch.
 */
void test_xProcessReceivedUDPPacket_NoListeningSocket_NBNSResponse_MismatchingPorts( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT + 1 );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    vConfigureInterfaceAndEndpoints( &xLocalNetworkBuffer, &xEndPoint, &xInterface );

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_ntohs( ipNBNS_PORT );

    pxUDPSocketLookup_ExpectAndReturn( usPort, NULL );

    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );
    ulNBNSHandlePacket_ExpectAndReturn( &xLocalNetworkBuffer, pdPASS );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when a matching socket is found but there is no handler listed.
 */
void test_xProcessReceivedUDPPacket_SocketFound_NoHandler_BufferFull( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    xEndPoint.ipv4_settings.ulIPAddress = 0xC01234BD;

    vConfigureInterfaceAndEndpoints( &xLocalNetworkBuffer, &xEndPoint, &xInterface );

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.xDataLength = ipconfigTCP_MSS;
    xLocalNetworkBuffer.xDataLength = sizeof( UDPPacket_t );

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    /* No socket handler listed for UDP packets. */
    xLocalSocket.u.xUDP.pxHandleReceive = NULL;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdFALSE );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1 );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when a matching socket is found but there is no handler listed.
 *        Also the packet comes in when DHCP process is going on.
 */
void test_xProcessReceivedUDPPacket_SocketFound_NoHandler_BufferFull1( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    xEndPoint.ipv4_settings.ulIPAddress = 0U;

    vConfigureInterfaceAndEndpoints( &xLocalNetworkBuffer, &xEndPoint, &xInterface );

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.xDataLength = ipconfigTCP_MSS;
    xLocalNetworkBuffer.xDataLength = sizeof( UDPPacket_t );

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    /* No socket handler listed for UDP packets. */
    xLocalSocket.u.xUDP.pxHandleReceive = NULL;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1 );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when a matching socket is found but there is no handler, event groups,
 *        socket set and user semaphore added to the socket.
 */
void test_xProcessReceivedUDPPacket_SocketFound_NoHandler_NoEventGroupSocketSetUSemaphore( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    xEndPoint.ipv4_settings.ulIPAddress = 0xC01234BD;

    vConfigureInterfaceAndEndpoints( &xLocalNetworkBuffer, &xEndPoint, &xInterface );

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = NULL;
    xLocalSocket.pxSocketSet = NULL;
    xLocalSocket.pxUserSemaphore = NULL;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdFALSE );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 0 );

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when a matching socket is found but there is no handler listed but there
 *        is a user semaphore, event group.
 */
void test_xProcessReceivedUDPPacket_SocketFound_NoHandler_ValidEventGroupUSemaphore( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    xEndPoint.ipv4_settings.ulIPAddress = 0xC01234BD;

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = ( void * ) 1;
    xLocalSocket.pxSocketSet = NULL;
    xLocalSocket.pxUserSemaphore = ( void * ) 1;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdFALSE );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn( &xEndPoint, pdPASS );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when a matching socket is found but there is no handler listed but there
 *        is a user semaphore and event group but the select bits are invalid.
 */
void test_xProcessReceivedUDPPacket_SocketFound_NoHandler_ValidEventGroupUSemaphoreSocketSet_InvalidSelectBits( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    xEndPoint.ipv4_settings.ulIPAddress = 0xC01234BD;

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = ( void * ) 1;
    xLocalSocket.pxSocketSet = ( void * ) 1;
    xLocalSocket.pxUserSemaphore = ( void * ) 1;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdFALSE );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn( &xEndPoint, pdPASS );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when a matching socket is found but there is no handler listed but there
 *        is a user semaphore and event group and the select bits are valid.
 */
void test_xProcessReceivedUDPPacket_SocketFound_NoHandler_ValidEventGroupUSemaphoreSocketSet_ValidSelectBits( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    SocketSelect_t xLocalSocketSet;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    xEndPoint.ipv4_settings.ulIPAddress = 0xC01234BD;

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = ( void * ) 1;
    xLocalSocket.pxSocketSet = &xLocalSocketSet;
    xLocalSocket.pxUserSemaphore = ( void * ) 1;

    /* Put in valid bits. */
    xLocalSocket.xSelectBits = eSELECT_READ;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdFALSE );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn( &xEndPoint, pdPASS );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when a matching socket is found and there is a handler listed but it returns a 0.
 *        Also, there is a user semaphore, socket set and event group and the select bits are valid.
 */
void test_xProcessReceivedUDPPacket_SocketFound_HandlerFoundReturnZero_ValidEventGroupUSemaphoreSocketSet_ValidSelectBits( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    SocketSelect_t xLocalSocketSet;
    struct xNetworkEndPoint xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    xEndPoint.ipv4_settings.ulIPAddress = 0xC01234BD;

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );
    ulFunctionCalled = 0;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    xLocalSocket.u.xUDP.pxHandleReceive = xLocalHandler;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = ( void * ) 1;
    xLocalSocket.pxSocketSet = &xLocalSocketSet;
    xLocalSocket.pxUserSemaphore = ( void * ) 1;
    xLocalSocket.xSelectBits = eSELECT_READ;

    xFunctionReturn = 0;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdFALSE );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn( &xEndPoint, pdPASS );

    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface = &xInterface;
    xLocalNetworkBuffer.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL( 1, ulFunctionCalled );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}

/*
 * @brief Test when a matching socket is found but the IP-address requires ARP
 * resolution.
 */
void test_xProcessReceivedUDPPacket_SocketFound_ARPResolutionRequired( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    SocketSelect_t xLocalSocketSet;
    struct xNetworkEndPoint xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0xC01234BD;

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );
    ulFunctionCalled = 0;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    xLocalSocket.u.xUDP.pxHandleReceive = xLocalHandler;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = ( void * ) 1;
    xLocalSocket.pxSocketSet = &xLocalSocketSet;
    xLocalSocket.pxUserSemaphore = ( void * ) 1;
    xLocalSocket.xSelectBits = eSELECT_READ;

    xFunctionReturn = 0;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdTRUE );

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL( 0, ulFunctionCalled );
    TEST_ASSERT_EQUAL( pdTRUE, xIsWaitingARPResolution );
}

/*
 * @brief Test when a matching socket is found and there is a handler listed
 *        which returns a non zero value.
 */
void test_xProcessReceivedUDPPacket_SocketFound_HandlerFoundReturnNonZero( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    SocketSelect_t xLocalSocketSet;
    struct xNetworkEndPoint xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0xC01234BD;

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );
    ulFunctionCalled = 0;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.xDataLength = ipconfigTCP_MSS;
    xLocalNetworkBuffer.pxEndPoint = &xEndPoint;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    xLocalSocket.u.xUDP.pxHandleReceive = xLocalHandler;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = ( void * ) 1;
    xLocalSocket.pxSocketSet = &xLocalSocketSet;
    xLocalSocket.pxUserSemaphore = ( void * ) 1;
    xLocalSocket.xSelectBits = eSELECT_READ;

    /* Return a non-zero value. */
    xFunctionReturn = 1;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdFALSE );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, &xEndPoint );

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL( 1, ulFunctionCalled );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}
