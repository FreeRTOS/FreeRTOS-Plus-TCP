/*
 * FreeRTOS+TCP V2.4.0
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

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
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

    /* Address not resolved. */
    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eCantSendPacket );

    /* Expect the buffer to be released in this case. */
    vReleaseNetworkBufferAndDescriptor_Expect( &xLocalNetworkBuffer );

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );

    /* Nothing to assert on since there was no modification. */
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

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    xLocalNetworkBuffer.ulIPAddress = ulIPAddr;

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t * ) pucLocalEthernetBuffer;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );
    eARPGetCacheEntry_ReturnMemThruPtr_pulIPAddress( &ulLocalIPAddress, sizeof( ulLocalIPAddress ) );

    vARPRefreshCacheEntry_Expect( NULL, ulLocalIPAddress );
    vARPGenerateRequestPacket_Expect( &xLocalNetworkBuffer );

    xNetworkInterfaceOutput_ExpectAndReturn( &xLocalNetworkBuffer, pdTRUE, pdTRUE );

    /* Make sure that the packet is smaller than minimum packet length. */
    xLocalNetworkBuffer.xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES - 2;

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );

    TEST_ASSERT_EQUAL( ulLocalIPAddress, xLocalNetworkBuffer.ulIPAddress );
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

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    xLocalNetworkBuffer.ulIPAddress = ulIPAddr;

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t * ) pucLocalEthernetBuffer;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );
    eARPGetCacheEntry_ReturnMemThruPtr_pulIPAddress( &ulLocalIPAddress, sizeof( ulLocalIPAddress ) );

    vARPRefreshCacheEntry_Expect( NULL, ulLocalIPAddress );
    vARPGenerateRequestPacket_Expect( &xLocalNetworkBuffer );

    xNetworkInterfaceOutput_ExpectAndReturn( &xLocalNetworkBuffer, pdTRUE, pdTRUE );

    xLocalNetworkBuffer.xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES + 2;

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );

    TEST_ASSERT_EQUAL( ulLocalIPAddress, xLocalNetworkBuffer.ulIPAddress );
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

    xLocalNetworkBuffer.ulIPAddress = ulIPAddr;
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

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    xLocalNetworkBuffer.ulIPAddress = ulIPAddr;
    /* Not ICMP data. */
    xLocalNetworkBuffer.usPort = ipPACKET_CONTAINS_ICMP_DATA + 1;
    xLocalNetworkBuffer.usBoundPort = 0x1023;
    xLocalNetworkBuffer.xDataLength = sizeof( UDPPacket_t );

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t * ) pucLocalEthernetBuffer;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    usGenerateChecksum_ExpectAndReturn( 0U, NULL, ipSIZE_OF_IPv4_HEADER, 0 );
    usGenerateChecksum_IgnoreArg_pucNextData();

    xNetworkInterfaceOutput_ExpectAndReturn( &xLocalNetworkBuffer, pdTRUE, pdTRUE );

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

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] = ucSocketOptions;

    xLocalNetworkBuffer.ulIPAddress = ulIPAddr;
    xLocalNetworkBuffer.usPort = ipPACKET_CONTAINS_ICMP_DATA;
    xLocalNetworkBuffer.usBoundPort = 0x1023;
    xLocalNetworkBuffer.xDataLength = sizeof( UDPPacket_t );

    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t * ) pucLocalEthernetBuffer;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    usGenerateChecksum_ExpectAndReturn( 0U, NULL, ipSIZE_OF_IPv4_HEADER, 0 );
    usGenerateChecksum_IgnoreArg_pucNextData();

    usGenerateProtocolChecksum_ExpectAndReturn( pucLocalEthernetBuffer, xLocalNetworkBuffer.xDataLength, pdTRUE, 0 );

    xNetworkInterfaceOutput_ExpectAndReturn( &xLocalNetworkBuffer, pdTRUE, pdTRUE );

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

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

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

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    /* Packet coming from a DNS port. */
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( ipDNS_PORT );

    /* No socket found. */
    pxUDPSocketLookup_ExpectAndReturn( usPort, NULL );

    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    ulDNSHandlePacket_ExpectAndReturn( &xLocalNetworkBuffer, pdPASS );

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

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    /* LLMNR port. */
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_ntohs( ipLLMNR_PORT );

    /* No socket found. */
    pxUDPSocketLookup_ExpectAndReturn( usPort, NULL );

    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    ulDNSHandlePacket_ExpectAndReturn( &xLocalNetworkBuffer, pdPASS );

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

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_ntohs( ipLLMNR_PORT );

    pxUDPSocketLookup_ExpectAndReturn( usPort, NULL );

    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    ulDNSHandlePacket_ExpectAndReturn( &xLocalNetworkBuffer, pdPASS );

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

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_ntohs( ipNBNS_PORT );

    pxUDPSocketLookup_ExpectAndReturn( usPort, NULL );

    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    ulNBNSHandlePacket_ExpectAndReturn( &xLocalNetworkBuffer, pdPASS );

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

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_ntohs( ipNBNS_PORT );

    pxUDPSocketLookup_ExpectAndReturn( usPort, NULL );

    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    ulNBNSHandlePacket_ExpectAndReturn( &xLocalNetworkBuffer, pdPASS );

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

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;

    /* No socket handler listed for UDP packets. */
    xLocalSocket.u.xUDP.pxHandleReceive = NULL;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdFALSE );
    vARPRefreshCacheEntryAge_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );

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

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;

    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = NULL;
    xLocalSocket.pxSocketSet = NULL;
    xLocalSocket.pxUserSemaphore = NULL;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdFALSE );
    vARPRefreshCacheEntryAge_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );

    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

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

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;

    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = ( void * ) 1;
    xLocalSocket.pxSocketSet = NULL;
    xLocalSocket.pxUserSemaphore = ( void * ) 1;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdFALSE );
    vARPRefreshCacheEntryAge_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );

    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn( pdPASS );

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

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;

    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = ( void * ) 1;
    xLocalSocket.pxSocketSet = ( void * ) 1;
    xLocalSocket.pxUserSemaphore = ( void * ) 1;

    pxUDPSocketLookup_ExpectAndReturn( usPort, &xLocalSocket );

    xCheckRequiresARPResolution_ExpectAnyArgsAndReturn( pdFALSE );
    vARPRefreshCacheEntryAge_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );

    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn( pdPASS );

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

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;

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
    vARPRefreshCacheEntryAge_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );

    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn( pdPASS );

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

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );
    ulFunctionCalled = 0;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;

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
    vARPRefreshCacheEntryAge_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );

    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn( pdPASS );

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

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );
    ulFunctionCalled = 0;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;

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

    /* Cleanup. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( &xLocalSocket, 0, sizeof( xLocalSocket ) );
    ulFunctionCalled = 0;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    pxUDPPacket = ( UDPPacket_t * ) xLocalNetworkBuffer.pucEthernetBuffer;

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
    vARPRefreshCacheEntryAge_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );

    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort, &xIsWaitingARPResolution );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL( 1, ulFunctionCalled );
    TEST_ASSERT_EQUAL( pdFALSE, xIsWaitingARPResolution );
}
