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
#include "mock_IP_DiffConfig_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_TCP_IP.h"
#include "mock_FreeRTOS_ICMP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_UDP_IP.h"

#include "FreeRTOS_IP.h"

/*#include "FreeRTOS_IP_stubs.c" */
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer );
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

extern BaseType_t xIPTaskInitialised;
extern BaseType_t xNetworkDownEventPending;
extern BaseType_t xNetworkUp;
extern UBaseType_t uxQueueMinimumSpace;

BaseType_t NetworkInterfaceOutputFunction_Stub_Called = 0;
BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    NetworkInterfaceOutputFunction_Stub_Called++;
    return 0;
}

static uint8_t ReleaseTCPPayloadBuffer[ 1500 ];
static BaseType_t ReleaseTCPPayloadBufferxByteCount = 100;
static size_t StubuxStreamBufferGetPtr_ReturnBadAddress( StreamBuffer_t * pxBuffer,
                                                         uint8_t ** ppucData,
                                                         int lCounter )
{
    *ppucData = &ReleaseTCPPayloadBuffer[ 150 ];

    return 0xFFFFFF;
}

static size_t StubuxStreamBufferGetPtr_ReturnIncorrectSize( StreamBuffer_t * pxBuffer,
                                                            uint8_t ** ppucData,
                                                            int lCounter )
{
    *ppucData = &ReleaseTCPPayloadBuffer[ 0 ];

    return( ReleaseTCPPayloadBufferxByteCount >> 1 );
}

static size_t StubuxStreamBufferGetPtr_ReturnCorrectVals( StreamBuffer_t * pxBuffer,
                                                          uint8_t ** ppucData,
                                                          int lCounter )
{
    *ppucData = &ReleaseTCPPayloadBuffer[ 0 ];

    return ReleaseTCPPayloadBufferxByteCount;
}

void test_prvAllowIPPacketIPv4_BufferLengthLess( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x46;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    for( uint32_t i = 0; i < sizeof( IPPacket_t ); i++ )
    {
        pxNetworkBuffer->xDataLength = i;
        eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

        TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    }
}

void test_prvAllowIPPacketIPv4_HeaderLengthLess( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( TCPPacket_t );
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45 - 2;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_HeaderLengthMore( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( TCPPacket_t );
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F + 2;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_HeaderLengthMoreThanTotalLength( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 );

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_IPPacketLengthMoreThanTotalLength( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );
    pxNetworkBuffer->xDataLength = FreeRTOS_ntohs( pxIPHeader->usLength ) - 1;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_UDP_IncorrectPacketLen( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER - 1;
    pxIPHeader->usLength = FreeRTOS_htons( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_TCP_IncorrectPacketLen( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_TCP_HEADER - 1;
    pxIPHeader->usLength = FreeRTOS_htons( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_ICMP_IncorrectPacketLen( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_ICMP;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMPv4_HEADER - 1;
    pxIPHeader->usLength = FreeRTOS_htons( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_IGMP_IncorrectPacketLen( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_IGMP;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMPv4_HEADER - 1;
    pxIPHeader->usLength = FreeRTOS_htons( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_NoProt( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = 0;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMPv4_HEADER - 1;
    pxIPHeader->usLength = FreeRTOS_htons( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_UDP_LengthLess( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxIPHeader->usLength = FreeRTOS_ntohs( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( pxProtPack->xUDPPacket.xUDPHeader ) - 1 );
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_UDP_LengthMore( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxIPHeader->usLength = FreeRTOS_ntohs( ipconfigNETWORK_MTU + 1 );
    pxNetworkBuffer->xDataLength = ipconfigNETWORK_MTU + 20;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}
