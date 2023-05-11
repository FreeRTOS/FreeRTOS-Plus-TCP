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
#include "FreeRTOSIPConfig.h"
#include "mock_IPv4_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_Routing.h"

#include "FreeRTOS_IPv4.h"

#include "catch_assert.h"


/* =========================== EXTERN VARIABLES =========================== */

const MACAddress_t xBroadcastMACAddress = { { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff } };

/* ============================ Unity Fixtures ============================ */

/*! called before each test case */
void setUp( void )
{
}

/*! called after each test case */
void tearDown( void )
{
}

/* ======================== Stub Callback Functions ========================= */

/* ============================== Test Cases ============================== */

void test_xIsIPv4Multicast_NotMultiCast( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0;

    xReturn = xIsIPv4Multicast( ulIPAddress );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_xIsIPv4Multicast_NotMultiCast2( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = FreeRTOS_htonl( 0xF0000000 );

    xReturn = xIsIPv4Multicast( ulIPAddress );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_xIsIPv4Multicast_IsMultiCast( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = FreeRTOS_htonl( 0xF0000000 - 1 );

    xReturn = xIsIPv4Multicast( ulIPAddress );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

void test_prvAllowIPPacketIPv4( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_FragmentedPacket( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->usFragmentOffset = ipFRAGMENT_OFFSET_BIT_MASK;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_FragmentedPacket1( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->usFragmentOffset = ipFRAGMENT_FLAGS_MORE_FRAGMENTS;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_IncorrectLength( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->ucVersionHeaderLength = 0xFF;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_NotMatchingIP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER + 1;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_IsNetworkUp_ExpectAndReturn( pdTRUE );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPMatch( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( &xEndpoint, 0, sizeof( xEndpoint ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    xEndpoint.ipv4_settings.ulIPAddress = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = xEndpoint.ipv4_settings.ulIPAddress;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndpoint );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPBrdCast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = 0xFFFFFFFF;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPBrdcast1( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    NetworkEndPoint_t xEndPoints;
    IPV4Parameters_t * xIPv4Addressing = &( xEndPoints.ipv4_settings );

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = xIPv4Addressing->ulBroadcastAddress;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_IsNetworkUp_ExpectAndReturn( pdFALSE );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPLLMNR( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = ipLLMNR_IP_ADDR;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SourceIPBrdCast_NoLocalIP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0x00;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER + 1;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_IsNetworkUp_ExpectAndReturn( pdFALSE );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_DestMACBrdCast_DestIPUnicast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0x00;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = 0x00;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_IsNetworkUp_ExpectAndReturn( pdTRUE );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SrcMACBrdCast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xSourceAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SrcMACBrdCast2( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xSourceAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SrcIPAddrIsMulticast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 1, sizeof( NetworkBufferDescriptor_t ) );
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxNetworkBuffer->pxEndPoint = NULL;

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = FreeRTOS_htonl( 0xE0000000 + 1 );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_IncorrectChecksum( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC - 1 );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_IncorrectProtocolChecksum( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAndReturn( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE, ( uint16_t ) ( ipCORRECT_CRC + 1 ) );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_HappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAndReturn( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

void test_prvCheckIP4HeaderOptions_HeaderLengthSmaller( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    /* Option length is 15 * 4 - 20 (IPv4 header) = 40 bytes */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS - sizeof( IPPacket_t ) );

    eResult = prvCheckIP4HeaderOptions( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
    TEST_ASSERT_EQUAL( ipconfigTCP_MSS - sizeof( IPPacket_t ) - 40, FreeRTOS_ntohs( pxIPHeader->usLength ) );
}
