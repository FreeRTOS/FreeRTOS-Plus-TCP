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

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IPv6.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* ===========================  EXTERN VARIABLES  =========================== */

/* The basic length for one IPv6 extension headers. */
#define TEST_IPv6_EXTESION_HEADER_LENGTH    ( 8U )

extern const struct xIPv6_Address xIPv6UnspecifiedAddress;
extern const struct xIPv6_Address FreeRTOS_in6addr_loopback;

/* First IPv6 address is 2001:1234:5678::5 */
const IPv6_Address_t xIPAddressFive = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05 };

/* Second IPv6 address is 2001:1234:5678::10 */
const IPv6_Address_t xIPAddressTen = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10 };

/* MAC Address for endpoint. */
const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };

/* ======================== Stub Callback Functions ========================= */

static NetworkEndPoint_t * prvInitializeEndpoint()
{
    static NetworkEndPoint_t xEndpoint;

    memset( &xEndpoint, 0, sizeof( xEndpoint ) );
    xEndpoint.bits.bIPv6 = 1U;
    memcpy( xEndpoint.ipv6_settings.xIPAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    return &xEndpoint;
}

static NetworkBufferDescriptor_t * prvInitializeNetworkDescriptor()
{
    static NetworkBufferDescriptor_t xNetworkBuffer;
    static uint8_t pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) ];
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pcNetworkBuffer;

    /* Initialize network buffer descriptor. */
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    xNetworkBuffer.pxEndPoint = prvInitializeEndpoint();
    xNetworkBuffer.pucEthernetBuffer = ( uint8_t * ) pxTCPPacket;
    xNetworkBuffer.xDataLength = sizeof( TCPPacket_IPv6_t );

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucMACAddress, sizeof( ucMACAddress ) );
    memcpy( pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes, ucMACAddress, sizeof( ucMACAddress ) );
    pxTCPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xIPAddressTen.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, sizeof( IPv6_Address_t ) );

    return &xNetworkBuffer;
}

/*
 * Prepare a packet have extension with following order. Check if eHandleIPv6ExtensionHeaders determines to process it.
 *  - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *  - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *  - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *  - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *  - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *  - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *  - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 */
static NetworkBufferDescriptor_t * prvInitializeNetworkDescriptorWithExtensionHeader( uint8_t ucProtocol )
{
    static NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t ucExtensionHeadersLength = ( 7U * TEST_IPv6_EXTESION_HEADER_LENGTH );
    /* Ethernet header + IPv6 header + Maximum protocol header + IPv6 Extension Headers + 1 payload */
    static uint8_t pcNetworkBuffer[ sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) + ucExtensionHeadersLength + sizeof( ICMPHeader_IPv6_t ) + 1U ];
    EthernetHeader_t * pxEthHeader = ( EthernetHeader_t * ) pcNetworkBuffer;
    IPHeader_IPv6_t * pxIPv6Header = ( IPHeader_IPv6_t * ) &( pcNetworkBuffer[ sizeof( EthernetHeader_t ) ] );
    uint8_t * pxIPv6ExtHeader = ( uint8_t * ) &( pcNetworkBuffer[ sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) ] );
    size_t uxIndex = sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t );
    uint8_t ucProtocolHeaderSize;

    if( ucProtocol == ipPROTOCOL_TCP )
    {
        ucProtocolHeaderSize = sizeof( TCPHeader_t );
    }
    else if( ucProtocol == ipPROTOCOL_UDP )
    {
        ucProtocolHeaderSize = sizeof( UDPHeader_t );
    }
    else if( ucProtocol == ipPROTOCOL_ICMP_IPv6 )
    {
        ucProtocolHeaderSize = sizeof( ICMPHeader_IPv6_t );
    }
    else
    {
        TEST_ASSERT_TRUE( false );
    }

    /* Initialize network buffer descriptor. */
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    xNetworkBuffer.pxEndPoint = prvInitializeEndpoint();
    xNetworkBuffer.pucEthernetBuffer = ( uint8_t * ) pcNetworkBuffer;
    xNetworkBuffer.xDataLength = sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) + ucExtensionHeadersLength + ucProtocolHeaderSize + 1U;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxEthHeader->xDestinationAddress.ucBytes, ucMACAddress, sizeof( ucMACAddress ) );
    memcpy( pxEthHeader->xSourceAddress.ucBytes, ucMACAddress, sizeof( ucMACAddress ) );
    pxEthHeader->usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxIPv6Header->xSourceAddress.ucBytes, xIPAddressTen.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( pxIPv6Header->xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, sizeof( IPv6_Address_t ) );
    pxIPv6Header->usPayloadLength = FreeRTOS_htons( ucExtensionHeadersLength + ucProtocolHeaderSize + 1U ); /* Extension header length + protocol header + payload */
    pxIPv6Header->ucNextHeader = ipIPv6_EXT_HEADER_HOP_BY_HOP;
    /* Append extension headers */
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_ROUTING_HEADER;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_FRAGMENT_HEADER;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_SECURE_PAYLOAD;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_AUTHEN_HEADER;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_DESTINATION_OPTIONS;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_MOBILITY_HEADER;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ucProtocol;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;

    return &xNetworkBuffer;
}

/* ============================== Test Cases ============================== */

/**
 * @brief test_prvAllowIPPacketIPv6_source_unspecified_address
 * Prepare a packet with unspecified address in source address.
 * Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_source_unspecified_address()
{
    IPHeader_IPv6_t xIPv6Address;
    eFrameProcessingResult_t eResult;

    memset( &xIPv6Address, 0, sizeof( xIPv6Address ) );
    memcpy( xIPv6Address.xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( xIPv6Address.xSourceAddress.ucBytes, xIPv6UnspecifiedAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    eResult = prvAllowIPPacketIPv6( &xIPv6Address, NULL, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_destination_unspecified_address
 * Prepare a packet with unspecified address in destination address.
 * Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_destination_unspecified_address()
{
    IPHeader_IPv6_t xIPv6Address;
    eFrameProcessingResult_t eResult;

    memset( &xIPv6Address, 0, sizeof( xIPv6Address ) );
    memcpy( xIPv6Address.xDestinationAddress.ucBytes, xIPv6UnspecifiedAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( xIPv6Address.xSourceAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    eResult = prvAllowIPPacketIPv6( &xIPv6Address, NULL, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_happy_path
 * Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::5. And it's not a loopback packet.
 * Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_happy_path()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_multicast_address
 * Prepare a packet from 2001:1234:5678::5 -> FF02::1. Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_multicast_address()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    /* Multicast IPv6 address is FF02::1 */
    IPv6_Address_t xMCIPAddress = { 0xFF, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xMCIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_loopback_address
 * Prepare a packet from 2001:1234:5678::5 -> ::1.
 * Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_loopback_address()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, FreeRTOS_in6addr_loopback.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, pxNetworkBuffer->pxEndPoint );
    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_loopback_not_match_dest
 * Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::11.
 * Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_loopback_not_match_dest()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes[ 15 ] = 0x11;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, pxNetworkBuffer->pxEndPoint );
    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 0 );
    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_loopback_not_match_src
 * Prepare a packet from 2001:1234:5678::10 -> ::1.
 * Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_loopback_not_match_src()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, FreeRTOS_in6addr_loopback.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, pxNetworkBuffer->pxEndPoint );
    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 0 );
    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_network_down
 * Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::FFFF when network is down.
 * Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_network_down()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxNetworkBuffer->pxEndPoint = NULL;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, NULL );
    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 0 );
    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_happy_path
 * Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::5. And the source MAC address in packet is same as endpoint.
 * Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_self_send()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, pxNetworkBuffer->pxEndPoint );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_checksum_error
 * Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::5. But the checksum is wrong.
 * Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_checksum_error()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipWRONG_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_invalid_packet
 * Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::5. But there is no rule to process this packet.
 * Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_invalid_packet()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxNetworkBuffer->pxEndPoint = NULL;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, NULL );
    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 1 );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_endpoint_different_address
 * Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::5. But the address in endpoint in network descriptor is different from packet.
 * Check if prvAllowIPPacketIPv6 determines to lease it.
 */
void test_prvAllowIPPacketIPv6_endpoint_different_address()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    NetworkEndPoint_t xEndpoint;
    /* Different IPv6 address is 2001:1234:5678::FFFF */
    IPv6_Address_t xDiffIPAddress = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF };

    memset( &xEndpoint, 0, sizeof( xEndpoint ) );
    xEndpoint.bits.bIPv6 = 1U;
    memcpy( xEndpoint.ipv6_settings.xIPAddress.ucBytes, xDiffIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    pxNetworkBuffer->pxEndPoint = &xEndpoint;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &( pxTCPPacket->xIPHeader.xSourceAddress ), NULL );
    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 1 );

    eResult = prvAllowIPPacketIPv6( &( pxTCPPacket->xIPHeader ), pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_eHandleIPv6ExtensionHeaders_TCP_happy_path
 * Prepare a packet have extension with following order. Check if eHandleIPv6ExtensionHeaders determines to process it.
 *  - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *  - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *  - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *  - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *  - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *  - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *  - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *  - ipPROTOCOL_TCP
 *     - 1 byte payload
 */
void test_eHandleIPv6ExtensionHeaders_TCP_happy_path()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );
    uint8_t ucExtensionHeadersLength = ( 7U * TEST_IPv6_EXTESION_HEADER_LENGTH );
    TCPHeader_t * pxProtocolHeader = ( TCPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ucExtensionHeadersLength ] );
    uint8_t * pxPayload;

    pxPayload = ( uint8_t * ) ( pxProtocolHeader + 1 );
    *pxPayload = 'a';

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
    TEST_ASSERT_EQUAL( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( TCPHeader_t ) + 1U, pxNetworkBuffer->xDataLength );
}

/**
 * @brief test_eHandleIPv6ExtensionHeaders_UDP_happy_path
 * Prepare a packet have extension with following order. Check if eHandleIPv6ExtensionHeaders determines to process it.
 *  - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *  - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *  - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *  - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *  - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *  - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *  - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *  - ipPROTOCOL_UDP
 *     - 1 byte payload
 */
void test_eHandleIPv6ExtensionHeaders_UDP_happy_path()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_UDP );
    uint8_t ucExtensionHeadersLength = ( 7U * TEST_IPv6_EXTESION_HEADER_LENGTH );
    UDPHeader_t * pxProtocolHeader = ( UDPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ucExtensionHeadersLength ] );
    uint8_t * pxPayload;

    pxPayload = ( uint8_t * ) ( pxProtocolHeader + 1 );
    *pxPayload = 'a';

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
    TEST_ASSERT_EQUAL( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( UDPHeader_t ) + 1U, pxNetworkBuffer->xDataLength );
}

/**
 * @brief test_eHandleIPv6ExtensionHeaders_ICMPv6_happy_path
 * Prepare a packet have extension with following order. Check if eHandleIPv6ExtensionHeaders determines to process it.
 *  - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *  - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *  - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *  - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *  - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *  - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *  - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *  - ipPROTOCOL_ICMP_IPv6
 *     - 1 byte payload
 */
void test_eHandleIPv6ExtensionHeaders_ICMPv6_happy_path()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_ICMP_IPv6 );
    uint8_t ucExtensionHeadersLength = ( 7U * TEST_IPv6_EXTESION_HEADER_LENGTH );
    ICMPHeader_IPv6_t * pxProtocolHeader = ( ICMPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ucExtensionHeadersLength ] );
    uint8_t * pxPayload;

    pxPayload = ( uint8_t * ) ( pxProtocolHeader + 1 );
    *pxPayload = 'a';

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
    TEST_ASSERT_EQUAL( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t ) + 1U, pxNetworkBuffer->xDataLength );
}

/**
 * @brief test_eHandleIPv6ExtensionHeaders_TCP_happy_path_not_remove
 * Prepare a packet have extension with following order. Check if eHandleIPv6ExtensionHeaders determines to release it due to not support.
 * And the extension headers still exist.
 *  - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *  - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *  - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *  - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *  - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *  - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *  - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *  - ipPROTOCOL_TCP
 *     - 1 byte payload
 */
void test_eHandleIPv6ExtensionHeaders_TCP_happy_path_not_remove()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );
    uint8_t ucExtensionHeadersLength = ( 7U * TEST_IPv6_EXTESION_HEADER_LENGTH );
    TCPHeader_t * pxProtocolHeader = ( TCPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ucExtensionHeadersLength ] );
    uint8_t * pxPayload;

    pxPayload = ( uint8_t * ) ( pxProtocolHeader + 1 );
    *pxPayload = 'a';

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdFALSE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    TEST_ASSERT_EQUAL( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ucExtensionHeadersLength + sizeof( TCPHeader_t ) + 1U, pxNetworkBuffer->xDataLength );
}

/**
 * @brief test_eHandleIPv6ExtensionHeaders_hop_by_hop_in_wrong_order
 * Prepare a packet have extension with following order. Check if eHandleIPv6ExtensionHeaders determines to release it.
 *  - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *  - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *  - ipPROTOCOL_TCP
 */
void test_eHandleIPv6ExtensionHeaders_hop_by_hop_in_wrong_order()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );
    IPHeader_IPv6_t * pxIPv6Header = ( IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    size_t uxIndex = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;

    /* Modify the extension header */
    pxIPv6Header->ucNextHeader = ipIPv6_EXT_HEADER_ROUTING_HEADER;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_HOP_BY_HOP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipPROTOCOL_TCP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_eHandleIPv6ExtensionHeaders_short_buffer_length
 * Prepare a packet with 0 buffer length. Check if eHandleIPv6ExtensionHeaders determines to release it.
 */
void test_eHandleIPv6ExtensionHeaders_short_buffer_length()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();

    pxNetworkBuffer->xDataLength = 0;

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_eHandleIPv6ExtensionHeaders_small_IP_payload_length
 * Prepare a packet with small IP payload length. Check if eHandleIPv6ExtensionHeaders determines to release it.
 */
void test_eHandleIPv6ExtensionHeaders_small_IP_payload_length()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );
    IPPacket_IPv6_t * pxIPPacket_IPv6 = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxIPPacket_IPv6->xIPHeader.usPayloadLength = FreeRTOS_htons( 20 ); /* Need to remove 56 bytes extension header but only 20 bytes length set in IP header. */

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_eHandleIPv6ExtensionHeaders_large_extension_header
 * Prepare a packet with large extension header length. Check if eHandleIPv6ExtensionHeaders determines to release it.
 */
void test_eHandleIPv6ExtensionHeaders_large_extension_header()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );
    IPHeader_IPv6_t * pxIPv6Header = ( IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    size_t uxIndex = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;

    /* Modify the extension header */
    pxIPv6Header->ucNextHeader = ipIPv6_EXT_HEADER_HOP_BY_HOP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_ROUTING_HEADER;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 200U; /* Extension header length is set to 200*8 + 8, which is larger than buffer size. */
    uxIndex += 8;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipPROTOCOL_TCP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_eHandleIPv6ExtensionHeaders_unknown_extension_header
 * Prepare a packet with unknown extension header. Check if eHandleIPv6ExtensionHeaders can skip it and process it.
 */
void test_eHandleIPv6ExtensionHeaders_unknown_extension_header()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );
    IPHeader_IPv6_t * pxIPv6Header = ( IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );

    /* Modify the extension header to 0x7F (unknown) */
    pxIPv6Header->ucNextHeader = 0x7F;

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_eHandleIPv6ExtensionHeaders_dest_then_routing
 * Prepare a packet with specific extension header order - destination -> routing.
 * Check if eHandleIPv6ExtensionHeaders determines to process it.
 */
void test_eHandleIPv6ExtensionHeaders_dest_then_routing()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );
    IPHeader_IPv6_t * pxIPv6Header = ( IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    size_t uxIndex = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;

    pxIPv6Header->ucNextHeader = ipIPv6_EXT_HEADER_DESTINATION_OPTIONS;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_ROUTING_HEADER;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 0U;

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_xIsIPv6AllowedMulticast_zero_scope
 * Prepare a IPv6 addresses FF00:: ~ FFF0::. Check if xIsIPv6AllowedMulticast returns pdFALSE.
 */
void test_xIsIPv6AllowedMulticast_zero_scope()
{
    IPv6_Address_t xMulticastZeroGroupID = { 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
    BaseType_t xReturn;
    uint16_t ucScope;

    for( ucScope = 0x0; ucScope <= 0xF0; ucScope += 0x10 )
    {
        xMulticastZeroGroupID.ucBytes[ 1 ] = ( uint8_t ) ucScope;
        xReturn = xIsIPv6AllowedMulticast( &xMulticastZeroGroupID );
        TEST_ASSERT_EQUAL( pdFALSE, xReturn );
    }
}

/**
 * @brief test_xIsIPv6AllowedMulticast_reserved_address
 * Prepare IPv6 addresses FF00:: ~ FF0F::. Check if xIsIPv6AllowedMulticast returns pdTRUE.
 */
void test_xIsIPv6AllowedMulticast_reserved_address()
{
    IPv6_Address_t xMulticastZeroFlag = { 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
    BaseType_t xReturn;
    uint8_t ucFlag;

    for( ucFlag = 0x0; ucFlag <= 0xF; ucFlag++ )
    {
        xMulticastZeroFlag.ucBytes[ 1 ] = ucFlag;
        xReturn = xIsIPv6AllowedMulticast( &xMulticastZeroFlag );
        TEST_ASSERT_EQUAL( pdFALSE, xReturn );
    }
}

/**
 * @brief test_xIsIPv6AllowedMulticast_valid_address
 * Prepare IPv6 address FF11::1. Check if xIsIPv6AllowedMulticast returns pdTRUE.
 */
void test_xIsIPv6AllowedMulticast_valid_address()
{
    IPv6_Address_t xMulticastZeroFlag = { 0xFF, 0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    BaseType_t xReturn;

    xReturn = xIsIPv6AllowedMulticast( &xMulticastZeroFlag );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_LLMNR
 * Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 *  - Left:  2001::00AB:CDEF
 *  - Right: FF02::FFAB:CDEF
 */
void test_xCompareIPv6_Address_LLMNR()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xab, 0xcd, 0xef };
    IPv6_Address_t xRightAddress = { 0xFF, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xab, 0xcd, 0xef };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 16 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_all_nodes
 * Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 *  - Left:  2001::00AB:CDEF
 *  - Right: FF02::1
 */
void test_xCompareIPv6_Address_all_nodes()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xab, 0xcd, 0xef };
    IPv6_Address_t xRightAddress = { 0xFF, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 16 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_both_local_addresses
 * Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 *  - Left:  FE80::1
 *  - Right: FE80::2
 */
void test_xCompareIPv6_Address_both_local_addresses()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    IPv6_Address_t xRightAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 16 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_coverage_local_address_left_FF80
 * Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 *  - Left:  FF80::1
 *  - Right: FE80::2
 */
void test_xCompareIPv6_Address_coverage_local_address_left_FF80()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0xFF, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    IPv6_Address_t xRightAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 128 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_coverage_local_address_left_FE81
 * Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 *  - Left:  FE81::1
 *  - Right: FE80::2
 */
void test_xCompareIPv6_Address_coverage_local_address_left_FE81()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0xFE, 0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    IPv6_Address_t xRightAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 128 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_coverage_local_address_right_FF80
 * Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 *  - Left:  FE80::1
 *  - Right: FF80::2
 */
void test_xCompareIPv6_Address_coverage_local_address_right_FF80()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    IPv6_Address_t xRightAddress = { 0xFF, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 128 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_coverage_local_address_right_FE81
 * Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 *  - Left:  FE80::1
 *  - Right: FE81::2
 */
void test_xCompareIPv6_Address_coverage_local_address_right_FE81()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    IPv6_Address_t xRightAddress = { 0xFE, 0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 128 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_zero_prefix_length
 * Prepare IPv6 address below. With prefix length 0, xCompareIPv6_Address should take all IP address as same region.
 *  - Left:  2001:1234:5678::5
 *  - Right: 2001:1234:5678::10
 */
void test_xCompareIPv6_Address_zero_prefix_length()
{
    BaseType_t xReturn;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xIPAddressTen, 0 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_same_address_prefix_128
 * Prepare IPv6 address below. With prefix length 128, xCompareIPv6_Address should compare whole IP address.
 *  - Left:  2001:1234:5678::5
 *  - Right: 2001:1234:5678::5
 */
void test_xCompareIPv6_Address_same_address_prefix_128()
{
    BaseType_t xReturn;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xIPAddressFive, 128 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_same_region_prefix_64
 * Prepare IPv6 address below. With prefix length 64, xCompareIPv6_Address should compare first 64 bit of IP address.
 *  - Left:  2001:1234:5678::5
 *  - Right: 2001:1234:5678::10
 */
void test_xCompareIPv6_Address_same_region_prefix_64()
{
    BaseType_t xReturn;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xIPAddressTen, 64 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_different_region_prefix_64
 * Prepare IPv6 address below. With prefix length 64, xCompareIPv6_Address should compare first 64 bit of IP address.
 *  - Left:  2001:1234:5678::5
 *  - Right: FF01::10
 */
void test_xCompareIPv6_Address_different_region_prefix_64()
{
    BaseType_t xReturn;
    IPv6_Address_t xRightAddress = { 0xFF, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10 };

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xRightAddress, 64 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_different_region_prefix_4
 * Prepare IPv6 address below. With prefix length 4, xCompareIPv6_Address should compare first 4 bit of IP address.
 *  - Left:  2001:1234:5678::5
 *  - Right: 4001:1234:5678::5
 */
void test_xCompareIPv6_Address_different_region_prefix_4()
{
    BaseType_t xReturn;
    IPv6_Address_t xRightAddress;

    memcpy( xRightAddress.ucBytes, &xIPAddressFive, ipSIZE_OF_IPv6_ADDRESS );
    xRightAddress.ucBytes[ 0 ] = 0x40;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xRightAddress, 4 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_different_region_prefix_44
 * Prepare IPv6 address below. With prefix length 44, xCompareIPv6_Address should compare first 44 bit of IP address.
 *  - Left:  2001:1234:5678::5
 *  - Right: 2001:1234:5688::5
 */
void test_xCompareIPv6_Address_different_region_prefix_44()
{
    BaseType_t xReturn;
    IPv6_Address_t xRightAddress;

    memcpy( xRightAddress.ucBytes, &xIPAddressFive, ipSIZE_OF_IPv6_ADDRESS );
    xRightAddress.ucBytes[ 5 ] = 0x88;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xRightAddress, 44 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief test_xCompareIPv6_Address_same_region_prefix_44
 * Prepare IPv6 address below. With prefix length 44, xCompareIPv6_Address should compare first 44 bit of IP address.
 *  - Left:  2001:1234:5678::5
 *  - Right: 2001:1234:5678::10
 */
void test_xCompareIPv6_Address_same_region_prefix_44()
{
    BaseType_t xReturn;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xIPAddressTen, 44 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}
