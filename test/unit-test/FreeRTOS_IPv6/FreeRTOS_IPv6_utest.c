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

#include "FreeRTOS_IPv6_stubs.c"

/* ===========================  EXTERN VARIABLES  =========================== */

extern const struct xIPv6_Address xIPv6UnspecifiedAddress;
extern const struct xIPv6_Address FreeRTOS_in6addr_loopback;

/* First IPv6 address is 2001:1234:5678::5 */
const IPv6_Address_t xIPAddressFive = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05 };

/* Second IPv6 address is 2001:1234:5678::10 */
const IPv6_Address_t xIPAddressTen = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10 };

/* MAC Address for endpoint. */
const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
}

/*! called after each test case */
void tearDown( void )
{
}

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
    static uint8_t pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );

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

static NetworkBufferDescriptor_t * prvInitializeNetworkDescriptorWithExtensionHeader()
{
    static NetworkBufferDescriptor_t xNetworkBuffer;
    static uint8_t pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );

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
    TCPPacket_IPv6_t * pxTCPPacket = pxNetworkBuffer->pucEthernetBuffer;

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
    TCPPacket_IPv6_t * pxTCPPacket = pxNetworkBuffer->pucEthernetBuffer;
    /* Multicast IPv6 address is FF02::1 */
    IPv6_Address_t xMCIPAddress = {0xFF, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01};
    
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xMCIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL(eProcessBuffer, eResult);
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
    TCPPacket_IPv6_t * pxTCPPacket = pxNetworkBuffer->pucEthernetBuffer;

    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, FreeRTOS_in6addr_loopback.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, pxNetworkBuffer->pxEndPoint );
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
    TCPPacket_IPv6_t * pxTCPPacket = pxNetworkBuffer->pucEthernetBuffer;

    pxNetworkBuffer->pxEndPoint = NULL;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, NULL );
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
    TCPPacket_IPv6_t * pxTCPPacket = pxNetworkBuffer->pucEthernetBuffer;

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
    TCPPacket_IPv6_t * pxTCPPacket = pxNetworkBuffer->pucEthernetBuffer;

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
    TCPPacket_IPv6_t * pxTCPPacket = pxNetworkBuffer->pucEthernetBuffer;

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
    TCPPacket_IPv6_t * pxTCPPacket = pxNetworkBuffer->pucEthernetBuffer;
    NetworkEndPoint_t xEndpoint;
    /* Different IPv6 address is 2001:1234:5678::FFFF */
    IPv6_Address_t xDiffIPAddress = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF };

    memset( &xEndpoint, 0, sizeof( xEndpoint ) );
    xEndpoint.bits.bIPv6 = 1U;
    memcpy( xEndpoint.ipv6_settings.xIPAddress.ucBytes, xDiffIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    pxNetworkBuffer->pxEndPoint = &xEndpoint;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, NULL );
    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 1 );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_eHandleIPv6ExtensionHeaders_happy_path
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
// void test_eHandleIPv6ExtensionHeaders_happy_path()
// {
//     eFrameProcessingResult_t eResult;
//     NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
//     TCPPacket_IPv6_t * pxTCPPacket = pxNetworkBuffer->pucEthernetBuffer;
//     NetworkEndPoint_t xEndpoint;
//     /* Different IPv6 address is 2001:1234:5678::FFFF */
//     IPv6_Address_t xDiffIPAddress = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF };

//     memset( &xEndpoint, 0, sizeof( xEndpoint ) );
//     xEndpoint.bits.bIPv6 = 1U;
//     memcpy( xEndpoint.ipv6_settings.xIPAddress.ucBytes, xDiffIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
//     pxNetworkBuffer->pxEndPoint = &xEndpoint;

//     FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, NULL );
//     FreeRTOS_IsNetworkUp_IgnoreAndReturn( 1 );

//     eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
//     TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
// }

/*
 * eFrameProcessingResult_t eHandleIPv6ExtensionHeaders( NetworkBufferDescriptor_t * const pxNetworkBuffer,
 *                                                    BaseType_t xDoRemove )
 * BaseType_t xIsIPv6AllowedMulticast( const IPv6_Address_t * pxIPAddress )
 * BaseType_t xCompareIPv6_Address( const IPv6_Address_t * pxLeft,
 *                               const IPv6_Address_t * pxRight,
 *                               size_t uxPrefixLength )
 * BaseType_t xGetExtensionOrder( uint8_t ucProtocol,
 *                             uint8_t ucNextHeader )
 */
