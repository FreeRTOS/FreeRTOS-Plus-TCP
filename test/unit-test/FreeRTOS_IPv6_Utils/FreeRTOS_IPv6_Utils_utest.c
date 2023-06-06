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
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"

#include "FreeRTOS_IPv6_Utils.h"

#include "FreeRTOSIPConfig.h"

/* ===========================  EXTERN VARIABLES  =========================== */

#ifndef ipconfigTCPv6_MSS
    #define ipconfigTCPv6_MSS    ( ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_TCP_HEADER ) )
#endif

/* Setting IPv6 address as "fe80::7009" */
const IPv6_Address_t xDefaultIPAddress =
{
    0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x09
};

#define ipSIZE_OF_IPv6_PAYLOAD_LEN    20

#define ipICMP_INCORRECT_MSG_IPv6     0

/* Buffer length check of ICMPv6 packet failed. */
#define ipFAIL_INVALID_LENGTH         10
/* Non Zero failure for prvChecksumIPv6Checks  */
#define ipFAIL_LEN_CHECK              1
#define ipFAIL_PACKET_CHECK           2
#define ipPASS_IPv6Checks             0

/* =============================== Test Cases =============================== */

/**
 * @brief This function verify correctly setting
 *        a MAC address.
 */
void test_vSetMultiCastIPv6MacAddress( void )
{
    IPv6_Address_t xIPAddress;
    MACAddress_t xMACAddress;

    /* Setting IPv6 address as "fe80::7009" */
    memcpy( &xIPAddress, &xDefaultIPAddress, sizeof( IPv6_Address_t ) );
    vSetMultiCastIPv6MacAddress( &xIPAddress, &xMACAddress );

    TEST_ASSERT_EQUAL( ( uint8_t ) 0x33U, xMACAddress.ucBytes[ 0 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) 0x33U, xMACAddress.ucBytes[ 1 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 12 ], xMACAddress.ucBytes[ 2 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 13 ], xMACAddress.ucBytes[ 3 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 14 ], xMACAddress.ucBytes[ 4 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 15 ], xMACAddress.ucBytes[ 5 ] );
}

/**
 * @brief This function validate handling of buffer length
 *        less than the minimum packet size.
 */
void test_prvChecksumIPv6Checks_InvalidLength( void )
{
    BaseType_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCPv6_MSS ];
    /* Buffer length less than the IPv6 Header size */
    size_t uxBufferLength = sizeof( IPHeader_IPv6_t ) - 1;
    BaseType_t xOutgoingPacket;
    struct xPacketSummary xSet;

    memset( pucEthernetBuffer, 0, ipconfigTCPv6_MSS );
    xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) pucEthernetBuffer );

    usReturn = prvChecksumIPv6Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    /* Return value other than zero implies length check fail */
    TEST_ASSERT_EQUAL( ipFAIL_LEN_CHECK, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function validate handling case of
 *        incomplete IPv6 packet.
 */
void test_prvChecksumIPv6Checks_IncompleteIPv6Packet( void )
{
    BaseType_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCPv6_MSS ];
    IPHeader_IPv6_t * pxIPv6Packet;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;
    struct xPacketSummary xSet;

    memset( pucEthernetBuffer, 0, ipconfigTCPv6_MSS );

    pxIPv6Packet = ( IPHeader_IPv6_t * ) pucEthernetBuffer;
    pxIPv6Packet->usPayloadLength = ipSIZE_OF_IPv6_PAYLOAD_LEN;
    xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) pucEthernetBuffer );

    usReturn = prvChecksumIPv6Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipFAIL_PACKET_CHECK, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function validate all length checks passing
 *        successfully.
 */
void test_prvChecksumIPv6Checks_Success( void )
{
    BaseType_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCPv6_MSS ];
    IPHeader_IPv6_t * pxIPv6Packet;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 1;
    struct xPacketSummary xSet;

    memset( pucEthernetBuffer, 0, ipconfigTCPv6_MSS );

    pxIPv6Packet = ( IPHeader_IPv6_t * ) pucEthernetBuffer;
    xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) pucEthernetBuffer );

    usReturn = prvChecksumIPv6Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipPASS_IPv6Checks, usReturn );
}

/**
 * @brief This function verify sending an invalid length.
 */
void test_prvChecksumICMPv6Checks_Default_InvalidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_ICMPv6_HEADER - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_INCORRECT_MSG_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipFAIL_INVALID_LENGTH, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function verify sending an valid length.
 */
void test_prvChecksumICMPv6Checks_Default_ValidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_ICMPv6_HEADER + 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = 0;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipPASS_IPv6Checks, usReturn );
    TEST_ASSERT_EQUAL( ipSIZE_OF_ICMPv6_HEADER, xSet.uxProtocolHeaderLength );
}

/**
 * @brief This function verify sending an invalid length
 *        for ipICMP_PING_REQUEST_IPv6.
 */
void test_prvChecksumICMPv6Checks_PingReq_InvalidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipFAIL_INVALID_LENGTH, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function verify sending an valid length
 *        for ipICMP_PING_REQUEST_IPv6.
 */
void test_prvChecksumICMPv6Checks_PingReq_ValidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) + 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipPASS_IPv6Checks, usReturn );
    TEST_ASSERT_EQUAL( sizeof( ICMPEcho_IPv6_t ), xSet.uxProtocolHeaderLength );
}

/**
 * @brief This function verify sending an invalid length
 *        for ipICMP_PING_REPLY_IPv6.
 */
void test_prvChecksumICMPv6Checks_PingReply_InvalidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipFAIL_INVALID_LENGTH, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function verify sending an valid length
 *        for ipICMP_PING_REPLY_IPv6.
 */
void test_prvChecksumICMPv6Checks_PingReply_ValidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) + 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipPASS_IPv6Checks, usReturn );
    TEST_ASSERT_EQUAL( sizeof( ICMPEcho_IPv6_t ), xSet.uxProtocolHeaderLength );
}

/**
 * @brief This function verify sending an invalid length
 *        for ipICMP_ROUTER_SOLICITATION_IPv6.
 */
void test_prvChecksumICMPv6Checks_RS_InvalidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_SOLICITATION_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipFAIL_INVALID_LENGTH, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function verify sending an valid length
 *        for ipICMP_ROUTER_SOLICITATION_IPv6.
 */
void test_prvChecksumICMPv6Checks_RS_ValidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) + 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_SOLICITATION_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipPASS_IPv6Checks, usReturn );
    TEST_ASSERT_EQUAL( sizeof( ICMPRouterSolicitation_IPv6_t ), xSet.uxProtocolHeaderLength );
}
