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

#include "FreeRTOS_IPv6_Utils_stubs.c"

#include "FreeRTOSIPConfig.h"

#ifndef ipconfigTCPv6_MSS
    #define ipconfigTCPv6_MSS    ( ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_TCP_HEADER ) )
#endif

/** @brief When ucASCIIToHex() can not convert a character,
 *         the value 255 will be returned.
 */
#define socketINVALID_HEX_CHAR    ( 0xffU )

uint8_t ucASCIIToHex( char cChar )
{
    char cValue = cChar;
    uint8_t ucNew;

    if( ( cValue >= '0' ) && ( cValue <= '9' ) )
    {
        cValue -= ( char ) '0';
        /* The value will be between 0 and 9. */
        ucNew = ( uint8_t ) cValue;
    }
    else if( ( cValue >= 'a' ) && ( cValue <= 'f' ) )
    {
        cValue -= ( char ) 'a';
        ucNew = ( uint8_t ) cValue;
        /* The value will be between 10 and 15. */
        ucNew += ( uint8_t ) 10;
    }
    else if( ( cValue >= 'A' ) && ( cValue <= 'F' ) )
    {
        cValue -= ( char ) 'A';
        ucNew = ( uint8_t ) cValue;
        /* The value will be between 10 and 15. */
        ucNew += ( uint8_t ) 10;
    }
    else
    {
        /* The character does not represent a valid hex number, return 255. */
        ucNew = ( uint8_t ) socketINVALID_HEX_CHAR;
    }

    return ucNew;
}

void test_vSetMultiCastIPv6MacAddress( void )
{
    IPv6_Address_t xIPAddress;
    MACAddress_t xMACAddress;

    FreeRTOS_inet_pton6( "fe80::7009", &xIPAddress );
    vSetMultiCastIPv6MacAddress( &xIPAddress, &xMACAddress );

    TEST_ASSERT_EQUAL( ( uint8_t ) 0x33U, xMACAddress.ucBytes[ 0 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) 0x33U, xMACAddress.ucBytes[ 1 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 12 ], xMACAddress.ucBytes[ 2 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 13 ], xMACAddress.ucBytes[ 3 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 14 ], xMACAddress.ucBytes[ 4 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 15 ], xMACAddress.ucBytes[ 5 ] );
}

void test_prvChecksumIPv6Checks_InvalidLength( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCPv6_MSS ];
    size_t uxBufferLength = sizeof( IPHeader_IPv6_t ) - 1;
    BaseType_t xOutgoingPacket;
    struct xPacketSummary xSet;

    memset( pucEthernetBuffer, 0, ipconfigTCPv6_MSS );
    xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) pucEthernetBuffer );

    usReturn = prvChecksumIPv6Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( usReturn, 1 );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

void test_prvChecksumIPv6Checks_IncompleteIPv6Packet( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCPv6_MSS ];
    IPHeader_IPv6_t * pxIPv6Packet;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;
    struct xPacketSummary xSet;

    memset( pucEthernetBuffer, 0, ipconfigTCPv6_MSS );

    pxIPv6Packet = ( IPHeader_IPv6_t * ) pucEthernetBuffer;
    pxIPv6Packet->usPayloadLength = 20;
    xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) pucEthernetBuffer );

    usReturn = prvChecksumIPv6Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( usReturn, 2 );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

void test_prvChecksumIPv6Checks_Success( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCPv6_MSS ];
    IPHeader_IPv6_t * pxIPv6Packet;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 1;
    struct xPacketSummary xSet;

    memset( pucEthernetBuffer, 0, ipconfigTCPv6_MSS );

    pxIPv6Packet = ( IPHeader_IPv6_t * ) pucEthernetBuffer;
    xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) pucEthernetBuffer );

    usReturn = prvChecksumIPv6Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( usReturn, 0 );
}

void test_prvChecksumICMPv6Checks_Default_InvalidLength( void )
{
    uint16_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_ICMPv6_HEADER - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = 0;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( usReturn, 10 );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

void test_prvChecksumICMPv6Checks_Default_ValidLength( void )
{
    uint16_t usReturn;
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

    TEST_ASSERT_EQUAL( usReturn, 0 );
    TEST_ASSERT_EQUAL( ipSIZE_OF_ICMPv6_HEADER, xSet.uxProtocolHeaderLength );
}

void test_prvChecksumICMPv6Checks_PingReq_InvalidLength( void )
{
    uint16_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( usReturn, 10 );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

void test_prvChecksumICMPv6Checks_PingReq_ValidLength( void )
{
    uint16_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) + 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( usReturn, 0 );
    TEST_ASSERT_EQUAL( sizeof( ICMPEcho_IPv6_t ), xSet.uxProtocolHeaderLength );
}

void test_prvChecksumICMPv6Checks_PingReply_InvalidLength( void )
{
    uint16_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( usReturn, 10 );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

void test_prvChecksumICMPv6Checks_PingReply_ValidLength( void )
{
    uint16_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) + 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( usReturn, 0 );
    TEST_ASSERT_EQUAL( sizeof( ICMPEcho_IPv6_t ), xSet.uxProtocolHeaderLength );
}

void test_prvChecksumICMPv6Checks_RS_InvalidLength( void )
{
    uint16_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_SOLICITATION_IPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( usReturn, 10 );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

void test_prvChecksumICMPv6Checks_RS_ValidLength( void )
{
    uint16_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) + 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_SOLICITATION_IPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( usReturn, 0 );
    TEST_ASSERT_EQUAL( sizeof( ICMPRouterSolicitation_IPv6_t ), xSet.uxProtocolHeaderLength );
}
