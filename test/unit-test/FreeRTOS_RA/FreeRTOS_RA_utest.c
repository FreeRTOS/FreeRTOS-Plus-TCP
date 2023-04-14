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

#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_NetworkBufferManagement.h"

#include "catch_assert.h"
#include "FreeRTOS_RA_stubs.c"

/** The default value for the IPv6-field 'ucVersionTrafficClass'. */
#define raDEFAULT_VERSION_TRAFFIC_CLASS     0x60U
/** The default value for the IPv6-field 'ucHopLimit'. */
#define raDEFAULT_HOP_LIMIT                 255U

/** @brief Options that can be sent in a ROuter Advertisement packet. */
#define ndICMP_SOURCE_LINK_LAYER_ADDRESS    1
#define ndICMP_TARGET_LINK_LAYER_ADDRESS    2
#define ndICMP_PREFIX_INFORMATION           3
#define ndICMP_REDIRECTED_HEADER            4
#define ndICMP_MTU_OPTION                   5


#define uxHeaderBytesRS                     ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) )
#define uxHeaderBytesRA                     ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterAdvertisement_IPv6_t ) )


/*
 * ===================================================
 *           Test for vNDSendRouterSolicitation
 * ===================================================
 */


/**
 * @brief This function verify sending an Router Solicitation ICMPv6
 *        message With a NULL Endpoint.
 */
void test_vNDSendRouterSolicitation_Null_Endpoint( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    IPv6_Address_t * pxIPAddress;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;

    catch_assert( vNDSendRouterSolicitation( pxNetworkBuffer, pxIPAddress ) );
}

/**
 * @brief This function verify sending an Router Solicitation ICMPv6 message
 *        With a bIPv6 not set in Endpoint.
 */
void test_vNDSendRouterSolicitation_False_bIPv6( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPv6_Address_t * pxIPAddress, xIPAddress;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.bits.bIPv6 = 0;

    catch_assert( vNDSendRouterSolicitation( pxNetworkBuffer, pxIPAddress ) );
}

/**
 * @brief This function verify sending an Router Solicitation ICMPv6 message
 *        And RA was able to find a Link-local address.
 */
void test_vNDSendRouterSolicitation_xHasLocal( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer, xNetworkBuffer2;
    NetworkEndPoint_t xEndPoint;
    IPv6_Address_t xIPAddress;
    ICMPPacket_IPv6_t * pxICMPPacket, xICMPPacket;
    IPHeader_IPv6_t xIPHeader;

    pxNetworkBuffer = &xNetworkBuffer;
    pxICMPPacket = &xICMPPacket;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRS - 1;
    xNetworkBuffer2.xDataLength = uxHeaderBytesRS + 1;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    xEndPoint.bits.bIPv6 = 1;
    pxICMPPacket->xIPHeader = xIPHeader;

    memset( &xEndPoint.ipv6_settings, 0, sizeof( IPV6Parameters_t ) );
    memset( &pxICMPPacket->xIPHeader, 0, sizeof( IPHeader_IPv6_t ) );

    /* Link-Local unicast address prefixed FE80::/10 */
    xEndPoint.ipv6_settings.xIPAddress.ucBytes[ 0 ] = 0xfeU;
    xEndPoint.ipv6_settings.xIPAddress.ucBytes[ 1 ] = 0x80U;

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    vNDSendRouterSolicitation( pxNetworkBuffer, &xIPAddress );
}

/**
 * @brief This function verify sending an Router Solicitation ICMPv6 message
 *        With a pxDescriptor being NULL.
 */
void test_vNDSendRouterSolicitation_NullDesc( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer, xNetworkBuffer2;
    NetworkEndPoint_t xEndPoint;
    IPv6_Address_t xIPAddress;
    ICMPPacket_IPv6_t * pxICMPPacket, xICMPPacket;
    IPHeader_IPv6_t xIPHeader;

    pxNetworkBuffer = &xNetworkBuffer;
    pxICMPPacket = &xICMPPacket;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRS - 1;
    xNetworkBuffer2.xDataLength = uxHeaderBytesRS + 1;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    xEndPoint.bits.bIPv6 = 1;
    pxICMPPacket->xIPHeader = xIPHeader;

    memset( &xEndPoint.ipv6_settings, 0, sizeof( IPV6Parameters_t ) );
    memset( &pxICMPPacket->xIPHeader, 0, sizeof( IPHeader_IPv6_t ) );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    vNDSendRouterSolicitation( pxNetworkBuffer, &xIPAddress );
}

/**
 * @brief This function verify succeffully sending an
 *        ICMPv6 message of the type: Router Solicitation
 */
void test_vNDSendRouterSolicitation_HappyPath( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPv6_Address_t xIPAddress;
    ICMPPacket_IPv6_t * pxICMPPacket, xICMPPacket;
    IPHeader_IPv6_t xIPHeader;

    pxNetworkBuffer = &xNetworkBuffer;
    pxICMPPacket = &xICMPPacket;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRS + 1;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    xEndPoint.bits.bIPv6 = 1;
    pxICMPPacket->xIPHeader = xIPHeader;

    memset( &xEndPoint.ipv6_settings, 0, sizeof( IPV6Parameters_t ) );
    memset( &pxICMPPacket->xIPHeader, 0, sizeof( IPHeader_IPv6_t ) );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    vNDSendRouterSolicitation( pxNetworkBuffer, &xIPAddress );

    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucVersionTrafficClass, raDEFAULT_VERSION_TRAFFIC_CLASS );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.usPayloadLength, FreeRTOS_htons( sizeof( ICMPRouterSolicitation_IPv6_t ) ) );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucNextHeader, ipPROTOCOL_ICMP_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucHopLimit, raDEFAULT_HOP_LIMIT );
}

/*
 * ===================================================
 *           Test for vReceiveNA
 * ===================================================
 */

/**
 * @brief This function verify received Neighbour Advertisement message
 *        without EndPoint.
 */
void test_vReceiveNA_NoEndPoint( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    ICMPPacket_IPv6_t xICMPPacket;

    pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( NULL );

    vReceiveNA( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( xEndPoint.xRAData.bits.bIPAddressInUse, 0 );
}

/**
 * @brief This function verify received Neighbour Advertisement message
 *        to see that the chosen IP-address is not in use.
 */
void test_vReceiveNA_bIPAddressNotInUse( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    ICMPPacket_IPv6_t xICMPPacket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    xEndPoint.bits.bWantRA = pdFALSE_UNSIGNED;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );

    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );

    vReceiveNA( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( xEndPoint.xRAData.bits.bIPAddressInUse, 0 );
}

/**
 * @brief This function verify received Neighbour Advertisement message
 *        to see that the chosen IP-address is already in use.
 */
void test_vReceiveNA_bIPAddressInUse( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    ICMPPacket_IPv6_t xICMPPacket;
    IPv6_Address_t xIPAddress;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    xEndPoint.bits.bWantRA = pdTRUE_UNSIGNED;
    xEndPoint.xRAData.eRAState = eRAStateIPWait;

    /* Setting IPv6 address as "fe80::7009" */
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
    xIPAddress.ucBytes[ 0 ] = 254;
    xIPAddress.ucBytes[ 1 ] = 128;
    xIPAddress.ucBytes[ 14 ] = 112;
    xIPAddress.ucBytes[ 15 ] = 9;

    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( xICMPPacket.xICMPHeaderIPv6.xIPv6Address.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_Ignore();

    vReceiveNA( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( xEndPoint.xRAData.bits.bIPAddressInUse, 1 );
}

/*
 * ===================================================
 *           Test for vReceiveRA
 * ===================================================
 */

/**
 * @brief This function verify the handling
 *        of incorrect data length.
 */
void test_vReceiveRA_IncorrectDataLength( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;

    pxNetworkBuffer = &xNetworkBuffer;
    /* Setting incorrect data length */
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA - 1;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify the handling
 *        of Advertisement Lifetime as zero.
 */
void test_vReceiveRA_ZeroAdvertisementLifetime( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;
    ICMPPacket_IPv6_t xICMPPacket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + 1;

    pxAdvertisement = ( ( const ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = 0;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify NULL ICMP prefix
 *        option pointer as no options field.
 */
void test_vReceiveRA_NULL_ICMPprefix( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present but data length less than the
 *        required data length by option field.
 */
void test_vReceiveRA_NULL_ICMPprefix_NotEnoughBytes( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    /* Data Length to be less than expected */
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + 10;
    uxNeededSize = uxHeaderBytesRA;

    pxPrefixOption = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_PREFIX_INFORMATION;
    /* Number of Options present - 8-byte blocks. */
    uxOptionsLength = 2;
    pxPrefixOption->ucLength = uxOptionsLength;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_SOURCE_LINK_LAYER_ADDRESS.
 */
void test_vReceiveRA_Valid_ICMPprefix_Option1( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    size_t uxPrefixOptionlen = 8;
    uint8_t * pucBytes;
    NetworkEndPoint_t xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + uxPrefixOptionlen;
    uxNeededSize = uxHeaderBytesRA;

    pxPrefixOption = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_SOURCE_LINK_LAYER_ADDRESS;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_TARGET_LINK_LAYER_ADDRESS.
 */
void test_vReceiveRA_Valid_ICMPprefix_Option2( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    size_t uxPrefixOptionlen = 8;
    uint8_t * pucBytes;
    NetworkEndPoint_t xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + uxPrefixOptionlen;
    uxNeededSize = uxHeaderBytesRA;

    pxPrefixOption = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_TARGET_LINK_LAYER_ADDRESS;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_PREFIX_INFORMATION.
 */
void test_vReceiveRA_Valid_ICMPprefix_Option3( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    size_t uxPrefixOptionlen = 8;
    uint8_t * pucBytes;
    NetworkEndPoint_t xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + uxPrefixOptionlen;
    uxNeededSize = uxHeaderBytesRA;

    pxPrefixOption = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_PREFIX_INFORMATION;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;


    xEndPoint.bits.bWantRA = pdFALSE_UNSIGNED;

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    vReceiveRA( pxNetworkBuffer );
}


/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_TARGET_LINK_LAYER_ADDRESS.
 */
void test_vReceiveRA_Valid_ICMPprefix_Option4( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    size_t uxPrefixOptionlen = 8;
    uint8_t * pucBytes;
    NetworkEndPoint_t xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + uxPrefixOptionlen;
    uxNeededSize = uxHeaderBytesRA;

    pxPrefixOption = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_REDIRECTED_HEADER;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_TARGET_LINK_LAYER_ADDRESS.
 */
void test_vReceiveRA_Valid_ICMPprefix_Option5( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    size_t uxPrefixOptionlen = 8;
    uint8_t * pucBytes;
    NetworkEndPoint_t xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + uxPrefixOptionlen;
    uxNeededSize = uxHeaderBytesRA;

    pxPrefixOption = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_MTU_OPTION;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    ulChar2u32_ExpectAnyArgsAndReturn( 0x12345678 );

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_TARGET_LINK_LAYER_ADDRESS.
 */
void test_vReceiveRA_Valid_ICMPprefix_IncorrectOption( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    size_t uxPrefixOptionlen = 8;
    uint8_t * pucBytes;
    NetworkEndPoint_t xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + uxPrefixOptionlen;
    uxNeededSize = uxHeaderBytesRA;

    pxPrefixOption = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = 0;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify vReceiveRA success case.
 */
void test_vReceiveRA_vRAProcess( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    size_t uxPrefixOptionlen = 8;
    uint8_t * pucBytes;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + uxPrefixOptionlen;
    uxNeededSize = uxHeaderBytesRA;
    pxAdvertisement = ( ( const ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = pdTRUE_UNSIGNED;

    pxPrefixOption = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_PREFIX_INFORMATION;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;


    xEndPoint.bits.bWantRA = pdTRUE_UNSIGNED;
    xEndPoint.xRAData.eRAState = eRAStateWait;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_Ignore();

    vReceiveRA( pxNetworkBuffer );


    TEST_ASSERT_EQUAL( pxEndPoint->ipv6_settings.uxPrefixLength, pxPrefixOption->ucPrefixLength );
    TEST_ASSERT_EQUAL( pxEndPoint->xRAData.bits.bRouterReplied, pdTRUE_UNSIGNED );
    TEST_ASSERT_EQUAL( pxEndPoint->xRAData.uxRetryCount, 0U );
    TEST_ASSERT_EQUAL( pxEndPoint->xRAData.ulPreferredLifeTime, FreeRTOS_ntohl( pxPrefixOption->ulPreferredLifeTime ) );
    TEST_ASSERT_EQUAL( pxEndPoint->xRAData.bits.bIPAddressInUse, pdFALSE_UNSIGNED );
    TEST_ASSERT_EQUAL( pxEndPoint->xRAData.eRAState, eRAStateIPWait );
}

/* ===================================================
 *           Test for vRAProcess
 * ===================================================
 */


/**
 *  @brief This function verify RA state machine with RA wait state
 *         as eRAStateApply {Set during RA_Init}
 *         And failed to get network buffer.
 */
void test_vRAProcess_eRAStateApply1( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    pxEndPoint = &xEndPoint;

    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_Ignore();

    /* pdTRUE for vRAProcessInit */
    vRAProcess( pdTRUE, &xEndPoint );

    TEST_ASSERT_EQUAL( xEndPoint.xRAData.eRAState, eRAStateWait );
}

/**
 *  @brief This function verify RA state machine with RA wait state as
 *         eRAStateApply {Set during RA_Init}
 *         And Send an ICMPv6 message of the type: Router Solicitation.
 */
void test_vRAProcess_eRAStateApply2( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;
    ICMPPacket_IPv6_t * pxICMPPacket, xICMPPacket;

    pxEndPoint = &xEndPoint;
    pxNetworkBuffer = &xNetworkBuffer;

    pxICMPPacket = &xICMPPacket;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;

    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxEndPoint->bits.bIPv6 = 1;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxHeaderBytesRS, 0, &xNetworkBuffer );
    vDHCP_RATimerReload_Ignore();

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    /* pdFALSE for vRAProcessInit */
    vRAProcess( pdTRUE, &xEndPoint );

    TEST_ASSERT_EQUAL( xEndPoint.xRAData.eRAState, eRAStateWait );
}

/**
 *  @brief This function verify RA state machine with RA wait state as eRAStateWait.
 */
void test_vRAProcess_eRAStateWait( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint->xRAData.eRAState = eRAStateWait;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_Ignore();

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( xEndPoint.xRAData.eRAState, eRAStateWait );
}

/**
 *  @brief This function verify RA state machine with RA wait state as eRAStateWait.
 *         Router Solicitation has been sent, waited for a reply, but no came and
 *         the retry count becomes more that ipconfigRA_SEARCH_COUNT.
 */
void test_vRAProcess_eRAStateWait_RetryExceed( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;
    UBaseType_t retry = ( UBaseType_t ) ipconfigRA_SEARCH_COUNT;

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint->xRAData.eRAState = eRAStateWait;
    pxEndPoint->xRAData.uxRetryCount = ( UBaseType_t ) ipconfigRA_SEARCH_COUNT;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_Ignore();

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( pxEndPoint->xRAData.bits.bRouterReplied, pdFALSE_UNSIGNED );
    TEST_ASSERT_EQUAL( pxEndPoint->xRAData.uxRetryCount, 0U );
    TEST_ASSERT_EQUAL( xEndPoint.xRAData.eRAState, eRAStateIPWait );
}

/**
 *  @brief This function verify RA state machine with RA wait state as eRAStateIPWait.
 *         With bIPAddressInUse True which implies Another device has
 *         responded with the same IPv4 address.
 */
void test_vRAProcess_eRAStateIPWait_AddressInUse( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint->xRAData.eRAState = eRAStateIPWait;
    pxEndPoint->xRAData.bits.bIPAddressInUse = pdTRUE_UNSIGNED;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_Ignore();

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( pxEndPoint->xRAData.uxRetryCount, 0U );
    TEST_ASSERT_EQUAL( xEndPoint.xRAData.eRAState, eRAStateIPWait );
}

/**
 *  @brief This function verify RA state machine with RA wait state as eRAStateIPWait,
 *         With retry.
 */
void test_vRAProcess_eRAStateIPWait_Retry( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint->xRAData.eRAState = eRAStateIPWait;
    pxEndPoint->xRAData.uxRetryCount = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_Ignore();

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( pxEndPoint->xRAData.uxRetryCount, 1U );
    TEST_ASSERT_EQUAL( xEndPoint.xRAData.eRAState, eRAStateIPWait );
}

/**
 *  @brief This function verify RA state machine with RA wait state as eRAStateIPWait.
 *         And Obtained configuration from a router.
 */
void test_vRAProcess_eRAStateIPWait_RA_SUCCESS( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint->xRAData.eRAState = eRAStateIPWait;
    pxEndPoint->xRAData.uxRetryCount = ipconfigRA_IP_TEST_COUNT;
    /* Obtained configuration from a router. */
    pxEndPoint->xRAData.bits.bRouterReplied = pdTRUE_UNSIGNED;

    vIPNetworkUpCalls_Expect( &xEndPoint );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( xEndPoint.xRAData.eRAState, eRAStateLease );
}

/**
 *  @brief This function verify RA state machine with RA wait state
 *         as eRAStateIPWait.
 *         Using the default network parameters.
 */
void test_vRAProcess_eRAStateIPWait_UsingDefaultAddress( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint->xRAData.eRAState = eRAStateIPWait;
    pxEndPoint->xRAData.uxRetryCount = ipconfigRA_IP_TEST_COUNT;
    /* Using the default network parameters. */
    pxEndPoint->xRAData.bits.bRouterReplied = pdFALSE_UNSIGNED;

    vIPNetworkUpCalls_Expect( &xEndPoint );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( xEndPoint.xRAData.eRAState, eRAStateFailed );
}
