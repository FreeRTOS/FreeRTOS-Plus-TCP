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
#define raDEFAULT_VERSION_TRAFFIC_CLASS    0x60U
/** The default value for the IPv6-field 'ucHopLimit'. */
#define raDEFAULT_HOP_LIMIT                255U

#define ndICMP_PREFIX_INFORMATION           3


#define uxHeaderBytesRS ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) )
#define uxHeaderBytesRA ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterAdvertisement_IPv6_t ) )

void test_vNDSendRouterSolicitation_Null_Endpoint( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    IPv6_Address_t * pxIPAddress;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;

    catch_assert( vNDSendRouterSolicitation( pxNetworkBuffer, pxIPAddress ) );
}

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

void test_vNDSendRouterSolicitation_HappyPath2( void )
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

void test_vNDSendRouterSolicitation_HappyPath1( void )
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

void test_vReceiveRA_IncorrectDataLength( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA - 1;

    vReceiveRA( pxNetworkBuffer );

}

/* Test to check that prefix can not be reached by the router indicating Advertisement Lifetime as zero. */
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

/* NULL ICMP prefix option pointer as no x`options field present */
void test_vReceiveRA_NULL_ICMPprefix( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA;

    vReceiveRA( pxNetworkBuffer );

}

void test_vReceiveRA_NULL_ICMPprefix_NotEnoughBytes( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    size_t uxIndex = 0U,  uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + 10;
    uxNeededSize = uxHeaderBytesRA;
    
    pxPrefixOption = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_PREFIX_INFORMATION;
    /* For Options */
    uxOptionsLength = 2;
    pxPrefixOption->ucLength = uxOptionsLength;

    vReceiveRA( pxNetworkBuffer );

}

void test_vReceiveRA_Valid_ICMPprefix( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    size_t uxIndex = 0U,  uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    NetworkEndPoint_t xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + sizeof(ICMPPrefixOption_IPv6_t);
    uxNeededSize = uxHeaderBytesRA;
    
    pxPrefixOption = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    memset( pxPrefixOption, 1, sizeof(ICMPPrefixOption_IPv6_t));
    pxPrefixOption->ucType = ndICMP_PREFIX_INFORMATION;

    xEndPoint.bits.bWantRA = pdFALSE_UNSIGNED;


    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    vReceiveRA( pxNetworkBuffer );

}

void test_vReceiveRA_vRAProcess( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    size_t uxIndex = 0U,  uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    NetworkEndPoint_t xEndPoint;
    ICMPPrefixOption_IPv6_t *pxPrefixOption;
    IPv6_Address_t xIPAddress;

    /* Setting IPv6 address as "fe80::7009" */
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
    xIPAddress.ucBytes[ 0 ] = 254;
    xIPAddress.ucBytes[ 1 ] = 128;
    xIPAddress.ucBytes[ 14 ] = 112;
    xIPAddress.ucBytes[ 15 ] = 9;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = &xICMPPacket;
    memcpy(&xICMPPacket.xIPHeader.xSourceAddress.ucBytes, &xIPAddress, ipSIZE_OF_IPv6_ADDRESS);
    pxNetworkBuffer->xDataLength = uxHeaderBytesRA + sizeof(ICMPPrefixOption_IPv6_t);
    uxNeededSize = uxHeaderBytesRA;
    pucBytes = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );

    pxPrefixOption = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    memset( pxPrefixOption, 1, sizeof(ICMPPrefixOption_IPv6_t));
    pxPrefixOption->ucType = ndICMP_PREFIX_INFORMATION;

    xEndPoint.bits.bWantRA = pdTRUE_UNSIGNED;
    xEndPoint.xRAData.eRAState = eRAStateWait;


    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_Ignore();

    vReceiveRA( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxPrefixOption->ucPrefixLength, xEndPoint.ipv6_settings.uxPrefixLength );
    TEST_ASSERT_EQUAL( xEndPoint.xRAData.bits.bRouterReplied, pdTRUE_UNSIGNED );
    TEST_ASSERT_EQUAL( xEndPoint.xRAData.ulPreferredLifeTime, pxPrefixOption->ulPreferredLifeTime );
    TEST_ASSERT_EQUAL( xEndPoint.xRAData.bits.bIPAddressInUse , pdFALSE_UNSIGNED );
    TEST_ASSERT_EQUAL( xEndPoint.xRAData.eRAState, eRAStateIPWait);
}

/* Verify RA state machine with RA wait state = eRAStateApply {Set during RA_Init} 
   Failed to get network buffer - pxGetNetworkBufferWithDescriptor
*/
void test_vRAProcess_eRAStateApply1(void)
{
    NetworkEndPoint_t xEndPoint, *pxEndPoint;
    IPv6_Address_t xIPAddress;

    pxEndPoint = &xEndPoint;

    memset(pxEndPoint , 0, sizeof(NetworkEndPoint_t));

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_Ignore();

    /* pdFALSE for vRAProcessInit */
    vRAProcess( pdTRUE, &xEndPoint );

    TEST_ASSERT_EQUAL( xEndPoint.xRAData.eRAState, eRAStateWait);
}

