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

#include "FreeRTOS.h"
#include "FreeRTOS_IP.h"

#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_task.h"
#include "mock_list.h"
#include "mock_queue.h"
#include "mock_FreeRTOS_DNS_Callback.h"
#include "mock_FreeRTOS_DNS_Cache.h"
#include "mock_FreeRTOS_DNS_Networking.h"
#include "mock_NetworkBufferManagement.h"

#include "FreeRTOS_DNS.h"
#include "catch_assert.h"
#include "FreeRTOSIPConfig.h"
#include "FreeRTOS_DNS_Parser.h"

#define LLMNR_ADDRESS     "freertos"
#define GOOD_ADDRESS      "www.freertos.org"
#define BAD_ADDRESS       "this is a bad address"
#define DOTTED_ADDRESS    "192.268.0.1"

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                uint32_t /* ulIPAddress */ );

/* ===========================   GLOBAL VARIABLES =========================== */
static int callback_called = 0;
static BaseType_t hook_return = pdFALSE;
static BaseType_t hook_called = pdFALSE;



/* ===========================  STATIC FUNCTIONS  =========================== */
static void dns_callback( const char * pcName,
                          void * pvSearchID,
                          uint32_t ulIPAddress )
{
    callback_called = 1;
}

/* ============================  TEST FIXTURES  ============================= */

extern BaseType_t xBufferAllocFixedSize;

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
    xBufferAllocFixedSize = pdFALSE;
    xDefaultPartUDPPacketHeader.ucBytes[ 0 ] = 1;
    xDefaultPartUDPPacketHeader.ucBytes[ 1 ] = 2;
    xDefaultPartUDPPacketHeader.ucBytes[ 2 ] = 3;
    xDefaultPartUDPPacketHeader.ucBytes[ 3 ] = 4;
    xDefaultPartUDPPacketHeader.ucBytes[ 4 ] = 5;
    xDefaultPartUDPPacketHeader.ulWords[ 0 ] = 6;
    xDefaultPartUDPPacketHeader.ulWords[ 1 ] = 7;
    xDefaultPartUDPPacketHeader.ulWords[ 2 ] = 8;
    xDefaultPartUDPPacketHeader.ulWords[ 3 ] = 9;
    xDefaultPartUDPPacketHeader.ulWords[ 4 ] = 10;
    xDefaultPartUDPPacketHeader.ulWords[ 5 ] = 11;
    xDefaultPartUDPPacketHeader.ulWords[ 6 ] = 12;
    xDefaultPartUDPPacketHeader.ulWords[ 7 ] = 13;
    xDefaultPartUDPPacketHeader.ulWords[ 8 ] = 14;
    callback_called = 0;
}

/**
 * @brief calls at the end of each test case
 */
void tearDown( void )
{
    hook_return = pdFALSE;
    hook_called = pdFALSE;
}

/* =============================  TEST MACROS  ============================== */
#define ASSERT_DNS_QUERY_HOOK_CALLED()            \
    do {                                          \
        TEST_ASSERT_EQUAL( pdTRUE, hook_called ); \
    } while( 0 )

/* =============================  TEST CASES  =============================== */

/**
 * @brief ensures when there is no empty spots in the  pucByte buffer zero is
 *        returned
 */
void test_DNS_ReadNameField_success_empty_uxRemainingBytes( void )
{
    uint8_t pucByte[ 300 ];
    size_t ret;

    memset( pucByte, 0x00, 300 );
    ret = DNS_ReadNameField( pucByte, 0, "name", 4 );
    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures that if the dns name is dnsNAME_IS_OFFSET  and the source
 *        length is less than 2 bytes zero is returned
 */
void test_DNS_ReadNameField_fail_offset_dns_name( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;

    ret = DNS_ReadNameField( pucByte, 2, "name", 4 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures that if the dns name is dnsNAME_IS_OFFSET  and the source
 *        length is greater than 2 bytes 2 is returned (sizeof (uint16_t)
 */
void test_DNS_ReadNameField_success_fully_coded_gt_uint16( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 300 );

    pucByte[ 0 ] = dnsNAME_IS_OFFSET;

    ret = DNS_ReadNameField( pucByte, 8, "name", 234 );

    TEST_ASSERT_EQUAL( sizeof( uint16_t ), ret );
}

/**
 * @brief ensures when the next name field size is zero, zero is returned
 */
void test_DNS_ReadNameField_zero_size_walk_over_nothing_to_do( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 300 );

    pucByte[ 0 ] = 0;

    ret = DNS_ReadNameField( pucByte, 300, "name", 234 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures when the name is 8 bytes 10 is returned . + '\0', and the name
 *        field is copied to pcName
 */
void test_DNS_ReadNameField_walk_over_copy_name( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );

    ret = DNS_ReadNameField( pucByte, 300, pcName, 300 );

    TEST_ASSERT_EQUAL( 10, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS", pcName );
}

/**
 * @brief ensures when the name is 8 bytes and the size passed is smaller
 *        zero is returned and field id copied to pcName
 */
void test_DNS_ReadNameField_walk_over_exact_source_length( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );

    ret = DNS_ReadNameField( pucByte, 9, pcName, 300 );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS", pcName );
    TEST_ASSERT_EQUAL( 0, pcName[ 8 ] );
    TEST_ASSERT_EQUAL( 0, pcName[ 9 ] );
    TEST_ASSERT_EQUAL( 0, pcName[ 10 ] );
}

/**
 * @brief ensures when we have 2 names fields
 *        their total + 2(dot, and \0) are returned
 *        and the result string in pcName
 */
void test_DNS_ReadNameField_walk_over_copy_2_names( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );
    size_t ret;

    ret = DNS_ReadNameField( pucByte, 300, pcName, 300 );

    TEST_ASSERT_EQUAL( 18, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.PlusTCP", pcName );
}

/**
 * @brief ensures that when the destination buffer (pcName) is shorter than the
 *        total string name field, zero is returned and the string is truncated i
 *        pcName
 */
void test_DNS_ReadNameField_short_destination( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );
    size_t ret;

    ret = DNS_ReadNameField( pucByte, 300, pcName, 12 );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.Plu", pcName );
}

/**
 * @brief ensures that when the source buffer (pucByte) is shorter than the size
 *        of the name field, zero is returned, and the resulting string (pcName)
 *        is truncated
 */
void test_DNS_ReadNameField_short_source( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );
    size_t ret;

    ret = DNS_ReadNameField( pucByte, 10, pcName, 300 );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.", pcName );
}

/**
 * @brief ensures when the second name does not fit the destination zero is
 *        returned and only the first string is returned
 */
void test_DNS_ReadNameField_fail_name_len_gt_destlen( void )
{
    uint8_t pucByte[ 15 ] = { 0 };
    char pcName[ 10 ] = { 0 };

    memset( pucByte, 0x00, 15 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 1;
    size_t ret;

    ret = DNS_ReadNameField( pucByte, 15, pcName, 10 );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.", pcName );
}


/* ==================== Testing  DNS_SkipNameField ===========================*/

/**
 * @brief ensures that if pucByte has a size of zero, zero is returned
 */
void test_DNS_SkipNameField_failed_zero_length()
{
    size_t ret;
    uint8_t pucByte[ 20 ];

    memset( pucByte, 0x00, 20 );

    ret = DNS_SkipNameField( pucByte, 0 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures that the appropriate size is returned + dot, dot, and \0
 */
void test_DNS_SkipNameField_failed_()
{
    uint8_t pucByte[ 300 ] = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );

    ret = DNS_SkipNameField( pucByte, 300 );

    TEST_ASSERT_EQUAL( 18, ret );
}


/**
 * @brief ensures that when it is an offset packet and the size is less than 2
 *        bytes, zero is returned
 */
void test_DNS_SkipNameField_fail_fully_coded( void )
{
    uint8_t pucByte[ 2 ] = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 2 );
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;

    ret = DNS_SkipNameField( pucByte, 2 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures that when it is an offset packet and the size is greater
 *        than 2, 2 is returned
 */
void test_DNS_SkipNameField_success_fully_coded_gt_uint16( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;

    ret = DNS_SkipNameField( pucByte, 84 );

    TEST_ASSERT_EQUAL( sizeof( uint16_t ), ret );
}

/**
 * @brief ensures that when the source is shorter than the size markings
 *        zero is returned
 */
void test_DNS_SkipNameField_short_source( void )
{
    uint8_t pucByte[ 300 ] = { 0 };

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );
    size_t ret;

    ret = DNS_SkipNameField( pucByte, 10 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures that when the last name field is less than the buffer
 *        remaining size, zero is returned
 */
void test_DNS_SkipNameField_small_buffer( void )
{
    uint8_t pucByte[ 300 ] = { 0 };

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );
    size_t ret;

    ret = DNS_SkipNameField( pucByte, 6 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/* =================== test prepare Reply DNS Message ======================= */

/**
 * @brief
 */
void test_prepareReplyDNSMessage_success( void )
{
    NetworkBufferDescriptor_t pxNetworkBuffer;
    uint8_t ether_buffer[ 300 ];
    size_t uxDataLength;

    pxNetworkBuffer.pucEthernetBuffer = ether_buffer;
    pxNetworkBuffer.xDataLength = 300;


    BaseType_t lNetLength = 50;
    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;
    UDPHeader_t * pxUDPHeader;

    pxUDPPacket = ( ( UDPPacket_t * )
                    &pxNetworkBuffer.pucEthernetBuffer );
    pxIPHeader = &pxUDPPacket->xIPHeader;
    pxUDPHeader = &pxUDPPacket->xUDPHeader;

    pxIPHeader->ulSourceIPAddress = 1234;

    usGenerateChecksum_ExpectAnyArgsAndReturn( 555 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 444 );

    prepareReplyDNSMessage( &pxNetworkBuffer,
                            lNetLength );

    uxDataLength = ( ( size_t ) lNetLength ) + ipSIZE_OF_IPv4_HEADER +
                   ipSIZE_OF_UDP_HEADER + ipSIZE_OF_ETH_HEADER;

    TEST_ASSERT_EQUAL( pxNetworkBuffer.xDataLength, uxDataLength );
}

/* =========================== test DNS_TreatNBNS  ========================== */

/**
 * @brief ensures that when a random payload is passed, vReturnEthernetFrame is
 *        not called
 */
void test_DNS_TreatNBNS_success( void )
{
    uint8_t pucPayload[ 300 ];
    size_t uxBufferLength;
    uint32_t ulIPAddress;


    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief ensures that when a random payload is passed, vReturnEthernetFrame is
 *        not called
 */
void test_DNS_TreatNBNS_success_nbns_mask( void )
{
    uint8_t pucPayload[ 300 ];
    size_t uxBufferLength;
    uint32_t ulIPAddress;


    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_MASK );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief ensures that when new buffer is NULL, vReturnEthernetFrame is not
 *        called
 */
void test_DNS_TreatNBNS_success_nbns_query_trailing_space( void )
{
    uint8_t pucPayload[ 300 ];
    size_t uxBufferLength;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t pxNetworkBuffer;

    hook_return = pdTRUE;
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when buffer is NULL, vReturnEthernetFrame is not
 *        called
 */
void test_DNS_TreatNBNS_success_nbns_query( void )
{
    uint8_t pucPayload[ 300 ];
    size_t uxBufferLength;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t pxNetworkBuffer;

    hook_return = pdTRUE;
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when new buffer is NULL, vReturnEthernetFrame is not
 *        called
 */
void test_DNS_TreatNBNS_success_nbns_query_network_buffer_null( void )
{
    uint8_t pucPayload[ 300 ];
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;


    hook_return = pdTRUE;
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( NULL );


    DNS_TreatNBNS( pucPayload,
                   uxBufferLength,
                   1234 );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief success path, formed packet is sent over the network with
 *        vReturnEthernetFrame
 */
void test_DNS_TreatNBNS_success_nbns_non_fixed_size_buffer( void )
{
    uint8_t pucPayload[ 300 ];
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t pxNetworkBuffer;
    NetworkBufferDescriptor_t pxNetworkBuffer_dup;

    uint8_t buffer[ 300 ];

    pxNetworkBuffer_dup.pucEthernetBuffer = buffer;
    pxNetworkBuffer_dup.xDataLength = 300;

    hook_return = pdTRUE;
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usFlags */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );      /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &pxNetworkBuffer_dup );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 4 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 4 );
    vReturnEthernetFrame_Expect( &pxNetworkBuffer_dup, pdFALSE ); /* goal */
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    DNS_TreatNBNS( pucPayload,
                   uxBufferLength,
                   1234 );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief success path, formed packet is sent over the network with
 *        vReturnEthernetFrame
 */
void test_DNS_TreatNBNS_success_nbns_non_fixed_size_buffer2( void )
{
    uint8_t pucPayload[ 300 ];
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;

    xBufferAllocFixedSize = pdTRUE;
    NetworkBufferDescriptor_t pxNetworkBuffer;
    NetworkBufferDescriptor_t pxNetworkBuffer_dup;

    uint8_t buffer[ 300 ];

    pxNetworkBuffer.pucEthernetBuffer = buffer;
    pxNetworkBuffer.xDataLength = 300;

    pxNetworkBuffer_dup.pucEthernetBuffer = buffer;
    pxNetworkBuffer_dup.xDataLength = 300;

    hook_return = pdTRUE;
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usFlags */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );      /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 4 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 4 );
    vReturnEthernetFrame_Expect( &pxNetworkBuffer, pdFALSE ); /* goal */

    DNS_TreatNBNS( pucPayload,
                   uxBufferLength,
                   1234 );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief success path, formed packet is sent over the network with
 *        vReturnEthernetFrame
 */
void test_DNS_TreatNBNS_success_nbns_non_fixed_size_buffer3( void )
{
    uint8_t pucPayload[ 300 ];
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t pxNetworkBuffer;
    NetworkBufferDescriptor_t pxNetworkBuffer_dup;

    uint8_t buffer[ 300 ];

    pxNetworkBuffer_dup.pucEthernetBuffer = buffer;
    pxNetworkBuffer_dup.xDataLength = 300;

    hook_return = pdTRUE;
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usFlags */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_CLASS_IN );           /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );

    DNS_TreatNBNS( pucPayload,
                   uxBufferLength,
                   1234 );
}

/**
 * @brief ensures that when pucPayload + dnsNBNS_ENCODED_NAME_LENGTH = 41U = 'A'
 *        we break out of the loop and nothing is sent over the network if the
 *        whole name if not in capital letters and terminated with '\0'
 */
void test_DNS_TreatNBNS_success_empty_char_nbns_name( void )
{
    uint8_t pucPayload[ 300 ];

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) +
                offsetof( NBNSRequest_t, ucName ) ] = 2 + 0x41U;
    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) +
                offsetof( NBNSRequest_t, ucName ) + 1 ] = ' ' + 0x41U;

    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY | dnsNBNS_FLAGS_RESPONSE );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( 1 );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief ensures that when pucPayload + dnsNBNS_ENCODED_NAME_LENGTH = 41U = 'A'
 *        we break out of the loop and nothing is sent over the network if the
 *        whole name if not in capital letters and terminated with '\0'
 */
void test_DNS_TreatNBNS_success_empty_char_nbns_name2( void )
{
    uint8_t pucPayload[ 300 ];


    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) +
                offsetof( NBNSRequest_t, ucName ) ] = 2 + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) + 1 ] = ' ' + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 1 ] = ' ' + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 2 ] = ' ' + 0x42U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 3 ] = ' ' + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 4 ] = ' ' + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 5 ] = ' ' + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 6 ] = ' ' + 0x41U;

    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY | dnsNBNS_FLAGS_RESPONSE );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( 1 );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}
/* ======================== test DNS_ParseDNSReply ========================== */

/**
 * @brief ensures that when the passed buffer is smaller than DNS_Message_t
 *        false is returned
 */
void test_DNS_ParseDNSReply_fail_small_buffer( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ sizeof( DNSMessage_t ) - 2 ];
    size_t uxBufferLength = sizeof( DNSMessage_t ) - 2;
    BaseType_t xExpected = pdFALSE;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief ensures that when the buffer is empty false is returned
 */
void test_DNS_ParseDNSReply_fail_no_namefield( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 300 ] = { 0 };
    size_t uxBufferLength = 300;
    BaseType_t xExpected = pdFALSE;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}


/**
 * @brief
 */
void test_DNS_ParseDNSReply_fail( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 300 ];
    size_t uxBufferLength = 300;
    BaseType_t xExpected = pdFALSE;
    int beg = sizeof( DNSMessage_t );

    memset( pucUDPPayloadBuffer, 0x00, 300 );

    pucUDPPayloadBuffer[ beg++ ] = 8;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS" );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief
 */
void test_DNS_ParseDNSReply_fail_empty_namefield( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 300 ];
    size_t uxBufferLength = 300;
    BaseType_t xExpected = pdFALSE;
    uint8_t beg = sizeof( DNSMessage_t );

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );
    pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usQuestions ) ] = 4;

    pucUDPPayloadBuffer[ beg++ ] = 8;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS" );

    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usClass */
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief
 */
void test_DNS_ParseDNSReply_fail_not_enough_space_lt_32( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ];
    size_t uxBufferLength = 250;
    char dns[ 64 ];

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usQuestions ) ] = 4;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111" );
    beg += 38;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief
 */
void test_DNS_ParseDNSReply_ansswer_record_no_answers( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ];
    size_t uxBufferLength = 250;
    char dns[ 64 ];

    memset( dns, 'a', 64 );
    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usQuestions ) ] = 0;
    pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usAnswers ) ] = 0;

    pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usFlags ) ] = dnsRX_FLAGS_MASK | dnsEXPECTED_RX_FLAGS;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief
 */
void test_DNS_ParseDNSReply_ansswer_record_too_many_answers( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ] = { 0 };
    size_t uxBufferLength = 250;
    char dns[ 64 ];

    memset( dns, 'a', 64 );
    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsEXPECTED_RX_FLAGS;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usClass */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usType */

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame
 */
void test_DNS_ParseDNSReply_ansswer_lmmnr_reply_xBufferAllocFixesize( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ] = { 0 };
    size_t uxBufferLength = 250;

    xBufferAllocFixedSize = pdTRUE;
    uint8_t * nullAddress = NULL;

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer;
    pxNetworkBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdTRUE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
    LLMNRAnswer_t * pxAnswer = &( pucNewBuffer[ 56 ] );  /* xOffset1 = 56 */

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );    /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 1234 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 123 );

    vReturnEthernetFrame_ExpectAnyArgs();
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( dnsPARSE_ERROR, ret );
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame
 */
void test_DNS_ParseDNSReply_ansswer_lmmnr_reply( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ] = { 0 };
    size_t uxBufferLength = 250;

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer;
    pxNetworkBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
    LLMNRAnswer_t * pxAnswer = &( pucNewBuffer[ 56 ] );  /* xOffset1 = 56 */

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );    /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &pxNewBuffer );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 1234 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 123 );

    vReturnEthernetFrame_Expect( &pxNewBuffer, pdFALSE );
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_CALLED();

    uint8_t value = ( ( uint8_t * ) pxAnswer )[ offsetof( LLMNRAnswer_t, ulIPAddress ) ];
    TEST_ASSERT_EQUAL( 11, value );
    TEST_ASSERT_EQUAL( 12, value + 1 );
    TEST_ASSERT_EQUAL( 13, value + 2 );
    TEST_ASSERT_EQUAL( 14, value + 3 );
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame
 */
void test_DNS_ParseDNSReply_ansswer_lmmnr_reply2( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ] = { 0 };
    size_t uxBufferLength = 250;

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer;
    pxNetworkBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 ); /* 0000000100000000 */
    dns_header->usAnswers = FreeRTOS_htons( 2 );   /* 0000001000000000 */
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
    LLMNRAnswer_t * pxAnswer = &( pucNewBuffer[ 56 ] ); /* xOffset1 = 56 */

    usChar2u16_ExpectAnyArgsAndReturn( 0 );             /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );   /* usClass */
    hook_return = pdTRUE;
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame
 */
void test_DNS_ParseDNSReply_ansswer_lmmnr_reply3( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ] = { 0 };
    size_t uxBufferLength = 250;

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer;
    pxNetworkBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
    LLMNRAnswer_t * pxAnswer = &( pucNewBuffer[ 56 ] );              /* xOffset1 = 56 */

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );             /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usClass */
    hook_return = pdTRUE;
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief ensures that when the dns query hook returns pdFALSE, the ip is not
 *        set and no packet is sent over the network
 */
void test_DNS_ParseDNSReply_ansswer_lmmnr_reply_query_hook_false( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ] = { 0 };

    memset( pucUDPPayloadBuffer, 0x0, 250 );
    size_t uxBufferLength = 250;

    NetworkBufferDescriptor_t pxNetworkBuffer;
    pxNetworkBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );    /* usClass */
    hook_return = pdFALSE;
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when the network buffer is created with a result of null,
 *        no packet is sent over the network
 */
void test_DNS_ParseDNSReply_ansswer_lmmnr_reply_null_new_netbuffer( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ] = { 0 };
    size_t uxBufferLength = 250;

    NetworkBufferDescriptor_t pxNetworkBuffer;

    pxNetworkBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );    /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( NULL );
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when the duplicated network buffer is null, no packet is
 *        sent over the network
 */
void test_DNS_ParseDNSReply_ansswer_lmmnr_reply_null_new_netbuffer2( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ] = { 0 };
    size_t uxBufferLength = 250;

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer;
    pxNetworkBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );    /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             xExpected );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when the number of answers is zero no packet is sent over
 *        the network
 */
void test_parseDNSAnswer_no_answers( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdFALSE;

    memset( pucByte, 0x00, uxsourceBytesRemaining );

    pxDNSMessageHeader.usAnswers = 0;

    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore );
    TEST_ASSERT_FALSE( ret );
    TEST_ASSERT_EQUAL( 0, uxBytesRead );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned
 */
void test_parseDNSAnswer_recordstored_gt_count( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    uint32_t ip_address = 1234;

    memset( pucByte, 0x00, uxsourceBytesRemaining );

    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ReturnThruPtr_pulIP( &ip_address );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( pdTRUE );


    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned
 */
void test_parseDNSAnswer_recordstored_gt_count2( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName = "FreeRTOS+TCP";
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSAnswerRecord_t * pxDNSAnswerRecord2;
    uint32_t ip_address = 1234;
    uint32_t ip_address2 = 2345;
    int index = 0;

    memset( pucByte, 0x00, uxsourceBytesRemaining );

    pucByte[ index ] = 38;
    index += 1;
    strcpy( pucByte + index, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    index += 39; /* String + \0 */
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + index );
    index += sizeof( DNSAnswerRecord_t );
    memcpy( pucByte + index, &ip_address, 4 );
    index += 4;

    pucByte[ index ] = 38;
    index += 1;
    strcpy( pucByte + index, "FreeRTOSaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" );
    index += 39; /* String + \0 */
    pxDNSAnswerRecord2 = ( DNSAnswerRecord_t * ) ( pucByte + index );
    index += sizeof( DNSAnswerRecord_t );
    memcpy( pucByte + index, &ip_address2, 4 );
    index += 4;
    pucByte[ index ] = 0;

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );
    pxDNSAnswerRecord->ulTTL = 23;
    pxDNSAnswerRecord->usClass = 45;

    pxDNSAnswerRecord2->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord2->usType = ( dnsTYPE_A_HOST );
    pxDNSAnswerRecord2->ulTTL = 67;
    pxDNSAnswerRecord2->usClass = 89;
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( pdTRUE );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( pdTRUE );


    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore );

    TEST_ASSERT_EQUAL( 1234, ret );
    TEST_ASSERT_EQUAL( 80, uxBytesRead );
}

/**
 * @brief ensures that when the number of entries is larger than the configured
 *        cache address entries, not packet is sent over the network
 */
void test_parseDNSAnswer_dns_nocallback_false( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    uint32_t ip_address = 5678;

    memset( pucByte, 0x00, uxsourceBytesRemaining );

    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdFALSE );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ReturnThruPtr_pulIP( &ip_address );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( "ignored" );

    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when the number of entries is larger than the configured
 *        cache address entries, not packet is sent over the network
 */
void test_parseDNSAnswer_do_store_false( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdFALSE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    memset( pucByte, 0x00, 300 );
    memset( pcName, 0x00, 300 );
    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    memset( &pxDNSMessageHeader, 0x00, sizeof( DNSMessage_t ) );
    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdFALSE );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( "ignored" );

    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when the number of entries is larger than the configured
 *        cache address entries, not packet is sent over the network
 *
 */
void test_parseDNSAnswer_dnsanswerrecord_datalength_ne_addresslength( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    memset( pucByte, 0x00, uxsourceBytesRemaining );
    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */

    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS + 2 );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when the number of entries is larger than the configured
 *        cache address entries, not packet is sent over the network
 *
 */
void test_parseDNSAnswer_remaining_gt_datalength( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 40 + sizeof( DNSAnswerRecord_t ) + 2;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    memset( pucByte, 0x00, 300 );

    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */

    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when source bytes remaining int pucByte are
 *        less than 16bytes processing is stopped and false is returned
 */
void test_parseDNSAnswer_remaining_lt_uint16( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 40 + 1;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when the number of entries is larger than the configured
 *        cache address entries, not packet is sent over the network
 *
 */
void test_parseDNSAnswer_remaining_lt_dnsanswerrecord( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = sizeof( DNSAnswerRecord_t ) + 38;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST + 1 );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST + 1 );
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );

    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore );
    TEST_ASSERT_FALSE( ret );
    TEST_ASSERT_EQUAL( 44, uxBytesRead );
}

BaseType_t xApplicationDNSQueryHook( const char * pcName )
{
    hook_called = pdTRUE;
    return hook_return;
}
