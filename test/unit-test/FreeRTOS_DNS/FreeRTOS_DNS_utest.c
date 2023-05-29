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

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_DNS_Networking.h"
#include "mock_task.h"
#include "mock_list.h"
#include "mock_queue.h"

#include "mock_FreeRTOS_DNS_Callback.h"
#include "mock_FreeRTOS_DNS_Cache.h"
#include "mock_FreeRTOS_DNS_Parser.h"
#include "mock_FreeRTOS_DNS_Networking.h"
#include "mock_NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"


#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"
#include "FreeRTOS_DNS_stubs.c"

/* ===========================  EXTERN VARIABLES  =========================== */

#define LLMNR_ADDRESS     "freertos"
#define GOOD_ADDRESS      "www.freertos.org"
#define BAD_ADDRESS       "this is a bad address"
#define DOTTED_IPV4_ADDRESS    "192.168.0.1"
#define DOTTED_IPV4_ADDRESS_UINT32    ( 0x0100A8C0 )
#define DOTTED_IPv6_ADDRESS    "2001::1"

IPv6_Address_t xIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                struct freertos_addrinfo * /* pxAddressInfo */ );

/* ============================  Unity Fixtures  ============================ */

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
    callback_called = 0;
    isMallocFail = false;
}

/* ============================== Test Cases ============================== */

/**
 * @brief Ensures all corresponding initialisation modules are called
 */
void test_vDNSInitialise( void )
{
    vDNSCallbackInitialise_Expect();
    vDNSInitialise();
}

/**
 * @brief Ensures when a network buffer cannot be allocated a zero is returned
 */
void test_FreeRTOS_gethostbyname_fail_allocate_network_buffer( void )
{
    uint32_t ret;
    NetworkEndPoint_t xEndPoint = { 0 };
    struct xSOCKET xDNSSocket;

    xEndPoint.bits.bIPv6 = 0;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] = 0xC0C0C0C0;
    xEndPoint.ipv4_settings.ucDNSIndex = 0;
    xDNSSocket.usLocalPort = 0;

    DNS_BindSocket_IgnoreAndReturn( 0 );

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 0 );
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );

    DNS_CreateSocket_ExpectAnyArgsAndReturn( &xDNSSocket );
    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    DNS_CloseSocket_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensure that when a NULL address is received a zero is returned
 */
void test_FreeRTOS_gethostbyname_fail_NULL_address( void )
{
    uint32_t ret;

    ret = FreeRTOS_gethostbyname( NULL );
    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensure that when the function receives a long (longer than
 *        ipconfigDNS_CACHE_NAME_LENGTH ) hostname, a zero is returned
 */
void test_FreeRTOS_gethostbyname_fail_long_address( void )
{
    uint32_t ret;
    char address[ ipconfigDNS_CACHE_NAME_LENGTH + 3 ];

    memset( address, 'a', ipconfigDNS_CACHE_NAME_LENGTH );
    address[ ipconfigDNS_CACHE_NAME_LENGTH + 3 ] = '\0';


    ret = FreeRTOS_gethostbyname( address );
    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief Ensures that when the supplied address is in the dotted format, it is
 *        translated to the numerical form and no lookup is performed
 */
void test_FreeRTOS_gethostbyname_success_dot_address( void )
{
    uint32_t ret;

    FreeRTOS_inet_addr_ExpectAndReturn( DOTTED_IPV4_ADDRESS, 12345 );

    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );
    ulChar2u32_IgnoreAndReturn( 12345 );
    ret = FreeRTOS_gethostbyname( DOTTED_IPV4_ADDRESS );
    TEST_ASSERT_EQUAL( 12345, ret );
}

/**
 * @brief Ensures that if the address is not in the dotted form and found in the cache,
 * it is returned to the caller
 */
void test_FreeRTOS_gethostbyname_success_address_in_cache( void )
{
    uint32_t ret;

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 12345 );

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL( 12345, ret );
}


/**
 * @brief Ensures that the code can handle when the client can't create a socket
 */
void test_FreeRTOS_gethostbyname_fail_NULL_socket( void )
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulNumber = 0;

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnThruPtr_pulNumber( &ulNumber );

    DNS_CreateSocket_ExpectAnyArgsAndReturn( NULL );

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief Ensures that when the dns request fails the function returns zero to
 *        the caller
 */
void test_FreeRTOS_gethostbyname_fail_send_dns_request( void )
{
    int i;
    uint32_t ret;
    uint32_t ulNumber = 0;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint = { 0 };
    struct xSOCKET xDNSSocket;

    xEndPoint.bits.bIPv6 = 0;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] = 0xC0C0C0C0;
    xEndPoint.ipv4_settings.ucDNSIndex = 0;
    xNetworkBuffer.xDataLength = 2280;
    xDNSSocket.usLocalPort = 0;

    xNetworkBuffer.pucEthernetBuffer = malloc( 2280 + ipBUFFER_PADDING );
    xNetworkBuffer.pucEthernetBuffer += ipBUFFER_PADDING;

    DNS_BindSocket_IgnoreAndReturn( 0 );
    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnThruPtr_pulNumber( &ulNumber );

    DNS_CreateSocket_ExpectAnyArgsAndReturn( &xDNSSocket );

    /* prvGetHostByNameOp */
    for( i = 0; i < ipconfigDNS_REQUEST_ATTEMPTS; i++ )
    {
        FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
        FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

        /* in prvGetHostByName */
        /* in prvGetPayloadBuffer */
        pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
        /* back in prvGetHostByName */
        /* prvFillSockAddress */
        /* back prvGetHostByNameOp */
        DNS_SendRequest_ExpectAnyArgsAndReturn( pdFAIL );
        vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();
    }

    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL( 0, ret );

    xNetworkBuffer.pucEthernetBuffer -= ipBUFFER_PADDING;
    free( xNetworkBuffer.pucEthernetBuffer );
}

/**
 * @brief Ensures when reading the dns reply fails, the test would try the set
 *        number of times, and return zero to the caller
 */
void test_FreeRTOS_gethostbyname_fail_read_dns_reply_null( void )
{
    uint32_t ret;
    int i;
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct xDNSBuffer xReceiveBuffer;
    NetworkEndPoint_t xEndPoint = { 0 };
    struct xSOCKET xDNSSocket;

    xEndPoint.bits.bIPv6 = 0;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] = 0xC0C0C0C0;
    xEndPoint.ipv4_settings.ucDNSIndex = 0;
    xReceiveBuffer.pucPayloadBuffer = NULL;
    xReceiveBuffer.uxPayloadLength = 0;
    xNetworkBuffer.xDataLength = 2280;
    xNetworkBuffer.pucEthernetBuffer = malloc( 2280 + ipBUFFER_PADDING );
    xNetworkBuffer.pucEthernetBuffer += ipBUFFER_PADDING;
    xDNSSocket.usLocalPort = 0;

    DNS_BindSocket_IgnoreAndReturn( 0 );
    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );
    FreeRTOS_inet_addr_ExpectAndReturn( LLMNR_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 0 );
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );
    DNS_CreateSocket_ExpectAnyArgsAndReturn( &xDNSSocket );

    /* prvGetHostByNameOp */
    /* prvFillSockAddress */
    for( i = 0; i < ipconfigDNS_REQUEST_ATTEMPTS; i++ )
    {
        /* in prvGetHostByName */
        /* in prvGetPayloadBuffer */
        pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
        /* back in prvGetHostByName */
        /* back prvGetHostByNameOp */
        DNS_SendRequest_ExpectAnyArgsAndReturn( pdPASS );

        DNS_ReadReply_ExpectAnyArgsAndReturn( 0 );
        DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    }

    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( LLMNR_ADDRESS );
    TEST_ASSERT_EQUAL( 0, ret );

    xNetworkBuffer.pucEthernetBuffer -= ipBUFFER_PADDING;
    free( xNetworkBuffer.pucEthernetBuffer );
}

/**
 * @brief Ensure that a bad parse of a DNS packet causes the return to be zero
 */
void test_FreeRTOS_gethostbyname_fail_send_dns_reply_zero( void )
{
    int i;
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct xDNSBuffer xReceiveBuffer;
    uint32_t ulNumber = 0;
    NetworkEndPoint_t xEndPoint = { 0 };
    struct xSOCKET xDNSSocket;
    uint8_t pucPayloadBuffer_Arr[ 300 ];

    uint8_t buffer[ 2280 + ipBUFFER_PADDING ];

    xEndPoint.bits.bIPv6 = 0;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] = 0xC0C0C0C0;
    xEndPoint.ipv4_settings.ucDNSIndex = 0;
    xReceiveBuffer.pucPayloadBuffer = pucPayloadBuffer_Arr;
    xReceiveBuffer.uxPayloadLength = 300;
    memset( xReceiveBuffer.pucPayloadBuffer, 0x00, 300 );
    DNSMessage_t * header = ( DNSMessage_t * ) xReceiveBuffer.pucPayloadBuffer;

    header->usIdentifier = 0;

    xNetworkBuffer.xDataLength = 2280;
    xNetworkBuffer.pucEthernetBuffer = buffer;
    xNetworkBuffer.pucEthernetBuffer += ipBUFFER_PADDING;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xDNSSocket.usLocalPort = 0;

    DNS_BindSocket_IgnoreAndReturn( 0 );
    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );
    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnThruPtr_pulNumber( &ulNumber );
    DNS_CreateSocket_ExpectAnyArgsAndReturn( &xDNSSocket );

    /* prvGetHostByNameOp */
    /* prvFillSockAddress */
    for( i = 0; i < ipconfigDNS_REQUEST_ATTEMPTS; i++ )
    {
        pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
        /* back prvGetHostByNameOp */
        DNS_SendRequest_ExpectAnyArgsAndReturn( pdPASS );
        DNS_ReadReply_ExpectAnyArgsAndReturn( 0 );
        DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );

        FreeRTOS_ReleaseUDPPayloadBuffer_ExpectAnyArgs();
    }

    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL( 0, ret );

    xNetworkBuffer.pucEthernetBuffer -= ipBUFFER_PADDING;
}

/**
 * @brief Successful case, Ensures that the parsed DNS packet's IP address is
 *        returned to the caller
 */
void test_FreeRTOS_gethostbyname_succes( void )
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct xDNSBuffer xReceiveBuffer;
    uint32_t ulNumber = 343;
    NetworkEndPoint_t xEndPoint = { 0 };
    struct xSOCKET xDNSSocket;

    uint8_t buffer[ 2280 + ipBUFFER_PADDING ];

    xEndPoint.bits.bIPv6 = 0;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] = 0xC0C0C0C0;
    xEndPoint.ipv4_settings.ucDNSIndex = 0;
    xReceiveBuffer.pucPayloadBuffer = malloc( 300 );
    xReceiveBuffer.uxPayloadLength = 300;
    memset( xReceiveBuffer.pucPayloadBuffer, 0x00, 300 );
    DNSMessage_t * header = ( DNSMessage_t * ) xReceiveBuffer.pucPayloadBuffer;

    header->usIdentifier = 0;
    xDNSSocket.usLocalPort = 0;

    xNetworkBuffer.xDataLength = 2280;
    xNetworkBuffer.pucEthernetBuffer = buffer;
    xNetworkBuffer.pucEthernetBuffer += ipBUFFER_PADDING;
    memset( xNetworkBuffer.pucEthernetBuffer, 0x00, 2280 );

    DNS_BindSocket_IgnoreAndReturn( 0 );
    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnThruPtr_pulNumber( &ulNumber );

    DNS_CreateSocket_ExpectAnyArgsAndReturn( &xDNSSocket );
    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */
    /* prvGetHostByNameOp */
    /*FreeRTOS_GetAddressConfiguration_ExpectAnyArgs(); */
    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    /* prvFillSockAddress */
    /* back prvGetHostByNameOp */
    DNS_SendRequest_ExpectAnyArgsAndReturn( pdPASS );
    DNS_ReadReply_ExpectAnyArgsAndReturn( 4 );
    DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    /* prvDNSReply */
    DNS_ParseDNSReply_ExpectAnyArgsAndReturn( 12345 );
    FreeRTOS_ReleaseUDPPayloadBuffer_ExpectAnyArgs();

    /* back in prvGetHostByName */
    DNS_CloseSocket_Ignore();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL( 12345, ret );

    xNetworkBuffer.pucEthernetBuffer -= ipBUFFER_PADDING;
    free( xReceiveBuffer.pucPayloadBuffer );
}

/**
 * @brief Ensures that DNS_ParseDNSReply is called, this function always returns
 *        pdFAIL
 * @warning Function not really tested besides code coverage
 */
void test_ulDNSHandlePacket_success( void )
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t );
    xNetworkBuffer.pucEthernetBuffer = malloc( sizeof( UDPPacket_t ) +
                                               sizeof( DNSMessage_t ) );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    DNS_ParseDNSReply_ExpectAnyArgsAndReturn( 0 );

    ret = ulDNSHandlePacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ret );
    free( xNetworkBuffer.pucEthernetBuffer );
}

/**
 * @brief This function always returns pdFAIL
 * @warning Function not really tested besides code coverage
 */
void test_ulDNSHandlePacket_fail_small_buffer( void )
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) - 2;
    xNetworkBuffer.pucEthernetBuffer = malloc( sizeof( UDPPacket_t ) - 2 );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    ret = ulDNSHandlePacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ret );
    free( xNetworkBuffer.pucEthernetBuffer );
}

/**
 * @brief Always returns pdFAIL, trying different scenarios to have move
 *        coverage
 * @warning Function not really tested besides code coverage
 */
void test_ulDNSHandlePacket_fail_small_buffer2( void )
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 2;
    xNetworkBuffer.pucEthernetBuffer = malloc( sizeof( UDPPacket_t ) + 2 );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    ret = ulDNSHandlePacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ret );
    free( xNetworkBuffer.pucEthernetBuffer );
}

/**
 * @brief Functions always returns pdFAIL
 * @warning Function not really tested besides code coverage
 */
void test_ulNBNSHandlePacket_success( void )
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;
    size_t uxBytesNeeded = sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t );

    xNetworkBuffer.xDataLength = uxBytesNeeded;
    xNetworkBuffer.pucEthernetBuffer = malloc( uxBytesNeeded );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    DNS_TreatNBNS_ExpectAnyArgs();

    ret = ulNBNSHandlePacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ret );
    free( xNetworkBuffer.pucEthernetBuffer );
}

/**
 * @brief Functions always returns pdFAIL
 * @warning Function not really tested besides code coverage
 */
void test_ulNBNSHandlePacket_fail_small_buffer( void )
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;
    size_t uxBytesNeeded = sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t );

    xNetworkBuffer.xDataLength = uxBytesNeeded - 5;
    xNetworkBuffer.pucEthernetBuffer = malloc( uxBytesNeeded - 5 );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    ret = ulNBNSHandlePacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ret );

    free( xNetworkBuffer.pucEthernetBuffer );
}

/**
 * @brief Ensures that vDNSCheckCallback is called
 */
void test_FreeRTOS_gethostbyname_cancel_success( void )
{
    void * pvSearchID = NULL;

    vDNSCheckCallBack_ExpectAnyArgs();
    FreeRTOS_gethostbyname_cancel( pvSearchID );
}


/**
 * @brief Ensures that if pCallback is not null and the hostname is not in the
 *        cache, the application support random number generation,
 *        the callback function is set
 */
void test_FreeRTOS_gethostbyname_a_set_callback( void )
{
    uint32_t ret;
    int pvSearchID = 32;
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct xSOCKET xDNSSocket;

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 0 );
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );
    vDNSSetCallBack_ExpectAnyArgs();
    DNS_CreateSocket_ExpectAnyArgsAndReturn( NULL );

    ret = FreeRTOS_gethostbyname_a( GOOD_ADDRESS,
                                    dns_callback,
                                    &pvSearchID,
                                    0 );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 0, callback_called );
}

/**
 * @brief Ensures that if the application has no random number generation
 *        support, and ip is zero, no action is performed
 */
void test_FreeRTOS_gethostbyname_a_no_set_callback( void )
{
    uint32_t ret;
    int pvSearchID = 32;
    NetworkBufferDescriptor_t xNetworkBuffer;

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 0 );
    xApplicationGetRandomNumber_IgnoreAndReturn( pdFALSE );

    ret = FreeRTOS_gethostbyname_a( GOOD_ADDRESS,
                                    dns_callback,
                                    &pvSearchID,
                                    0 );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 0, callback_called );
}


/**
 * @brief Ensures that if the function receives a callback, and ip address is
 *        not zero, the callback is called
 */
void test_FreeRTOS_gethostbyname_a_callback( void )
{
    uint32_t ret;
    int pvSearchID = 32;

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 5 );
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );

    ret = FreeRTOS_gethostbyname_a( GOOD_ADDRESS,
                                    dns_callback,
                                    &pvSearchID,
                                    0 );
    TEST_ASSERT_EQUAL( 5, ret );
    TEST_ASSERT_EQUAL( 1, callback_called );
}

/**
 * @brief Ensures that if vDNSSetCallBack is called the client is put in
 *        asynchronous mode, and only one retry is performed by calling
 *        prvGetHostByNameOp instead of prvGetHostByNameOp_WithRetry
 */
void test_FreeRTOS_gethostbyname_a_no_callback_retry_once( void )
{
    uint32_t ret;
    uint32_t ulNumber = 34;
    int pvSearchID = 32;
    NetworkEndPoint_t xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct xDNSBuffer xReceiveBuffer;
    struct xSOCKET xDNSSocket;
    size_t uxBytesNeeded = sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t );

    xNetworkBuffer.pucEthernetBuffer = malloc( uxBytesNeeded + ipBUFFER_PADDING );
    xNetworkBuffer.pucEthernetBuffer += ipBUFFER_PADDING;
    xNetworkBuffer.xDataLength = uxBytesNeeded;
    xReceiveBuffer.pucPayloadBuffer = malloc( 300 );
    xReceiveBuffer.uxPayloadLength = 300;
    ( void ) memset( xNetworkBuffer.pucEthernetBuffer, 0x00, uxBytesNeeded );
    ( void ) memset( xReceiveBuffer.pucPayloadBuffer, 0x00, 300 );
    DNSMessage_t * header = ( DNSMessage_t * ) xReceiveBuffer.pucPayloadBuffer;

    header->usIdentifier = 12;
    xDNSSocket.usLocalPort = 0;
    xEndPoint.bits.bIPv6 = pdFALSE;
    xEndPoint.ipv4_settings.ucDNSIndex = 0;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] = 0xC0C0C0C0;

    DNS_BindSocket_IgnoreAndReturn( 0 );
    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnThruPtr_pulNumber( &ulNumber );
    vDNSSetCallBack_ExpectAnyArgs();

    /* in prvGetHostByName */
    DNS_CreateSocket_ExpectAnyArgsAndReturn( &xDNSSocket );
    /* prvGetHostByNameOp */
    /* prvFillSockAddress */
    /* in prvSendBuffer */
    /* in prvGetPayloadBuffer */

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );

    /* back in prvSendBuffer */
    DNS_SendRequest_ExpectAnyArgsAndReturn( pdPASS );

    /* back in prvGetHostByNameOp */
    DNS_ReadReply_ExpectAnyArgsAndReturn( 4 );
    DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    /* prvDNSReply */
    DNS_ParseDNSReply_ExpectAnyArgsAndReturn( 12345 );
    FreeRTOS_ReleaseUDPPayloadBuffer_ExpectAnyArgs();

    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname_a( GOOD_ADDRESS,
                                    dns_callback,
                                    &pvSearchID,
                                    0 );
    TEST_ASSERT_EQUAL( 12345, ret );
    TEST_ASSERT_EQUAL( 0, callback_called );

    free( xNetworkBuffer.pucEthernetBuffer - ipBUFFER_PADDING );
    free( xReceiveBuffer.pucPayloadBuffer );
}

/**
 * @brief NULL input
 */
void test_FreeRTOS_getaddrinfo_NullInput( void )
{
    BaseType_t xReturn;

    xReturn = FreeRTOS_getaddrinfo( "Domain", "Service", NULL, NULL );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Unknown family in preferences
 */
void test_FreeRTOS_getaddrinfo_a_UnknownHintFamily( void )
{
    BaseType_t xReturn;
    struct freertos_addrinfo xAddress, * pxAddress = &xAddress;
    struct freertos_addrinfo xHint, * pxHint = &xHint;

    memset( &xAddress, 0, sizeof( struct freertos_addrinfo ) );
    memset( &xHint, 0, sizeof( struct freertos_addrinfo ) );

    xHint.ai_family = FREERTOS_AF_INET6 + 1;

    xReturn = FreeRTOS_getaddrinfo_a( GOOD_ADDRESS, "Service", pxHint, &pxAddress, dns_callback, NULL, 0U );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxAddress );
}

/**
 * @brief IP address found with IPv4 address input
 */
void test_FreeRTOS_getaddrinfo_a_IPv4AddressFound( void )
{
    BaseType_t xReturn;
    struct freertos_addrinfo xAddress, * pxAddress = &xAddress;
    struct freertos_addrinfo xHint, * pxHint = &xHint;

    memset( &xAddress, 0, sizeof( struct freertos_addrinfo ) );
    memset( &xHint, 0, sizeof( struct freertos_addrinfo ) );

    xHint.ai_family = FREERTOS_AF_INET4;

    FreeRTOS_inet_addr_ExpectAndReturn( DOTTED_IPV4_ADDRESS, DOTTED_IPV4_ADDRESS_UINT32 );
    ulChar2u32_IgnoreAndReturn( DOTTED_IPV4_ADDRESS_UINT32 );

    xReturn = FreeRTOS_getaddrinfo_a( DOTTED_IPV4_ADDRESS, "Service", pxHint, &pxAddress, dns_callback, NULL, 0U );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 1, callback_called );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET4, pxAddress->ai_family );
    TEST_ASSERT_EQUAL( DOTTED_IPV4_ADDRESS_UINT32, FreeRTOS_htonl( pxAddress->ai_addr->sin_address.ulIP_IPv4 ) );
    TEST_ASSERT_EQUAL( ipSIZE_OF_IPv4_ADDRESS, pxAddress->ai_addrlen );
}

/**
 * @brief IP address found with IPv6 address input
 */
void test_FreeRTOS_getaddrinfo_a_IPv6AddressFound( void )
{
    BaseType_t xReturn;
    struct freertos_addrinfo xAddress, * pxAddress = &xAddress;
    struct freertos_addrinfo xHint, * pxHint = &xHint;

    memset( &xAddress, 0, sizeof( struct freertos_addrinfo ) );
    memset( &xHint, 0, sizeof( struct freertos_addrinfo ) );

    xHint.ai_family = FREERTOS_AF_INET6;

    FreeRTOS_inet_pton6_ExpectAndReturn( DOTTED_IPv6_ADDRESS, NULL, 1 );
    FreeRTOS_inet_pton6_IgnoreArg_pvDestination();
    FreeRTOS_inet_pton6_ReturnMemThruPtr_pvDestination( &xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xReturn = FreeRTOS_getaddrinfo_a( DOTTED_IPv6_ADDRESS, "Service", pxHint, &pxAddress, dns_callback, NULL, 0U );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 1, callback_called );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, pxAddress->ai_family );
    TEST_ASSERT_EQUAL_MEMORY( xIPv6Address.ucBytes, pxAddress->ai_addr->sin_address.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( ipSIZE_OF_IPv6_ADDRESS, pxAddress->ai_addrlen );
}

/**
 * @brief IP address found with IPv4 domain input
 */
void test_FreeRTOS_getaddrinfo_a_IPv4DomainCacheFound( void )
{
    BaseType_t xReturn;
    struct freertos_addrinfo xAddress, * pxAddress = &xAddress;
    struct freertos_addrinfo xExpectedAddress, * pxExpectedAddress = &xExpectedAddress;

    memset( &xAddress, 0, sizeof( struct freertos_addrinfo ) );
    memset( &xExpectedAddress, 0, sizeof( struct freertos_addrinfo ) );

    xExpectedAddress.ai_family = FREERTOS_AF_INET4;

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAndReturn( GOOD_ADDRESS, FREERTOS_AF_INET4, &pxAddress, DOTTED_IPV4_ADDRESS_UINT32 );
    Prepare_CacheLookup_ReturnMemThruPtr_ppxAddressInfo( &pxExpectedAddress, sizeof( struct freertos_addrinfo ) );

    xReturn = FreeRTOS_getaddrinfo_a( GOOD_ADDRESS, "Service", NULL, &pxAddress, dns_callback, NULL, 0U );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 1, callback_called );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET4, pxAddress->ai_family );
}

/**
 * @brief IP address found with IPv6 domain input
 */
void test_FreeRTOS_getaddrinfo_a_IPv6DomainCacheFound( void )
{
    BaseType_t xReturn;
    struct freertos_addrinfo xAddress, * pxAddress = &xAddress;
    struct freertos_addrinfo xExpectedAddress, * pxExpectedAddress = &xExpectedAddress;
    struct freertos_addrinfo xHint, * pxHint = &xHint;

    memset( &xAddress, 0, sizeof( struct freertos_addrinfo ) );
    memset( &xHint, 0, sizeof( struct freertos_addrinfo ) );
    memset( &xExpectedAddress, 0, sizeof( struct freertos_addrinfo ) );

    xHint.ai_family = FREERTOS_AF_INET6;

    xExpectedAddress.ai_family = FREERTOS_AF_INET6;

    FreeRTOS_inet_pton6_ExpectAndReturn( GOOD_ADDRESS, NULL, 0 );
    FreeRTOS_inet_pton6_IgnoreArg_pvDestination();
    Prepare_CacheLookup_ExpectAndReturn( GOOD_ADDRESS, FREERTOS_AF_INET6, &pxAddress, 1 );
    Prepare_CacheLookup_ReturnThruPtr_ppxAddressInfo( &pxExpectedAddress );

    xReturn = FreeRTOS_getaddrinfo_a( GOOD_ADDRESS, "Service", pxHint, &pxAddress, dns_callback, NULL, 0U );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 1, callback_called );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, pxAddress->ai_family );
}

/**
 * @brief IP address not found with IPv4 domain input. But we get unique identifier from random.
 */
void test_FreeRTOS_getaddrinfo_a_IPv4DomainCacheMiss_Random( void )
{
    BaseType_t xReturn;
    struct freertos_addrinfo xAddress, * pxAddress = &xAddress;
    uint32_t ulRandom = 0x1234U;

    memset( &xAddress, 0, sizeof( struct freertos_addrinfo ) );

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAndReturn( GOOD_ADDRESS, FREERTOS_AF_INET4, &pxAddress, 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnMemThruPtr_pulNumber( &ulRandom, sizeof( uint32_t ) );
    vDNSSetCallBack_Expect( GOOD_ADDRESS, NULL, dns_callback, 0U, ulRandom, pdFALSE );
    DNS_CreateSocket_ExpectAndReturn( 0U, NULL );

    xReturn = FreeRTOS_getaddrinfo_a( GOOD_ADDRESS, "Service", NULL, &pxAddress, dns_callback, NULL, 0U );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOENT, xReturn );
}

/**
 * @brief IP address not found with IPv6 domain input. But we get unique identifier from random.
 */
void test_FreeRTOS_getaddrinfo_a_IPv6DomainCacheMiss_Random( void )
{
    BaseType_t xReturn;
    struct freertos_addrinfo xAddress, * pxAddress = &xAddress;
    struct freertos_addrinfo xHint, * pxHint = &xHint;
    uint32_t ulRandom = 0x1234U;

    memset( &xAddress, 0, sizeof( struct freertos_addrinfo ) );
    memset( &xHint, 0, sizeof( struct freertos_addrinfo ) );

    xHint.ai_family = FREERTOS_AF_INET6;

    FreeRTOS_inet_pton6_ExpectAndReturn( GOOD_ADDRESS, NULL, 0 );
    FreeRTOS_inet_pton6_IgnoreArg_pvDestination();
    Prepare_CacheLookup_ExpectAndReturn( GOOD_ADDRESS, FREERTOS_AF_INET6, &pxAddress, 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnMemThruPtr_pulNumber( &ulRandom, sizeof( uint32_t ) );
    vDNSSetCallBack_Expect( GOOD_ADDRESS, NULL, dns_callback, 0U, ulRandom, pdTRUE );
    DNS_CreateSocket_ExpectAndReturn( 0U, NULL );

    xReturn = FreeRTOS_getaddrinfo_a( GOOD_ADDRESS, "Service", pxHint, &pxAddress, dns_callback, NULL, 0U );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOENT, xReturn );
}

/**
 * @brief IP address found with IPv4 domain input but the address returned is NULL.
 */
void test_FreeRTOS_getaddrinfo_a_IPv4DomainCacheFoundButNull( void )
{
    BaseType_t xReturn;
    struct freertos_addrinfo xAddress, * pxAddress = &xAddress;
    struct freertos_addrinfo xExpectedAddress, * pxExpectedAddress = &xExpectedAddress;

    memset( &xAddress, 0, sizeof( struct freertos_addrinfo ) );
    memset( &xExpectedAddress, 0, sizeof( struct freertos_addrinfo ) );

    xExpectedAddress.ai_family = FREERTOS_AF_INET4;

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAndReturn( GOOD_ADDRESS, FREERTOS_AF_INET4, &pxAddress, DOTTED_IPV4_ADDRESS_UINT32 );

    xReturn = FreeRTOS_getaddrinfo_a( GOOD_ADDRESS, "Service", NULL, &pxAddress, dns_callback, NULL, 0U );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOMEM, xReturn );
}

/**
 * @brief No memory available for malloc.
 */
void test_pxNew_AddrInfo_MallocFail( void )
{
    struct freertos_addrinfo * pxAddress;

    isMallocFail = true;

    pxAddress = pxNew_AddrInfo( GOOD_ADDRESS, FREERTOS_AF_INET4, NULL );

    TEST_ASSERT_EQUAL( NULL, pxAddress );
}

/**
 * @brief Unknown family input.
 */
void test_pxNew_AddrInfo_UnknownFamily( void )
{
    struct freertos_addrinfo * pxAddress;

    pxAddress = pxNew_AddrInfo( GOOD_ADDRESS, FREERTOS_AF_INET4 + 1, NULL );

    TEST_ASSERT_EQUAL( NULL, pxAddress );
}

/**
 * @brief Input with NULL pointer.
 */
void test_FreeRTOS_freeaddrinfo_NullInput( void )
{
    FreeRTOS_freeaddrinfo( NULL );
}
