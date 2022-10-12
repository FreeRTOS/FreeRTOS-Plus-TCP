/*
 * FreeRTOS+TCP V3.1.0
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
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
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

#define LLMNR_ADDRESS     "freertos"
#define GOOD_ADDRESS      "www.freertos.org"
#define BAD_ADDRESS       "this is a bad address"
#define DOTTED_ADDRESS    "192.268.0.1"

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                uint32_t /* ulIPAddress */ );

/* ===========================   GLOBAL VARIABLES =========================== */
static int callback_called = 0;


/* ===========================  STATIC FUNCTIONS  =========================== */
static void dns_callback( const char * pcName,
                          void * pvSearchID,
                          uint32_t ulIPAddress )
{
    callback_called = 1;
}


/* ============================  TEST FIXTURES  ============================= */

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
    callback_called = 0;
}

/**
 * @brief calls at the end of each test case
 */
void tearDown( void )
{
}

/* =============================  TEST CASES  =============================== */

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

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    FreeRTOS_dnslookup_ExpectAndReturn( GOOD_ADDRESS, 0 );
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );

    DNS_CreateSocket_ExpectAnyArgsAndReturn( ( void * ) 23 );
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
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

    FreeRTOS_inet_addr_ExpectAndReturn( DOTTED_ADDRESS, 12345 );
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );

    ret = FreeRTOS_gethostbyname( DOTTED_ADDRESS );
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
    FreeRTOS_dnslookup_ExpectAndReturn( GOOD_ADDRESS, 12345 );

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
    FreeRTOS_dnslookup_ExpectAndReturn( GOOD_ADDRESS, 0 );
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

    xNetworkBuffer.xDataLength = 2280;
    xNetworkBuffer.pucEthernetBuffer = malloc( 2280 );

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    FreeRTOS_dnslookup_ExpectAndReturn( GOOD_ADDRESS, 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnThruPtr_pulNumber( &ulNumber );

    DNS_CreateSocket_ExpectAnyArgsAndReturn( ( void * ) 23 );

    /* prvGetHostByNameOp */
    for( i = 0; i < ipconfigDNS_REQUEST_ATTEMPTS; i++ )
    {
        FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
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

    xReceiveBuffer.pucPayloadBuffer = NULL;
    xReceiveBuffer.uxPayloadLength = 0;
    xNetworkBuffer.xDataLength = 2280;
    xNetworkBuffer.pucEthernetBuffer = malloc( 2280 );

    FreeRTOS_inet_addr_ExpectAndReturn( LLMNR_ADDRESS, 0 );
    FreeRTOS_dnslookup_ExpectAndReturn( LLMNR_ADDRESS, 0 );
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );
    DNS_CreateSocket_ExpectAnyArgsAndReturn( ( void * ) 23 );

    /* prvGetHostByNameOp */
    /* prvFillSockAddress */
    for( i = 0; i < ipconfigDNS_REQUEST_ATTEMPTS; i++ )
    {
        FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
        /* in prvGetHostByName */
        /* in prvGetPayloadBuffer */
        pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
        /* back in prvGetHostByName */
        /* back prvGetHostByNameOp */
        DNS_SendRequest_ExpectAnyArgsAndReturn( pdPASS );

        DNS_ReadReply_ExpectAnyArgs();
        DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    }

    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( LLMNR_ADDRESS );
    TEST_ASSERT_EQUAL( 0, ret );

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

    xReceiveBuffer.pucPayloadBuffer = malloc( 300 );
    xReceiveBuffer.uxPayloadLength = 300;
    memset( xReceiveBuffer.pucPayloadBuffer, 0x00, 300 );
    DNSMessage_t * header = ( DNSMessage_t * ) xReceiveBuffer.pucPayloadBuffer;
    header->usIdentifier = 0;

    xNetworkBuffer.xDataLength = 2280;
    xNetworkBuffer.pucEthernetBuffer = malloc( 2280 );

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    FreeRTOS_dnslookup_ExpectAndReturn( GOOD_ADDRESS, 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnThruPtr_pulNumber( &ulNumber );
    DNS_CreateSocket_ExpectAnyArgsAndReturn( ( void * ) 23 );

    /* prvGetHostByNameOp */
    /* prvFillSockAddress */
    for( i = 0; i < ipconfigDNS_REQUEST_ATTEMPTS; i++ )
    {
        /* in prvGetHostByName */
        /* in prvGetPayloadBuffer */
        /* back in prvGetHostByName */
        FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
        pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
        /* back prvGetHostByNameOp */
        DNS_SendRequest_ExpectAnyArgsAndReturn( pdPASS );
        DNS_ReadReply_ExpectAnyArgs();
        DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
        /* prvDNSReply */
        DNS_ParseDNSReply_ExpectAnyArgsAndReturn( 0 );
        FreeRTOS_ReleaseUDPPayloadBuffer_ExpectAnyArgs();
    }

    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL( 0, ret );

    free( xReceiveBuffer.pucPayloadBuffer );
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

    xReceiveBuffer.pucPayloadBuffer = malloc( 300 );
    xReceiveBuffer.uxPayloadLength = 300;
    memset( xReceiveBuffer.pucPayloadBuffer, 0x00, 300 );
    DNSMessage_t * header = ( DNSMessage_t * ) xReceiveBuffer.pucPayloadBuffer;
    header->usIdentifier = 0;

    xNetworkBuffer.xDataLength = 2280;
    xNetworkBuffer.pucEthernetBuffer = malloc( 2280 );
    memset( xNetworkBuffer.pucEthernetBuffer, 0x00, 2280 );

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    FreeRTOS_dnslookup_ExpectAndReturn( GOOD_ADDRESS, 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnThruPtr_pulNumber( &ulNumber );

    DNS_CreateSocket_ExpectAnyArgsAndReturn( ( void * ) 23 );
    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */
    /* prvGetHostByNameOp */
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    /* prvFillSockAddress */
    /* back prvGetHostByNameOp */
    DNS_SendRequest_ExpectAnyArgsAndReturn( pdPASS );
    DNS_ReadReply_ExpectAnyArgs();
    DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    /* prvDNSReply */
    DNS_ParseDNSReply_ExpectAnyArgsAndReturn( 12345 );
    FreeRTOS_ReleaseUDPPayloadBuffer_ExpectAnyArgs();

    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL( 12345, ret );

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

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    FreeRTOS_dnslookup_ExpectAndReturn( GOOD_ADDRESS, 0 );
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
    FreeRTOS_dnslookup_ExpectAndReturn( GOOD_ADDRESS, 0 );
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
    FreeRTOS_dnslookup_ExpectAndReturn( GOOD_ADDRESS, 5 );
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
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct xDNSBuffer xReceiveBuffer;
    size_t uxBytesNeeded = sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t );

    xNetworkBuffer.pucEthernetBuffer = malloc( uxBytesNeeded );
    xNetworkBuffer.xDataLength = uxBytesNeeded;
    xReceiveBuffer.pucPayloadBuffer = malloc( 300 );
    xReceiveBuffer.uxPayloadLength = 300;
    ( void ) memset( xNetworkBuffer.pucEthernetBuffer, 0x00, uxBytesNeeded );
    ( void ) memset( xReceiveBuffer.pucPayloadBuffer, 0x00, 300 );
    DNSMessage_t * header = ( DNSMessage_t * ) xReceiveBuffer.pucPayloadBuffer;
    header->usIdentifier = 12;

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    FreeRTOS_dnslookup_ExpectAndReturn( GOOD_ADDRESS, 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnThruPtr_pulNumber( &ulNumber );
    vDNSSetCallBack_ExpectAnyArgs();

    /* in prvGetHostByName */
    DNS_CreateSocket_ExpectAnyArgsAndReturn( ( void * ) 23 );
    /* prvGetHostByNameOp */
    /* prvFillSockAddress */
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
    /* in prvSendBuffer */
    /* in prvGetPayloadBuffer */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );

    /* back in prvSendBuffer */
    DNS_SendRequest_ExpectAnyArgsAndReturn( pdPASS );

    /* back in prvGetHostByNameOp */
    DNS_ReadReply_ExpectAnyArgs();
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

    free( xNetworkBuffer.pucEthernetBuffer );
    free( xReceiveBuffer.pucPayloadBuffer );
}
