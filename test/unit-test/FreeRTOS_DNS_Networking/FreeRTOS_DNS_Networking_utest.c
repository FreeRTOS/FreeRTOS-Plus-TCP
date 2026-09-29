/*
 * FreeRTOS+TCP
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
/*#include "mock_FreeRTOS_DNS_Cache.h" */
#include "mock_FreeRTOS_DNS_Parser.h"
/* #include "mock_FreeRTOS_DNS_Networking.h"*/
#include "mock_NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"


#include "catch_assert.h"
#include "FreeRTOS_DNS_Networking.h"

#include "FreeRTOSIPConfig.h"

#define LLMNR_ADDRESS     "freertos"
#define GOOD_ADDRESS      "www.freertos.org"
#define BAD_ADDRESS       "this is a bad address"
#define DOTTED_ADDRESS    "192.268.0.1"

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                struct freertos_addrinfo * /* pxAddressInfo */ );

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
 * @brief Ensures that when the socket is invalid, null is returned
 */
void test_CreateSocket_fail_socket( void )
{
    Socket_t s;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET,
                                     FREERTOS_SOCK_DGRAM,
                                     FREERTOS_IPPROTO_UDP,
                                     NULL );
    xSocketValid_ExpectAndReturn( NULL, pdFALSE );

    s = DNS_CreateSocket( 235 );

    TEST_ASSERT_EQUAL( NULL, s );
}

/**
 * @brief Happy path!
 */
void test_CreateSocket_success( void )
{
    Socket_t s;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET,
                                     FREERTOS_SOCK_DGRAM,
                                     FREERTOS_IPPROTO_UDP,
                                     ( Socket_t ) 235 );
    xSocketValid_ExpectAndReturn( ( Socket_t ) 235, pdTRUE );
    FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( 0 );
    FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( 0 );

    s = DNS_CreateSocket( 235 );

    TEST_ASSERT_EQUAL( ( Socket_t ) 235, s );
}

/**
 * @brief  Happy path!
 */
void test_BindSocket_success( void )
{
    struct freertos_sockaddr xAddress;
    struct xSOCKET xSocket;
    uint32_t ret;

    FreeRTOS_bind_ExpectAnyArgsAndReturn( 1 );

    ret = DNS_BindSocket( &xSocket, 80 );

    TEST_ASSERT_EQUAL( 1, ret );
}

/**
 * @brief  Happy path!
 */
void test_SendRequest_success( void )
{
    Socket_t s = ( Socket_t ) 123;
    uint32_t ret;
    struct freertos_sockaddr xAddress;
    struct xDNSBuffer pxDNSBuf;

    pxDNSBuf.uxPayloadLength = 1024;

    FreeRTOS_sendto_ExpectAnyArgsAndReturn( pxDNSBuf.uxPayloadLength );

    ret = DNS_SendRequest( s, &xAddress, &pxDNSBuf );

    TEST_ASSERT_EQUAL( pdTRUE, ret );
}

/**
 * @brief  Ensures that when SendTo fails false is returned
 */
void test_SendRequest_fail( void )
{
    Socket_t s = ( Socket_t ) 123;
    uint32_t ret;
    struct freertos_sockaddr xAddress;
    struct xDNSBuffer pxDNSBuf;

    pxDNSBuf.uxPayloadLength = 1024;
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1023 );

    ret = DNS_SendRequest( s, &xAddress, &pxDNSBuf );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/* Provided by FreeRTOS_DNS_Networking_stubs.c */
extern struct freertos_sockaddr xStubFromAddress;
extern int32_t FreeRTOS_recvfrom_ReturnFromAddress( const ConstSocket_t xSocket,
                                                    void * pvBuffer,
                                                    size_t uxBufferLength,
                                                    BaseType_t xFlags,
                                                    struct freertos_sockaddr * pxSourceAddress,
                                                    socklen_t * pxSourceAddressLength,
                                                    int cmock_num_calls );

/* 203.0.113.7 in network byte order (TEST-NET-3, a stand-in DNS server). */
#define TEST_SERVER_IPv4    FreeRTOS_htonl( 0xCB007107U )
/* 198.51.100.9 in network byte order (a different, "wrong" source). */
#define TEST_WRONG_IPv4     FreeRTOS_htonl( 0xC6336409U )

/**
 * @brief Set up a stubbed reply arriving from ulSourceIPv4, and run
 *        DNS_ReadReply() with the query addressed to *pxTarget.
 */
static BaseType_t prvRunReadReply( const IPv46_Address_t * pxTarget,
                                   uint32_t ulSourceIPv4 )
{
    Socket_t s = ( Socket_t ) 123;
    struct freertos_sockaddr xAddress;
    struct xDNSBuffer pxDNSBuf;

    ( void ) memset( &xStubFromAddress, 0, sizeof( xStubFromAddress ) );
    xStubFromAddress.sin_family = FREERTOS_AF_INET4;
    xStubFromAddress.sin_address.ulIP_IPv4 = ulSourceIPv4;

    xIsCallingFromIPTask_IgnoreAndReturn( pdTRUE );
    FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( 0 );
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_ReturnFromAddress );

    return DNS_ReadReply( s, &xAddress, &pxDNSBuf, pxTarget );
}

/**
 * @brief A reply from the queried server is accepted (both config states).
 */
void test_ReadReply_source_matches_server_accepted( void )
{
    IPv46_Address_t xTarget;
    BaseType_t xReturn;

    ( void ) memset( &xTarget, 0, sizeof( xTarget ) );
    xTarget.xIs_IPv6 = pdFALSE;
    xTarget.xIPAddress.ulIP_IPv4 = TEST_SERVER_IPv4;

    xReturn = prvRunReadReply( &xTarget, TEST_SERVER_IPv4 );

    /* The reply came from the queried server: accepted regardless of the
     * source-IP-check configuration. */
    TEST_ASSERT_EQUAL( 300, xReturn );
}

/**
 * @brief A reply from a DIFFERENT source than the queried server.
 *
 * With ipconfigDNS_CHECK_REPLY_SOURCE_IP enabled this is the poisoning packet
 * the fix must reject. With the check disabled (default) the legacy behaviour
 * of accepting any source is preserved.
 */
void test_ReadReply_source_mismatch( void )
{
    IPv46_Address_t xTarget;
    BaseType_t xReturn;

    ( void ) memset( &xTarget, 0, sizeof( xTarget ) );
    xTarget.xIs_IPv6 = pdFALSE;
    xTarget.xIPAddress.ulIP_IPv4 = TEST_SERVER_IPv4;

    xReturn = prvRunReadReply( &xTarget, TEST_WRONG_IPv4 );

    #if ( ipconfigDNS_CHECK_REPLY_SOURCE_IP == 1 )
        /* Forged/off-path reply from the wrong source is discarded. */
        TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
    #else
        /* Opt-in check disabled: legacy accept-any-source behaviour. */
        TEST_ASSERT_EQUAL( 300, xReturn );
    #endif
}

/**
 * @brief mDNS legacy mode: the query is addressed to the mDNS multicast
 *        address and the responder replies from its own unicast address.
 *        The reply must be accepted even with the source-IP check enabled.
 */
void test_ReadReply_mdns_target_accepts_any_source( void )
{
    IPv46_Address_t xTarget;
    BaseType_t xReturn;

    ( void ) memset( &xTarget, 0, sizeof( xTarget ) );
    xTarget.xIs_IPv6 = pdFALSE;
    xTarget.xIPAddress.ulIP_IPv4 = ipMDNS_IP_ADDRESS;

    /* Responder answers from an arbitrary subnet address. */
    xReturn = prvRunReadReply( &xTarget, TEST_WRONG_IPv4 );

    TEST_ASSERT_EQUAL( 300, xReturn );
}

/**
 * @brief With the source-IP check enabled, a reply whose address family does
 *        not match the queried server cannot have come from it and is rejected.
 *        With the check disabled, it is accepted (legacy behaviour).
 */
void test_ReadReply_wrong_family( void )
{
    Socket_t s = ( Socket_t ) 123;
    struct freertos_sockaddr xAddress;
    struct xDNSBuffer pxDNSBuf;
    IPv46_Address_t xTarget;
    BaseType_t xReturn;

    ( void ) memset( &xTarget, 0, sizeof( xTarget ) );
    xTarget.xIs_IPv6 = pdFALSE;
    xTarget.xIPAddress.ulIP_IPv4 = TEST_SERVER_IPv4;

    /* Reply arrives as IPv6 while an IPv4 server was queried. */
    ( void ) memset( &xStubFromAddress, 0, sizeof( xStubFromAddress ) );
    xStubFromAddress.sin_family = FREERTOS_AF_INET6;

    xIsCallingFromIPTask_IgnoreAndReturn( pdTRUE );
    FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( 0 );
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_ReturnFromAddress );

    xReturn = DNS_ReadReply( s, &xAddress, &pxDNSBuf, &xTarget );

    #if ( ipconfigDNS_CHECK_REPLY_SOURCE_IP == 1 )
        TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
    #else
        TEST_ASSERT_EQUAL( 300, xReturn );
    #endif
}

/**
 * @brief  recvfrom failure/timeout is propagated unchanged.
 */
void test_ReadReply_recvfrom_timeout( void )
{
    Socket_t s = ( Socket_t ) 123;
    struct freertos_sockaddr xAddress;
    struct xDNSBuffer pxDNSBuf;
    IPv46_Address_t xTarget;
    BaseType_t xReturn;

    ( void ) memset( &xTarget, 0, sizeof( xTarget ) );
    xTarget.xIs_IPv6 = pdFALSE;
    xTarget.xIPAddress.ulIP_IPv4 = TEST_SERVER_IPv4;

    xIsCallingFromIPTask_IgnoreAndReturn( pdTRUE );
    FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( 0 );
    FreeRTOS_recvfrom_ExpectAnyArgsAndReturn( -pdFREERTOS_ERRNO_EWOULDBLOCK );

    xReturn = DNS_ReadReply( s, &xAddress, &pxDNSBuf, &xTarget );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EWOULDBLOCK, xReturn );
}

/**
 * @brief  Happy path!
 */
void test_CloseSocket_success( void )
{
    Socket_t s = ( Socket_t ) 123;

    FreeRTOS_closesocket_ExpectAndReturn( s, pdTRUE );

    DNS_CloseSocket( s );
}
