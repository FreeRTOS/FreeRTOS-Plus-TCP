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
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_BitConfig.h"
#include "mock_FreeRTOS_Sockets.h"

/*#include "FreeRTOS_IP_stubs.c" */
#include "catch_assert.h"

#include "FreeRTOS_DHCPv6.h"
#include "FreeRTOS_DHCPv6_stubs.c"

/* ===========================  EXTERN VARIABLES  =========================== */

#define TEST_DHCPV6_TRANSACTION_ID    ( 0x123456 )
static uint8_t ucTestDHCPv6TransactionID[ 3 ] = { 0x12, 0x34, 0x56 };

const uint8_t ucDefaultMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };
const IPv6_Address_t xDefaultNetPrefix = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };

Socket_t xStubFreeRTOS_setsockopt_xSocket;
size_t xStubFreeRTOS_setsockopt_uxOptionLength;
int32_t xStubFreeRTOS_setsockopt_lOptionName_BitMap;
FreeRTOS_Socket_t * xStubvSocketBind_pxSocket;

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
    InitializeUnitTest();
}

/*! called after each test case */
void tearDown( void )
{
}

/* ======================== Stub Callback Functions ========================= */

void prvSetCheckerAndReturn_FreeRTOS_setsockopt( Socket_t xSocket,
                                                 size_t uxOptionLength )
{
    xStubFreeRTOS_setsockopt_xSocket = xSocket;
    xStubFreeRTOS_setsockopt_uxOptionLength = uxOptionLength;
    xStubFreeRTOS_setsockopt_lOptionName_BitMap = 0;
}

BaseType_t xStubFreeRTOS_setsockopt( Socket_t xSocket,
                                     int32_t lLevel,
                                     int32_t lOptionName,
                                     const void * pvOptionValue,
                                     size_t uxOptionLength,
                                     int NumCalls )
{
    TEST_ASSERT_EQUAL( xStubFreeRTOS_setsockopt_xSocket, xSocket );
    TEST_ASSERT_EQUAL( xStubFreeRTOS_setsockopt_uxOptionLength, uxOptionLength );

    xStubFreeRTOS_setsockopt_lOptionName_BitMap |= ( 1 << lOptionName );

    return pdTRUE;
}

void prvSetCheckerAndReturn_vSocketBind( FreeRTOS_Socket_t * pxSocket )
{
    xStubvSocketBind_pxSocket = pxSocket;
}

BaseType_t xStubvSocketBind( FreeRTOS_Socket_t * pxSocket,
                             struct freertos_sockaddr * pxBindAddress,
                             size_t uxAddressLength,
                             BaseType_t xInternal,
                             int NumCalls )
{
    TEST_ASSERT_EQUAL( xStubvSocketBind_pxSocket, pxSocket );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, pxBindAddress->sin_family );
    TEST_ASSERT_EQUAL( sizeof( struct freertos_sockaddr ), pxBindAddress->sin_len );
    TEST_ASSERT_EQUAL( ipDHCPv6_CLIENT_PORT, FreeRTOS_ntohs( pxBindAddress->sin_port ) );
    TEST_ASSERT_EQUAL( pdFALSE, xInternal );

    return 0;
}

BaseType_t xStubxApplicationGetRandomNumber( uint32_t * pulNumber,
                                             int NumCalls )
{
    if( pulNumber != NULL )
    {
        *pulNumber = 0xFF000000 | TEST_DHCPV6_TRANSACTION_ID;
    }

    return pdPASS;
}

void xStubvBitConfig_write_8_solicit( BitConfig_t * pxConfig,
                                      uint8_t ucValue,
                                      int NumCalls )
{
    enum eCall
    {
        eCallMsgTypeSolicit = 0,
        eCallIPv6PrefixLength
    };

    switch( NumCalls )
    {
        case eCallMsgTypeSolicit:
            TEST_ASSERT_EQUAL( DHCPv6_message_Type_Solicit, ucValue );
            break;

        case eCallIPv6PrefixLength:
            TEST_ASSERT_EQUAL( 64, ucValue );
            break;

        default:
            TEST_ASSERT_TRUE( false );
            break;
    }
}

void xStubvBitConfig_write_16_solicit( BitConfig_t * pxConfig,
                                       uint16_t usValue,
                                       int NumCalls )
{
    enum eCall
    {
        eCallOptionClientID = 0,
        eCallOptionClientIDLength,
        eCallOptionClientIDDUIDType,
        eCallOptionClientIDHWType,
        eCallOptionElapsedTime,
        eCallOptionElapsedTimeLength,
        eCallOptionElapsedTimeValue,
        eCallOptionIAPD,
        eCallOptionIAPDLength,
        eCallOptionIAPrefix,
        eCallOptionIAPrefixLength,
        eCallOptionIANA,
        eCallOptionIANALength,
    };

    switch( NumCalls )
    {
        case eCallOptionClientID:
            TEST_ASSERT_EQUAL( DHCPv6_Option_Client_Identifier, usValue );
            break;

        case eCallOptionClientIDLength:
            /* Length of client ID. */
            TEST_ASSERT_EQUAL( 14, usValue );
            break;

        case eCallOptionClientIDDUIDType:
            /* DUID type (Link Layer address + time) of client ID. */
            TEST_ASSERT_EQUAL( 1, usValue );
            break;

        case eCallOptionClientIDHWType:
            /* Hardware type (Ethernet) of client ID. */
            TEST_ASSERT_EQUAL( 1, usValue );
            break;

        case eCallOptionElapsedTime:
            TEST_ASSERT_EQUAL( DHCPv6_Option_Elapsed_Time, usValue );
            break;

        case eCallOptionElapsedTimeLength:
            TEST_ASSERT_EQUAL( 2, usValue );
            break;

        case eCallOptionElapsedTimeValue:
            TEST_ASSERT_EQUAL( 0x0000, usValue );
            break;

        case eCallOptionIAPD:
            TEST_ASSERT_EQUAL( DHCPv6_Option_IA_for_Prefix_Delegation, usValue );
            break;

        case eCallOptionIAPDLength:
            TEST_ASSERT_EQUAL( 41, usValue );
            break;

        case eCallOptionIAPrefix:
            TEST_ASSERT_EQUAL( DHCPv6_Option_IA_Prefix, usValue );
            break;

        case eCallOptionIAPrefixLength:
            TEST_ASSERT_EQUAL( 25, usValue );
            break;

        case eCallOptionIANA:
            TEST_ASSERT_EQUAL( DHCPv6_Option_NonTemporaryAddress, usValue );
            break;

        case eCallOptionIANALength:
            TEST_ASSERT_EQUAL( 12, usValue );
            break;

        default:
            TEST_ASSERT_TRUE( false );
            break;
    }
}

void xStubvBitConfig_write_32_solicit( BitConfig_t * pxConfig,
                                       uint32_t ulValue,
                                       int NumCalls )
{
    enum eCall
    {
        eCallTimeStamp = 0,
        eCallIAPDIAID,
        eCallIAPDTime1,
        eCallIAPDTime2,
        eCallIAPrefixPreferLifeTime,
        eCallIAPrefixValidLifeTime,
        eCallIANAIAID,
        eCallIANAPreferLifeTime,
        eCallIANAPrefixValidLifeTime
    };

    switch( NumCalls )
    {
        case eCallTimeStamp:
            break;

        case eCallIAPDIAID:
        case eCallIANAIAID:
            /* IAID is hardcoded to 0x27fe8f95. */
            TEST_ASSERT_EQUAL( 0x27fe8f95, ulValue );
            break;

        case eCallIAPDTime1:
            /* Time 1. */
            TEST_ASSERT_EQUAL( 3600, ulValue );
            break;

        case eCallIAPDTime2:
            /* Time 1. */
            TEST_ASSERT_EQUAL( 5400, ulValue );
            break;

        case eCallIAPrefixPreferLifeTime:
        case eCallIANAPreferLifeTime:
            /* ulPreferredLifeTime. */
            TEST_ASSERT_EQUAL( 4500, ulValue );
            break;

        case eCallIAPrefixValidLifeTime:
        case eCallIANAPrefixValidLifeTime:
            /* ulPValidLifeTime. */
            TEST_ASSERT_EQUAL( 7200, ulValue );
            break;

        default:
            TEST_ASSERT_TRUE( false );
            break;
    }
}

void xStubvBitConfig_write_uc_solicit( BitConfig_t * pxConfig,
                                       const uint8_t * pucData,
                                       size_t uxSize,
                                       int NumCalls )
{
    enum eCall
    {
        eCallTransactionID = 0,
        eCallMACAddress,
        eCallIPv6Prefix,
    };

    switch( NumCalls )
    {
        case eCallTransactionID:
            TEST_ASSERT_EQUAL( 3, uxSize );
            TEST_ASSERT_EQUAL_MEMORY( ucTestDHCPv6TransactionID, pucData, uxSize );
            break;

        case eCallMACAddress:
            TEST_ASSERT_EQUAL( ipMAC_ADDRESS_LENGTH_BYTES, uxSize );
            TEST_ASSERT_EQUAL_MEMORY( ucDefaultMACAddress, pucData, uxSize );
            break;

        case eCallIPv6Prefix:
            /* IPv6 prefix. */
            TEST_ASSERT_EQUAL( ipSIZE_OF_IPv6_ADDRESS, uxSize );
            TEST_ASSERT_EQUAL_MEMORY( &xDefaultNetPrefix.ucBytes, pucData, uxSize );
            break;

        default:
            TEST_ASSERT_TRUE( false );
            break;
    }
}


/* ==============================  Test Cases  ============================== */

/**
 * @brief prvPrepareSolicitation
 * Prepare function calls for sending DHCPv6 solicitation message.
 */
static void prvPrepareSolicitation()
{
    xBitConfig_init_IgnoreAndReturn( pdTRUE );
    vBitConfig_write_8_Stub( xStubvBitConfig_write_8_solicit );
    vBitConfig_write_uc_Stub( xStubvBitConfig_write_uc_solicit );
    vBitConfig_write_16_Stub( xStubvBitConfig_write_16_solicit );
    vBitConfig_write_32_Stub( xStubvBitConfig_write_32_solicit );
    pucBitConfig_peek_last_index_uc_IgnoreAndReturn( pdTRUE );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );
    vBitConfig_release_Ignore();
}

/**
 * @brief test_eGetDHCPv6State_happy_path
 * Check if eGetDHCPv6State can return DHCP state correctly.
 *
 * Test step:
 *  - Set endpoint's DHCP state.
 *  - Call eGetDHCPv6State to get state and check if it's correct.
 */
void test_eGetDHCPv6State_happy_path()
{
    NetworkEndPoint_t xEndPoint;
    eDHCPState_t eState = eInitialWait, eStateMax = eNotUsingLeasedAddress;
    eDHCPState_t eReturnState;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    for( eState = eInitialWait; eState <= eNotUsingLeasedAddress; eState++ )
    {
        xEndPoint.xDHCPData.eDHCPState = eState;
        eReturnState = eGetDHCPv6State( &xEndPoint );
        TEST_ASSERT_EQUAL( eState, eReturnState );
    }
}

/**
 * @brief test_eGetDHCPv6State_null
 * Check if eGetDHCPv6State trigger assertion when input is NULL.
 *
 * Test step:
 *  - Call eGetDHCPv6State with NULL.
 */
void test_eGetDHCPv6State_null()
{
    catch_assert( eGetDHCPv6State( NULL ) );
}

/**
 * @brief test_vDHCPv6Process_null
 * Check if vDHCPv6Process trigger assertion when input is NULL.
 *
 * Test step:
 *  - Call vDHCPv6Process with NULL endpoint.
 */
void test_vDHCPv6Process_null()
{
    catch_assert( vDHCPv6Process( pdTRUE, NULL ) );
    catch_assert( vDHCPv6Process( pdFALSE, NULL ) );
}

/**
 * @brief test_vDHCPv6Process_reset_from_init
 * Check if vDHCPv6Process can reset successfully from eInitialWait.
 *
 * Test step:
 *  - Set endpoint's DHCP state to eInitialWait.
 *  - Call vDHCPv6Process with reset flag and check the state after calling.
 */
void test_vDHCPv6Process_reset_from_init()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    xEndPoint.xDHCPData.eDHCPState = eInitialWait;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xDHCPv6Socket );
    xSocketValid_ExpectAndReturn( &xDHCPv6Socket, pdTRUE );
    prvSetCheckerAndReturn_FreeRTOS_setsockopt( &xDHCPv6Socket, sizeof( TickType_t ) );
    FreeRTOS_setsockopt_Stub( xStubFreeRTOS_setsockopt );
    prvSetCheckerAndReturn_vSocketBind( &xDHCPv6Socket );
    vSocketBind_Stub( xStubvSocketBind );
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdTRUE, &xEndPoint );

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingSendFirstDiscover. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint.xDHCPData.eDHCPState );
    /* We should set 2 socket options (FREERTOS_SO_RCVTIMEO and FREERTOS_SO_SNDTIMEO). */
    TEST_ASSERT_EQUAL( ( 1 << FREERTOS_SO_RCVTIMEO | 1 << FREERTOS_SO_SNDTIMEO ), xStubFreeRTOS_setsockopt_lOptionName_BitMap );
}

/**
 * @brief test_vDHCPv6Process_reset_from_lease
 * Check if vDHCPv6Process can reset successfully from eLeasedAddress.
 *
 * Test step:
 *  - Set endpoint's DHCP state to eLeasedAddress.
 *     - Set IPv6 address to 2001::1.
 *  - Call vDHCPv6Process with reset flag and check the state after calling.
 */
void test_vDHCPv6Process_reset_from_lease()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xDHCPv6Socket;
    const IPv6_Address_t xIPAddress = { 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    xEndPoint.xDHCPData.eDHCPState = eLeasedAddress;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xDHCPv6Socket );
    xSocketValid_ExpectAndReturn( &xDHCPv6Socket, pdTRUE );
    prvSetCheckerAndReturn_FreeRTOS_setsockopt( &xDHCPv6Socket, sizeof( TickType_t ) );
    FreeRTOS_setsockopt_Stub( xStubFreeRTOS_setsockopt );
    prvSetCheckerAndReturn_vSocketBind( &xDHCPv6Socket );
    vSocketBind_Stub( xStubvSocketBind );
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdTRUE, &xEndPoint );

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingSendFirstDiscover. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint.xDHCPData.eDHCPState );
    /* We should set 2 socket options (FREERTOS_SO_RCVTIMEO and FREERTOS_SO_SNDTIMEO). */
    TEST_ASSERT_EQUAL( ( 1 << FREERTOS_SO_RCVTIMEO | 1 << FREERTOS_SO_SNDTIMEO ), xStubFreeRTOS_setsockopt_lOptionName_BitMap );
}

/**
 * @brief test_vDHCPv6Process_continue_solicitation_happy_path
 * Check if vDHCPv6Process can continue from eWaitingSendFirstDiscover successfully.
 *
 * Test step:
 *  - Set endpoint's DHCP state to eWaitingSendFirstDiscover.
 *  - Call vDHCPv6Process with reset flag and check the state after calling.
 */
void test_vDHCPv6Process_continue_solicitation_happy_path()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    xEndPoint.xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    xEndPoint.pxDHCPMessage = &xDHCPMessage;
    xEndPoint.xDHCPData.xDHCPSocket = &xDHCPv6Socket;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    /* Prepare transaction ID. */
    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );

    /* Prepare bit message for solicitation. */
    prvPrepareSolicitation();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingOffer. */
    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL( 0, xDHCPMessage.ulTimeStamp );
    TEST_ASSERT_EQUAL( TEST_DHCPV6_TRANSACTION_ID, xEndPoint.xDHCPData.ulTransactionId );
}
