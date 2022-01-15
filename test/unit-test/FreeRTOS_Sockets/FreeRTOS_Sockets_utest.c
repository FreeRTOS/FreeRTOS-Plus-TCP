/*
 * FreeRTOS+TCP V2.3.4
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
#include "mock_Sockets_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_portable.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"

#include "FreeRTOS_Sockets.h"

#include "FreeRTOS_Sockets_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

extern List_t xBoundUDPSocketsList;
extern List_t xBoundTCPSocketsList;

BaseType_t prvValidSocket( const FreeRTOS_Socket_t * pxSocket,
                           BaseType_t xProtocol,
                           BaseType_t xIsBound );

uint8_t ucASCIIToHex( char cChar );

BaseType_t bMayConnect( FreeRTOS_Socket_t const * pxSocket );

static uint32_t xRandomNumberToReturn;
static BaseType_t xRNGStatus;
static UBaseType_t uxGlobalCallbackCount;
static BaseType_t xLocalReceiveCallback_Return;
static uint8_t xLocalReceiveCallback_Called = 0;

static FreeRTOS_Socket_t xGlobalSocket;

static void vUserCallbackLocal( FreeRTOS_Socket_t * xSocket )
{
    uxGlobalCallbackCount++;
}

static BaseType_t xStubApplicationGetRandomNumber( uint32_t * xRndNumber,
                                                   int count )
{
    ( void ) count;
    *xRndNumber = xRandomNumberToReturn;
    return xRNGStatus;
}

static void vpxListFindListItemWithValue_NotFound( void )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );
}

static void vpxListFindListItemWithValue_Found( const List_t * pxList,
                                                TickType_t xWantedItemValue,
                                                const ListItem_t * pxReturn )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( &( pxList->xListEnd ), pxReturn );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( pxReturn, xWantedItemValue );
}

static BaseType_t xStubForEventGroupWaitBits( EventGroupHandle_t xEventGroup,
                                              const EventBits_t uxBitsToWaitFor,
                                              const BaseType_t xClearOnExit,
                                              const BaseType_t xWaitForAllBits,
                                              TickType_t xTicksToWait,
                                              int CallbackCount )
{
    xGlobalSocket.u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;
}

static BaseType_t xLocalReceiveCallback( Socket_t xSocket,
                                         void * pvData,
                                         size_t xLength )
{
    xLocalReceiveCallback_Called++;
    return xLocalReceiveCallback_Return;
}

/* Test for FreeRTOS_inet_pton4 function. */
void test_FreeRTOS_inet_pton4( void )
{
    char * pucValidString1 = "192.68.1.1";
    uint32_t ulValidResponse1 = 0x010144C0;
    char * pucValidString2 = "192.0.1.1";
    uint32_t ulValidResponse2 = 0x010100C0;
    char * pucValidString3 = "192.68.1.0";
    uint32_t ulValidResponse3 = 0x000144C0;
    char * pucValidString4 = "0.0.0.0";
    uint32_t ulValidResponse4 = 0x00000000;
    char * pucValidString5 = "0.68.1.1";
    uint32_t ulValidResponse5 = 0x01014400;

    char * pucInvalidString1 = "0192.68.1.1";
    char * pucInvalidString2 = "192.68.00.1";
    char * pucInvalidString3 = "192.00.1.1";
    char * pucInvalidString4 = "freertos.com";
    char * pucInvalidString5 = "192.freertos.com";
    char * pucInvalidString6 = "\0";
    char * pucInvalidString7 = "1234.68.1.1";
    char * pucInvalidString8 = "123.68.0a.1";
    uint32_t ulInValidResponse = 0x00;

    BaseType_t xResult;
    uint32_t ulIPAddress;

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucValidString1, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulValidResponse1, ulIPAddress, "Could not convert string 1 correctly." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucValidString2, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulValidResponse2, ulIPAddress, "Could not convert string 2 correctly." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucValidString3, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulValidResponse3, ulIPAddress, "Could not convert string 3 correctly." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucValidString4, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulValidResponse4, ulIPAddress, "Could not convert string 4 correctly." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucValidString5, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulValidResponse5, ulIPAddress, "Could not convert string 5 correctly." );

    /* Invalid test cases. */
    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString1, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 1." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString2, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 2." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString3, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 3." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString4, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 4." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString5, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 5." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString6, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 6." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString7, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 7." );

    ulIPAddress = 0xABABABAB;
    xResult = FreeRTOS_inet_pton4( pucInvalidString8, &ulIPAddress );
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
    TEST_ASSERT_EQUAL_MESSAGE( ulInValidResponse, ulIPAddress, "Incorrectly converted string 8." );
}

void test_prvValidSocket_InvalidOrNULLSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) FREERTOS_INVALID_SOCKET;
    BaseType_t xProtocol, xIsBound;

    xReturn = prvValidSocket( NULL, xProtocol, xIsBound );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    xReturn = prvValidSocket( pxSocket, xProtocol, xIsBound );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_prvValidSocket_SocketBoundSetButNotBound( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xProtocol, xIsBound = pdTRUE;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xReturn = prvValidSocket( &xSocket, xProtocol, xIsBound );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_prvValidSocket_SocketBoundResetButBound( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xProtocol, xIsBound = pdFALSE;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket.ucProtocol = xProtocol;

    xReturn = prvValidSocket( &xSocket, xProtocol, xIsBound );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

void test_prvValidSocket_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xProtocol, xIsBound = pdTRUE;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xSocket.ucProtocol = xProtocol + 1;

    xReturn = prvValidSocket( &xSocket, xProtocol, xIsBound );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_vNetworkSocketsInit( void )
{
    vListInitialise_Expect( &xBoundUDPSocketsList );
    vListInitialise_Expect( &xBoundTCPSocketsList );

    vNetworkSocketsInit();
}

void test_prvDetermineSocketSize_IPTaskNotInit( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain, xType, xProtocol;
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    xReturn = prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_prvDetermineSocketSize_CatchAssert( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET + 1, xType, xProtocol;
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

void test_prvDetermineSocketSize_CatchAssert2( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType, xProtocol;
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdFALSE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );

    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

void test_prvDetermineSocketSize_CatchAssert3( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType, xProtocol;
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdFALSE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );
    memset( &xBoundTCPSocketsList, 0, sizeof( xBoundTCPSocketsList ) );

    xBoundUDPSocketsList.xListEnd.xItemValue = portMAX_DELAY;

    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

void test_prvDetermineSocketSize_CatchAssert4( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType, xProtocol = ~( FREERTOS_IPPROTO_UDP | FREERTOS_IPPROTO_TCP );
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );
    memset( &xBoundTCPSocketsList, 0, sizeof( xBoundTCPSocketsList ) );

    xBoundUDPSocketsList.xListEnd.xItemValue = portMAX_DELAY;
    xBoundTCPSocketsList.xListEnd.xItemValue = portMAX_DELAY;

    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

void test_prvDetermineSocketSize_CatchAssert5( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM + 1, xProtocol = FREERTOS_IPPROTO_UDP;
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );
    memset( &xBoundTCPSocketsList, 0, sizeof( xBoundTCPSocketsList ) );

    xBoundUDPSocketsList.xListEnd.xItemValue = portMAX_DELAY;
    xBoundTCPSocketsList.xListEnd.xItemValue = portMAX_DELAY;

    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

void test_prvDetermineSocketSize_UDPSocket( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_IPPROTO_UDP;
    size_t xSocketSize;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );
    memset( &xBoundTCPSocketsList, 0, sizeof( xBoundTCPSocketsList ) );

    xBoundUDPSocketsList.xListEnd.xItemValue = portMAX_DELAY;
    xBoundTCPSocketsList.xListEnd.xItemValue = portMAX_DELAY;

    xReturn = prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xUDP ), xSocketSize );
}

void test_prvDetermineSocketSize_CatchAssert6( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_IPPROTO_TCP;
    size_t xSocketSize;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );
    memset( &xBoundTCPSocketsList, 0, sizeof( xBoundTCPSocketsList ) );

    xBoundUDPSocketsList.xListEnd.xItemValue = portMAX_DELAY;
    xBoundTCPSocketsList.xListEnd.xItemValue = portMAX_DELAY;

    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

void test_prvDetermineSocketSize_TCPSocket( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    size_t xSocketSize;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    xReturn = prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), xSocketSize );
}

void test_FreeRTOS_socket_NoMemory( void )
{
    Socket_t xSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), NULL );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, xSocket );
}

void test_FreeRTOS_socket_EventGroupCreationFailed( void )
{
    Socket_t xSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    FreeRTOS_Socket_t const * pxSocket = NULL;
    uint8_t ucSocket[ ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ) ];

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), ( void * ) ucSocket );

    xEventGroupCreate_ExpectAndReturn( NULL );

    vPortFree_Expect( ucSocket );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, xSocket );
}

void test_FreeRTOS_socket_TCPSocket( void )
{
    Socket_t xSocket;
    FreeRTOS_Socket_t * pxSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    uint8_t ucSocket[ ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ) ];
    uint8_t xEventGroup[ sizeof( uintptr_t ) ];

    pxSocket = ( FreeRTOS_Socket_t * ) ucSocket;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), ( void * ) ucSocket );

    xEventGroupCreate_ExpectAndReturn( xEventGroup );

    vListInitialiseItem_Expect( &( pxSocket->xBoundSocketListItem ) );

    listSET_LIST_ITEM_OWNER_Expect( &( pxSocket->xBoundSocketListItem ), pxSocket );

    FreeRTOS_round_up_ExpectAndReturn( ipconfigTCP_TX_BUFFER_LENGTH, ipconfigTCP_MSS, 0xAABB );
    FreeRTOS_max_uint32_ExpectAndReturn( 1U, ( uint32_t ) ( ipconfigTCP_RX_BUFFER_LENGTH / 2U ) / ipconfigTCP_MSS, 0x1234 );
    FreeRTOS_max_uint32_ExpectAndReturn( 1U, ( uint32_t ) ( 0xAABB / 2U ) / ipconfigTCP_MSS, 0x3456 );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( ucSocket, xSocket );
    TEST_ASSERT_EQUAL( xSocket->xEventGroup, xEventGroup );
    TEST_ASSERT_EQUAL( xSocket->xReceiveBlockTime, ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->xSendBlockTime, ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->ucSocketOptions, ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT );
    TEST_ASSERT_EQUAL( xSocket->ucProtocol, ( uint8_t ) xProtocol );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.usMSS, ( uint16_t ) ipconfigTCP_MSS );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.uxRxStreamSize, ( size_t ) ipconfigTCP_RX_BUFFER_LENGTH );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.uxTxStreamSize, 0xAABB );
    TEST_ASSERT_EQUAL( 0x1234, pxSocket->u.xTCP.uxRxWinSize );
    TEST_ASSERT_EQUAL( 0x3456, pxSocket->u.xTCP.uxTxWinSize );
}

void test_FreeRTOS_socket_UDPSocket( void )
{
    Socket_t xSocket;
    FreeRTOS_Socket_t * pxSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_IPPROTO_UDP;
    uint8_t ucSocket[ ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xUDP ) ];
    uint8_t xEventGroup[ sizeof( uintptr_t ) ];

    pxSocket = ( FreeRTOS_Socket_t * ) ucSocket;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xUDP ), ( void * ) ucSocket );

    xEventGroupCreate_ExpectAndReturn( xEventGroup );

    vListInitialise_Expect( &( pxSocket->u.xUDP.xWaitingPacketsList ) );

    vListInitialiseItem_Expect( &( pxSocket->xBoundSocketListItem ) );

    listSET_LIST_ITEM_OWNER_Expect( &( pxSocket->xBoundSocketListItem ), pxSocket );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( ucSocket, xSocket );
    TEST_ASSERT_EQUAL( xSocket->xEventGroup, xEventGroup );
    TEST_ASSERT_EQUAL( xSocket->xReceiveBlockTime, ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->xSendBlockTime, ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->ucSocketOptions, ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT );
    TEST_ASSERT_EQUAL( xSocket->ucProtocol, ( uint8_t ) xProtocol );
    TEST_ASSERT_EQUAL( xSocket->u.xUDP.uxMaxPackets, ( UBaseType_t ) ipconfigUDP_MAX_RX_PACKETS );
}

void test_FreeRTOS_CreateSocketSet_NoMemory( void )
{
    SocketSelect_t * pxSocketSet;

    pvPortMalloc_ExpectAndReturn( sizeof( *pxSocketSet ), NULL );

    pxSocketSet = FreeRTOS_CreateSocketSet();

    TEST_ASSERT_EQUAL( NULL, pxSocketSet );
}

void test_FreeRTOS_CreateSocketSet_EventGroupCreationFails( void )
{
    SocketSelect_t * pxSocketSet;
    uint8_t ucSocket[ sizeof( *pxSocketSet ) ];

    pvPortMalloc_ExpectAndReturn( sizeof( *pxSocketSet ), ucSocket );

    xEventGroupCreate_ExpectAndReturn( NULL );

    vPortFree_Expect( ucSocket );

    pxSocketSet = FreeRTOS_CreateSocketSet();

    TEST_ASSERT_EQUAL( NULL, pxSocketSet );
}

void test_FreeRTOS_CreateSocketSet_HappyPath( void )
{
    SocketSelect_t * pxSocketSet;
    uint8_t ucSocketSet[ sizeof( *pxSocketSet ) ];
    uint8_t xEventGroup[ sizeof( uintptr_t ) ];

    pvPortMalloc_ExpectAndReturn( sizeof( *pxSocketSet ), ucSocketSet );

    xEventGroupCreate_ExpectAndReturn( xEventGroup );

    pxSocketSet = FreeRTOS_CreateSocketSet();

    TEST_ASSERT_EQUAL( ucSocketSet, pxSocketSet );
    TEST_ASSERT_EQUAL( xEventGroup, pxSocketSet->xSelectGroup );
}

void test_FreeRTOS_DeleteSocketSet_happyPath( void )
{
    SocketSet_t xSocketSet;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    FreeRTOS_DeleteSocketSet( xSocketSet );
}

void test_FreeRTOS_DeleteSocketSet_SendingFailed( void )
{
    SocketSet_t xSocketSet;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdFAIL );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    FreeRTOS_DeleteSocketSet( xSocketSet );
}

void test_FreeRTOS_FD_SET_CatchAssert1( void )
{
    Socket_t xSocket = NULL;
    SocketSet_t xSocketSet;
    EventBits_t xBitsToSet;

    catch_assert( FreeRTOS_FD_SET( xSocket, xSocketSet, xBitsToSet ) );
}

void test_FreeRTOS_FD_SET_CatchAssert2( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ucSocket;
    SocketSet_t xSocketSet = NULL;
    EventBits_t xBitsToSet;

    catch_assert( FreeRTOS_FD_SET( xSocket, xSocketSet, xBitsToSet ) );
}

void test_FreeRTOS_FD_SET_NoBitsToSet( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ucSocket;
    SocketSet_t xSocketSet = ucSocketSet;
    EventBits_t xBitsToSet = 0;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    FreeRTOS_FD_SET( xSocket, xSocketSet, xBitsToSet );

    TEST_ASSERT_EQUAL( 0, xSocket->xSelectBits );
}

void test_FreeRTOS_FD_SET_AllBitsToSet( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ucSocket;
    SocketSet_t xSocketSet = ucSocketSet;
    EventBits_t xBitsToSet = eSELECT_ALL;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, 0 );
    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    FreeRTOS_FD_SET( xSocket, xSocketSet, xBitsToSet );

    TEST_ASSERT_EQUAL( eSELECT_ALL, xSocket->xSelectBits );
    TEST_ASSERT_EQUAL( ucSocketSet, xSocket->pxSocketSet );
}

void test_FreeRTOS_FD_CLR_CatchAssert1( void )
{
    Socket_t xSocket = NULL;
    SocketSet_t xSocketSet;
    EventBits_t xBitsToClear;

    catch_assert( FreeRTOS_FD_CLR( xSocket, xSocketSet, xBitsToClear ) );
}

void test_FreeRTOS_FD_CLR_CatchAssert2( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ucSocket;
    SocketSet_t xSocketSet = NULL;
    EventBits_t xBitsToClear;

    catch_assert( FreeRTOS_FD_CLR( xSocket, xSocketSet, xBitsToClear ) );
}

void test_FreeRTOS_FD_CLR_NoBitsToClear( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ucSocket;
    SocketSet_t xSocketSet = ucSocketSet;
    EventBits_t xBitsToClear = 0;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    xSocket->xSelectBits = 0;

    FreeRTOS_FD_CLR( xSocket, xSocketSet, xBitsToClear );

    TEST_ASSERT_EQUAL( NULL, xSocket->pxSocketSet );
    TEST_ASSERT_EQUAL( 0, xSocket->xSelectBits );
}

void test_FreeRTOS_FD_CLR_AllBitsToClear( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ucSocket;
    SocketSet_t xSocketSet = ucSocketSet;
    EventBits_t xBitsToClear = 0;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    xSocket->xSelectBits = eSELECT_ALL;

    FreeRTOS_FD_CLR( xSocket, xSocketSet, xBitsToClear );

    TEST_ASSERT_EQUAL( xSocketSet, xSocket->pxSocketSet );
    TEST_ASSERT_EQUAL( eSELECT_ALL, xSocket->xSelectBits );
}

void test_FreeRTOS_FD_ISSET_CatchAssert1( void )
{
    Socket_t xSocket = NULL;
    SocketSet_t xSocketSet;

    catch_assert( FreeRTOS_FD_ISSET( xSocket, xSocketSet ) );
}

void test_FreeRTOS_FD_ISSET_CatchAssert2( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ucSocket;
    SocketSet_t xSocketSet = NULL;

    catch_assert( FreeRTOS_FD_ISSET( xSocket, xSocketSet ) );
}

void test_FreeRTOS_FD_ISSET_SocketSetDifferent( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ucSocket;
    SocketSet_t xSocketSet = ucSocketSet;
    EventBits_t xReturn;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    xReturn = FreeRTOS_FD_ISSET( xSocket, xSocketSet );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_FreeRTOS_FD_ISSET_SocketSetSame( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ucSocket;
    SocketSet_t xSocketSet = ucSocketSet;
    EventBits_t xReturn;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    xSocket->pxSocketSet = xSocketSet;

    xSocket->xSocketBits = 0x12;

    xReturn = FreeRTOS_FD_ISSET( xSocket, xSocketSet );

    TEST_ASSERT_EQUAL( 0x12 & eSELECT_ALL, xReturn );
}

void test_FreeRTOS_select_CatchAssert( void )
{
    BaseType_t xReturn;
    SocketSet_t xSocketSet = NULL;
    TickType_t xBlockTimeTicks;

    catch_assert( FreeRTOS_select( xSocketSet, xBlockTimeTicks ) );
}

void test_FreeRTOS_select_BitsMatched( void )
{
    BaseType_t xReturn;
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    SocketSet_t xSocketSet = ucSocketSet;
    TickType_t xBlockTimeTicks = 0xAB12;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( ( EventBits_t ) eSELECT_ALL ), pdFALSE, pdFALSE, xBlockTimeTicks, pdFALSE );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdFALSE );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, 0, 0x123 );

    xReturn = FreeRTOS_select( xSocketSet, xBlockTimeTicks );

    TEST_ASSERT_EQUAL( 0x123, xReturn );
}

void test_FreeRTOS_select_Timeout( void )
{
    BaseType_t xReturn;
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    SocketSet_t xSocketSet = ucSocketSet;
    TickType_t xBlockTimeTicks = 0xAB12;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( ( EventBits_t ) eSELECT_ALL ), pdFALSE, pdFALSE, xBlockTimeTicks, pdFALSE );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdFALSE );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, 0, 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = FreeRTOS_select( xSocketSet, xBlockTimeTicks );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_FreeRTOS_select_TimeoutSecondTime( void )
{
    BaseType_t xReturn;
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    SocketSet_t xSocketSet = ucSocketSet;
    TickType_t xBlockTimeTicks = 0xAB12;

    vTaskSetTimeOutState_ExpectAnyArgs();

    for( int i = 0; i < 2; i++ )
    {
        xEventGroupWaitBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( ( EventBits_t ) eSELECT_ALL ), pdFALSE, pdFALSE, xBlockTimeTicks, pdFALSE );

        xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdFALSE );

        xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

        xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, 0, 0 );

        if( i == 0 )
        {
            xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );
        }
        else
        {
            xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );
        }
    }

    xReturn = FreeRTOS_select( xSocketSet, xBlockTimeTicks );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_FreeRTOS_select_FoundWaitBits( void )
{
    BaseType_t xReturn;
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    SocketSet_t xSocketSet = ucSocketSet;
    TickType_t xBlockTimeTicks = 0xAB12;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( ( EventBits_t ) eSELECT_ALL ), pdFALSE, pdFALSE, xBlockTimeTicks, eSELECT_INTR );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_INTR, pdFALSE );

    xReturn = FreeRTOS_select( xSocketSet, xBlockTimeTicks );

    TEST_ASSERT_EQUAL( eSELECT_INTR, xReturn );
}

void test_prvFindSelectedSocket_SendFail( void )
{
    SocketSelect_t xSocketSet;

    xEventGroupClearBits_ExpectAndReturn( xSocketSet.xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdFALSE );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    prvFindSelectedSocket( &xSocketSet );
}

void test_prvFindSelectedSocket_SendSuccess( void )
{
    SocketSelect_t xSocketSet;

    xEventGroupClearBits_ExpectAndReturn( xSocketSet.xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdFALSE );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    xEventGroupWaitBits_ExpectAndReturn( xSocketSet.xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdTRUE, pdFALSE, portMAX_DELAY, pdTRUE );

    prvFindSelectedSocket( &xSocketSet );
}

void test_FreeRTOS_recvfrom_NullSocket( void )
{
    int32_t lReturn;
    Socket_t xSocket = NULL;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, lReturn );
}

void test_FreeRTOS_recvfrom_TCPSocket( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_TCP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, lReturn );
}

void test_FreeRTOS_recvfrom_NonBlockingInterrupted( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0, eSOCKET_INTR );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINTR, lReturn );
}

void test_FreeRTOS_recvfrom_NonBlocking( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0, ~eSOCKET_INTR );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EWOULDBLOCK, lReturn );
}

void test_FreeRTOS_recvfrom_NonBlockingFlagSet( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = FREERTOS_MSG_DONTWAIT;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EWOULDBLOCK, lReturn );
}

void test_FreeRTOS_recvfrom_BlockingButTimeout( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EWOULDBLOCK, lReturn );
}

void test_FreeRTOS_recvfrom_BlockingButTimeoutSecondTime( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EWOULDBLOCK, lReturn );
}

void test_FreeRTOS_recvfrom_BlockingButInterrupted( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, eSOCKET_INTR );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINTR, lReturn );
}

void test_FreeRTOS_recvfrom_BlockingButInterruptedAndReceived( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, eSOCKET_INTR | eSOCKET_RECEIVE );

    xEventGroupSetBits_ExpectAndReturn( xSocket->xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdFALSE );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINTR, lReturn );
}

void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_JustUDPHeader( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xGlobalSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = ipconfigTCP_MSS;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xSourceAddress;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t );
    xNetworkBuffer.ulIPAddress = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xGlobalSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xGlobalSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xGlobalSocket->xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xGlobalSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xGlobalSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xGlobalSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xGlobalSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

    uxListRemove_ExpectAndReturn( &( xNetworkBuffer.xBufferListItem ), 0 );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xGlobalSocket, pvBuffer, uxBufferLength, xFlags, &xSourceAddress, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( xSourceAddress.sin_port, xNetworkBuffer.usPort );
    TEST_ASSERT_EQUAL_UINT32( xSourceAddress.sin_addr, xNetworkBuffer.ulIPAddress );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, pvBuffer, ipconfigTCP_MSS );
}

void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_Packet100( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xGlobalSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = ipconfigTCP_MSS;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xSourceAddress;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.ulIPAddress = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xGlobalSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xGlobalSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xGlobalSocket->xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xGlobalSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xGlobalSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xGlobalSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xGlobalSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

    uxListRemove_ExpectAndReturn( &( xNetworkBuffer.xBufferListItem ), 0 );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xGlobalSocket, pvBuffer, uxBufferLength, xFlags, &xSourceAddress, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 100, lReturn );
    TEST_ASSERT_EQUAL( xSourceAddress.sin_port, xNetworkBuffer.usPort );
    TEST_ASSERT_EQUAL_UINT32( xSourceAddress.sin_addr, xNetworkBuffer.ulIPAddress );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, 100 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, &pvBuffer[ 100 ], ipconfigTCP_MSS - 100 );
}

void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_Packet100SizeSmall( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xGlobalSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = 50;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xSourceAddress;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.ulIPAddress = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xGlobalSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xGlobalSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xGlobalSocket->xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xGlobalSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xGlobalSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xGlobalSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xGlobalSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

    uxListRemove_ExpectAndReturn( &( xNetworkBuffer.xBufferListItem ), 0 );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xGlobalSocket, pvBuffer, uxBufferLength, xFlags, &xSourceAddress, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 50, lReturn );
    TEST_ASSERT_EQUAL( xSourceAddress.sin_port, xNetworkBuffer.usPort );
    TEST_ASSERT_EQUAL_UINT32( xSourceAddress.sin_addr, xNetworkBuffer.ulIPAddress );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, uxBufferLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, &pvBuffer[ uxBufferLength ], ipconfigTCP_MSS - uxBufferLength );
}

void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_Packet100SizeSmall_Peek( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xGlobalSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = 50;
    BaseType_t xFlags = FREERTOS_MSG_PEEK;
    struct freertos_sockaddr xSourceAddress;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.ulIPAddress = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xGlobalSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xGlobalSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xGlobalSocket->xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xGlobalSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xGlobalSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xGlobalSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xGlobalSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xGlobalSocket, pvBuffer, uxBufferLength, xFlags, &xSourceAddress, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 50, lReturn );
    TEST_ASSERT_EQUAL( xSourceAddress.sin_port, xNetworkBuffer.usPort );
    TEST_ASSERT_EQUAL_UINT32( xSourceAddress.sin_addr, xNetworkBuffer.ulIPAddress );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, uxBufferLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, &pvBuffer[ uxBufferLength ], ipconfigTCP_MSS - uxBufferLength );
}

void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_Packet100SizeSmall_Peek_SourceAddrNULL( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xGlobalSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = 50;
    BaseType_t xFlags = FREERTOS_MSG_PEEK;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.ulIPAddress = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xGlobalSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xGlobalSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xGlobalSocket->xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xGlobalSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xGlobalSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xGlobalSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xGlobalSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xGlobalSocket, pvBuffer, uxBufferLength, xFlags, NULL, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 50, lReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, uxBufferLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, &pvBuffer[ uxBufferLength ], ipconfigTCP_MSS - uxBufferLength );
}

void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_Packet100SizeSmall_ZeroCopyAndPeek( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xGlobalSocket = ( Socket_t ) ucSocket;
    char * pvBuffer;
    size_t uxBufferLength = 50;
    BaseType_t xFlags = FREERTOS_MSG_PEEK | FREERTOS_ZERO_COPY;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.ulIPAddress = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xGlobalSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );

    xGlobalSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xGlobalSocket->xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xGlobalSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xGlobalSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xGlobalSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xGlobalSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xGlobalSocket, &pvBuffer, uxBufferLength, xFlags, NULL, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 100, lReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, 100 );
}

void test_FreeRTOS_recvfrom_BlockingGetsPacketInBegining_Packet100SizeSmall_ZeroCopyAndPeek( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xGlobalSocket = ( Socket_t ) ucSocket;
    char * pvBuffer;
    size_t uxBufferLength = 50;
    BaseType_t xFlags = FREERTOS_MSG_PEEK | FREERTOS_ZERO_COPY;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.ulIPAddress = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xGlobalSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );

    xGlobalSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xGlobalSocket->xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xGlobalSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    xListItem.pvOwner = &xNetworkBuffer;
    xGlobalSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xGlobalSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xGlobalSocket, &pvBuffer, uxBufferLength, xFlags, NULL, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 100, lReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, 100 );
}

void test_prvMakeSureSocketIsBound_NULLSocket( void )
{
    BaseType_t xResult;

    xResult = prvMakeSureSocketIsBound( NULL );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

void test_prvMakeSureSocketIsBound_TCPProtocol( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xResult = prvMakeSureSocketIsBound( &xSocket );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

void test_prvMakeSureSocketIsBound_SocketAlreadyBound( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xResult = prvMakeSureSocketIsBound( &xSocket );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

void test_prvMakeSureSocketIsBound_SocketNotBound_BindingFails( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    xResult = prvMakeSureSocketIsBound( &xSocket );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

void test_prvMakeSureSocketIsBound_SocketNotBound_BindingSuccess( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, ( EventBits_t ) eSOCKET_BOUND, pdTRUE, pdFALSE, portMAX_DELAY, pdTRUE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xResult = prvMakeSureSocketIsBound( &xSocket );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

void test_FreeRTOS_sendto_CatchAssert( void )
{
    int32_t lResult;
    Socket_t xSocket;
    char * pvBuffer = NULL;
    size_t uxTotalDataLength;
    BaseType_t xFlags;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;

    catch_assert( FreeRTOS_sendto( xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength ) );
}

void test_FreeRTOS_sendto_MoreDataThanUDPPayload( void )
{
    int32_t lResult;
    Socket_t xSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxTotalDataLength = ipMAX_UDP_PAYLOAD_LENGTH + 1;
    BaseType_t xFlags;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;

    lResult = FreeRTOS_sendto( xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
}

void test_FreeRTOS_sendto_TCPSocket( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ ipMAX_UDP_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = ipMAX_UDP_PAYLOAD_LENGTH;
    BaseType_t xFlags;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
}

void test_FreeRTOS_sendto_IPTaskCalling_NoNetworkBuffer( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ ipMAX_UDP_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = ipMAX_UDP_PAYLOAD_LENGTH;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
}

void test_FreeRTOS_sendto_IPTaskCalling_NonZeroCOpy( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ ipMAX_UDP_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = ipMAX_UDP_PAYLOAD_LENGTH;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    memset( pucEthernetBuffer, 0, ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv4, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( ipMAX_UDP_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
    TEST_ASSERT_EQUAL( xNetworkBuffer.ulIPAddress, xDestinationAddress.sin_addr );
}

void test_FreeRTOS_sendto_IPTaskCalling_NonZeroCopy1( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ ipMAX_UDP_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = ipMAX_UDP_PAYLOAD_LENGTH;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    memset( pucEthernetBuffer, 0, ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv4, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( ipMAX_UDP_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
    TEST_ASSERT_EQUAL( xNetworkBuffer.ulIPAddress, xDestinationAddress.sin_addr );
}

void test_FreeRTOS_sendto_IPTaskCalling_NonZeroCopy2( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ ipMAX_UDP_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = ipMAX_UDP_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_MSG_DONTWAIT;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    memset( pucEthernetBuffer, 0, ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv4, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( ipMAX_UDP_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
    TEST_ASSERT_EQUAL( xNetworkBuffer.ulIPAddress, xDestinationAddress.sin_addr );
}

void test_FreeRTOS_sendto_IPTaskCalling_NonZeroCopy3( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ ipMAX_UDP_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = ipMAX_UDP_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_MSG_DONTWAIT;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    memset( pucEthernetBuffer, 0, ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv4, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( ipMAX_UDP_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
    TEST_ASSERT_EQUAL( xNetworkBuffer.ulIPAddress, xDestinationAddress.sin_addr );
}

void test_FreeRTOS_sendto_IPTaskCalling_ZeroCopy( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ ipMAX_UDP_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = ipMAX_UDP_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    memset( pucEthernetBuffer, 0, ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pvBuffer, &xNetworkBuffer );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( ipMAX_UDP_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
    TEST_ASSERT_EQUAL( xNetworkBuffer.ulIPAddress, xDestinationAddress.sin_addr );
}

static uint32_t ulCalled = 0;
static void xLocalFunctionPointer( Socket_t xSocket,
                                   size_t xLength )
{
    ulCalled++;
}

void test_FreeRTOS_sendto_IPTaskCalling_ZeroCopy_ValidFunctionPointer( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ ipMAX_UDP_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = ipMAX_UDP_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    ulCalled = 0;

    memset( pucEthernetBuffer, 0, ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = xLocalFunctionPointer;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pvBuffer, &xNetworkBuffer );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( ipMAX_UDP_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
    TEST_ASSERT_EQUAL( xNetworkBuffer.ulIPAddress, xDestinationAddress.sin_addr );
    TEST_ASSERT_EQUAL( 1, ulCalled );
}

void test_FreeRTOS_sendto_IPTaskCalling_ZeroCopy_SendingToIPTaskFails( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ ipMAX_UDP_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = ipMAX_UDP_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    ulCalled = 0;

    memset( pucEthernetBuffer, 0, ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = xLocalFunctionPointer;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pvBuffer, &xNetworkBuffer );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
    TEST_ASSERT_EQUAL( xNetworkBuffer.ulIPAddress, xDestinationAddress.sin_addr );
    TEST_ASSERT_EQUAL( 0, ulCalled );
}

void test_FreeRTOS_sendto_IPTaskCalling_NonZeroCopy_SendingToIPTaskFails( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ ipMAX_UDP_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = ipMAX_UDP_PAYLOAD_LENGTH;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    ulCalled = 0;

    memset( pucEthernetBuffer, 0, ipMAX_UDP_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = xLocalFunctionPointer;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv4, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
    TEST_ASSERT_EQUAL( xNetworkBuffer.ulIPAddress, xDestinationAddress.sin_addr );
    TEST_ASSERT_EQUAL( 0, ulCalled );
}

void test_FreeRTOS_bind_catchAssert( void )
{
    BaseType_t xReturn;
    Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    catch_assert( FreeRTOS_bind( xSocket, &xAddress, xAddressLength ) );
}

void test_FreeRTOS_bind_SocketIsNULL( void )
{
    BaseType_t xReturn;
    Socket_t xSocket = NULL;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xReturn = FreeRTOS_bind( xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_bind_SocketIsInvalid( void )
{
    BaseType_t xReturn;
    Socket_t xSocket = FREERTOS_INVALID_SOCKET;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xReturn = FreeRTOS_bind( xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_bind_SocketIsAlreadyBound( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xReturn = FreeRTOS_bind( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_bind_SendToIPTaskFailed( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdFAIL );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_bind( &xSocket, NULL, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ECANCELED, xReturn );
}

void test_FreeRTOS_bind_IPTaskDidNotBindTheSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, ( EventBits_t ) eSOCKET_BOUND, pdTRUE, pdFALSE, portMAX_DELAY, pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xReturn = FreeRTOS_bind( &xSocket, NULL, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_bind_NonNullAddress( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, ( EventBits_t ) eSOCKET_BOUND, pdTRUE, pdFALSE, portMAX_DELAY, pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xReturn = FreeRTOS_bind( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_vSocketBind_CatchAssert1( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal;

    catch_assert( vSocketBind( NULL, &xBindAddress, uxAddressLength, xInternal ) );
}

void test_vSocketBind_CatchAssert2( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal;

    catch_assert( vSocketBind( FREERTOS_INVALID_SOCKET, &xBindAddress, uxAddressLength, xInternal ) );
}

void test_vSocketBind_TCP( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_vSocketBind_TCPNULLAddress( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );
    xReturn = vSocketBind( &xSocket, NULL, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRNOTAVAIL, xReturn );
}

void test_vSocketBind_RNGFails( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xBindAddress.sin_port = 0;

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRNOTAVAIL, xReturn );
}

void test_vSocketBind_NonZeroPortNumber( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xBindAddress.sin_port = 0x12;

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_vSocketBind_GotNULLItem( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdTRUE;
    ListItem_t xLocalList;
    ListItem_t * xListStart = NULL;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAnyArgsAndReturn( xListStart );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( xListStart, 0 );

    listGET_NEXT_ExpectAnyArgsAndReturn( xListStart );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( xListStart, xBindAddress.sin_port );

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xBindAddress.sin_port ), xSocket.usLocalPort );
}

void test_vSocketBind_GotANonNULLValue( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdTRUE;
    ListItem_t xLocalList;
    ListItem_t * xListStart = &xLocalList;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAnyArgsAndReturn( xListStart );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( xListStart, 0 );

    listGET_NEXT_ExpectAnyArgsAndReturn( xListStart );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( xListStart, xBindAddress.sin_port );

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRINUSE, xReturn );
    TEST_ASSERT_EQUAL( 0, xSocket.usLocalPort );
}

void test_vSocketBind_TCPGotAProperValue( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdTRUE;
    ListItem_t xLocalList;
    ListItem_t * xListStart = &xLocalList;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xBindAddress.sin_port ), xSocket.usLocalPort );
}

void test_vSocketBind_TCPGotAProperValuePortZero( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdTRUE;
    MiniListItem_t xLocalList;

    xBoundTCPSocketsList.xListEnd = xLocalList;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xBindAddress.sin_port = 0;

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xBoundTCPSocketsList.xListEnd ) );

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), FreeRTOS_htons( 1024 ) );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xBindAddress.sin_port ), xSocket.usLocalPort );
}

void test_FreeRTOS_closesocket_NULLSocket( void )
{
    BaseType_t xReturn;
    Socket_t xSocket = NULL;

    xReturn = FreeRTOS_closesocket( xSocket );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_FreeRTOS_closesocket_InvalidSocket( void )
{
    BaseType_t xReturn;
    Socket_t xSocket = ( Socket_t ) ( uintptr_t ) FREERTOS_INVALID_SOCKET;

    xReturn = FreeRTOS_closesocket( xSocket );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_FreeRTOS_closesocket_TCPSocketSendFail( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdFAIL );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_closesocket( &xSocket );

    TEST_ASSERT_EQUAL( -1, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleConnected );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleReceive );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleSent );
}

void test_FreeRTOS_closesocket_TCPSocketSendPass( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_closesocket( &xSocket );

    TEST_ASSERT_EQUAL( 1, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleConnected );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleReceive );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleSent );
}

void test_FreeRTOS_closesocket_UDPSocketSendFail( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdFAIL );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_closesocket( &xSocket );

    TEST_ASSERT_EQUAL( -1, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xUDP.pxHandleReceive );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xUDP.pxHandleSent );
}

void test_FreeRTOS_closesocket_UDPSocketSendPass( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_closesocket( &xSocket );

    TEST_ASSERT_EQUAL( 1, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xUDP.pxHandleReceive );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xUDP.pxHandleSent );
}

void test_FreeRTOS_closesocket_UnknownProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_closesocket( &xSocket );

    TEST_ASSERT_EQUAL( 1, xReturn );
}

void test_vSocketClose_UnknownProtocol_NotBound( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    vEventGroupDelete_Expect( xSocket.xEventGroup );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

void test_vSocketClose_UnknownProtocol_NotBound_EventGroupNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

void test_vSocketClose_TCP_EverythingNonNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;
    ListItem_t xLocalList;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;
    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    vTCPWindowDestroy_Expect( &( xSocket.u.xTCP.xTCPWindow ) );

    vPortFree_Expect( xSocket.u.xTCP.rxStream );

    vPortFree_Expect( xSocket.u.xTCP.txStream );

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

void test_vSocketClose_TCP_LastAckMessageNonNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;
    ListItem_t xLocalList;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;
    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xSocket.u.xTCP.pxAckMessage = NULL;

    vTCPWindowDestroy_Expect( &( xSocket.u.xTCP.xTCPWindow ) );

    vPortFree_Expect( xSocket.u.xTCP.rxStream );

    vPortFree_Expect( xSocket.u.xTCP.txStream );

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

void test_vSocketClose_TCP_AllFieldsNonNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;
    ListItem_t xLocalList;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;
    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xSocket.u.xTCP.pxAckMessage = NULL;
    xSocket.u.xTCP.rxStream = NULL;
    xSocket.u.xTCP.txStream = NULL;

    vTCPWindowDestroy_Expect( &( xSocket.u.xTCP.xTCPWindow ) );

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) 0x12345678 );

    uxListRemove_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0 );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

void test_vSocketClose_UDP_NoWaitingPackets( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;
    ListItem_t xLocalList;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;
    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket.u.xUDP.xWaitingPacketsList ), 0 );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

void test_vSocketClose_UDP_SomeWaitingPackets( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;
    ListItem_t xLocalList;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;
    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket.u.xUDP.xWaitingPacketsList ), 5 );

    for( int i = 0; i < 5; i++ )
    {
        listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xSocket.u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

        uxListRemove_ExpectAndReturn( &( xNetworkBuffer.xBufferListItem ), pdPASS );

        vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

        listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket.u.xUDP.xWaitingPacketsList ), 4 - i );
    }

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

void test_prvTCPSetSocketCount_ListeningSocketNoChildren( void )
{
    FreeRTOS_Socket_t xSocketToDelete;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );
}

void test_prvTCPSetSocketCount_ListeningSocketNonZeroChildren1( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;

    xChildSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );
}

void test_prvTCPSetSocketCount_ListeningSocketNonZeroChildren2( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    xChildSocket.usLocalPort = usLocalPort + 1;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );
}

void test_prvTCPSetSocketCount_ListeningSocketNonZeroChildren3( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.bits.bPassQueued = pdFALSE_UNSIGNED;
    xChildSocket.u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );
}

void test_prvTCPSetSocketCount_ListeningSocketNonZeroChildren4( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.bits.bPassQueued = pdFALSE_UNSIGNED;
    xChildSocket.u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );
}

void test_prvTCPSetSocketCount_ListeningSock_HappyPath1( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;
    xChildSocket.u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;
    xChildSocket.xEventGroup = NULL;
    xChildSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xChildSocket.u.xTCP.pxAckMessage = NULL;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), &( xBoundTCPSocketsList.xListEnd ) );

    vTCPWindowDestroy_Expect( &( xChildSocket.u.xTCP.xTCPWindow ) );

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xChildSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xChildSocket );

    prvTCPSetSocketCount( &xSocketToDelete );
}

void test_prvTCPSetSocketCount_ListeningSock_HappyPath2( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.bits.bPassQueued = pdFALSE_UNSIGNED;
    xChildSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xChildSocket.xEventGroup = NULL;
    xChildSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xChildSocket.u.xTCP.pxAckMessage = NULL;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), &( xBoundTCPSocketsList.xListEnd ) );

    vTCPWindowDestroy_Expect( &( xChildSocket.u.xTCP.xTCPWindow ) );

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xChildSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xChildSocket );

    prvTCPSetSocketCount( &xSocketToDelete );
}

void test_prvTCPSetSocketCount_ListeningSock_HappyPath3( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;
    xChildSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xChildSocket.xEventGroup = NULL;
    xChildSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xChildSocket.u.xTCP.pxAckMessage = NULL;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), &( xBoundTCPSocketsList.xListEnd ) );

    vTCPWindowDestroy_Expect( &( xChildSocket.u.xTCP.xTCPWindow ) );

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xChildSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xChildSocket );

    prvTCPSetSocketCount( &xSocketToDelete );
}

void test_prvTCPSetSocketCount_NotListeningSock_1( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    xChildSocket.u.xTCP.usChildCount = 100;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );

    TEST_ASSERT_EQUAL( 100, xChildSocket.u.xTCP.usChildCount );
}

void test_prvTCPSetSocketCount_NotListeningSock_2( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xChildSocket.usLocalPort = usLocalPort + 1;
    xChildSocket.u.xTCP.usChildCount = 100;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );

    TEST_ASSERT_EQUAL( 100, xChildSocket.u.xTCP.usChildCount );
}

void test_prvTCPSetSocketCount_NotListeningSock_3( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.usChildCount = 0;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );

    TEST_ASSERT_EQUAL( 0, xChildSocket.u.xTCP.usChildCount );
}

void test_prvTCPSetSocketCount_NotListeningSock_HappyPath( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.usChildCount = 100;

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    prvTCPSetSocketCount( &xSocketToDelete );

    TEST_ASSERT_EQUAL( 99, xChildSocket.u.xTCP.usChildCount );
}

void test_prvSockopt_so_buffer_InvalidProtocol( void )
{
    FreeRTOS_Socket_t xSocket;
    int32_t lOptionName;
    uint8_t vOptionValue[ sizeof( uintptr_t ) ];
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = prvSockopt_so_buffer( &xSocket, lOptionName, vOptionValue );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_prvSockopt_so_buffer_InvalidOption1( void )
{
    FreeRTOS_Socket_t xSocket;
    int32_t lOptionName;
    uint32_t vOptionValue = 0xABCD1234;
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    lOptionName = FREERTOS_SO_SNDBUF;
    xSocket.u.xTCP.txStream = NULL;
    xSocket.u.xTCP.usMSS = 0x12;

    FreeRTOS_round_up_ExpectAndReturn( vOptionValue, xSocket.u.xTCP.usMSS, 0xAB );

    xReturn = prvSockopt_so_buffer( &xSocket, lOptionName, &vOptionValue );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0xAB, xSocket.u.xTCP.uxTxStreamSize );
}

void test_prvSockopt_so_buffer_InvalidOption2( void )
{
    FreeRTOS_Socket_t xSocket;
    int32_t lOptionName;
    uint8_t vOptionValue[ sizeof( uintptr_t ) ];
    BaseType_t xReturn;
    StreamBuffer_t xBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    lOptionName = FREERTOS_SO_SNDBUF;
    xSocket.u.xTCP.txStream = &xBuffer;

    xReturn = prvSockopt_so_buffer( &xSocket, lOptionName, vOptionValue );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_prvSockopt_so_buffer_InvalidOption3( void )
{
    FreeRTOS_Socket_t xSocket;
    int32_t lOptionName;
    uint32_t vOptionValue = 0xABCD1234;
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    lOptionName = FREERTOS_SO_RCVBUF;
    xSocket.u.xTCP.rxStream = NULL;

    xReturn = prvSockopt_so_buffer( &xSocket, lOptionName, &vOptionValue );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.u.xTCP.uxRxStreamSize );
}

void test_prvSockopt_so_buffer_InvalidOption4( void )
{
    FreeRTOS_Socket_t xSocket;
    int32_t lOptionName;
    uint8_t vOptionValue[ sizeof( uintptr_t ) ];
    BaseType_t xReturn;
    StreamBuffer_t xBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    lOptionName = FREERTOS_SO_RCVBUF;
    xSocket.u.xTCP.rxStream = &xBuffer;

    xReturn = prvSockopt_so_buffer( &xSocket, lOptionName, vOptionValue );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_NULLSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName;
    const void * pvOptionValue;
    size_t uxOptionLength;

    xReturn = FreeRTOS_setsockopt( NULL, lLevel, lOptionName, pvOptionValue, uxOptionLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_InvalidSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName;
    const void * pvOptionValue;
    size_t uxOptionLength;

    xReturn = FreeRTOS_setsockopt( FREERTOS_INVALID_SOCKET, lLevel, lOptionName, pvOptionValue, uxOptionLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_RecvTimeOut( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_RCVTIMEO;
    TickType_t vOptionValue = 0x123;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.xReceiveBlockTime );
}

void test_FreeRTOS_setsockopt_SendTimeOut( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SNDTIMEO;
    TickType_t vOptionValue = 0x123;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.xSendBlockTime );
}

void test_FreeRTOS_setsockopt_SendTimeOutUDP( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SNDTIMEO;
    TickType_t vOptionValue = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.xSendBlockTime );
}

void test_FreeRTOS_setsockopt_SendTimeOutUDPMoreBockingTime( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SNDTIMEO;
    TickType_t vOptionValue = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS + 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS, xSocket.xSendBlockTime );
}

void test_FreeRTOS_setsockopt_UDPMaxRxPackets( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_MAX_RX_PACKETS;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 100, xSocket.u.xUDP.uxMaxPackets );
}

void test_FreeRTOS_setsockopt_UDPMaxRxPacketsNonUDPSock( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_MAX_RX_PACKETS;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xUDP.uxMaxPackets );
}

void test_FreeRTOS_setsockopt_UDPChkSumNULL( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDPCKSUM_OUT;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.ucSocketOptions = ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, NULL, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0, xSocket.ucSocketOptions );
}

void test_FreeRTOS_setsockopt_UDPChkSum( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDPCKSUM_OUT;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( FREERTOS_SO_UDPCKSUM_OUT, xSocket.ucSocketOptions );
}

void test_FreeRTOS_setsockopt_TCPConnInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_CONN_HANDLER;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_TCPConnSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_CONN_HANDLER;
    F_TCP_UDP_Handler_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.pxOnTCPConnected = ( uintptr_t ) 0x123ABD;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0x123ABD, xSocket.u.xTCP.pxHandleConnected );
}

void test_FreeRTOS_setsockopt_TCPRecvInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_RECV_HANDLER;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_TCPRecvSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_RECV_HANDLER;
    F_TCP_UDP_Handler_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.pxOnTCPReceive = ( uintptr_t ) 0x123ABD;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0x123ABD, xSocket.u.xTCP.pxHandleReceive );
}

void test_FreeRTOS_setsockopt_TCPSendInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_SENT_HANDLER;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_TCPSendSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_SENT_HANDLER;
    F_TCP_UDP_Handler_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.pxOnTCPSent = ( uintptr_t ) 0x123ABD;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0x123ABD, xSocket.u.xTCP.pxHandleSent );
}

void test_FreeRTOS_setsockopt_UDPRecvInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_RECV_HANDLER;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_UDPRecvSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_RECV_HANDLER;
    F_TCP_UDP_Handler_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    vOptionValue.pxOnUDPReceive = ( uintptr_t ) 0x123ABD;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0x123ABD, xSocket.u.xUDP.pxHandleReceive );
}

void test_FreeRTOS_setsockopt_UDPSendInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_SENT_HANDLER;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_UDPSendSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_SENT_HANDLER;
    F_TCP_UDP_Handler_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    vOptionValue.pxOnUDPSent = ( uintptr_t ) 0x123ABD;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0x123ABD, xSocket.u.xUDP.pxHandleSent );
}

void test_FreeRTOS_setsockopt_SetSemaphore( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_SEMAPHORE;
    SemaphoreHandle_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.pxUserSemaphore );
}

void test_FreeRTOS_setsockopt_WakeUpCallback( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WAKEUP_CALLBACK;
    SemaphoreHandle_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( &vOptionValue, xSocket.pxUserWakeCallback );
}

void test_FreeRTOS_setsockopt_SetLowHighWaterInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_LOW_HIGH_WATER;
    SemaphoreHandle_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_SetLowHighWaterInvalidValues1( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_LOW_HIGH_WATER;
    LowHighWater_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.uxLittleSpace = 0x123;
    vOptionValue.uxEnoughSpace = vOptionValue.uxLittleSpace;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_SetLowHighWaterInvalidValues2( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_LOW_HIGH_WATER;
    LowHighWater_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.uxLittleSpace = 0x123;
    vOptionValue.uxEnoughSpace = vOptionValue.uxLittleSpace - 0x12;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_SetLowHighWaterInvalidValues3( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_LOW_HIGH_WATER;
    LowHighWater_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.uxLittleSpace = 0x123;
    vOptionValue.uxEnoughSpace = vOptionValue.uxLittleSpace + 0x123;
    xSocket.u.xTCP.uxRxStreamSize = vOptionValue.uxEnoughSpace - 0x12;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_SetLowHighWaterHappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_LOW_HIGH_WATER;
    LowHighWater_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.uxLittleSpace = 0x123;
    vOptionValue.uxEnoughSpace = vOptionValue.uxLittleSpace + 0x123;
    xSocket.u.xTCP.uxRxStreamSize = vOptionValue.uxEnoughSpace + 0x12;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue.uxLittleSpace, xSocket.u.xTCP.uxLittleSpace );
    TEST_ASSERT_EQUAL( vOptionValue.uxEnoughSpace, xSocket.u.xTCP.uxEnoughSpace );
}

void test_FreeRTOS_setsockopt_SendBuff( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SNDBUF;
    uint32_t vOptionValue = 0xABCD1234;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = NULL;
    xSocket.u.xTCP.usMSS = 0x12;

    FreeRTOS_round_up_ExpectAndReturn( vOptionValue, xSocket.u.xTCP.usMSS, 0xAB );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0xAB, xSocket.u.xTCP.uxTxStreamSize );
}

void test_FreeRTOS_setsockopt_RecvBuff( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_RCVBUF;
    uint32_t vOptionValue = 0xABCD1234;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.rxStream = NULL;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.u.xTCP.uxRxStreamSize );
}

void test_FreeRTOS_setsockopt_WinPropsInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WIN_PROPERTIES;
    uint32_t vOptionValue = 0xABCD1234;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_WinPropsInvalidTxStream( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WIN_PROPERTIES;
    uint32_t vOptionValue = 0xABCD1234;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = 0x1234;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_WinPropsInvalidRxStream( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WIN_PROPERTIES;
    WinProperties_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    vOptionValue.lTxBufSize = 0xBB;

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.rxStream = 0x1234;
    xSocket.u.xTCP.usMSS = 0x12;

    FreeRTOS_round_up_ExpectAndReturn( vOptionValue.lTxBufSize, xSocket.u.xTCP.usMSS, 0xAB );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_WinPropsTCPWinNotInit( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WIN_PROPERTIES;
    WinProperties_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &vOptionValue, 0xCB, sizeof( vOptionValue ) );

    vOptionValue.lTxBufSize = 0xBB;

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.usMSS = 0x12;
    xSocket.u.xTCP.xTCPWindow.u.bits.bHasInit = pdFALSE;

    FreeRTOS_round_up_ExpectAndReturn( vOptionValue.lTxBufSize, xSocket.u.xTCP.usMSS, 0xAB );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( ( uint32_t ) vOptionValue.lTxWinSize, xSocket.u.xTCP.uxRxWinSize );
    TEST_ASSERT_EQUAL( ( uint32_t ) vOptionValue.lTxWinSize, xSocket.u.xTCP.uxTxWinSize );
}

void test_FreeRTOS_setsockopt_WinPropsTCPWinInit( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WIN_PROPERTIES;
    WinProperties_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &vOptionValue, 0xCB, sizeof( vOptionValue ) );

    vOptionValue.lTxBufSize = 0xBB;

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.usMSS = 0x12;
    xSocket.u.xTCP.xTCPWindow.u.bits.bHasInit = pdTRUE;

    FreeRTOS_round_up_ExpectAndReturn( vOptionValue.lTxBufSize, xSocket.u.xTCP.usMSS, 0xAB );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( ( uint32_t ) vOptionValue.lRxWinSize, xSocket.u.xTCP.uxRxWinSize );
    TEST_ASSERT_EQUAL( ( uint32_t ) vOptionValue.lTxWinSize, xSocket.u.xTCP.uxTxWinSize );
    TEST_ASSERT_EQUAL_UINT32( ( ( uint32_t ) vOptionValue.lRxWinSize * xSocket.u.xTCP.usMSS ), xSocket.u.xTCP.xTCPWindow.xSize.ulRxWindowLength );
    TEST_ASSERT_EQUAL_UINT32( ( ( uint32_t ) vOptionValue.lTxWinSize * xSocket.u.xTCP.usMSS ), xSocket.u.xTCP.xTCPWindow.xSize.ulTxWindowLength );
}

void test_FreeRTOS_setsockopt_ReUseListenSock_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_REUSE_LISTEN_SOCKET;
    BaseType_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &vOptionValue, 0xCB, sizeof( vOptionValue ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_ReUseListenSock_Set( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_REUSE_LISTEN_SOCKET;
    BaseType_t vOptionValue = pdTRUE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bReuseSocket );
}

void test_FreeRTOS_setsockopt_ReUseListenSock_Reset( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_REUSE_LISTEN_SOCKET;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bReuseSocket );
}

void test_FreeRTOS_setsockopt_SockClose_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_CLOSE_AFTER_SEND;
    BaseType_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_SockClose_Set( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_CLOSE_AFTER_SEND;
    BaseType_t vOptionValue = pdTRUE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bCloseAfterSend );
}

void test_FreeRTOS_setsockopt_SockClose_Reset( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_CLOSE_AFTER_SEND;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bCloseAfterSend );
}

void test_FreeRTOS_setsockopt_SetFullSize_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_FULL_SIZE;
    BaseType_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_setsockopt_SetFullSize_Set( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_FULL_SIZE;
    BaseType_t vOptionValue = pdTRUE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.xTCPWindow.u.bits.bSendFullSize );
}

void test_FreeRTOS_setsockopt_SetFullSize_Reset_StateIncorrect( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_FULL_SIZE;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;
    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED - 1;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.xTCPWindow.u.bits.bSendFullSize );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.usTimeout );
}

void test_FreeRTOS_setsockopt_SetFullSize_Reset_StateCorrect( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_FULL_SIZE;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;
    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.xTCPWindow.u.bits.bSendFullSize );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.usTimeout );
}

void test_FreeRTOS_setsockopt_SetFullSize_Reset_HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_FULL_SIZE;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;
    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;
    xSocket.u.xTCP.txStream = ( uintptr_t ) 0xABCD;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.txStream, 0x123 );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdTRUE );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.xTCPWindow.u.bits.bSendFullSize );
    TEST_ASSERT_EQUAL( 1, xSocket.u.xTCP.usTimeout );
}

void test_FreeRTOS_setsockopt_StopRx_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_STOP_RX;
    BaseType_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.usTimeout );
}

void test_FreeRTOS_setsockopt_StopRx_Set( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_STOP_RX;
    BaseType_t vOptionValue = pdTRUE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bRxStopped );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1, xSocket.u.xTCP.usTimeout );
}

void test_FreeRTOS_setsockopt_StopRx_Reset( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_STOP_RX;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bRxStopped );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1, xSocket.u.xTCP.usTimeout );
}

void test_FreeRTOS_setsockopt_InvalidOption( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = 100;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOPROTOOPT, xReturn );
}

void test_prvGetPrivatePortNumber_TCP_RNGFails( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_TCP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( 0, usReturn );
}

void test_prvGetPrivatePortNumber_TCP_IPTaskNotReady( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_TCP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( 4, usReturn );
}

void test_prvGetPrivatePortNumber_TCP_Found( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_TCP;
    ListItem_t xLocalListEnd;
    ListItem_t xIterator;

    xRNGStatus = pdTRUE;
    xRandomNumberToReturn = 1234;
    TickType_t xWantedItemValue = 53768;

    xApplicationGetRandomNumber_Stub( xStubApplicationGetRandomNumber );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &xIterator );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &xIterator, xWantedItemValue );

    xApplicationGetRandomNumber_Stub( xStubApplicationGetRandomNumber );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( xWantedItemValue, usReturn );
}

void test_prvGetPrivatePortNumber_UDP_RNGFails( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_UDP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( 0, usReturn );
}

void test_prvGetPrivatePortNumber_UDP_IPTaskNotReady( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_UDP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( 4, usReturn );
}

void test_prvGetPrivatePortNumber_UDP_Found( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_UDP;
    ListItem_t xLocalListEnd;
    ListItem_t xIterator;

    xRNGStatus = pdTRUE;
    xRandomNumberToReturn = 1234;
    TickType_t xWantedItemValue = 53768;

    xApplicationGetRandomNumber_Stub( xStubApplicationGetRandomNumber );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( &( xBoundUDPSocketsList.xListEnd ), &xIterator );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &xIterator, xWantedItemValue );

    xApplicationGetRandomNumber_Stub( xStubApplicationGetRandomNumber );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( xWantedItemValue, usReturn );
}

void test_pxListFindListItemWithValue_NULLList( void )
{
    ListItem_t * pxReturn;
    List_t xList;
    TickType_t xWantedItemValue;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    pxReturn = pxListFindListItemWithValue( NULL, xWantedItemValue );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

void test_pxListFindListItemWithValue_IPTaskNotReady( void )
{
    ListItem_t * pxReturn;
    List_t xList;
    TickType_t xWantedItemValue;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    pxReturn = pxListFindListItemWithValue( &xList, xWantedItemValue );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

void test_pxListFindListItemWithValue_ListLengthZero( void )
{
    ListItem_t * pxReturn;
    List_t xList;
    TickType_t xWantedItemValue;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( &( xList.xListEnd ), &( xList.xListEnd ) );

    pxReturn = pxListFindListItemWithValue( &xList, xWantedItemValue );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

void test_pxListFindListItemWithValue_NotFound( void )
{
    ListItem_t * pxReturn;
    List_t xList;
    ListItem_t xLocalListItem;
    TickType_t xWantedItemValue = 0xABAB;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( &( xList.xListEnd ), &( xLocalListItem ) );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xLocalListItem ), xWantedItemValue - 1 );

    listGET_NEXT_ExpectAndReturn( &( xLocalListItem ), &( xList.xListEnd ) );

    pxReturn = pxListFindListItemWithValue( &xList, xWantedItemValue );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

void test_pxListFindListItemWithValue_Found( void )
{
    ListItem_t * pxReturn;
    List_t xList;
    ListItem_t xLocalListItem;
    TickType_t xWantedItemValue = 0xABAB;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( &( xList.xListEnd ), &( xLocalListItem ) );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xLocalListItem ), xWantedItemValue );

    pxReturn = pxListFindListItemWithValue( &xList, xWantedItemValue );

    TEST_ASSERT_EQUAL_UINT32( &( xLocalListItem ), pxReturn );
}

void test_pxUDPSocketLookup_NotFound( void )
{
    FreeRTOS_Socket_t * pxReturn;
    UBaseType_t uxLocalPort;

    vpxListFindListItemWithValue_NotFound();

    pxReturn = pxUDPSocketLookup( uxLocalPort );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

void test_pxUDPSocketLookup_FoundNULLSocket( void )
{
    FreeRTOS_Socket_t * pxReturn;
    UBaseType_t uxLocalPort = 0xBCDEF;
    ListItem_t xListItem;

    vpxListFindListItemWithValue_Found( &xBoundUDPSocketsList, uxLocalPort, &xListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xListItem, NULL );

    catch_assert( pxUDPSocketLookup( uxLocalPort ) );
}

void test_pxUDPSocketLookup_Found( void )
{
    FreeRTOS_Socket_t * pxReturn;
    UBaseType_t uxLocalPort = 0xBCDEF;
    ListItem_t xListItem;
    FreeRTOS_Socket_t xLocalSocket;

    vpxListFindListItemWithValue_Found( &xBoundUDPSocketsList, uxLocalPort, &xListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xListItem, &xLocalSocket );

    pxReturn = pxUDPSocketLookup( uxLocalPort );

    TEST_ASSERT_EQUAL( &xLocalSocket, pxReturn );
}

void test_FreeRTOS_inet_ntoa_1( void )
{
    char * pucReturn;
    uint32_t ulIPAddress = 0;
    char pcBuffer[ 255 ];
    char * pucIdealReturn = "0.0.0.0";

    pucReturn = FreeRTOS_inet_ntoa( ulIPAddress, pcBuffer );

    TEST_ASSERT_EQUAL( pucReturn, pcBuffer );
    TEST_ASSERT_EQUAL_STRING( pucIdealReturn, pucReturn );
}

void test_FreeRTOS_inet_ntoa_2( void )
{
    char * pucReturn;
    uint32_t ulIPAddress = 0xAAAAAAAA;
    char pcBuffer[ 255 ];
    char * pucIdealReturn = "170.170.170.170";

    pucReturn = FreeRTOS_inet_ntoa( ulIPAddress, pcBuffer );

    TEST_ASSERT_EQUAL( pucReturn, pcBuffer );
    TEST_ASSERT_EQUAL_STRING( pucIdealReturn, pucReturn );
}

void test_FreeRTOS_inet_ntoa_3( void )
{
    char * pucReturn;
    uint32_t ulIPAddress = 0xFFFFFFFF;
    char pcBuffer[ 255 ];
    char * pucIdealReturn = "255.255.255.255";

    pucReturn = FreeRTOS_inet_ntoa( ulIPAddress, pcBuffer );

    TEST_ASSERT_EQUAL( pucReturn, pcBuffer );
    TEST_ASSERT_EQUAL_STRING( pucIdealReturn, pucReturn );
}

void test_FreeRTOS_inet_pton_IncorrectAddressFamily( void )
{
    BaseType_t xReturn;
    BaseType_t xAddressFamily = FREERTOS_AF_INET + 1;
    const char * pcSource;
    void * pvDestination;

    xReturn = FreeRTOS_inet_pton( xAddressFamily, pcSource, pvDestination );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAFNOSUPPORT, xReturn );
}

void test_FreeRTOS_inet_pton_Octal( void )
{
    BaseType_t xReturn;
    BaseType_t xAddressFamily = FREERTOS_AF_INET;
    const char * pcSource = "00.01.2.3";
    uint32_t ulDestination = 0;

    xReturn = FreeRTOS_inet_pton( xAddressFamily, pcSource, &ulDestination );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL( 0, ulDestination );
}

void test_FreeRTOS_inet_pton_HappyPath( void )
{
    BaseType_t xReturn;
    BaseType_t xAddressFamily = FREERTOS_AF_INET;
    const char * pcSource = "255.255.255.255";
    uint32_t ulDestination;

    xReturn = FreeRTOS_inet_pton( xAddressFamily, pcSource, &ulDestination );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL_UINT32( 0xFFFFFFFF, ulDestination );
}

void test_FreeRTOS_inet_ntop_IncorrectAddrFamily( void )
{
    char * pucReturn;
    BaseType_t xAddressFamily = FREERTOS_AF_INET + 1;
    uint32_t ulSource;
    char * pcDestination;
    socklen_t uxSize;

    pucReturn = FreeRTOS_inet_ntop( xAddressFamily, &ulSource, pcDestination, uxSize );

    TEST_ASSERT_EQUAL( NULL, pucReturn );
}

void test_FreeRTOS_inet_ntop_IncorrectSize( void )
{
    char * pucReturn;
    BaseType_t xAddressFamily = FREERTOS_AF_INET;
    uint32_t ulSource;
    const socklen_t uxSize = 15;
    char pcDestination[ uxSize ];

    pucReturn = FreeRTOS_inet_ntop( xAddressFamily, &ulSource, pcDestination, uxSize );

    TEST_ASSERT_EQUAL( NULL, pucReturn );
}

void test_FreeRTOS_inet_ntop_HappyCase( void )
{
    char * pucReturn;
    BaseType_t xAddressFamily = FREERTOS_AF_INET;
    uint32_t ulSource;
    const socklen_t uxSize = 16;
    char pcDestination[ uxSize ];

    ulSource = 0xFFFFFFFF;
    pucReturn = FreeRTOS_inet_ntop( xAddressFamily, &ulSource, pcDestination, uxSize );

    TEST_ASSERT_EQUAL( pcDestination, pucReturn );
    TEST_ASSERT_EQUAL_STRING( "255.255.255.255", pcDestination );

    ulSource = 0;
    pucReturn = FreeRTOS_inet_ntop( xAddressFamily, &ulSource, pcDestination, uxSize );

    TEST_ASSERT_EQUAL( pcDestination, pucReturn );
    TEST_ASSERT_EQUAL_STRING( "0.0.0.0", pcDestination );

    ulSource = 0xABCDEF12;
    pucReturn = FreeRTOS_inet_ntop( xAddressFamily, &ulSource, pcDestination, uxSize );

    TEST_ASSERT_EQUAL( pcDestination, pucReturn );
    TEST_ASSERT_EQUAL_STRING( "18.239.205.171", pcDestination );
}

void test_ucASCIIToHex( void )
{
    uint8_t ucHex, IdealValue;
    char ucInput;

    ucInput = '0';
    IdealValue = 0;

    for( int i = 0; i <= 9; i++ )
    {
        ucHex = ucASCIIToHex( ucInput + i );
        TEST_ASSERT_EQUAL( IdealValue + i, ucHex );
    }

    ucInput = 'a';
    IdealValue = 10;

    for( int i = 0; i < 6; i++ )
    {
        ucHex = ucASCIIToHex( ucInput + i );
        TEST_ASSERT_EQUAL( IdealValue + i, ucHex );
    }

    ucInput = 'A';
    IdealValue = 10;

    for( int i = 0; i < 6; i++ )
    {
        ucHex = ucASCIIToHex( ucInput + i );
        TEST_ASSERT_EQUAL( IdealValue + i, ucHex );
    }

    for( char i = 0; ; i++ )
    {
        if( !( ( ( i >= 'a' ) && ( i <= 'f' ) ) ||
               ( ( i >= 'A' ) && ( i <= 'F' ) ) ||
               ( ( i >= '0' ) && ( i <= '9' ) ) ) )
        {
            ucHex = ucASCIIToHex( i );
            TEST_ASSERT_EQUAL( 0xFF, ucHex );
        }

        if( i == 125 )
        {
            break;
        }
    }
}

void test_FreeRTOS_EUI48_ntop1( void )
{
    uint8_t pucSource[ 6 ] = { 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA };
    char pcTarget[ 18 ];
    char cTen = 'A';
    char cSeparator = ':';

    memset( pcTarget, 0, sizeof( pcTarget ) );

    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "AA:AA:AA:AA:AA:AA", pcTarget );

    cTen = 'a';
    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "aa:aa:aa:aa:aa:aa", pcTarget );

    cTen = 'a';
    cSeparator = '-';
    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "aa-aa-aa-aa-aa-aa", pcTarget );
}

void test_FreeRTOS_EUI48_ntop2( void )
{
    uint8_t pucSource[ 6 ] = { 0x12, 0x34, 0x56, 0x78, 0xef, 0xdc };
    char pcTarget[ 18 ];
    char cTen = 'A';
    char cSeparator = ':';

    memset( pcTarget, 0, sizeof( pcTarget ) );

    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "12:34:56:78:EF:DC", pcTarget );

    cSeparator = '-';
    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "12-34-56-78-EF-DC", pcTarget );

    cTen = 'a';
    cSeparator = ':';
    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "12:34:56:78:ef:dc", pcTarget );

    cTen = 'a';
    cSeparator = '-';
    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "12-34-56-78-ef-dc", pcTarget );
}

void test_FreeRTOS_EUI48_pton_InvalidInput( void )
{
    BaseType_t xReturn;
    const char * pcSource = "12345678::::";
    uint8_t pucTarget[ 6 ];

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_FreeRTOS_EUI48_pton_InvalidInput2( void )
{
    BaseType_t xReturn;
    const char * pcSource = "12:34:56:78:ab:ty";
    uint8_t pucTarget[ 6 ];

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_FreeRTOS_EUI48_pton_InvalidInput3( void )
{
    BaseType_t xReturn;
    const char * pcSource = "12:34#56:78:ab:cd";
    uint8_t pucTarget[ 6 ];

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_FreeRTOS_EUI48_pton_InvalidInput4( void )
{
    BaseType_t xReturn;
    const char * pcSource = "";
    uint8_t pucTarget[ 6 ];

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_FreeRTOS_EUI48_pton_HappyPath( void )
{
    BaseType_t xReturn;
    const char * pcSource = "12:34:56:78:ab:cd";
    uint8_t pucTarget[ 6 ];
    uint8_t pucIdeal[] = { 0x12, 0x34, 0x56, 0x78, 0xab, 0xcd };

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( pucIdeal, pucTarget, 6 );
}

void test_FreeRTOS_EUI48_pton_HappyPath1( void )
{
    BaseType_t xReturn;
    const char * pcSource = "12-34-56-78-ab-cd";
    uint8_t pucTarget[ 6 ];
    uint8_t pucIdeal[] = { 0x12, 0x34, 0x56, 0x78, 0xab, 0xcd };

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( pucIdeal, pucTarget, 6 );
}

void test_FreeRTOS_EUI48_pton_HappyPath2( void )
{
    BaseType_t xReturn;
    const char * pcSource = "FF-34-56-78-ab-cd";
    uint8_t pucTarget[ 6 ];
    uint8_t pucIdeal[] = { 0xff, 0x34, 0x56, 0x78, 0xab, 0xcd };

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( pucIdeal, pucTarget, 6 );
}

void test_FreeRTOS_inet_addr_InvalidString( void )
{
    uint32_t ulReturn;
    char * pcIPAddress = "0..12.34.4";

    ulReturn = FreeRTOS_inet_addr( pcIPAddress );
    TEST_ASSERT_EQUAL( 0, ulReturn );
}

void test_FreeRTOS_inet_addr_ValidString( void )
{
    uint32_t ulReturn;
    char * pcIPAddress = "1.2.3.4";

    ulReturn = FreeRTOS_inet_addr( pcIPAddress );
    TEST_ASSERT_EQUAL( 0x04030201, ulReturn );
}

void test_FreeRTOS_GetLocalAddress( void )
{
    size_t uxReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.usLocalPort = 0xAB12;
    *ipLOCAL_IP_ADDRESS_POINTER = 0xABFC8769;

    uxReturn = FreeRTOS_GetLocalAddress( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( sizeof( xAddress ), uxReturn );
    TEST_ASSERT_EQUAL( 0xABFC8769, xAddress.sin_addr );
    TEST_ASSERT_EQUAL( FreeRTOS_htons( 0xAB12 ), xAddress.sin_port );
}

void test_vSocketWakeUpUser_AllNULL( void )
{
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    vSocketWakeUpUser( &xSocket );

    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
}

void test_vSocketWakeUpUser_AllNonNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    uint8_t xLocalSemaphore[ sizeof( xSocket.pxUserSemaphore ) ];
    uint8_t xLocalSocketSet[ sizeof( xSocket.pxSocketSet ) ];
    uint8_t xLocalEventGroup[ sizeof( xSocket.xEventGroup ) ];

    uxGlobalCallbackCount = 0;
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.pxUserSemaphore = xLocalSemaphore;
    xSocket.pxUserWakeCallback = vUserCallbackLocal;
    xSocket.pxSocketSet = xLocalSocketSet;
    xSocket.xEventGroup = xLocalEventGroup;

    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    vSocketWakeUpUser( &xSocket );

    TEST_ASSERT_EQUAL( 1, uxGlobalCallbackCount );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
}

void test_vSocketWakeUpUser_AllNonNULL_EventBitsSet( void )
{
    FreeRTOS_Socket_t xSocket;
    uint8_t xLocalSemaphore[ sizeof( xSocket.pxUserSemaphore ) ];
    uint8_t xLocalSocketSet[ sizeof( xSocket.pxSocketSet ) ];
    uint8_t xLocalEventGroup[ sizeof( xSocket.xEventGroup ) ];

    uxGlobalCallbackCount = 0;
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.pxUserSemaphore = xLocalSemaphore;
    xSocket.pxUserWakeCallback = vUserCallbackLocal;
    xSocket.pxSocketSet = xLocalSocketSet;
    xSocket.xEventGroup = xLocalEventGroup;

    xSocket.xEventBits = ( eSOCKET_ALL << SOCKET_EVENT_BIT_COUNT ) | eSOCKET_ALL;

    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSOCKET_ALL & eSELECT_ALL, pdPASS );
    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_ALL, pdPASS );

    vSocketWakeUpUser( &xSocket );

    TEST_ASSERT_EQUAL( 1, uxGlobalCallbackCount );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
}

void test_bMayConnect( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.ucTCPState = eCLOSED;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    xSocket.u.xTCP.ucTCPState = eCLOSE_WAIT;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    xSocket.u.xTCP.ucTCPState = eCONNECT_SYN;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINPROGRESS, xReturn );

    xSocket.u.xTCP.ucTCPState = eTCP_LISTEN;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.ucTCPState = eSYN_FIRST;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.ucTCPState = eSYN_RECEIVED;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.ucTCPState = eFIN_WAIT_1;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.ucTCPState = eFIN_WAIT_2;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.ucTCPState = eCLOSING;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.ucTCPState = eLAST_ACK;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.ucTCPState = eTIME_WAIT;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );
}

void test_prvTCPConnectStart_AddressNULL( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xReturn = prvTCPConnectStart( &xSocket, NULL );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_prvTCPConnectStart_InvalidSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EBADF, xReturn );
}

void test_prvTCPConnectStart_SocketAlreadyConnected( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EISCONN, xReturn );
}

void test_prvTCPConnectStart_SocketNotBound_Success( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    xEventGroupWaitBits_ExpectAnyArgsAndReturn( pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xSocket, eCONNECT_SYN );

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_prvTCPConnectStart_SocketNotBound_Failure( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    xEventGroupWaitBits_ExpectAnyArgsAndReturn( pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xSocket, eCONNECT_SYN );

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFAIL );

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ECANCELED, xReturn );
}

void test_prvTCPConnectStart_SocketNotBound_Failure2( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eCONNECT_SYN;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    xEventGroupWaitBits_ExpectAnyArgsAndReturn( pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), &xBoundTCPSocketsList );

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINPROGRESS, xReturn );
}

void test_prvTCPConnectStart_SocketBound_Failure( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eCONNECT_SYN;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), &xBoundTCPSocketsList );

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINPROGRESS, xReturn );
}

void test_FreeRTOS_connect_SocketValuesNULL( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EBADF, xResult );
}

void test_FreeRTOS_connect_InvalidValues( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid protocol. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EBADF, xResult );

    /* Socket not bound. Binding failed. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );
    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ECANCELED, xResult );

    /* Socket NULL. */
    xResult = FreeRTOS_connect( NULL, &xAddress, xAddressLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EBADF, xResult );

    /* Address NULL. */
    xResult = FreeRTOS_connect( &xSocket, NULL, xAddressLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xResult );
}

void test_FreeRTOS_connect_NonBlocking( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xSocket, eCONNECT_SYN );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EWOULDBLOCK, xResult );
}

void test_FreeRTOS_connect_Timeout( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    /* Non 0 value to show blocking. */
    xSocket.xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xSocket, eCONNECT_SYN );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    /* Using a local variable. */
    vTaskSetTimeOutState_ExpectAnyArgs();

    /* No timeout the first time. */
    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_CONNECT, pdTRUE, pdFALSE, xSocket.xReceiveBlockTime, pdTRUE );

    /* Timed out! */
    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ETIMEDOUT, xResult );
}

void test_FreeRTOS_connect_Connected( void )
{
    BaseType_t xResult;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xGlobalSocket, 0, sizeof( xGlobalSocket ) );

    xGlobalSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    /* Non 0 value to show blocking. */
    xGlobalSocket.xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xGlobalSocket, eCONNECT_SYN );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    /* Using a local variable. */
    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_Stub( xStubForEventGroupWaitBits );

    xResult = FreeRTOS_connect( &xGlobalSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( 0, xResult );
}

void test_FreeRTOS_accept_InvalidParams( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );

    /* Invalid Protocol */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, pxReturn );

    /* NULL socket. */
    pxReturn = FreeRTOS_accept( NULL, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, pxReturn );

    /* Unbound Socket */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, pxReturn );

    /* Socket is not in listen mode. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN + 1;
    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, pxReturn );
}

void test_FreeRTOS_accept_ClientSocketTaken( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn, xPeerSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );
    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );

    /* Invalid Protocol */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;

    xServerSocket.u.xTCP.pxPeerSocket = &xPeerSocket;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( NULL, pxReturn );
    TEST_ASSERT_EQUAL( NULL, xServerSocket.u.xTCP.pxPeerSocket );
}

void test_FreeRTOS_accept_PeerSocketNULL( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn, xPeerSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );
    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;

    xServerSocket.u.xTCP.pxPeerSocket = NULL;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( NULL, pxReturn );
    TEST_ASSERT_EQUAL( NULL, xServerSocket.u.xTCP.pxPeerSocket );
}

void test_FreeRTOS_accept_NotReuseSocket( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn, xPeerSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength = 0;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );
    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;

    xServerSocket.u.xTCP.pxPeerSocket = &xPeerSocket;
    xPeerSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xPeerSocket.u.xTCP.ulRemoteIP = 0xAABBCCDD;
    xPeerSocket.u.xTCP.usRemotePort = 0x1234;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( &xPeerSocket, pxReturn );
    TEST_ASSERT_EQUAL( NULL, xServerSocket.u.xTCP.pxPeerSocket );
    TEST_ASSERT_EQUAL( pdFALSE, xPeerSocket.u.xTCP.bits.bPassAccept );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohl( xPeerSocket.u.xTCP.ulRemoteIP ), xAddress.sin_addr );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xPeerSocket.u.xTCP.usRemotePort ), xAddress.sin_port );
    TEST_ASSERT_EQUAL( sizeof( xAddress ), xAddressLength );
}

void test_FreeRTOS_accept_ReuseSocket( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn, xPeerSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength = 0;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );
    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xServerSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
    xServerSocket.u.xTCP.pxPeerSocket = &xPeerSocket;
    xServerSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xServerSocket.u.xTCP.ulRemoteIP = 0xAABBCCDD;
    xServerSocket.u.xTCP.usRemotePort = 0x1234;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( &xServerSocket, pxReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xServerSocket.u.xTCP.bits.bPassAccept );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohl( xServerSocket.u.xTCP.ulRemoteIP ), xAddress.sin_addr );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xServerSocket.u.xTCP.usRemotePort ), xAddress.sin_port );
    TEST_ASSERT_EQUAL( sizeof( xAddress ), xAddressLength );
}

void test_FreeRTOS_accept_ReuseSocket_NULLAddress( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn, xPeerSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength = 0;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );
    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xServerSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
    xServerSocket.u.xTCP.pxPeerSocket = &xPeerSocket;
    xServerSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xServerSocket.u.xTCP.ulRemoteIP = 0xAABBCCDD;
    xServerSocket.u.xTCP.usRemotePort = 0x1234;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    pxReturn = FreeRTOS_accept( &xServerSocket, NULL, NULL );
    TEST_ASSERT_EQUAL( &xServerSocket, pxReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xServerSocket.u.xTCP.bits.bPassAccept );
}

void test_FreeRTOS_accept_ReuseSocket_Timeout( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn, xPeerSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength = 0;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );
    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xServerSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
    xServerSocket.u.xTCP.pxPeerSocket = &xPeerSocket;
    xServerSocket.u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;
    xServerSocket.u.xTCP.ulRemoteIP = 0xAABBCCDD;
    xServerSocket.u.xTCP.usRemotePort = 0x1234;
    xServerSocket.xReceiveBlockTime = 0xAA;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xServerSocket.xEventGroup, eSOCKET_ACCEPT, pdTRUE, pdFALSE, 0xAA, pdFALSE );

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( NULL, pxReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xServerSocket.u.xTCP.bits.bPassAccept );
}

void test_FreeRTOS_recv_InvalidValues( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* NULL socket. */
    xReturn = FreeRTOS_recv( NULL, pvBuffer, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Unbound Socket */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    xFlags = FREERTOS_ZERO_COPY;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xReturn = FreeRTOS_recv( &xSocket, NULL, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_recv_NotConnectedAndNoMemory( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOTCONN, xReturn );

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bMallocError = pdTRUE_UNSIGNED;
    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOMEM, xReturn );
}

void test_FreeRTOS_recv_EstablishedConnection_NoWait( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_INTR, pdTRUE, pdFALSE, 0, 0 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_FreeRTOS_recv_TimeOut( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_FreeRTOS_recv_Interrupted( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED | ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0xAA, eSOCKET_INTR );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINTR, xReturn );
}

void test_FreeRTOS_recv_Interrupted1( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED | ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0xAA, eSOCKET_RECEIVE | eSOCKET_CLOSED | eSOCKET_INTR );

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE | eSOCKET_CLOSED, 0 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINTR, xReturn );
}

void test_FreeRTOS_recv_RxStreamNULL( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED | ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0xAA, 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_FreeRTOS_recv_12BytesAlreadyInBuffer( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = pvBuffer;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    uxStreamBufferGet_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0U, pvBuffer, ( size_t ) uxBufferLength, 0, 12 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 12, xReturn );
}

void test_FreeRTOS_recv_LowWaterReached( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = pvBuffer;
    xSocket.u.xTCP.bits.bLowWater = pdTRUE_UNSIGNED;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    uxStreamBufferGet_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0U, pvBuffer, ( size_t ) uxBufferLength, 0, 12 );

    uxStreamBufferFrontSpace_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdTRUE );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 12, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1U, xSocket.u.xTCP.usTimeout );
}

void test_FreeRTOS_recv_LowWaterReached2( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = pvBuffer;
    xSocket.u.xTCP.bits.bLowWater = pdTRUE_UNSIGNED;
    xSocket.u.xTCP.uxEnoughSpace = 13;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    uxStreamBufferGet_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0U, pvBuffer, ( size_t ) uxBufferLength, 0, 12 );

    uxStreamBufferFrontSpace_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 12, xReturn );
}

void test_FreeRTOS_recv_12BytesArriveLater( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = pvBuffer;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED | ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0xAA, 0 );

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    uxStreamBufferGetPtr_ExpectAndReturn( xSocket.u.xTCP.rxStream, pvBuffer, 12 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 12, xReturn );
}

void test_FreeRTOS_recv_12BytesArriveLater_Timeout( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = FREERTOS_ZERO_COPY | FREERTOS_MSG_DONTWAIT;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = pvBuffer;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_prvTCPSendCheck_InvalidValues( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxDataLength;
    uint8_t ucStream[ 1500 ];
    uint8_t array[] = { eCLOSED, eCLOSE_WAIT, eCLOSING };
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid protocol. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, lReturn );

    /* Unbound socket. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, lReturn );

    /* No memory. */
    xSocket.u.xTCP.bits.bMallocError = pdTRUE;
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOMEM, lReturn );

    /* Invalid states. */
    xSocket.u.xTCP.bits.bMallocError = pdFALSE;
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    for( int i = 0; i < sizeof( array ); i++ )
    {
        xSocket.u.xTCP.ucTCPState = array[ i ];
        listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
        lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
        TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOTCONN, lReturn );
    }

    /* Closing connection. */
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( 0, lReturn );

    /* 0 data length. */
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    uxDataLength = 0;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( 0, lReturn );

    /* Couldn't allocate a stream. */
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    uxDataLength = 10;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );
    vTCPStateChange_ExpectAnyArgs();
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOMEM, lReturn );

    /* Allocate a stream. */
    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    uxDataLength = 10;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    size_t xSizeOfBufferRequested = ( ( sizeof( size_t ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xLocalStreamBuffer ) ) - sizeof( xLocalStreamBuffer.ucArray );
    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( 1, lReturn );
    TEST_ASSERT_EQUAL( ( sizeof( size_t ) & ( ~( sizeof( size_t ) - 1U ) ) ), ( ( StreamBuffer_t * ) ucStream )->LENGTH );
    TEST_ASSERT_EQUAL( ucStream, xSocket.u.xTCP.txStream );

    /* Already allocated a stream. */
    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    uxDataLength = 10;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( 1, lReturn );
}

void test_FreeRTOS_get_tx_head_InvalidParams( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    pucReturn = FreeRTOS_get_tx_head( &xSocket, &xLength );
    TEST_ASSERT_EQUAL( NULL, pucReturn );

    /* NULL socket. */
    pucReturn = FreeRTOS_get_tx_head( NULL, &xLength );
    TEST_ASSERT_EQUAL( NULL, pucReturn );

    /* NULL stream. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    pucReturn = FreeRTOS_get_tx_head( &xSocket, &xLength );
    TEST_ASSERT_EQUAL( NULL, pucReturn );
}

void test_FreeRTOS_get_tx_head_AllNULL( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xLength;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucStream, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    uxStreamBufferGetSpace_ExpectAndReturn( ucStream, 0 );

    pucReturn = FreeRTOS_get_tx_head( &xSocket, &xLength );
    TEST_ASSERT_EQUAL_UINT32( ( ( StreamBuffer_t * ) ucStream )->ucArray, pucReturn );
    TEST_ASSERT_EQUAL( 0, xLength );
}

void test_FreeRTOS_get_tx_head_LessSpace( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xLength;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucStream, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    ( ( StreamBuffer_t * ) ucStream )->LENGTH = 20;
    ( ( StreamBuffer_t * ) ucStream )->uxHead = 10;

    uxStreamBufferGetSpace_ExpectAndReturn( ucStream, 10 );

    pucReturn = FreeRTOS_get_tx_head( &xSocket, &xLength );
    TEST_ASSERT_EQUAL_UINT32( &( ( ( StreamBuffer_t * ) ucStream )->ucArray[ 10 ] ), pucReturn );
    TEST_ASSERT_EQUAL( 10, xLength );
}

void test_FreeRTOS_get_tx_head_MoreSpace( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xLength;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucStream, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    ( ( StreamBuffer_t * ) ucStream )->LENGTH = 200;
    ( ( StreamBuffer_t * ) ucStream )->uxHead = 10;

    uxStreamBufferGetSpace_ExpectAndReturn( ucStream, 10 );

    pucReturn = FreeRTOS_get_tx_head( &xSocket, &xLength );
    TEST_ASSERT_EQUAL_UINT32( &( ( ( StreamBuffer_t * ) ucStream )->ucArray[ 10 ] ), pucReturn );
    TEST_ASSERT_EQUAL( 10, xLength );
}

void test_FreeRTOS_send_InvalidInput( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    uxDataLength = 0;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );
    TEST_ASSERT_EQUAL( 0, xReturn );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 0 );
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );
    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOSPC, xReturn );

    /* Socket is not connected any more. */
    xSocket.u.xTCP.ucTCPState = eESTABLISHED + 1;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 0 );
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );
    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOTCONN, xReturn );
}

void test_FreeRTOS_send_ExactSpaceInStreamBuffer( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags;
    StreamBuffer_t xLocalStreamBuffer;

    /* 1. Last set of bytes. */
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.u.xTCP.bits.bCloseAfterSend = pdTRUE_UNSIGNED;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength );
    vTaskSuspendAll_Expect();
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength, uxDataLength );
    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );
    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bCloseRequested );


    /* 2. Not last set of bytes. */
    xSocket.u.xTCP.bits.bCloseAfterSend = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.bits.bCloseRequested = pdFALSE;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength, uxDataLength );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );
    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bCloseRequested );
}

void test_FreeRTOS_send_MoreSpaceInStreamBuffer( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.u.xTCP.bits.bCloseAfterSend = pdTRUE_UNSIGNED;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength + 20 );
    vTaskSuspendAll_Expect();
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength, uxDataLength );
    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );
    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bCloseRequested );
}

void test_FreeRTOS_send_LessSpaceInStreamBuffer_Timeout( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags = 0;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.u.xTCP.bits.bCloseAfterSend = pdTRUE_UNSIGNED;
    xSocket.xSendBlockTime = 100;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength - 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength - 20, uxDataLength - 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    vTaskSetTimeOutState_ExpectAnyArgs();
    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_SEND | eSOCKET_CLOSED, pdTRUE, pdFALSE, 100, pdFALSE );

    /* Second Iteration. No space still. */
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength - 20, xReturn );
}

void test_FreeRTOS_send_LessSpaceInStreamBuffer_EventuallySpaceAvailable( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags = 0;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.xSendBlockTime = 100;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength - 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength - 20, uxDataLength - 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    vTaskSetTimeOutState_ExpectAnyArgs();
    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_SEND | eSOCKET_CLOSED, pdTRUE, pdFALSE, 100, pdFALSE );

    /* Second Iteration. */
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, &pvBuffer[ 80 ], 20, 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );

    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength, xReturn );
}

void test_FreeRTOS_send_MultipleIterationsAndNoSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags = 0;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.xSendBlockTime = 100;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength - 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength - 20, uxDataLength - 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    vTaskSetTimeOutState_ExpectAnyArgs();
    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_SEND | eSOCKET_CLOSED, pdTRUE, pdFALSE, 100, pdFALSE );

    /* Second Iteration. */
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 10 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, &pvBuffer[ 80 ], 10, 10 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_SEND | eSOCKET_CLOSED, pdTRUE, pdFALSE, 100, pdFALSE );

    /* Third iteration. No space still. */
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength - 10, xReturn );
}

void test_FreeRTOS_send_IPTaskWithNULLBuffer( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags = 0;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.xSendBlockTime = 100;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength - 20 );

    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, NULL, uxDataLength - 20, uxDataLength - 20 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xReturn = FreeRTOS_send( &xSocket, NULL, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength - 20, xReturn );
}

void test_FreeRTOS_send_DontWaitFlag( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags = FREERTOS_MSG_DONTWAIT;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.xSendBlockTime = 100;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength - 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength - 20, uxDataLength - 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength - 20, xReturn );
}

void test_FreeRTOS_listen_InvalidValues( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xBacklog;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* Unbound. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* NULL socket. */
    xReturn = FreeRTOS_listen( NULL, xBacklog );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* Invalid state. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );
}

void test_FreeRTOS_listen_Success( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xBacklog = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eCLOSED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    FreeRTOS_min_int32_ExpectAndReturn( ( int32_t ) 0xffff, ( int32_t ) xBacklog, xBacklog );

    vTCPStateChange_Expect( &xSocket, eTCP_LISTEN );

    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( 0, xReturn );

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eCLOSE_WAIT;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    FreeRTOS_min_int32_ExpectAndReturn( ( int32_t ) 0xffff, ( int32_t ) xBacklog, xBacklog );

    vTCPStateChange_Expect( &xSocket, eTCP_LISTEN );

    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_FreeRTOS_listen_Success_WithReuseSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xBacklog = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eCLOSED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    memset( xSocket.u.xTCP.xPacket.u.ucLastPacket, 0xFF, sizeof( xSocket.u.xTCP.xPacket.u.ucLastPacket ) );
    memset( &xSocket.u.xTCP.xTCPWindow, 0xFF, sizeof( xSocket.u.xTCP.xTCPWindow ) );
    memset( &xSocket.u.xTCP.bits, 0xFF, sizeof( xSocket.u.xTCP.bits ) );

    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;

    FreeRTOS_min_int32_ExpectAndReturn( ( int32_t ) 0xffff, ( int32_t ) xBacklog, xBacklog );

    vTCPStateChange_Expect( &xSocket, eTCP_LISTEN );

    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bReuseSocket );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, xSocket.u.xTCP.xPacket.u.ucLastPacket, sizeof( xSocket.u.xTCP.xPacket.u.ucLastPacket ) );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xSocket.u.xTCP.xTCPWindow, sizeof( xSocket.u.xTCP.xTCPWindow ) );
}

void test_FreeRTOS_listen_Success_WithReuseSocket_StreamsNonNULL( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xBacklog = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eCLOSED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    memset( xSocket.u.xTCP.xPacket.u.ucLastPacket, 0xFF, sizeof( xSocket.u.xTCP.xPacket.u.ucLastPacket ) );
    memset( &xSocket.u.xTCP.xTCPWindow, 0xFF, sizeof( xSocket.u.xTCP.xTCPWindow ) );
    memset( &xSocket.u.xTCP.bits, 0xFF, sizeof( xSocket.u.xTCP.bits ) );

    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
    xSocket.u.xTCP.rxStream = &xReturn;
    xSocket.u.xTCP.txStream = &xReturn;

    FreeRTOS_min_int32_ExpectAndReturn( ( int32_t ) 0xffff, ( int32_t ) xBacklog, xBacklog );

    vStreamBufferClear_Expect( xSocket.u.xTCP.rxStream );
    vStreamBufferClear_Expect( xSocket.u.xTCP.txStream );

    vTCPStateChange_Expect( &xSocket, eTCP_LISTEN );

    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bReuseSocket );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, xSocket.u.xTCP.xPacket.u.ucLastPacket, sizeof( xSocket.u.xTCP.xPacket.u.ucLastPacket ) );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xSocket.u.xTCP.xTCPWindow, sizeof( xSocket.u.xTCP.xTCPWindow ) );
}

void test_FreeRTOS_shutdown_Invalid( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xHow;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xReturn = FreeRTOS_shutdown( &xSocket, xHow );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* Unbound. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xReturn = FreeRTOS_shutdown( &xSocket, xHow );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* NULL socket. */
    xReturn = FreeRTOS_shutdown( NULL, xHow );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* Invalid state. */
    for( int i = 0; i < 255; i++ )
    {
        if( i != eESTABLISHED )
        {
            xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
            xSocket.u.xTCP.ucTCPState = i;
            listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
            xReturn = FreeRTOS_shutdown( &xSocket, xHow );
            TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOTCONN, xReturn );
        }
    }
}

void test_FreeRTOS_shutdown_Success( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xHow;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );

    xReturn = FreeRTOS_shutdown( &xSocket, xHow );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bUserShutdown );
    TEST_ASSERT_EQUAL( 1U, xSocket.u.xTCP.usTimeout );
}

void test_xTCPTimerCheck_EmptyList( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep;

    xTaskGetTickCount_ExpectAndReturn( 0 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &( xBoundTCPSocketsList.xListEnd ) );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 1000 ), xReturn );
}

void test_xTCPTimerCheck_NonEmptyList_SocketCheckError( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.u.xTCP.usTimeout = 10;

    xTaskGetTickCount_ExpectAndReturn( 100 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &( xBoundTCPSocketsList.xListEnd ) );

    xTCPSocketCheck_ExpectAndReturn( &xSocket, -1 );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 1000 ), xReturn );
}

void test_xTCPTimerCheck_NonEmptyList_NoError( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.usTimeout = 10;

    xTaskGetTickCount_ExpectAndReturn( 100 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &( xBoundTCPSocketsList.xListEnd ) );

    xTCPSocketCheck_ExpectAndReturn( &xSocket, 0 );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 1000 ), xReturn );
}

void test_xTCPTimerCheck_NonEmptyList_DeltaLessThanTimeout( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket, xTimeOutZeroSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xTimeOutZeroSocket, 0, sizeof( xTimeOutZeroSocket ) );

    xSocket.u.xTCP.usTimeout = 10;

    xTaskGetTickCount_ExpectAndReturn( 0 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xTimeOutZeroSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &( xBoundTCPSocketsList.xListEnd ) );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 9 ), xReturn );
    TEST_ASSERT_EQUAL( 9, xSocket.u.xTCP.usTimeout );
}

void test_xTCPTimerCheck_NonEmptyList_DeltaLessThanTimeout1( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket, xTimeOutZeroSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xTimeOutZeroSocket, 0, sizeof( xTimeOutZeroSocket ) );

    xSocket.u.xTCP.usTimeout = 1008;

    xTaskGetTickCount_ExpectAndReturn( 0 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xTimeOutZeroSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &( xBoundTCPSocketsList.xListEnd ) );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 1000 ), xReturn );
    TEST_ASSERT_EQUAL( 1007, xSocket.u.xTCP.usTimeout );
}

void test_xTCPTimerCheck_EventBitsNonZeroWontSleep( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep = 0;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket, xTimeOutZeroSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xTimeOutZeroSocket, 0, sizeof( xTimeOutZeroSocket ) );

    xSocket.u.xTCP.usTimeout = 1008;
    xSocket.xEventBits = 12;

    xTaskGetTickCount_ExpectAndReturn( 0 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xTimeOutZeroSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &( xBoundTCPSocketsList.xListEnd ) );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 0 ), xReturn );
    TEST_ASSERT_EQUAL( 1007, xSocket.u.xTCP.usTimeout );
}

void test_xTCPTimerCheck_EventBitsNonZeroWillSleep( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep = pdTRUE;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket, xTimeOutZeroSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xTimeOutZeroSocket, 0, sizeof( xTimeOutZeroSocket ) );

    xSocket.u.xTCP.usTimeout = 1008;
    xSocket.xEventBits = 12;

    xTaskGetTickCount_ExpectAndReturn( 0 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xTimeOutZeroSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &( xBoundTCPSocketsList.xListEnd ) );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 1000 ), xReturn );
    TEST_ASSERT_EQUAL( 1007, xSocket.u.xTCP.usTimeout );
}

void test_pxTCPSocketLookup_FoundAMatch( void )
{
    FreeRTOS_Socket_t * pxReturn, xSocket, xMatchingSocket;
    uint32_t ulLocalIP = 0xAABBCCDD;
    UBaseType_t uxLocalPort = 0x1234;
    uint32_t ulRemoteIP = 0xBCBCDCDC;
    UBaseType_t uxRemotePort = 0x4567;
    ListItem_t xLocalListItem;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xMatchingSocket, 0, sizeof( xMatchingSocket ) );

    xMatchingSocket.usLocalPort = uxLocalPort;
    xMatchingSocket.u.xTCP.usRemotePort = uxRemotePort;
    xMatchingSocket.u.xTCP.ulRemoteIP = ulRemoteIP;

    /* First iteration, no match. */
    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    /* Second iteration and we have a match. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xMatchingSocket );

    pxReturn = pxTCPSocketLookup( ulLocalIP, uxLocalPort, ulRemoteIP, uxRemotePort );

    TEST_ASSERT_EQUAL_UINT32( &xMatchingSocket, pxReturn );
}

void test_pxTCPSocketLookup_NoMatch( void )
{
    FreeRTOS_Socket_t * pxReturn, xSocket, xMatchingSocket;
    uint32_t ulLocalIP = 0xAABBCCDD;
    UBaseType_t uxLocalPort = 0x1234;
    uint32_t ulRemoteIP = 0xBCBCDCDC;
    UBaseType_t uxRemotePort = 0x4567;
    ListItem_t xLocalListItem;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xMatchingSocket, 0, sizeof( xMatchingSocket ) );

    xMatchingSocket.usLocalPort = uxLocalPort;
    xMatchingSocket.u.xTCP.usRemotePort = uxRemotePort;
    xMatchingSocket.u.xTCP.ulRemoteIP = ulRemoteIP + 1;

    /* First iteration, no match. */
    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    /* Second iteration and we have a match. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xMatchingSocket );

    /* Third iteration. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &( xBoundTCPSocketsList.xListEnd ) );

    pxReturn = pxTCPSocketLookup( ulLocalIP, uxLocalPort, ulRemoteIP, uxRemotePort );

    TEST_ASSERT_EQUAL_UINT32( NULL, pxReturn );
}

void test_pxTCPSocketLookup_NoMatch2( void )
{
    FreeRTOS_Socket_t * pxReturn, xSocket, xMatchingSocket;
    uint32_t ulLocalIP = 0xAABBCCDD;
    UBaseType_t uxLocalPort = 0x1234;
    uint32_t ulRemoteIP = 0xBCBCDCDC;
    UBaseType_t uxRemotePort = 0x4567;
    ListItem_t xLocalListItem;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xMatchingSocket, 0, sizeof( xMatchingSocket ) );

    xMatchingSocket.usLocalPort = uxLocalPort;
    xMatchingSocket.u.xTCP.usRemotePort = uxRemotePort + 1;
    xMatchingSocket.u.xTCP.ulRemoteIP = ulRemoteIP + 1;

    /* First iteration, no match. */
    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    /* Second iteration and we have a match. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xMatchingSocket );

    /* Third iteration. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &( xBoundTCPSocketsList.xListEnd ) );

    pxReturn = pxTCPSocketLookup( ulLocalIP, uxLocalPort, ulRemoteIP, uxRemotePort );

    TEST_ASSERT_EQUAL_UINT32( NULL, pxReturn );
}

void test_pxTCPSocketLookup_FoundAPartialMatch( void )
{
    FreeRTOS_Socket_t * pxReturn, xSocket, xMatchingSocket;
    uint32_t ulLocalIP = 0xAABBCCDD;
    UBaseType_t uxLocalPort = 0x1234;
    uint32_t ulRemoteIP = 0xBCBCDCDC;
    UBaseType_t uxRemotePort = 0x4567;
    ListItem_t xLocalListItem;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xMatchingSocket, 0, sizeof( xMatchingSocket ) );

    xMatchingSocket.usLocalPort = uxLocalPort;
    xMatchingSocket.u.xTCP.usRemotePort = uxRemotePort + 1;
    xMatchingSocket.u.xTCP.ulRemoteIP = ulRemoteIP;
    xMatchingSocket.u.xTCP.ucTCPState = eTCP_LISTEN;

    /* First iteration, no match. */
    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    /* Second iteration and we have a partial match. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xMatchingSocket );

    /* Third iteration. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &( xBoundTCPSocketsList.xListEnd ) );

    pxReturn = pxTCPSocketLookup( ulLocalIP, uxLocalPort, ulRemoteIP, uxRemotePort );

    TEST_ASSERT_EQUAL_UINT32( &xMatchingSocket, pxReturn );
}

void test_FreeRTOS_get_rx_buf_InvalidInput( void )
{
    struct xSTREAM_BUFFER * pxReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    pxReturn = FreeRTOS_get_rx_buf( &xSocket );
    TEST_ASSERT_EQUAL( NULL, pxReturn );

    /* NULL socket. */
    pxReturn = FreeRTOS_get_rx_buf( NULL );
    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

void test_FreeRTOS_get_rx_buf_ValidInput( void )
{
    struct xSTREAM_BUFFER * pxReturn, xStream;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* NULL socket. */
    xSocket.u.xTCP.rxStream = &xStream;
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    pxReturn = FreeRTOS_get_rx_buf( &xSocket );
    TEST_ASSERT_EQUAL( &xStream, pxReturn );
}

void test_prvTCPCreateStream( void )
{
    StreamBuffer_t * pxReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xIsInputStream = pdTRUE;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 20;
    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( *pxReturn ) ) - sizeof( pxReturn->ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    pxReturn = prvTCPCreateStream( &xSocket, xIsInputStream );

    TEST_ASSERT_EQUAL( 4, xSocket.u.xTCP.uxLittleSpace );
    TEST_ASSERT_EQUAL( 16, xSocket.u.xTCP.uxEnoughSpace );
    TEST_ASSERT_EQUAL( ucStream, xSocket.u.xTCP.rxStream );
}

void test_prvTCPCreateStream_LowAndHighFieldsDefined( void )
{
    StreamBuffer_t * pxReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xIsInputStream = pdTRUE;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 20;
    xSocket.u.xTCP.uxLittleSpace = 3;
    xSocket.u.xTCP.uxEnoughSpace = 17;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( *pxReturn ) ) - sizeof( pxReturn->ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    pxReturn = prvTCPCreateStream( &xSocket, xIsInputStream );

    TEST_ASSERT_EQUAL( 3, xSocket.u.xTCP.uxLittleSpace );
    TEST_ASSERT_EQUAL( 17, xSocket.u.xTCP.uxEnoughSpace );
    TEST_ASSERT_EQUAL( ucStream, xSocket.u.xTCP.rxStream );
}

void test_lTCPAddRxdata_StreamCannotBeAllocated( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount;
    StreamBuffer_t xStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 20;
    xSocket.u.xTCP.uxLittleSpace = 3;
    xSocket.u.xTCP.uxEnoughSpace = 17;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, NULL );

    vTCPStateChange_Expect( &xSocket, eCLOSE_WAIT );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( -1, lReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bMallocError );
}

void test_lTCPAddRxdata_SteamCreationSuccessful_AllBytesAdded( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 20;
    xSocket.u.xTCP.uxLittleSpace = 3;
    xSocket.u.xTCP.uxEnoughSpace = 17;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferAdd_ExpectAndReturn( ucStream, uxOffset, pcData, ulByteCount, ulByteCount );

    uxStreamBufferFrontSpace_ExpectAndReturn( ucStream, 10 );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( eSOCKET_RECEIVE, xSocket.xEventBits );
}

void test_lTCPAddRxdata_SteamCreationSuccessful_AllBytesNotAdded( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 20;
    xSocket.u.xTCP.uxLittleSpace = 3;
    xSocket.u.xTCP.uxEnoughSpace = 17;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferAdd_ExpectAndReturn( ucStream, uxOffset, pcData, ulByteCount, ulByteCount - 10 );

    uxStreamBufferFrontSpace_ExpectAndReturn( ucStream, 10 );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( eSOCKET_RECEIVE, xSocket.xEventBits );
}

void test_lTCPAddRxdata_FrontSpaceLessThanLowMark( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferAdd_ExpectAndReturn( ucStream, uxOffset, pcData, ulByteCount, ulByteCount - 10 );

    uxStreamBufferFrontSpace_ExpectAndReturn( ucStream, 10 );

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( eSOCKET_RECEIVE | ( eSELECT_READ << SOCKET_EVENT_BIT_COUNT ), xSocket.xEventBits );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1U, xSocket.u.xTCP.usTimeout );
}

void test_lTCPAddRxdata_LowWaterTrue( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.rxStream = ucStream;
    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;
    xSocket.u.xTCP.bits.bLowWater = pdTRUE;

    uxStreamBufferAdd_ExpectAndReturn( ucStream, uxOffset, pcData, ulByteCount, ulByteCount - 10 );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( eSOCKET_RECEIVE | ( eSELECT_READ << SOCKET_EVENT_BIT_COUNT ), xSocket.xEventBits );
}

void test_lTCPAddRxdata_HasValidHandler( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    xLocalReceiveCallback_Called = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;
    xSocket.u.xTCP.pxHandleReceive = xLocalReceiveCallback;
    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferGetSize_ExpectAndReturn( ucStream, 0U );

    uxStreamBufferAdd_ExpectAndReturn( ucStream, uxOffset, NULL, ulByteCount, ulByteCount - 10 );

    uxStreamBufferGet_ExpectAndReturn( ucStream, 0U, NULL, ulByteCount, pdFALSE, pdTRUE );

    uxStreamBufferGetPtr_ExpectAnyArgsAndReturn( 0U );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 0U, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( 1U, xLocalReceiveCallback_Called );
}

void test_lTCPAddRxdata_HasValidHandler_DataNULL( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    xLocalReceiveCallback_Called = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;
    xSocket.u.xTCP.pxHandleReceive = xLocalReceiveCallback;
    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferGetSize_ExpectAndReturn( ucStream, 0U );

    uxStreamBufferAdd_ExpectAndReturn( ucStream, uxOffset, NULL, ulByteCount, ulByteCount - 10 );

    uxStreamBufferGetPtr_ExpectAnyArgsAndReturn( 0U );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, NULL, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 0U, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( 0U, xLocalReceiveCallback_Called );
}

void test_lTCPAddRxdata_HasValidHandler_NonZeroOffset( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 10;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    xLocalReceiveCallback_Called = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;
    xSocket.u.xTCP.pxHandleReceive = xLocalReceiveCallback;
    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferGetSize_ExpectAndReturn( ucStream, 0U );

    uxStreamBufferAdd_ExpectAndReturn( ucStream, uxOffset, pcData, ulByteCount, ulByteCount - 10 );

    /*uxStreamBufferGet_ExpectAndReturn( ucStream, 0U, NULL, ulByteCount, pdFALSE, pdTRUE ); */

    /*uxStreamBufferGetPtr_ExpectAnyArgsAndReturn( 0U ); */

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 0U, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( 0U, xLocalReceiveCallback_Called );
}

void test_lTCPAddRxdata_HasValidHandlerWithNonZeroSize( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    xLocalReceiveCallback_Called = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;
    xSocket.u.xTCP.pxHandleReceive = xLocalReceiveCallback;
    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferGetSize_ExpectAndReturn( ucStream, 10U );

    uxStreamBufferAdd_ExpectAndReturn( ucStream, uxOffset, pcData, ulByteCount, ulByteCount - 10 );

    uxStreamBufferGetPtr_ExpectAnyArgsAndReturn( 0U );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 0U, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( 0U, xLocalReceiveCallback_Called );
}

void test_FreeRTOS_GetRemoteAddress_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xReturn = FreeRTOS_GetRemoteAddress( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_GetRemoteAddress_HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ulRemoteIP = 0xABCDEF12;
    xSocket.u.xTCP.usRemotePort = 0x1234;

    xReturn = FreeRTOS_GetRemoteAddress( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( sizeof( xAddress ), xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 0xABCDEF12 ), xAddress.sin_addr );
    TEST_ASSERT_EQUAL( FreeRTOS_htons( 0x1234 ), xAddress.sin_port );
}

void test_FreeRTOS_maywrite_InvalidValues( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Invalid State. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eCONNECT_SYN - 1;
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( -1, xReturn );

    xSocket.u.xTCP.ucTCPState = eESTABLISHED + 1;
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( -1, xReturn );

    xSocket.u.xTCP.ucTCPState = eCONNECT_SYN;
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    xSocket.u.xTCP.ucTCPState = eCONNECT_SYN + 1;
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    /* Transmission NULL. */
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.uxTxStreamSize = 0x123;
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( 0x123, xReturn );
}

void test_FreeRTOS_maywrite_HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t ucStream[ 20 ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xSocket.u.xTCP.txStream = ucStream;

    uxStreamBufferGetSpace_ExpectAndReturn( ucStream, 0x3344 );

    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( 0x3344, xReturn );
}

void test_FreeRTOS_tx_space_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_tx_space( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_tx_space_NULLStream( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.uxTxStreamSize = 0xBB;
    xReturn = FreeRTOS_tx_space( &xSocket );
    TEST_ASSERT_EQUAL( 0xBB, xReturn );
}

void test_FreeRTOS_tx_space_ValidStream( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t ucStream[ 20 ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ucStream;

    uxStreamBufferGetSpace_ExpectAndReturn( ucStream, 0xABCD );

    xReturn = FreeRTOS_tx_space( &xSocket );
    TEST_ASSERT_EQUAL( 0xABCD, xReturn );
}

void test_FreeRTOS_tx_size( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t ucStream[ 20 ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_tx_size( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Valid Protocol. Stream NULL. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xReturn = FreeRTOS_tx_size( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    /* Valid Protocol. Stream non-NULL. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ucStream;
    uxStreamBufferGetSize_ExpectAndReturn( ucStream, 0x345 );
    xReturn = FreeRTOS_tx_size( &xSocket );
    TEST_ASSERT_EQUAL( 0x345, xReturn );
}

void test_FreeRTOS_issocketconnected( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_issocketconnected( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Valid Protocol. Invalid State. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED - 1;
    xReturn = FreeRTOS_issocketconnected( &xSocket );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    /* Valid Protocol. Invalid State. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eCLOSE_WAIT;
    xReturn = FreeRTOS_issocketconnected( &xSocket );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    /* Valid Protocol. Valid State. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.ucTCPState = ( uint8_t ) eCLOSE_WAIT - 1;
    xReturn = FreeRTOS_issocketconnected( &xSocket );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

void test_FreeRTOS_mss( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_mss( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Valid Protocol. Invalid State. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.usMSS = 0xFD;
    xReturn = FreeRTOS_mss( &xSocket );
    TEST_ASSERT_EQUAL( 0xFD, xReturn );
}

void test_FreeRTOS_connstatus( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_connstatus( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Valid Protocol. Invalid State. */
    for( uint8_t i = 0; i < 125; i++ )
    {
        xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
        xSocket.u.xTCP.ucTCPState = ( uint8_t ) i;
        xReturn = FreeRTOS_connstatus( &xSocket );
        TEST_ASSERT_EQUAL( i, xReturn );
    }
}

void test_FreeRTOS_rx_size( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t ucStream[ 20 ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_rx_size( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Valid Protocol. Stream NULL. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xReturn = FreeRTOS_rx_size( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    /* Valid Protocol. Stream non-NULL. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.rxStream = ucStream;
    uxStreamBufferGetSize_ExpectAndReturn( ucStream, 0xAB );
    xReturn = FreeRTOS_rx_size( &xSocket );
    TEST_ASSERT_EQUAL( 0xAB, xReturn );
}

void test_xSocketValid( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    /* NULL Socket. */
    xReturn = xSocketValid( NULL );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    /* Invalid Socket. */
    xReturn = xSocketValid( ( FreeRTOS_Socket_t * ) FREERTOS_INVALID_SOCKET );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    /* Valid Socket. */
    xReturn = xSocketValid( &xSocket );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

void test_FreeRTOS_netstat( void )
{
    xSendEventStructToIPTask_ExpectAndReturn( NULL, pdMS_TO_TICKS( 1000U ), pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();
    FreeRTOS_netstat();
}

void test_vTCPNetStat_IPStackNotInit( void )
{
    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( 0 );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 0 );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdFALSE );

    vTCPNetStat();
}

void test_vTCPNetStat_IPStackInit( void )
{
    ListItem_t xLocalTCPItem, xLocalUDPItem, xIterator;
    FreeRTOS_Socket_t xSocket, xSocket2;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xSocket2, 0, sizeof( xSocket2 ) );

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( 0 );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 0 );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    listGET_END_MARKER_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalTCPItem );
    listGET_END_MARKER_ExpectAndReturn( &xBoundUDPSocketsList, &xLocalUDPItem );

    /* First Iteration. */
    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xIterator );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xSocket );

    xTaskGetTickCount_ExpectAndReturn( 0x10 );

    /* Second Iteration. */
    xSocket2.u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    listGET_NEXT_ExpectAndReturn( &xIterator, &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xSocket2 );

    xTaskGetTickCount_ExpectAndReturn( 0x20 );

    /* TCP last iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xLocalTCPItem );


    /* UDP */
    /* First Iteration. */
    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundUDPSocketsList, &xIterator );

    /* Second Iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xIterator );

    /* TCP last iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xLocalUDPItem );

    vTCPNetStat();
}

void test_vSocketSelect_UDPSocketsOnly( void )
{
    SocketSelect_t xSocketSet;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket, xSocket2, xSocket3, xSocket4;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xSocket2, 0, sizeof( xSocket2 ) );
    memset( &xSocket3, 0, sizeof( xSocket3 ) );
    memset( &xSocket4, 0, sizeof( xSocket4 ) );

    xSocket2.pxSocketSet = &xSocketSet;
    xSocket3.pxSocketSet = &xSocketSet;
    xSocket4.pxSocketSet = &xSocketSet;

    /* Round 0. Not same socket set. */
    listGET_NEXT_ExpectAndReturn( &( xBoundUDPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    /* Round 1. Same socket set. No select bits. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket2 );

    /* Round 2. Same socket set. elect bits. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket3 );

    xSocket3.xSelectBits = eSELECT_READ;
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket3.u.xUDP.xWaitingPacketsList ), 0 );

    /* Round 3. Same socket set. elect bits. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket4 );

    xSocket4.xSelectBits = eSELECT_READ;
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket4.u.xUDP.xWaitingPacketsList ), 3 );

    /* Last item. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &( xBoundUDPSocketsList.xListEnd ) );

    /* Last item. Nothing in TCP. */
    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xBoundTCPSocketsList.xListEnd ) );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet.xSelectGroup, 0, 0 );

    xEventGroupSetBits_ExpectAndReturn( xSocketSet.xSelectGroup, eSELECT_READ | eSELECT_CALL_IP, pdPASS );

    vSocketSelect( &xSocketSet );

    TEST_ASSERT_EQUAL( 0, xSocket.xSocketBits );
    TEST_ASSERT_EQUAL( 0, xSocket2.xSocketBits );
    TEST_ASSERT_EQUAL( 0, xSocket3.xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_READ, xSocket4.xSocketBits );
}

void test_vSocketSelect_TCPSocketsOnly( void )
{
    SocketSelect_t xSocketSet;
    ListItem_t xLocalListItem;
    uint8_t ucStream[ 20 ];
    FreeRTOS_Socket_t xSocket[ 9 ], xPeerSocket, xPeerSocket1;

    for( int i = 1; i < 9; i++ )
    {
        memset( &xSocket[ i ], 0, sizeof( xSocket[ i ] ) );
        xSocket[ i ].pxSocketSet = &xSocketSet;
        xSocket[ i ].ucProtocol = FREERTOS_IPPROTO_TCP;
    }

    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );
    memset( &xPeerSocket1, 0, sizeof( xPeerSocket1 ) );
    memset( &xSocket[ 0 ], 0, sizeof( xSocket[ 0 ] ) );

    xSocket[ 0 ].ucProtocol = FREERTOS_IPPROTO_TCP;

    /* Last item. Nothing in UDP. */
    listGET_NEXT_ExpectAndReturn( &( xBoundUDPSocketsList.xListEnd ), &( xBoundUDPSocketsList.xListEnd ) );

    /* Round 0. Not same socket set. */
    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 0 ] );

    /* Round 1. Same socket set. No bits Set. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 1 ] );

    /* Round 2. Same socket set. All bits Set. */
    xSocket[ 2 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 2 ] );

    /* Round 3. */
    xSocket[ 3 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 3 ].u.xTCP.bits.bPassAccept = pdTRUE;
    xSocket[ 3 ].u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xSocket[ 3 ].u.xTCP.pxPeerSocket = &xPeerSocket;
    xSocket[ 3 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 3 ] );

    /* Round 4. */
    xSocket[ 4 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 4 ].u.xTCP.bits.bPassAccept = pdTRUE;
    xSocket[ 4 ].u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xSocket[ 4 ].u.xTCP.pxPeerSocket = &xPeerSocket1;
    xSocket[ 4 ].u.xTCP.pxPeerSocket->u.xTCP.bits.bPassAccept = pdTRUE;
    xSocket[ 4 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 4 ] );

    /* Round 5. */
    xSocket[ 5 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 5 ].u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;
    xSocket[ 5 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    xSocket[ 5 ].u.xTCP.txStream = ucStream;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 5 ] );
    uxStreamBufferGetSpace_ExpectAndReturn( ucStream, 0xABCD );

    /* Round 5. */
    xSocket[ 6 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 6 ].u.xTCP.ucTCPState = ( uint8_t ) eCLOSE_WAIT;
    xSocket[ 6 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    xSocket[ 6 ].u.xTCP.txStream = ucStream;
    xSocket[ 6 ].u.xTCP.rxStream = ucStream;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 6 ] );
    uxStreamBufferGetSize_ExpectAndReturn( ucStream, 0xAB );
    uxStreamBufferGetSpace_ExpectAndReturn( ucStream, 0xABCD );

    /* Round 6. */
    xSocket[ 7 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 7 ].u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;
    xSocket[ 7 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    xSocket[ 7 ].u.xTCP.bits.bPassQueued = pdTRUE;
    xSocket[ 7 ].u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 7 ] );

    /* Round 7. */
    xSocket[ 8 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 8 ].u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;
    xSocket[ 8 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    xSocket[ 8 ].u.xTCP.bits.bPassQueued = pdTRUE;
    xSocket[ 8 ].u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
    xSocket[ 8 ].u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xSocket[ 8 ].u.xTCP.bits.bConnPassed = pdTRUE_UNSIGNED;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 8 ] );

    /* Last item. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &( xBoundTCPSocketsList.xListEnd ) );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet.xSelectGroup, 0, eSELECT_READ );

    xEventGroupSetBits_ExpectAnyArgsAndReturn( pdPASS ); /*AndReturn( xSocketSet.xSelectGroup, eSELECT_READ | eSELECT_CALL_IP, pdPASS ); */

    /*xEventGroupClearBits_ExpectAnyArgsAndReturn( pdPASS ); */

    vSocketSelect( &xSocketSet );

    TEST_ASSERT_EQUAL( 0, xSocket[ 0 ].xSocketBits );
    TEST_ASSERT_EQUAL( 0, xSocket[ 1 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_EXCEPT, xSocket[ 2 ].xSocketBits );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket[ 2 ].u.xTCP.bits.bConnPassed );
    TEST_ASSERT_EQUAL( 0, xSocket[ 3 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_READ, xSocket[ 4 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_WRITE, xSocket[ 5 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_WRITE | eSELECT_READ | eSELECT_EXCEPT, xSocket[ 6 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_WRITE, xSocket[ 7 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_READ, xSocket[ 8 ].xSocketBits );
}

void test_vSocketSelect_NoSocketsAtAll( void )
{
    SocketSelect_t xSocketSet;
    ListItem_t xLocalListItem;
    uint8_t ucStream[ 20 ];

    /* Last item. Nothing in UDP. */
    listGET_NEXT_ExpectAndReturn( &( xBoundUDPSocketsList.xListEnd ), &( xBoundUDPSocketsList.xListEnd ) );

    /* Last item. Nothing in TCP. */
    listGET_NEXT_ExpectAndReturn( &( xBoundTCPSocketsList.xListEnd ), &( xBoundTCPSocketsList.xListEnd ) );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet.xSelectGroup, 0, eSELECT_READ );
    xEventGroupClearBits_ExpectAnyArgsAndReturn( pdPASS );
    xEventGroupSetBits_ExpectAndReturn( xSocketSet.xSelectGroup, eSELECT_CALL_IP, pdPASS );

    vSocketSelect( &xSocketSet );
}

void test_FreeRTOS_SignalSocket_InvalidSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_SignalSocket( NULL );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    xReturn = FreeRTOS_SignalSocket( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

void test_FreeRTOS_SignalSocket_NonNULLEventGroup( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    SocketSelect_t xSocketSet;
    uint8_t xEventGroup[ sizeof( size_t ) ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xSocketSet, 0, sizeof( xSocketSet ) );

    xSocket.pxSocketSet = &xSocketSet;
    xSocket.xEventGroup = xEventGroup;

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_INTR, pdFALSE );

    xReturn = FreeRTOS_SignalSocket( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_FreeRTOS_SignalSocket_NonNULLSelectGroup( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    SocketSelect_t xSocketSet;
    uint8_t xSelectGroup[ sizeof( size_t ) ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xSocketSet, 0, sizeof( xSocketSet ) );

    xSocket.pxSocketSet = &xSocketSet;
    xSocket.pxSocketSet->xSelectGroup = xSelectGroup;

    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSELECT_INTR, pdFALSE );

    xReturn = FreeRTOS_SignalSocket( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_FreeRTOS_SignalSocketFromISR_catchAsserts( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xHigherPriorityTaskWoken;

    catch_assert( FreeRTOS_SignalSocketFromISR( NULL, &xHigherPriorityTaskWoken ) );

    memset( &xSocket, 0, sizeof( xSocket ) );
    catch_assert( FreeRTOS_SignalSocketFromISR( &xSocket, &xHigherPriorityTaskWoken ) );

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    catch_assert( FreeRTOS_SignalSocketFromISR( &xSocket, &xHigherPriorityTaskWoken ) );
}

void test_FreeRTOS_SignalSocketFromISR_HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xHigherPriorityTaskWoken;
    uint8_t xEventGroup[ sizeof( size_t ) ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.xEventGroup = xEventGroup;

    xQueueGenericSendFromISR_ExpectAnyArgsAndReturn( 0xABC );

    xReturn = FreeRTOS_SignalSocketFromISR( &xSocket, &xHigherPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 0xABC, xReturn );
}
