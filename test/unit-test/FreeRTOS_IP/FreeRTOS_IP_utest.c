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
#include "mock_IP_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_TCP_IP.h"
#include "mock_FreeRTOS_ICMP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_IPv4_Private.h"
#include "mock_FreeRTOS_ND.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IPv4.h"

#include "FreeRTOS_IP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

extern NetworkInterface_t xInterfaces[ 1 ];
extern BaseType_t xIPTaskInitialised;
extern BaseType_t xNetworkDownEventPending;

void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer );
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

static BaseType_t NetworkInterfaceOutputFunction_Stub_Called = 0;

/* ============================ Unity Fixtures ============================ */

/*! called before each test case */
void setUp( void )
{
    pxNetworkInterfaces = NULL;
    xNetworkDownEventPending = pdFALSE;
}

/*! called after each test case */
void tearDown( void )
{
}

/* ======================== Stub Callback Functions ========================= */

static BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                       NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                       BaseType_t xReleaseAfterSend )
{
    NetworkInterfaceOutputFunction_Stub_Called++;
    return 0;
}

static uint8_t ReleaseTCPPayloadBuffer[ 1500 ];
static BaseType_t ReleaseTCPPayloadBufferxByteCount = 100;
static size_t StubuxStreamBufferGetPtr_ReturnBadAddress( StreamBuffer_t * pxBuffer,
                                                         uint8_t ** ppucData,
                                                         int lCounter )
{
    *ppucData = &ReleaseTCPPayloadBuffer[ 150 ];

    return 0xFFFFFF;
}

static size_t StubuxStreamBufferGetPtr_ReturnIncorrectSize( StreamBuffer_t * pxBuffer,
                                                            uint8_t ** ppucData,
                                                            int lCounter )
{
    *ppucData = &ReleaseTCPPayloadBuffer[ 0 ];

    return( ReleaseTCPPayloadBufferxByteCount >> 1 );
}

static size_t StubuxStreamBufferGetPtr_ReturnCorrectVals( StreamBuffer_t * pxBuffer,
                                                          uint8_t ** ppucData,
                                                          int lCounter )
{
    *ppucData = &ReleaseTCPPayloadBuffer[ 0 ];

    return ReleaseTCPPayloadBufferxByteCount;
}

/* ============================== Test Cases ============================== */

void test_vIPNetworkUpCalls( void )
{
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.bits.bEndPointUp = pdFALSE;

    vApplicationIPNetworkEventHook_Multi_Expect( eNetworkUp, &xEndPoint );
    vDNSInitialise_Expect();
    vARPTimerReload_Expect( pdMS_TO_TICKS( 10000 ) );

    vIPNetworkUpCalls( &xEndPoint );

    TEST_ASSERT_EQUAL( pdTRUE, xEndPoint.bits.bEndPointUp );
}

void test_FreeRTOS_NetworkDown_SendToIPTaskSuccessful( void )
{
    struct xNetworkInterface xNetworkInterface;

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xQueueGenericSend_ExpectAnyArgsAndReturn( pdPASS );

    FreeRTOS_NetworkDown( &xNetworkInterface );

    TEST_ASSERT_EQUAL( pdFALSE, xIsNetworkDownEventPending() );
}

void test_FreeRTOS_NetworkDown_SendToIPTaskNotSuccessful( void )
{
    struct xNetworkInterface xNetworkInterface;

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xQueueGenericSend_ExpectAnyArgsAndReturn( pdFAIL );

    FreeRTOS_NetworkDown( &xNetworkInterface );

    TEST_ASSERT_EQUAL( pdTRUE, xIsNetworkDownEventPending() );
}

void test_FreeRTOS_NetworkDownFromISR_SendToIPTaskSuccessful( void )
{
    BaseType_t xHasPriorityTaskAwoken = pdTRUE;
    BaseType_t xReturn;
    struct xNetworkInterface xNetworkInterface;

    xQueueGenericSendFromISR_ExpectAnyArgsAndReturn( pdPASS );
    xQueueGenericSendFromISR_ReturnThruPtr_pxHigherPriorityTaskWoken( &xHasPriorityTaskAwoken );

    xReturn = FreeRTOS_NetworkDownFromISR( &xNetworkInterface );

    TEST_ASSERT_EQUAL( pdFALSE, xIsNetworkDownEventPending() );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

void test_FreeRTOS_NetworkDownFromISR_SendToIPTaskUnsuccessful( void )
{
    BaseType_t xHasPriorityTaskAwoken = pdFALSE;
    BaseType_t xReturn;
    struct xNetworkInterface xNetworkInterface;

    xQueueGenericSendFromISR_ExpectAnyArgsAndReturn( pdFAIL );
    xQueueGenericSendFromISR_ReturnThruPtr_pxHigherPriorityTaskWoken( &xHasPriorityTaskAwoken );

    xReturn = FreeRTOS_NetworkDownFromISR( &xNetworkInterface );

    TEST_ASSERT_EQUAL( pdTRUE, xIsNetworkDownEventPending() );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeEqualToConfig( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS;
    void * pvReturn;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t pucEthernetBuffer[ 1500 ];

    /* Put the ethernet buffer in place. */
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->xDataLength = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, uxBlockTimeTicks, pxNetworkBuffer );

    pvReturn = FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, ipTYPE_IPv4 );

    TEST_ASSERT_EQUAL( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL_PTR( &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_t ) ] ), pvReturn );
}

void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeLessThanConfig( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS - 1;
    void * pvReturn;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t pucEthernetBuffer[ 1500 ];

    /* Put the ethernet buffer in place. */
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->xDataLength = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, uxBlockTimeTicks, pxNetworkBuffer );

    pvReturn = FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, ipTYPE_IPv4 );

    TEST_ASSERT_EQUAL( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL_PTR( &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_t ) ] ), pvReturn );
}

void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeMoreThanConfig( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS + 1;
    void * pvReturn;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t pucEthernetBuffer[ 1500 ];

    /* Put the ethernet buffer in place. */
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->xDataLength = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS, pxNetworkBuffer );

    pvReturn = FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, ipTYPE_IPv4 );

    TEST_ASSERT_EQUAL( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL_PTR( &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_t ) ] ), pvReturn );
}

void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeMoreThanConfig_NULLBufferReturned( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS + 1;
    void * pvReturn;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS, NULL );

    pvReturn = FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, ipTYPE_IPv4 );

    TEST_ASSERT_NULL( pvReturn );
}

void test_FreeRTOS_GetUDPPayloadBuffer_UnknownType( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS;

    catch_assert( FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, 0xFF ) );
}

void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeEqualToConfig_IPv6( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS;
    void * pvReturn;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t pucEthernetBuffer[ 1500 ];

    /* Put the ethernet buffer in place. */
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->xDataLength = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( UDPPacket_IPv6_t ) + uxRequestedSizeBytes, uxBlockTimeTicks, pxNetworkBuffer );

    pvReturn = FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, ipTYPE_IPv6 );

    TEST_ASSERT_EQUAL( sizeof( UDPPacket_IPv6_t ) + uxRequestedSizeBytes, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL_PTR( &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_IPv6_t ) ] ), pvReturn );
}

void test_FreeRTOS_ReleaseUDPPayloadBuffer( void )
{
    void * pvBuffer = ( void * ) 0xFFCDEA;

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pvBuffer, ( NetworkBufferDescriptor_t * ) 0x12123434 );
    vReleaseNetworkBufferAndDescriptor_Expect( ( NetworkBufferDescriptor_t * ) 0x12123434 );

    FreeRTOS_ReleaseUDPPayloadBuffer( pvBuffer );
}

void test_FreeRTOS_ReleaseUDPPayloadBuffer_NullNetworkDescriptor( void )
{
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( NULL, ( NetworkBufferDescriptor_t * ) NULL );

    catch_assert( FreeRTOS_ReleaseUDPPayloadBuffer( NULL ) );
}

void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBufferAssert( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xByteCount = 100;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnBadAddress );

    catch_assert( FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, xByteCount ) );
}

void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectSizeAssert( void )
{
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnIncorrectSize );

    catch_assert( FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, ReleaseTCPPayloadBufferxByteCount ) );
}

void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBytesReleasedAssert( void )
{
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnCorrectVals );

    FreeRTOS_recv_ExpectAndReturn( &xSocket, NULL, ReleaseTCPPayloadBufferxByteCount, FREERTOS_MSG_DONTWAIT, ( ReleaseTCPPayloadBufferxByteCount >> 1 ) );

    catch_assert( FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, ReleaseTCPPayloadBufferxByteCount ) );
}

void test_FreeRTOS_ReleaseTCPPayloadBuffer_HappyPath( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnCorrectVals );

    FreeRTOS_recv_ExpectAndReturn( &xSocket, NULL, ReleaseTCPPayloadBufferxByteCount, FREERTOS_MSG_DONTWAIT, ReleaseTCPPayloadBufferxByteCount );

    xReturn = FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, ReleaseTCPPayloadBufferxByteCount );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

void test_prvIPTask( void )
{
    /* Reset the static variable. */
    xIPTaskInitialised = pdFALSE;

    vNetworkTimerReload_Ignore();


    vTCPTimerReload_ExpectAnyArgs();

    vIPSetARPResolutionTimerEnableState_Expect( pdFALSE );

    vDNSInitialise_Ignore();
    ipFOREVER_ExpectAndReturn( 0 );

    /* Parameters do not matter here. */
    prvIPTask( NULL );

    TEST_ASSERT_EQUAL( pdTRUE, xIPTaskInitialised );
    TEST_ASSERT_EQUAL( pdFALSE, xNetworkDownEventPending );
}

void test_prvIPTask_NetworkDown( void )
{
    NetworkInterface_t xNetworkInterface;
    IPStackEvent_t xDownEvent;

    memset( &xNetworkInterface, 0, sizeof(xNetworkInterface) );
    pxNetworkInterfaces = &xNetworkInterface;

    xDownEvent.eEventType = eNetworkDownEvent;
    xDownEvent.pvData = &xNetworkInterface;

    /* Reset the static variable. */
    xIPTaskInitialised = pdFALSE;

    /* In prvIPTask_Initialise. */
    vNetworkTimerReload_Ignore();

    /* In FreeRTOS_NetworkDown. */
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );
    xQueueGenericSend_ExpectAnyArgsAndReturn( pdPASS );

    /* In prvIPTask_Initialise. */
    vTCPTimerReload_ExpectAnyArgs();
    vIPSetARPResolutionTimerEnableState_Expect( pdFALSE );
    vDNSInitialise_Ignore();

    /* In prvIPTask. */
    ipFOREVER_ExpectAndReturn( pdTRUE );

    /* In prvProcessIPEventsAndTimers. */
    vCheckNetworkTimers_Ignore();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xDownEvent, sizeof( xDownEvent ) );
    prvProcessNetworkDownEvent_Expect( &xNetworkInterface );

    /* In prvIPTask. */
    ipFOREVER_ExpectAndReturn( pdFALSE );

    /* Parameters do not matter here. */
    prvIPTask( NULL );

    TEST_ASSERT_EQUAL( pdTRUE, xIPTaskInitialised );
}

void test_prvProcessIPEventsAndTimers_NoEventReceived( void )
{
    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    /* No event received. */
    xQueueReceive_ExpectAnyArgsAndReturn( pdFALSE );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eNetworkRxEventNULL( void )
{
    IPStackEvent_t xReceivedEvent;

    xReceivedEvent.eEventType = eNetworkRxEvent;
    xReceivedEvent.pvData = NULL;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    catch_assert( prvProcessIPEventsAndTimers() );
}

void test_prvProcessIPEventsAndTimers_eNetworkRxEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t ) - 1;

    xReceivedEvent.eEventType = eNetworkRxEvent;
    xReceivedEvent.pvData = pxNetworkBuffer;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessIPEventsAndTimers();
}


void test_prvProcessIPEventsAndTimers_eNetworkTxEvent( void )
{
    struct xNetworkInterface xInterface;
    IPStackEvent_t xReceivedEvent;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t ) - 1;
    pxNetworkBuffer->pxInterface = &xInterface;

    NetworkInterfaceOutputFunction_Stub_Called = 0;
    pxNetworkBuffer->pxInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xReceivedEvent.eEventType = eNetworkTxEvent;
    xReceivedEvent.pvData = pxNetworkBuffer;
    xNetworkDownEventPending = pdFALSE;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    NetworkInterfaceOutputFunction_Stub_Called = 0;

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
}


void test_prvProcessIPEventsAndTimers_eNetworkTxEvent_NullInterface( void )
{
    IPStackEvent_t xReceivedEvent;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t ) - 1;
    pxNetworkBuffer->pxInterface = NULL;

    NetworkInterfaceOutputFunction_Stub_Called = 0;

    xReceivedEvent.eEventType = eNetworkTxEvent;
    xReceivedEvent.pvData = pxNetworkBuffer;
    xNetworkDownEventPending = pdFALSE;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eARPTimerEvent( void )
{
    IPStackEvent_t xReceivedEvent;

    xReceivedEvent.eEventType = eARPTimerEvent;
    xReceivedEvent.pvData = NULL;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vARPAgeCache_Expect();
    vNDAgeCache_Expect();

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eSocketBindEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    FreeRTOS_Socket_t xSocket;

    xReceivedEvent.eEventType = eSocketBindEvent;
    xReceivedEvent.pvData = &xSocket;

    xSocket.usLocalPort = ( uint16_t ) ~0U;
    xSocket.xEventBits = 0;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vSocketBind_ExpectAndReturn( &xSocket, NULL, sizeof( struct freertos_sockaddr ), pdFALSE, 0 );
    vSocketBind_IgnoreArg_pxBindAddress();

    vSocketWakeUpUser_Expect( &xSocket );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( 0, xSocket.usLocalPort );
    TEST_ASSERT_EQUAL( eSOCKET_BOUND, xSocket.xEventBits | eSOCKET_BOUND );
}

void test_prvProcessIPEventsAndTimers_eSocketBindEvent_IPv6( void )
{
    IPStackEvent_t xReceivedEvent;
    FreeRTOS_Socket_t xSocket;

    xReceivedEvent.eEventType = eSocketBindEvent;
    xReceivedEvent.pvData = &xSocket;

    xSocket.usLocalPort = ( uint16_t ) ~0U;
    xSocket.xEventBits = 0;
    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;

    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vSocketBind_ExpectAndReturn( &xSocket, NULL, sizeof( struct freertos_sockaddr ), pdFALSE, 0 );
    vSocketBind_IgnoreArg_pxBindAddress();

    vSocketWakeUpUser_Expect( &xSocket );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( 0, xSocket.usLocalPort );
    TEST_ASSERT_EQUAL( eSOCKET_BOUND, xSocket.xEventBits | eSOCKET_BOUND );
}

void test_prvProcessIPEventsAndTimers_eSocketCloseEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    FreeRTOS_Socket_t xSocket;

    xReceivedEvent.eEventType = eSocketCloseEvent;
    xReceivedEvent.pvData = &xSocket;

    xSocket.usLocalPort = ( uint16_t ) ~0U;
    xSocket.xEventBits = 0;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vSocketClose_ExpectAndReturn( &xSocket, 0 );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eStackTxEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xReceivedEvent.eEventType = eStackTxEvent;
    xReceivedEvent.pvData = &xNetworkBuffer;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vProcessGeneratedUDPPacket_Expect( &xNetworkBuffer );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eDHCPEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    uint32_t ulDHCPEvent = 0x1234;
    NetworkEndPoint_t xEndPoints, * pxEndPoints = &xEndPoints;

    memset( pxEndPoints, 0, sizeof( NetworkEndPoint_t ) );
    pxEndPoints->bits.bWantDHCP = pdTRUE_UNSIGNED;
    pxEndPoints->bits.bIPv6 = pdFALSE_UNSIGNED;

    xReceivedEvent.eEventType = eDHCPEvent;
    xReceivedEvent.pvData = pxEndPoints;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vDHCPProcess_Expect( pdFALSE, pxEndPoints );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eSocketSelectEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    uint32_t ulData = 0x1234;

    xReceivedEvent.eEventType = eSocketSelectEvent;
    xReceivedEvent.pvData = ( void * ) ulData;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vSocketSelect_Expect( ( SocketSelect_t * ) ulData );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eSocketSignalEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    uint32_t ulData = 0x1234;

    xReceivedEvent.eEventType = eSocketSignalEvent;
    xReceivedEvent.pvData = ( void * ) ulData;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    FreeRTOS_SignalSocket_ExpectAndReturn( ( Socket_t ) ulData, 0 );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eTCPTimerEvent( void )
{
    IPStackEvent_t xReceivedEvent;

    xReceivedEvent.eEventType = eTCPTimerEvent;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vIPSetTCPTimerExpiredState_Expect( pdTRUE );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eTCPAcceptEvent_NoNewClient( void )
{
    IPStackEvent_t xReceivedEvent;
    FreeRTOS_Socket_t xSocket;

    xReceivedEvent.eEventType = eTCPAcceptEvent;
    xReceivedEvent.pvData = &xSocket;

    xSocket.xEventBits = 0;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    xTCPCheckNewClient_ExpectAndReturn( &xSocket, pdFALSE );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
}

void test_prvProcessIPEventsAndTimers_eTCPAcceptEvent_NewClient( void )
{
    IPStackEvent_t xReceivedEvent;
    FreeRTOS_Socket_t xSocket;

    xReceivedEvent.eEventType = eTCPAcceptEvent;
    xReceivedEvent.pvData = &xSocket;

    xSocket.xEventBits = 0;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    xTCPCheckNewClient_ExpectAndReturn( &xSocket, pdTRUE );

    vSocketWakeUpUser_Expect( &xSocket );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( eSOCKET_ACCEPT, xSocket.xEventBits | eSOCKET_ACCEPT );
}

void test_prvProcessIPEventsAndTimers_eTCPNetStat( void )
{
    IPStackEvent_t xReceivedEvent;

    xReceivedEvent.eEventType = eTCPNetStat;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vTCPNetStat_Expect();

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eSocketSetDeleteEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    SocketSelect_t * pxSocketSet = malloc( sizeof( SocketSelect_t ) );

    xReceivedEvent.eEventType = eSocketSetDeleteEvent;
    xReceivedEvent.pvData = pxSocketSet;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vEventGroupDelete_Expect( pxSocketSet->xSelectGroup );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eSocketSetDeleteEvent_NetDownPending( void )
{
    IPStackEvent_t xReceivedEvent;
    NetworkInterface_t xNetworkInterface[2], * pxInterface = &xNetworkInterface[1];
    SocketSelect_t * pxSocketSet = malloc( sizeof( SocketSelect_t ) );

    xNetworkDownEventPending = pdTRUE;
    xNetworkInterface[0].bits.bCallDownEvent = pdFALSE_UNSIGNED;
    xNetworkInterface[1].bits.bCallDownEvent = pdTRUE_UNSIGNED;

    xReceivedEvent.eEventType = eSocketSetDeleteEvent;
    xReceivedEvent.pvData = pxSocketSet;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vEventGroupDelete_Expect( pxSocketSet->xSelectGroup );

    FreeRTOS_FirstNetworkInterface_ExpectAndReturn( &xNetworkInterface[0] );
    FreeRTOS_NextNetworkInterface_ExpectAndReturn( &xNetworkInterface[0], pxInterface );
    /* Since network down event is pending, a call to this function should be expected. */
    prvProcessNetworkDownEvent_Expect( pxInterface );

    FreeRTOS_NextNetworkInterface_ExpectAndReturn( pxInterface, NULL );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( pxInterface->bits.bCallDownEvent, pdFALSE_UNSIGNED );
}

void test_prvProcessIPEventsAndTimers_Error( void )
{
    IPStackEvent_t xReceivedEvent;

    xNetworkDownEventPending = pdFALSE;

    xReceivedEvent.eEventType = eSocketSetDeleteEvent + 1;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    prvProcessIPEventsAndTimers();
}

void test_FreeRTOS_SendPingRequest_HappyPath( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    /* 32 byte ping to send. */
    size_t uxNumberOfBytesToSend = 32;
    ICMPHeader_t * pxICMPHeader;
    EthernetHeader_t * pxEthernetHeader;

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigNETWORK_MTU - ( sizeof( IPHeader_t ) + sizeof( ICMPHeader_t ) ) ];

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;

    pxICMPHeader = ( ICMPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipIP_PAYLOAD_OFFSET ] );
    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    xIPTaskInitialised = pdTRUE;

    /* At least 4 free network buffers must be there to send a ping. */
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNumberOfBytesToSend + sizeof( ICMPPacket_t ), uxBlockTimeTicks, pxNetworkBuffer );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xQueueGenericSend_ExpectAnyArgsAndReturn( pdPASS );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( 1, xReturn );
    TEST_ASSERT_EQUAL( 8 /* ipICMP_ECHO_REQUEST */, pxICMPHeader->ucTypeOfMessage );
    TEST_ASSERT_EQUAL( 0, pxICMPHeader->ucTypeOfService );
    TEST_ASSERT_EQUAL( 1, pxICMPHeader->usIdentifier );
    TEST_ASSERT_EQUAL( 1, pxICMPHeader->usSequenceNumber );
    TEST_ASSERT_EQUAL( ipIPv4_FRAME_TYPE, pxEthernetHeader->usFrameType );
    TEST_ASSERT_EQUAL( FREERTOS_SO_UDPCKSUM_OUT, pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] );
    TEST_ASSERT_EQUAL( ulIPAddress, pxNetworkBuffer->xIPAddress.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( ipPACKET_CONTAINS_ICMP_DATA, pxNetworkBuffer->usPort );
}

void test_FreeRTOS_SendPingRequest_SendingToIPTaskFails( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    /* 32 byte ping to send. */
    size_t uxNumberOfBytesToSend = 32;
    ICMPHeader_t * pxICMPHeader;
    EthernetHeader_t * pxEthernetHeader;

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigNETWORK_MTU - ( sizeof( IPHeader_t ) + sizeof( ICMPHeader_t ) ) ];

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;

    pxICMPHeader = ( ICMPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipIP_PAYLOAD_OFFSET ] );
    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    /* At least 4 free network buffers must be there to send a ping. */
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNumberOfBytesToSend + sizeof( ICMPPacket_t ), uxBlockTimeTicks, pxNetworkBuffer );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xQueueGenericSend_ExpectAnyArgsAndReturn( pdFAIL );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL( 8 /* ipICMP_ECHO_REQUEST */, pxICMPHeader->ucTypeOfMessage );
    TEST_ASSERT_EQUAL( 0, pxICMPHeader->ucTypeOfService );
    TEST_ASSERT_EQUAL( 1, pxICMPHeader->usIdentifier );
    TEST_ASSERT_EQUAL( 1, pxICMPHeader->usSequenceNumber );
    TEST_ASSERT_EQUAL( ipIPv4_FRAME_TYPE, pxEthernetHeader->usFrameType );
    TEST_ASSERT_EQUAL( FREERTOS_SO_UDPCKSUM_OUT, pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] );
    TEST_ASSERT_EQUAL( ulIPAddress, pxNetworkBuffer->xIPAddress.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( ipPACKET_CONTAINS_ICMP_DATA, pxNetworkBuffer->usPort );
}

void test_FreeRTOS_SendPingRequest_TooManyBytes( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    size_t uxNumberOfBytesToSend = ipconfigNETWORK_MTU - ( sizeof( IPHeader_t ) + sizeof( ICMPHeader_t ) );

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    /* At least 4 free network buffers must be there to send a ping. */
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_FreeRTOS_SendPingRequest_TooLessBytes( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    size_t uxNumberOfBytesToSend = 0;

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    /* At least 4 free network buffers must be there to send a ping. */
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_FreeRTOS_SendPingRequest_NotEnoughFreeBuffers( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    /* 32 byte ping to send. */
    size_t uxNumberOfBytesToSend = 32;

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 3U );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_FreeRTOS_SendPingRequest_NetworkBufferFailure( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    /* 32 byte ping to send. */
    size_t uxNumberOfBytesToSend = 32;

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNumberOfBytesToSend + sizeof( ICMPPacket_t ), uxBlockTimeTicks, NULL );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xSendEventToIPTask( void )
{
    BaseType_t xReturn;
    eIPEvent_t eEvent = eNetworkRxEvent;

    xIPTaskInitialised = pdFALSE;

    xReturn = xSendEventToIPTask( eEvent );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xSendEventStructToIPTask_IPTaskNotInit_NoNetworkDownEvent( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout;

    xIPTaskInitialised = pdFALSE;

    xEvent.eEventType = eNetworkDownEvent + 1;

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEvent( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 1;

    xIPTaskInitialised = pdFALSE;
    xEvent.eEventType = eNetworkDownEvent;

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 0, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

void test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEvent1( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 0;

    xIPTaskInitialised = pdFALSE;
    xEvent.eEventType = eNetworkDownEvent;

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 0, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

void test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEvent2( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 0;

    xIPTaskInitialised = pdFALSE;
    xEvent.eEventType = eNetworkDownEvent;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 0, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

void test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEvent3( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 10;

    xIPTaskInitialised = pdFALSE;
    xEvent.eEventType = eNetworkDownEvent;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 10, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

void test_xSendEventStructToIPTask_IPTaskInit_NetworkDownEvent( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 10;

    xIPTaskInitialised = pdTRUE;
    xEvent.eEventType = eNetworkDownEvent;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 10, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

void test_xSendEventStructToIPTask_IPTaskInit_eTCPTimerEvent( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 10;

    xIPTaskInitialised = pdTRUE;
    xEvent.eEventType = eTCPTimerEvent;

    vIPSetTCPTimerExpiredState_Expect( pdTRUE );

    uxQueueMessagesWaiting_ExpectAndReturn( xNetworkEventQueue, 0 );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 10, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

void test_xSendEventStructToIPTask_IPTaskInit_eTCPTimerEvent1( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 10;

    xIPTaskInitialised = pdTRUE;
    xEvent.eEventType = eTCPTimerEvent;

    vIPSetTCPTimerExpiredState_Expect( pdTRUE );

    uxQueueMessagesWaiting_ExpectAndReturn( xNetworkEventQueue, 0 );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 10, 0, pdFAIL );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xSendEventStructToIPTask_IPTaskInit_eTCPTimerEvent2( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 10;

    xIPTaskInitialised = pdTRUE;
    xEvent.eEventType = eTCPTimerEvent;

    vIPSetTCPTimerExpiredState_Expect( pdTRUE );

    uxQueueMessagesWaiting_ExpectAndReturn( xNetworkEventQueue, 1 );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

void test_eConsiderFrameForProcessing_NoMatch( void )
{
    eFrameProcessingResult_t eResult;
    const NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( pxEndPoint );

    memset( ucEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( ipLOCAL_MAC_ADDRESS, 0xAA, sizeof( MACAddress_t ) );

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_eConsiderFrameForProcessing_LocalMACMatch( void )
{
    eFrameProcessingResult_t eResult;
    const NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( pxEndPoint );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );
    memset( ipLOCAL_MAC_ADDRESS, 0xAA, sizeof( MACAddress_t ) );

    memcpy( pxEthernetHeader->xDestinationAddress.ucBytes, ipLOCAL_MAC_ADDRESS, sizeof( MACAddress_t ) );
    pxEthernetHeader->usFrameType = 0x00;

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_eConsiderFrameForProcessing_LocalMACMatch1( void )
{
    eFrameProcessingResult_t eResult;
    const NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( pxEndPoint );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );
    memset( ipLOCAL_MAC_ADDRESS, 0xAA, sizeof( MACAddress_t ) );

    memcpy( pxEthernetHeader->xDestinationAddress.ucBytes, ipLOCAL_MAC_ADDRESS, sizeof( MACAddress_t ) );
    pxEthernetHeader->usFrameType = 0xFFFF;

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

void test_eConsiderFrameForProcessing_LocalMACMatch2( void )
{
    eFrameProcessingResult_t eResult;
    const NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( pxEndPoint );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );
    memset( ipLOCAL_MAC_ADDRESS, 0xAA, sizeof( MACAddress_t ) );

    memcpy( pxEthernetHeader->xDestinationAddress.ucBytes, ipLOCAL_MAC_ADDRESS, sizeof( MACAddress_t ) );
    pxEthernetHeader->usFrameType = 0x0600;

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_eConsiderFrameForProcessing_BroadCastMACMatch( void )
{
    eFrameProcessingResult_t eResult;
    const NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( pxEndPoint );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );
    memset( ipLOCAL_MAC_ADDRESS, 0xAA, sizeof( MACAddress_t ) );

    memcpy( pxEthernetHeader->xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );
    pxEthernetHeader->usFrameType = 0xFFFF;

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

void test_eConsiderFrameForProcessing_LLMNR_MACMatch( void )
{
    eFrameProcessingResult_t eResult;
    const NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( pxEndPoint );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );
    memset( ipLOCAL_MAC_ADDRESS, 0xAA, sizeof( MACAddress_t ) );

    memcpy( pxEthernetHeader->xDestinationAddress.ucBytes, xLLMNR_MacAdress.ucBytes, sizeof( MACAddress_t ) );
    pxEthernetHeader->usFrameType = 0xFFFF;

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

void test_prvProcessEthernetPacket_NoData( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->xDataLength = 0;
    pxNetworkBuffer->pucEthernetBuffer = NULL;

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

void test_prvProcessEthernetPacket_CatchAssert( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->xDataLength = 0;
    pxNetworkBuffer->pucEthernetBuffer = NULL;
    catch_assert( prvProcessEthernetPacket( NULL ) );
}

void test_prvProcessEthernetPacket_UnknownFrameType( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

void test_prvProcessEthernetPacket_ARPFrameType1( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eReleaseBuffer );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

void test_prvProcessEthernetPacket_ARPFrameType2( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eProcessBuffer );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

void test_prvProcessEthernetPacket_ARPFrameType_WaitingARPResolution( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;

    pxARPWaitingNetworkBuffer = NULL;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eWaitingARPResolution );

    vIPTimerStartARPResolution_ExpectAnyArgs();

    prvProcessEthernetPacket( pxNetworkBuffer );
}

void test_prvProcessEthernetPacket_ARPFrameType_WaitingARPResolution2( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;

    pxARPWaitingNetworkBuffer = ( NetworkBufferDescriptor_t * ) 0x1234ABCD;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eWaitingARPResolution );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

void test_prvProcessEthernetPacket_ARPFrameType_eReturnEthernetFrame( void )
{
    struct xNetworkInterface xInterface, * pxInterface = &xInterface;
    NetworkBufferDescriptor_t xNetworkBuffer, xARPWaitingBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkEndPoint xEndPoint = { 0 };

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.pxNetworkInterface = &xInterfaces;
    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    pxARPWaitingNetworkBuffer = &xARPWaitingBuffer;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eReturnEthernetFrame );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    prvProcessEthernetPacket( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
}

void test_prvProcessEthernetPacket_ARPFrameType_eFrameConsumed( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, xARPWaitingBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;

    pxARPWaitingNetworkBuffer = &xARPWaitingBuffer;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eFrameConsumed );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

void test_prvProcessEthernetPacket_ARPFrameType_SmallerDataLength( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t );
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

void test_prvProcessEthernetPacket_IPv4FrameType_LessData( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t );
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipIPv4_FRAME_TYPE;

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

void test_prvProcessEthernetPacket_IPv4FrameType_AptData( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipIPv4_FRAME_TYPE;

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

void test_xIsIPv4Multicast_NotMultiCast( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0;

    xReturn = xIsIPv4Multicast( ulIPAddress );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_xIsIPv4Multicast_NotMultiCast2( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = FreeRTOS_htonl( 0xF0000000 );

    xReturn = xIsIPv4Multicast( ulIPAddress );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_xIsIPv4Multicast_IsMultiCast( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = FreeRTOS_htonl( 0xF0000000 - 1 );

    xReturn = xIsIPv4Multicast( ulIPAddress );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

void test_prvAllowIPPacketIPv4( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_FragmentedPacket( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->usFragmentOffset = ipFRAGMENT_OFFSET_BIT_MASK;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_FragmentedPacket1( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->usFragmentOffset = ipFRAGMENT_FLAGS_MORE_FRAGMENTS;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_IncorrectLength( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->ucVersionHeaderLength = 0xFF;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_NotMatchingIP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER + 1;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );


    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPMatch( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );


    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPBrdCast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = 0xFFFFFFFF;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPBrdcast1( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    NetworkEndPoint_t xEndPoints;
    IPV4Parameters_t * xIPv4Addressing = &( xEndPoints.ipv4_settings );

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = xIPv4Addressing->ulBroadcastAddress;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );


    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPLLMNR( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = ipLLMNR_IP_ADDR;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );


    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SourceIPBrdCast_NoLocalIP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0x00;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER + 1;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );


    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_DestMACBrdCast_DestIPUnicast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0x00;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = 0x00;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );


    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SrcMACBrdCast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xSourceAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SrcMACBrdCast2( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xSourceAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_SrcIPAddrIsMulticast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 1, sizeof( NetworkBufferDescriptor_t ) );
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxNetworkBuffer->pxEndPoint = NULL;

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = FreeRTOS_htonl( 0xE0000000 + 1 );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_IncorrectChecksum( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC - 1 );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_IncorrectProtocolChecksum( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAndReturn( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE, ( uint16_t ) ( ipCORRECT_CRC + 1 ) );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacketIPv4_HappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAndReturn( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

void test_prvProcessIPPacket_HeaderLengthSmaller( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->ucVersionHeaderLength = 0xF0;

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvProcessIPPacket_HeaderLengthGreater( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->ucVersionHeaderLength = 0xFF;

    /* Let the data length be greater than the ethernet header but small
     * enough to make the IP header bigger than the total length. */
    pxNetworkBuffer->xDataLength = 30;

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvProcessIPPacket_ValidHeaderButNoData( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->ucVersionHeaderLength = 0xF6;

    /* Let the data length be greater than the ethernet header but small
     * enough to make the IP header bigger than the total length. */
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvProcessIPPacket_ValidHeader_ARPResolutionReqd( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdTRUE );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eWaitingARPResolution, eResult );
}

void test_prvProcessIPPacket_ARPResolutionNotReqd_InvalidProt( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x46;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );

    vARPRefreshCacheEntry_ExpectAnyArgs();

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvProcessIPPacket_ARPResolutionNotReqd_ICMP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x46;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );

    vARPRefreshCacheEntry_ExpectAnyArgs();

    /* Set the protocol to be ICMP. */
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    ProcessICMPPacket_ExpectAndReturn( pxNetworkBuffer, eReleaseBuffer );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvProcessIPPacket_ARPResolutionNotReqd_ICMP2( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFE;

    pxIPHeader->ucVersionHeaderLength = 0x46;

    /* Packet not meant for this node. */
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER + 1;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );

    vARPRefreshCacheEntry_ExpectAnyArgs();

    ProcessICMPPacket_ExpectAndReturn( pxNetworkBuffer, eProcessBuffer );

    /* Set the protocol to be ICMP. */
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

void test_prvProcessIPPacket_ARPResolutionNotReqd_UDP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFE;

    pxIPHeader->ucVersionHeaderLength = 0x46;

    /* Packet not meant for this node. */
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER + 1;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    /* Set the protocol to be ICMP. */
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvProcessIPPacket_ARPResolutionNotReqd_UDP_DataLengthCorrect( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t );

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFE;

    pxIPHeader->ucVersionHeaderLength = 0x46;

    /* Packet not meant for this node. */
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER + 1;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    /* Set the protocol to be ICMP. */
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvProcessIPPacket_ARPResolutionNotReqd_UDP_AllLengthCorrect( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    UDPPacket_t * pxUDPPacket;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;

    pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFE;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );

    /* Packet not meant for this node. */
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    /* Set the protocol to be ICMP. */
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxUDPPacket->xUDPHeader.usLength = ipconfigTCP_MSS;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvProcessIPPacket_ARPResolutionNotReqd_UDP_AllLengthCorrect2( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    UDPPacket_t * pxUDPPacket;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFE;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );

    /* Packet not meant for this node. */
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    /* Set the protocol to be ICMP. */
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_ntohs( sizeof( UDPPacket_t ) );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xProcessReceivedUDPPacket_ExpectAnyArgsAndReturn( pdPASS );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eFrameConsumed, eResult );
}

void test_prvProcessIPPacket_ARPResolutionNotReqd_UDP_AllLengthCorrect3( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    UDPPacket_t * pxUDPPacket;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFE;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );

    /* Packet not meant for this node. */
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    /* Set the protocol to be ICMP. */
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_ntohs( sizeof( UDPPacket_t ) );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xProcessReceivedUDPPacket_ExpectAnyArgsAndReturn( pdFAIL );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvProcessIPPacket_ARPResolutionReqd_UDP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    UDPPacket_t * pxUDPPacket;
    BaseType_t xReturnValue = pdTRUE;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFE;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );

    /* Packet not meant for this node. */
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    /* Set the protocol to be ICMP. */
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_ntohs( sizeof( UDPPacket_t ) );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xProcessReceivedUDPPacket_ExpectAndReturn( pxNetworkBuffer, pxUDPPacket->xUDPHeader.usDestinationPort, NULL, pdFAIL );
    xProcessReceivedUDPPacket_IgnoreArg_pxIsWaitingForARPResolution();
    xProcessReceivedUDPPacket_ReturnThruPtr_pxIsWaitingForARPResolution( &xReturnValue );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eWaitingARPResolution, eResult );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) - sizeof( UDPHeader_t ) + sizeof( UDPPacket_t ), pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xIPAddress.ulIP_IPv4, pxUDPPacket->xIPHeader.ulSourceIPAddress );
}

void test_prvProcessIPPacket_ARPResolutionReqd_UDP1( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    UDPPacket_t * pxUDPPacket;
    BaseType_t xReturnValue = pdTRUE;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t );

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFE;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );

    /* Packet not meant for this node. */
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    /* Set the protocol to be ICMP. */
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_ntohs( sizeof( UDPPacket_t ) );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xProcessReceivedUDPPacket_ExpectAndReturn( pxNetworkBuffer, pxUDPPacket->xUDPHeader.usDestinationPort, NULL, pdFAIL );
    xProcessReceivedUDPPacket_IgnoreArg_pxIsWaitingForARPResolution();
    xProcessReceivedUDPPacket_ReturnThruPtr_pxIsWaitingForARPResolution( &xReturnValue );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eWaitingARPResolution, eResult );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xIPAddress.ulIP_IPv4, pxUDPPacket->xIPHeader.ulSourceIPAddress );
}

void test_prvProcessIPPacket_TCP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    BaseType_t xReturnValue = pdTRUE;
    uint32_t backup = xProcessedTCPMessage;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t );

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFE;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );
    /* Packet not meant for this node. */
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Set the protocol to be TCP. */
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntry_ExpectAnyArgs();

    xProcessReceivedTCPPacket_ExpectAndReturn( pxNetworkBuffer, pdPASS );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eFrameConsumed, eResult );
    TEST_ASSERT_EQUAL( backup + 1, xProcessedTCPMessage );
}

void test_prvProcessIPPacket_TCP1( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    BaseType_t xReturnValue = pdTRUE;
    uint32_t backup = xProcessedTCPMessage;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t );

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFE;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );
    /* Packet not meant for this node. */
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Set the protocol to be TCP. */
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntry_ExpectAnyArgs();

    xProcessReceivedTCPPacket_ExpectAndReturn( pxNetworkBuffer, pdFAIL );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
    TEST_ASSERT_EQUAL( backup + 1, xProcessedTCPMessage );
}

void test_vReturnEthernetFrame( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;
    xEndPoint.pxNetworkInterface = &xInterfaces;
    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10;

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxNetworkBuffer->pxEndPoint );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
}

void test_vReturnEthernetFrame_DataLenMoreThanRequired( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;
    xEndPoint.pxNetworkInterface = &xInterfaces;
    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;
    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxNetworkBuffer->pxEndPoint );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAA, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
}

void test_FreeRTOS_GetIPAddress( void ) /* TODO */
{
    uint32_t ulIPAddress;

    NetworkEndPoint_t xEndPoint = { 0 };

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    xEndPoint.ipv4_settings.ulIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );

    ulIPAddress = FreeRTOS_GetIPAddress();

    TEST_ASSERT_EQUAL( *ipLOCAL_IP_ADDRESS_POINTER, ulIPAddress );
}

void test_FreeRTOS_IsNetworkUp( void )
{
    BaseType_t xReturn;
    struct xNetworkEndPoint xEndPoint = { 0 };

    memset( &xEndPoint, 0, sizeof( struct xNetworkEndPoint ) );


    xEndPoint.bits.bEndPointUp = pdTRUE;
    /* xNetworkUp = pdTRUE; */
    /* xReturn = FreeRTOS_IsNetworkUp(); */
    xReturn = FreeRTOS_IsEndPointUp( &xEndPoint );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );

    /* xNetworkUp = pdFALSE; */
    /* xReturn = FreeRTOS_IsNetworkUp(); */
    xEndPoint.bits.bEndPointUp = pdFALSE;
    xReturn = FreeRTOS_IsEndPointUp( &xEndPoint );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    /* xReturn = FreeRTOS_IsNetworkUp(); TODO to be checked in routing */
    /* TEST_ASSERT_EQUAL( pdFALSE, xReturn ); */
}

void test_CastingFunctions( void )
{
    void * pvPtr;

    const IPPacket_t * pxIPPacket = ( ( const IPPacket_t * ) pvPtr );
    const IPHeader_t * pxIPHeader = ( ( const IPHeader_t * ) pvPtr );
    const TCPPacket_t * pxConstTCPPacket = ( ( const TCPPacket_t * ) pvPtr );
    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pvPtr );
    ProtocolPacket_t * pxProtPacket = ( ( ProtocolPacket_t * ) pvPtr );
    const ProtocolPacket_t * pxConstProtPacket = ( ( const ProtocolPacket_t * ) pvPtr );
    const SocketSelect_t * pxSockSelPtr = ( ( const SocketSelect_t * ) pvPtr );
    const SocketSelectMessage_t * pxConstSockSelMsgPtr = ( ( const SocketSelectMessage_t * ) pvPtr );
    SocketSelectMessage_t * pxSockSelMsgPtr = ( ( SocketSelectMessage_t * ) pvPtr );
    NetworkBufferDescriptor_t * pxNetworkBuffer = ( ( NetworkBufferDescriptor_t * ) pvPtr );
    ListItem_t * pxList = ( ( ListItem_t * ) pvPtr );
    const ListItem_t * pxConstList = ( ( const ListItem_t * ) pvPtr );
    const FreeRTOS_Socket_t * pxSocket = ( ( const FreeRTOS_Socket_t * ) pvPtr );
    const ProtocolHeaders_t * pxConstProtHeader = ( ( const ProtocolHeaders_t * ) pvPtr );
    ProtocolHeaders_t * pxProtHeader = ( ( ProtocolHeaders_t * ) pvPtr );
}

void test_FreeRTOS_IPInit_Multi_NoInterface( void )
{
    FreeRTOS_FirstNetworkInterface_IgnoreAndReturn( NULL );
    catch_assert( FreeRTOS_IPInit_Multi() );
}

void test_FreeRTOS_GetEndPointConfiguration_AllConfigurations( void )
{
    uint32_t ulIPAddress;
    uint32_t ulNetMask;
    uint32_t ulGatewayAddress;
    uint32_t ulDNSServerAddress;
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xEndPoint.ipv4_settings.ulIPAddress = 1;
    xEndPoint.ipv4_settings.ulNetMask = 2;
    xEndPoint.ipv4_settings.ulGatewayAddress = 3;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[0] = 4;

    FreeRTOS_GetEndPointConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress, &xEndPoint );
    TEST_ASSERT_EQUAL( 1, ulIPAddress );
    TEST_ASSERT_EQUAL( 2, ulNetMask );
    TEST_ASSERT_EQUAL( 3, ulGatewayAddress );
    TEST_ASSERT_EQUAL( 4, ulDNSServerAddress );
}

void test_FreeRTOS_GetEndPointConfiguration_AllNull( void )
{
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xEndPoint.ipv4_settings.ulIPAddress = 1;
    xEndPoint.ipv4_settings.ulNetMask = 2;
    xEndPoint.ipv4_settings.ulGatewayAddress = 3;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[0] = 4;

    FreeRTOS_GetEndPointConfiguration( NULL, NULL, NULL, NULL, &xEndPoint );
}
