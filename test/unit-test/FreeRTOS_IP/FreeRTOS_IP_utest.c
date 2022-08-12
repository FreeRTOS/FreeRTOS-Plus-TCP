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
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_UDP_IP.h"

#include "FreeRTOS_IP.h"

#include "FreeRTOS_IP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer );
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );
eFrameProcessingResult_t prvAllowIPPacket( const IPPacket_t * const pxIPPacket,
                                           const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                           UBaseType_t uxHeaderLength );

extern BaseType_t xIPTaskInitialised;
extern BaseType_t xNetworkDownEventPending;
extern BaseType_t xNetworkUp;

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

static void vSetIPTaskHandle( TaskHandle_t xTaskHandleToSet )
{
    const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ];
    const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ];
    const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ];
    const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ];
    const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ];

    vPreCheckConfigs_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xQueueGenericCreateStatic_ExpectAnyArgsAndReturn( ( QueueHandle_t ) 0x1234ABCD );
    #else
        xQueueGenericCreate__ExpectAnyArgsAndReturn( ( QueueHandle_t ) 0x1234ABCD );
    #endif /* configSUPPORT_STATIC_ALLOCATION */

    #if ( configQUEUE_REGISTRY_SIZE > 0 )
        vQueueAddToRegistry_ExpectAnyArgs();
    #endif

    xNetworkBuffersInitialise_ExpectAndReturn( pdPASS );

    vNetworkSocketsInit_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xTaskCreateStatic_ExpectAnyArgsAndReturn( xTaskHandleToSet );
    #else
        xTaskCreate_ReturnThruPtr_pxCreatedTask( xTaskHandleToSet );
    #endif

    FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );
}



/* Test for FreeRTOS_inet_pton4 function. */
void test_FreeRTOS_GetIPTaskHandle( void )
{
    TaskHandle_t xIPTaskHandleToSet = ( TaskHandle_t ) 0x12ABCD34;

    vSetIPTaskHandle( xIPTaskHandleToSet );

    TEST_ASSERT_EQUAL( xIPTaskHandleToSet, FreeRTOS_GetIPTaskHandle() );
}

void test_vIPNetworkUpCalls( void )
{
    xNetworkUp = pdFALSE;

    vApplicationIPNetworkEventHook_Expect( eNetworkUp );
    vDNSInitialise_Expect();
    vARPTimerReload_Expect( pdMS_TO_TICKS( 10000 ) );

    vIPNetworkUpCalls();

    TEST_ASSERT_EQUAL( pdTRUE, xNetworkUp );
}

void test_FreeRTOS_NetworkDown_SendToIPTaskSuccessful( void )
{
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xQueueGenericSend_ExpectAnyArgsAndReturn( pdPASS );

    FreeRTOS_NetworkDown();

    TEST_ASSERT_EQUAL( pdFALSE, xIsNetworkDownEventPending() );
}

void test_FreeRTOS_NetworkDown_SendToIPTaskNotSuccessful( void )
{
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xQueueGenericSend_ExpectAnyArgsAndReturn( pdFAIL );

    FreeRTOS_NetworkDown();

    TEST_ASSERT_EQUAL( pdTRUE, xIsNetworkDownEventPending() );
}

void test_FreeRTOS_NetworkDownFromISR_SendToIPTaskSuccessful( void )
{
    BaseType_t xHasPriorityTaskAwoken = pdTRUE;
    BaseType_t xReturn;

    xQueueGenericSendFromISR_ExpectAnyArgsAndReturn( pdPASS );
    xQueueGenericSendFromISR_ReturnThruPtr_pxHigherPriorityTaskWoken( &xHasPriorityTaskAwoken );

    xReturn = FreeRTOS_NetworkDownFromISR();

    TEST_ASSERT_EQUAL( pdFALSE, xIsNetworkDownEventPending() );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

void test_FreeRTOS_NetworkDownFromISR_SendToIPTaskUnsuccessful( void )
{
    BaseType_t xHasPriorityTaskAwoken = pdFALSE;
    BaseType_t xReturn;

    xQueueGenericSendFromISR_ExpectAnyArgsAndReturn( pdFAIL );
    xQueueGenericSendFromISR_ReturnThruPtr_pxHigherPriorityTaskWoken( &xHasPriorityTaskAwoken );

    xReturn = FreeRTOS_NetworkDownFromISR();

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

    pvReturn = FreeRTOS_GetUDPPayloadBuffer( uxRequestedSizeBytes, uxBlockTimeTicks );

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

    pvReturn = FreeRTOS_GetUDPPayloadBuffer( uxRequestedSizeBytes, uxBlockTimeTicks );

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

    pvReturn = FreeRTOS_GetUDPPayloadBuffer( uxRequestedSizeBytes, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL_PTR( &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_t ) ] ), pvReturn );
}

void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeMoreThanConfig_NULLBufferReturned( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS + 1;
    void * pvReturn;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS, NULL );

    pvReturn = FreeRTOS_GetUDPPayloadBuffer( uxRequestedSizeBytes, uxBlockTimeTicks );

    TEST_ASSERT_NULL( pvReturn );
}

void test_FreeRTOS_IPInit_HappyPath( void )
{
    const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC0, 0xB0, 0xAB, 0x12 };
    const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC1, 0xB2, 0xAC, 0x13 };
    const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC2, 0xB3, 0xAC, 0x14 };
    const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC3, 0xB4, 0xAD, 0x15 };
    const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF };
    BaseType_t xReturn;
    QueueHandle_t ulPointerToQueue = ( QueueHandle_t ) 0x1234ABCD;
    TaskHandle_t xTaskHandleToSet = ( TaskHandle_t ) 0xCDBA9087;

    /* Set the local IP to something other than 0. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD;

    /* Clear default values. */
    memset( &xDefaultAddressing, 0, sizeof( xDefaultAddressing ) );
    memset( &xNetworkAddressing, 0, sizeof( xDefaultAddressing ) );

    vPreCheckConfigs_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xQueueGenericCreateStatic_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), NULL, NULL, 0, ulPointerToQueue );
        xQueueGenericCreateStatic_IgnoreArg_pucQueueStorage();
        xQueueGenericCreateStatic_IgnoreArg_pxStaticQueue();
    #else
        xQueueGenericCreate__ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), ulPointerToQueue );
    #endif /* configSUPPORT_STATIC_ALLOCATION */

    #if ( configQUEUE_REGISTRY_SIZE > 0 )
        vQueueAddToRegistry_Expect( ulPointerToQueue, "NetEvnt" );
    #endif

    xNetworkBuffersInitialise_ExpectAndReturn( pdPASS );

    vNetworkSocketsInit_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xTaskCreateStatic_ExpectAnyArgsAndReturn( xTaskHandleToSet );
    #else
        xTaskCreate_ReturnThruPtr_pxCreatedTask( xTaskHandleToSet );
    #endif

    xReturn = FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucIPAddress[ 0 ], ucIPAddress[ 1 ], ucIPAddress[ 2 ], ucIPAddress[ 3 ] ), xNetworkAddressing.ulDefaultIPAddress );
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucNetMask[ 0 ], ucNetMask[ 1 ], ucNetMask[ 2 ], ucNetMask[ 3 ] ), xNetworkAddressing.ulNetMask );
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucGatewayAddress[ 0 ], ucGatewayAddress[ 1 ], ucGatewayAddress[ 2 ], ucGatewayAddress[ 3 ] ), xNetworkAddressing.ulGatewayAddress );
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucDNSServerAddress[ 0 ], ucDNSServerAddress[ 1 ], ucDNSServerAddress[ 2 ], ucDNSServerAddress[ 3 ] ), xNetworkAddressing.ulDNSServerAddress );
    TEST_ASSERT_EQUAL( ( ( xNetworkAddressing.ulDefaultIPAddress & xNetworkAddressing.ulNetMask ) | ~xNetworkAddressing.ulNetMask ), xNetworkAddressing.ulBroadcastAddress );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultAddressing, &xNetworkAddressing, sizeof( xDefaultAddressing ) );
    TEST_ASSERT_EQUAL( 0, *ipLOCAL_IP_ADDRESS_POINTER );
    TEST_ASSERT_EQUAL_MEMORY( ucMACAddress, ipLOCAL_MAC_ADDRESS, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( xTaskHandleToSet, FreeRTOS_GetIPTaskHandle() );
}

void test_FreeRTOS_IPInit_QueueCreationFails( void )
{
    const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC0, 0xB0, 0xAB, 0x12 };
    const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC1, 0xB2, 0xAC, 0x13 };
    const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC2, 0xB3, 0xAC, 0x14 };
    const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC3, 0xB4, 0xAD, 0x15 };
    const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF };
    BaseType_t xReturn;
    QueueHandle_t pxPointerToQueue = NULL;

    /* Set the local IP to something other than 0. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD;

    /* Clear default values. */
    memset( &xDefaultAddressing, 0, sizeof( xDefaultAddressing ) );
    memset( &xNetworkAddressing, 0, sizeof( xDefaultAddressing ) );
    memset( ipLOCAL_MAC_ADDRESS, 0, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

    vPreCheckConfigs_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xQueueGenericCreateStatic_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), NULL, NULL, 0, pxPointerToQueue );
        xQueueGenericCreateStatic_IgnoreArg_pucQueueStorage();
        xQueueGenericCreateStatic_IgnoreArg_pxStaticQueue();
    #else
        xQueueGenericCreate__ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), pxPointerToQueue );
    #endif /* configSUPPORT_STATIC_ALLOCATION */

    xReturn = FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xNetworkAddressing.ulDefaultIPAddress, ipIP_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xNetworkAddressing.ulNetMask, ipIP_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xNetworkAddressing.ulGatewayAddress, ipIP_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xNetworkAddressing.ulDNSServerAddress, ipIP_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xNetworkAddressing.ulBroadcastAddress, ipIP_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultAddressing, &xNetworkAddressing, sizeof( xDefaultAddressing ) );
    TEST_ASSERT_EQUAL( 0xABCD, *ipLOCAL_IP_ADDRESS_POINTER );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, ipLOCAL_MAC_ADDRESS, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
}

void test_FreeRTOS_IPInit_BufferCreationFails( void )
{
    const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC0, 0xB0, 0xAB, 0x12 };
    const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC1, 0xB2, 0xAC, 0x13 };
    const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC2, 0xB3, 0xAC, 0x14 };
    const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC3, 0xB4, 0xAD, 0x15 };
    const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF };
    BaseType_t xReturn;
    QueueHandle_t pxPointerToQueue = ( QueueHandle_t ) 0x1234ABCD;

    /* Set the local IP to something other than 0. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD;

    /* Clear default values. */
    memset( &xDefaultAddressing, 0, sizeof( xDefaultAddressing ) );
    memset( &xNetworkAddressing, 0, sizeof( xDefaultAddressing ) );
    memset( ipLOCAL_MAC_ADDRESS, 0, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

    vPreCheckConfigs_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xQueueGenericCreateStatic_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), NULL, NULL, 0, pxPointerToQueue );
        xQueueGenericCreateStatic_IgnoreArg_pucQueueStorage();
        xQueueGenericCreateStatic_IgnoreArg_pxStaticQueue();
    #else
        xQueueGenericCreate__ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), pxPointerToQueue );
    #endif /* configSUPPORT_STATIC_ALLOCATION */

    #if ( configQUEUE_REGISTRY_SIZE > 0 )
        vQueueAddToRegistry_Expect( pxPointerToQueue, "NetEvnt" );
    #endif

    xNetworkBuffersInitialise_ExpectAndReturn( pdFAIL );

    vQueueDelete_Expect( pxPointerToQueue );

    xReturn = FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xNetworkAddressing.ulDefaultIPAddress, ipIP_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xNetworkAddressing.ulNetMask, ipIP_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xNetworkAddressing.ulGatewayAddress, ipIP_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xNetworkAddressing.ulDNSServerAddress, ipIP_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xNetworkAddressing.ulBroadcastAddress, ipIP_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultAddressing, &xNetworkAddressing, sizeof( xDefaultAddressing ) );
    TEST_ASSERT_EQUAL( 0xABCD, *ipLOCAL_IP_ADDRESS_POINTER );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, ipLOCAL_MAC_ADDRESS, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
}

void test_FreeRTOS_IPInit_TaskCreationFails( void )
{
    const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC0, 0xB0, 0xAB, 0x12 };
    const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC1, 0xB2, 0xAC, 0x13 };
    const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC2, 0xB3, 0xAC, 0x14 };
    const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC3, 0xB4, 0xAD, 0x15 };
    const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF };
    BaseType_t xReturn;
    QueueHandle_t pxPointerToQueue = ( QueueHandle_t ) 0x1234ABCD;

    /* Set the local IP to something other than 0. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD;

    /* Clear default values. */
    memset( &xDefaultAddressing, 0, sizeof( xDefaultAddressing ) );
    memset( &xNetworkAddressing, 0, sizeof( xDefaultAddressing ) );
    memset( ipLOCAL_MAC_ADDRESS, 0, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

    vPreCheckConfigs_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xQueueGenericCreateStatic_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), NULL, NULL, 0, pxPointerToQueue );
        xQueueGenericCreateStatic_IgnoreArg_pucQueueStorage();
        xQueueGenericCreateStatic_IgnoreArg_pxStaticQueue();
    #else
        xQueueGenericCreate__ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), pxPointerToQueue );
    #endif /* configSUPPORT_STATIC_ALLOCATION */

    #if ( configQUEUE_REGISTRY_SIZE > 0 )
        vQueueAddToRegistry_Expect( pxPointerToQueue, "NetEvnt" );
    #endif

    xNetworkBuffersInitialise_ExpectAndReturn( pdPASS );

    vNetworkSocketsInit_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xTaskCreateStatic_ExpectAnyArgsAndReturn( NULL );
    #else
        xTaskCreate_ExpectAnyArgsAndReturn( pdFAIL );
        xTaskCreate_ReturnThruPtr_pxCreatedTask( NULL );
    #endif

    xReturn = FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucIPAddress[ 0 ], ucIPAddress[ 1 ], ucIPAddress[ 2 ], ucIPAddress[ 3 ] ), xNetworkAddressing.ulDefaultIPAddress );
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucNetMask[ 0 ], ucNetMask[ 1 ], ucNetMask[ 2 ], ucNetMask[ 3 ] ), xNetworkAddressing.ulNetMask );
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucGatewayAddress[ 0 ], ucGatewayAddress[ 1 ], ucGatewayAddress[ 2 ], ucGatewayAddress[ 3 ] ), xNetworkAddressing.ulGatewayAddress );
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucDNSServerAddress[ 0 ], ucDNSServerAddress[ 1 ], ucDNSServerAddress[ 2 ], ucDNSServerAddress[ 3 ] ), xNetworkAddressing.ulDNSServerAddress );
    TEST_ASSERT_EQUAL( ( ( xNetworkAddressing.ulDefaultIPAddress & xNetworkAddressing.ulNetMask ) | ~xNetworkAddressing.ulNetMask ), xNetworkAddressing.ulBroadcastAddress );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultAddressing, &xNetworkAddressing, sizeof( xDefaultAddressing ) );
    TEST_ASSERT_EQUAL( 0, *ipLOCAL_IP_ADDRESS_POINTER );
    TEST_ASSERT_EQUAL_MEMORY( ucMACAddress, ipLOCAL_MAC_ADDRESS, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( NULL, FreeRTOS_GetIPTaskHandle() );
}

void test_FreeRTOS_GetAddressConfiguration_HappyPath( void )
{
    uint32_t ulIPAddress, ulNetMask, ulGatewayAddress, ulDNSServerAddress;
    uint32_t ulStoredIPAddress = 0x12345678;
    uint32_t ulStoredNetMask = 0xABCDEF12;
    uint32_t ulStoredGatewayAddress = 0xAABBCCDD;
    uint32_t ulStoredDNSServerAddress = 0x12121212;
    uint32_t * pulIPAddress = &ulIPAddress;
    uint32_t * pulNetMask = &ulNetMask;
    uint32_t * pulGatewayAddress = &ulGatewayAddress;
    uint32_t * pulDNSServerAddress = &ulDNSServerAddress;

    *ipLOCAL_IP_ADDRESS_POINTER = ulStoredIPAddress;
    xNetworkAddressing.ulNetMask = ulStoredNetMask;
    xNetworkAddressing.ulGatewayAddress = ulStoredGatewayAddress;
    xNetworkAddressing.ulDNSServerAddress = ulStoredDNSServerAddress;

    FreeRTOS_GetAddressConfiguration( pulIPAddress, pulNetMask, pulGatewayAddress, pulDNSServerAddress );

    TEST_ASSERT_EQUAL( ulStoredIPAddress, *pulIPAddress );
    TEST_ASSERT_EQUAL( ulStoredNetMask, *pulNetMask );
    TEST_ASSERT_EQUAL( ulStoredGatewayAddress, *pulGatewayAddress );
    TEST_ASSERT_EQUAL( ulStoredDNSServerAddress, *pulDNSServerAddress );
}

void test_FreeRTOS_GetAddressConfiguration_AllPointersNull( void )
{
    uint32_t ulStoredIPAddress = 0x12345678;
    uint32_t ulStoredNetMask = 0xABCDEF12;
    uint32_t ulStoredGatewayAddress = 0xAABBCCDD;
    uint32_t ulStoredDNSServerAddress = 0x12121212;
    uint32_t * pulIPAddress = NULL;
    uint32_t * pulNetMask = NULL;
    uint32_t * pulGatewayAddress = NULL;
    uint32_t * pulDNSServerAddress = NULL;

    *ipLOCAL_IP_ADDRESS_POINTER = ulStoredIPAddress;
    xNetworkAddressing.ulNetMask = ulStoredNetMask;
    xNetworkAddressing.ulGatewayAddress = ulStoredGatewayAddress;
    xNetworkAddressing.ulDNSServerAddress = ulStoredDNSServerAddress;

    FreeRTOS_GetAddressConfiguration( pulIPAddress, pulNetMask, pulGatewayAddress, pulDNSServerAddress );

    TEST_ASSERT_EQUAL( NULL, pulIPAddress );
    TEST_ASSERT_EQUAL( NULL, pulNetMask );
    TEST_ASSERT_EQUAL( NULL, pulGatewayAddress );
    TEST_ASSERT_EQUAL( NULL, pulDNSServerAddress );
}

void test_FreeRTOS_SetAddressConfiguration_HappyPath( void )
{
    uint32_t ulStoredIPAddress = 0x12345678;
    uint32_t ulStoredNetMask = 0xABCDEF12;
    uint32_t ulStoredGatewayAddress = 0xAABBCCDD;
    uint32_t ulStoredDNSServerAddress = 0x12121212;
    uint32_t * pulIPAddress = &ulStoredIPAddress;
    uint32_t * pulNetMask = &ulStoredNetMask;
    uint32_t * pulGatewayAddress = &ulStoredGatewayAddress;
    uint32_t * pulDNSServerAddress = &ulStoredDNSServerAddress;

    *ipLOCAL_IP_ADDRESS_POINTER = 0;
    xNetworkAddressing.ulNetMask = 0;
    xNetworkAddressing.ulGatewayAddress = 0;
    xNetworkAddressing.ulDNSServerAddress = 0;

    FreeRTOS_SetAddressConfiguration( pulIPAddress, pulNetMask, pulGatewayAddress, pulDNSServerAddress );

    TEST_ASSERT_EQUAL( ulStoredIPAddress, *ipLOCAL_IP_ADDRESS_POINTER );
    TEST_ASSERT_EQUAL( ulStoredNetMask, xNetworkAddressing.ulNetMask );
    TEST_ASSERT_EQUAL( ulStoredGatewayAddress, xNetworkAddressing.ulGatewayAddress );
    TEST_ASSERT_EQUAL( ulStoredDNSServerAddress, xNetworkAddressing.ulDNSServerAddress );
}

void test_FreeRTOS_SetAddressConfiguration_AllValuesNULL( void )
{
    uint32_t * pulIPAddress = NULL;
    uint32_t * pulNetMask = NULL;
    uint32_t * pulGatewayAddress = NULL;
    uint32_t * pulDNSServerAddress = NULL;

    *ipLOCAL_IP_ADDRESS_POINTER = 0;
    xNetworkAddressing.ulNetMask = 0;
    xNetworkAddressing.ulGatewayAddress = 0;
    xNetworkAddressing.ulDNSServerAddress = 0;

    FreeRTOS_SetAddressConfiguration( pulIPAddress, pulNetMask, pulGatewayAddress, pulDNSServerAddress );

    TEST_ASSERT_EQUAL( 0, *ipLOCAL_IP_ADDRESS_POINTER );
    TEST_ASSERT_EQUAL( 0, xNetworkAddressing.ulNetMask );
    TEST_ASSERT_EQUAL( 0, xNetworkAddressing.ulGatewayAddress );
    TEST_ASSERT_EQUAL( 0, xNetworkAddressing.ulDNSServerAddress );
}

void test_FreeRTOS_ReleaseUDPPayloadBuffer( void )
{
    void * pvBuffer = ( void * ) 0xFFCDEA;

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pvBuffer, ( NetworkBufferDescriptor_t * ) 0x12123434 );
    vReleaseNetworkBufferAndDescriptor_Expect( ( NetworkBufferDescriptor_t * ) 0x12123434 );

    FreeRTOS_ReleaseUDPPayloadBuffer( pvBuffer );
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

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xQueueGenericSend_ExpectAnyArgsAndReturn( pdTRUE );

    vTCPTimerReload_ExpectAnyArgs();

    vIPSetARPResolutionTimerEnableState_Expect( pdFALSE );

    /* Let the task get called first time. */
    ipFOREVER_ExpectAndReturn( 1 );

    /* Expect the timers to be checked every iteration. */
    vCheckNetworkTimers_Expect();

    /* Sleep time doesn't matter here. */
    xCalculateSleepTime_ExpectAndReturn( 0 );

    /* No event received. */
    xQueueReceive_ExpectAnyArgsAndReturn( pdFALSE );

    /* Second time around, we should exit the task. */
    ipFOREVER_ExpectAndReturn( 0 );

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

void test_prvProcessIPEventsAndTimers_eNetworkDownEvent( void )
{
    IPStackEvent_t xReceivedEvent;

    xReceivedEvent.eEventType = eNetworkDownEvent;

    xNetworkUp = pdTRUE;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    prvProcessNetworkDownEvent_Expect();

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( pdFALSE, xNetworkUp );
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
    IPStackEvent_t xReceivedEvent;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t ) - 1;

    xReceivedEvent.eEventType = eNetworkTxEvent;
    xReceivedEvent.pvData = pxNetworkBuffer;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    xNetworkInterfaceOutput_ExpectAndReturn( pxNetworkBuffer, pdTRUE, pdPASS );

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

    xReceivedEvent.eEventType = eDHCPEvent;
    xReceivedEvent.pvData = ( void * ) ulDHCPEvent;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vDHCPProcess_Expect( pdFALSE, ulDHCPEvent );

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
    SocketSelect_t * pxSocketSet = malloc( sizeof( SocketSelect_t ) );

    xNetworkDownEventPending = pdTRUE;

    xReceivedEvent.eEventType = eSocketSetDeleteEvent;
    xReceivedEvent.pvData = pxSocketSet;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    vEventGroupDelete_Expect( pxSocketSet->xSelectGroup );

    /* Since network down event is pending, a call to this function should be expected. */
    prvProcessNetworkDownEvent_Expect();

    prvProcessIPEventsAndTimers();
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
    TEST_ASSERT_EQUAL( ulIPAddress, pxNetworkBuffer->ulIPAddress );
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
    TEST_ASSERT_EQUAL( ulIPAddress, pxNetworkBuffer->ulIPAddress );
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
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];

    memset( ucEthernetBuffer, 0, ipconfigTCP_MSS );
    memset( ipLOCAL_MAC_ADDRESS, 0xAA, sizeof( MACAddress_t ) );

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_eConsiderFrameForProcessing_LocalMACMatch( void )
{
    eFrameProcessingResult_t eResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

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
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

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
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

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
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

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
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

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

    eARPProcessPacket_ExpectAndReturn( ( ARPPacket_t * const ) pxNetworkBuffer->pucEthernetBuffer, eReleaseBuffer );

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

    eARPProcessPacket_ExpectAndReturn( ( ARPPacket_t * const ) pxNetworkBuffer->pucEthernetBuffer, eProcessBuffer );

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

    eARPProcessPacket_ExpectAndReturn( ( ARPPacket_t * const ) pxNetworkBuffer->pucEthernetBuffer, eWaitingARPResolution );

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

    eARPProcessPacket_ExpectAndReturn( ( ARPPacket_t * const ) pxNetworkBuffer->pucEthernetBuffer, eWaitingARPResolution );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

void test_prvProcessEthernetPacket_ARPFrameType_eReturnEthernetFrame( void )
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

    eARPProcessPacket_ExpectAndReturn( ( ARPPacket_t * const ) pxNetworkBuffer->pucEthernetBuffer, eReturnEthernetFrame );

    xNetworkInterfaceOutput_ExpectAndReturn( pxNetworkBuffer, pdTRUE, pdPASS );

    prvProcessEthernetPacket( pxNetworkBuffer );
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

    eARPProcessPacket_ExpectAndReturn( ( ARPPacket_t * const ) pxNetworkBuffer->pucEthernetBuffer, eFrameConsumed );

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

void test_prvAllowIPPacket( void )
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

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_FragmentedPacket( void )
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

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_FragmentedPacket1( void )
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

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_IncorrectLength( void )
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

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_NotMatchingIP( void )
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
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER + 1;

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_SourceIPBrdCast_DestIPMatch( void )
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

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_SourceIPBrdCast_DestIPBrdCast( void )
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

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_SourceIPBrdCast_DestIPBrdcast1( void )
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
    pxIPHeader->ulDestinationIPAddress = xNetworkAddressing.ulBroadcastAddress;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_SourceIPBrdCast_DestIPLLMNR( void )
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

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_SourceIPBrdCast_NoLocalIP( void )
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

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_DestMACBrdCast_DestIPUnicast( void )
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

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_SrcMACBrdCast( void )
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

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_SrcMACBrdCast2( void )
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

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_SrcIPAddrIsMulticast( void )
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

    pxIPHeader->ulSourceIPAddress = FreeRTOS_htonl( 0xE0000000 + 1 );

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_IncorrectChecksum( void )
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

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC - 1 );

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_IncorrectProtocolChecksum( void )
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

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAndReturn( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE, ( uint16_t ) ( ipCORRECT_CRC + 1 ) );

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_HappyPath( void )
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

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAndReturn( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

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

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

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

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

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

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

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

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );

    vARPRefreshCacheEntry_ExpectAnyArgs();

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

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

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

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

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

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

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

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

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

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xProcessReceivedUDPPacket_ExpectAnyArgsAndReturn( pdFAIL );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
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

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xProcessReceivedUDPPacket_ExpectAndReturn( pxNetworkBuffer, pxUDPPacket->xUDPHeader.usDestinationPort, NULL, pdFAIL );
    xProcessReceivedUDPPacket_IgnoreArg_pxIsWaitingForARPResolution();
    xProcessReceivedUDPPacket_ReturnThruPtr_pxIsWaitingForARPResolution( &xReturnValue );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eWaitingARPResolution, eResult );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) - sizeof( UDPHeader_t ) + sizeof( UDPPacket_t ), pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->ulIPAddress, pxUDPPacket->xIPHeader.ulSourceIPAddress );
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

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xProcessReceivedUDPPacket_ExpectAndReturn( pxNetworkBuffer, pxUDPPacket->xUDPHeader.usDestinationPort, NULL, pdFAIL );
    xProcessReceivedUDPPacket_IgnoreArg_pxIsWaitingForARPResolution();
    xProcessReceivedUDPPacket_ReturnThruPtr_pxIsWaitingForARPResolution( &xReturnValue );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eWaitingARPResolution, eResult );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->ulIPAddress, pxUDPPacket->xIPHeader.ulSourceIPAddress );
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
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntry_Expect( &( pxIPPacket->xEthernetHeader.xSourceAddress ), pxIPHeader->ulSourceIPAddress );

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
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    usGenerateChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );

    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntry_Expect( &( pxIPPacket->xEthernetHeader.xSourceAddress ), pxIPHeader->ulSourceIPAddress );

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

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10;

    xNetworkInterfaceOutput_ExpectAndReturn( pxNetworkBuffer, xReleaseAfterSend, pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( ipLOCAL_MAC_ADDRESS, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
}

void test_vReturnEthernetFrame_DataLenMoreThanRequired( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;

    xNetworkInterfaceOutput_ExpectAndReturn( pxNetworkBuffer, xReleaseAfterSend, pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAA, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( ipLOCAL_MAC_ADDRESS, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
}

void test_FreeRTOS_GetIPAddress( void )
{
    uint32_t ulIPAddress;

    ulIPAddress = FreeRTOS_GetIPAddress();

    TEST_ASSERT_EQUAL( *ipLOCAL_IP_ADDRESS_POINTER, ulIPAddress );
}

void test_FreeRTOS_SetIPAddress( void )
{
    uint32_t ulIPAddress = 0x1234ABCD;

    FreeRTOS_SetIPAddress( ulIPAddress );

    TEST_ASSERT_EQUAL( ulIPAddress, *ipLOCAL_IP_ADDRESS_POINTER );
}

void test_FreeRTOS_GetGatewayAddress( void )
{
    uint32_t ulGatewayAddress;

    ulGatewayAddress = FreeRTOS_GetGatewayAddress();

    TEST_ASSERT_EQUAL( xNetworkAddressing.ulGatewayAddress, ulGatewayAddress );
}

void test_FreeRTOS_GetDNSServerAddress( void )
{
    uint32_t ulDNSServerAddress;

    ulDNSServerAddress = FreeRTOS_GetDNSServerAddress();

    TEST_ASSERT_EQUAL( xNetworkAddressing.ulDNSServerAddress, ulDNSServerAddress );
}

void test_FreeRTOS_GetNetmask( void )
{
    uint32_t ulNetmask;

    ulNetmask = FreeRTOS_GetNetmask();

    TEST_ASSERT_EQUAL( xNetworkAddressing.ulNetMask, ulNetmask );
}

void test_FreeRTOS_UpdateMACAddress( void )
{
    const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xFF, 0xFA, 0x12, 0xBC, 0x12, 0x33 };

    FreeRTOS_UpdateMACAddress( ucMACAddress );

    TEST_ASSERT_EQUAL_MEMORY( ucMACAddress, ipLOCAL_MAC_ADDRESS, ipMAC_ADDRESS_LENGTH_BYTES );
}

void test_FreeRTOS_GetMACAddress( void )
{
    const uint8_t * pucMACAddrPtr;

    pucMACAddrPtr = FreeRTOS_GetMACAddress();

    TEST_ASSERT_EQUAL_PTR( ipLOCAL_MAC_ADDRESS, pucMACAddrPtr );
}

void test_FreeRTOS_SetNetmask( void )
{
    uint32_t ulNetmask = 0xAB12BC23;

    FreeRTOS_SetNetmask( ulNetmask );

    TEST_ASSERT_EQUAL( ulNetmask, xNetworkAddressing.ulNetMask );
}

void test_FreeRTOS_SetGatewayAddress( void )
{
    uint32_t ulGatewayAddress = 0x1234ABCD;

    FreeRTOS_SetGatewayAddress( ulGatewayAddress );

    TEST_ASSERT_EQUAL( ulGatewayAddress, xNetworkAddressing.ulGatewayAddress );
}

void test_FreeRTOS_IsNetworkUp( void )
{
    BaseType_t xReturn;

    xNetworkUp = pdTRUE;
    xReturn = FreeRTOS_IsNetworkUp();
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );

    xNetworkUp = pdFALSE;
    xReturn = FreeRTOS_IsNetworkUp();
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
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
