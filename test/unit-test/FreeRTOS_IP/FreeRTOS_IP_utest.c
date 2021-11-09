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
#include "mock_IP_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_TCP_IP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"

#include "FreeRTOS_IP.h"

#include "FreeRTOS_IP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );

extern BaseType_t xIPTaskInitialised;
extern BaseType_t xNetworkDownEventPending;
extern BaseType_t xNetworkUp;


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
    vReleaseNetworkBufferAndDescriptor_Expect( 0x12123434 );

    FreeRTOS_ReleaseUDPPayloadBuffer( pvBuffer );
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
    
    /* No event received. */
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
    
    /* No event received. */
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
    
    /* No event received. */
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );
    
    prvProcessIPEventsAndTimers();
}

void test_FreeRTOS_SendPingRequest_HappyPath( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    /* 32 byte ping to send. */
    size_t uxNumberOfBytesToSend = 32;

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigNETWORK_MTU - ( sizeof( IPHeader_t ) + sizeof( ICMPHeader_t ) ) ];

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;

    /* At least 4 free network buffers must be there to send a ping. */
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNumberOfBytesToSend + sizeof( ICMPPacket_t ), uxBlockTimeTicks, pxNetworkBuffer );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );
}











































