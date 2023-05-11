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
#include "FreeRTOSIPConfig.h"

#include "mock_IP_DiffConfig1_list_macros.h"
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
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_IPv4_Private.h"
#include "mock_FreeRTOS_ND.h"
#include "mock_FreeRTOS_IPv4.h"

#include "FreeRTOS_IP.h"

#include "FreeRTOS_IP_DiffConfig1_stubs.c"
#include "catch_assert.h"

extern NetworkInterface_t xInterfaces[ 1 ];

void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer );
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

static BaseType_t NetworkInterfaceOutputFunction_Stub_Called = 0;

static BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                       NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                       BaseType_t xReleaseAfterSend )
{
    NetworkInterfaceOutputFunction_Stub_Called++;
    return 0;
}

extern BaseType_t xIPTaskInitialised;
extern BaseType_t xNetworkDownEventPending;

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
    NetworkEndPoint_t xFirstEndPoint = { 0 }, * pxFirstEndPoint = &xFirstEndPoint;

    pxFillInterfaceDescriptor_IgnoreAndReturn( pdTRUE );
    FreeRTOS_FillEndPoint_Ignore();

    FreeRTOS_FirstNetworkInterface_IgnoreAndReturn( pdTRUE );

    vPreCheckConfigs_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xQueueGenericCreateStatic_ExpectAnyArgsAndReturn( ( QueueHandle_t ) 0x1234ABCD );
    #else
        xQueueGenericCreate_ExpectAnyArgsAndReturn( ( QueueHandle_t ) 0x1234ABCD );
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
    NetworkEndPoint_t xFirstEndPoint = { 0 };


    /* Set the local IP to something other than 0. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD;

    FreeRTOS_FillEndPoint_Ignore();
    FreeRTOS_FirstNetworkInterface_IgnoreAndReturn( pdTRUE );
    pxFillInterfaceDescriptor_IgnoreAndReturn( pdTRUE );

    vPreCheckConfigs_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xQueueGenericCreateStatic_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), NULL, NULL, 0, ulPointerToQueue );
        xQueueGenericCreateStatic_IgnoreArg_pucQueueStorage();
        xQueueGenericCreateStatic_IgnoreArg_pxStaticQueue();
    #else
        xQueueGenericCreate_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), 0, ulPointerToQueue );
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
    NetworkEndPoint_t xFirstEndPoint = { 0 };

    /* Set the local IP to something other than 0. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD;

    FreeRTOS_FillEndPoint_Ignore();
    FreeRTOS_FirstNetworkInterface_IgnoreAndReturn( pdTRUE );
    pxFillInterfaceDescriptor_IgnoreAndReturn( pdTRUE );

    /* Clear default values. */
    memset( ipLOCAL_MAC_ADDRESS, 0, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

    vPreCheckConfigs_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xQueueGenericCreateStatic_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), NULL, NULL, 0, pxPointerToQueue );
        xQueueGenericCreateStatic_IgnoreArg_pucQueueStorage();
        xQueueGenericCreateStatic_IgnoreArg_pxStaticQueue();
    #else
        xQueueGenericCreate_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), 0, pxPointerToQueue );
    #endif /* configSUPPORT_STATIC_ALLOCATION */

    xReturn = FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
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
    NetworkEndPoint_t xFirstEndPoint = { 0 };

    /* Set the local IP to something other than 0. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD;

    FreeRTOS_FillEndPoint_Ignore();
    FreeRTOS_FirstNetworkInterface_IgnoreAndReturn( pdTRUE );
    pxFillInterfaceDescriptor_IgnoreAndReturn( pdTRUE );

    /* Clear default values. */
    memset( ipLOCAL_MAC_ADDRESS, 0, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

    vPreCheckConfigs_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xQueueGenericCreateStatic_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), NULL, NULL, 0, pxPointerToQueue );
        xQueueGenericCreateStatic_IgnoreArg_pucQueueStorage();
        xQueueGenericCreateStatic_IgnoreArg_pxStaticQueue();
    #else
        xQueueGenericCreate_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), 0, pxPointerToQueue );
    #endif /* configSUPPORT_STATIC_ALLOCATION */

    #if ( configQUEUE_REGISTRY_SIZE > 0 )
        vQueueAddToRegistry_Expect( pxPointerToQueue, "NetEvnt" );
    #endif

    xNetworkBuffersInitialise_ExpectAndReturn( pdFAIL );

    vQueueDelete_Expect( pxPointerToQueue );

    xReturn = FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
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
    NetworkEndPoint_t xFirstEndPoint = { 0 };

    /* Set the local IP to something other than 0. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD;

    FreeRTOS_FillEndPoint_Ignore();
    FreeRTOS_FirstNetworkInterface_IgnoreAndReturn( pdTRUE );
    pxFillInterfaceDescriptor_IgnoreAndReturn( pdTRUE );

    /* Clear default values. */
    memset( ipLOCAL_MAC_ADDRESS, 0, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

    vPreCheckConfigs_Expect();

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        xQueueGenericCreateStatic_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), NULL, NULL, 0, pxPointerToQueue );
        xQueueGenericCreateStatic_IgnoreArg_pucQueueStorage();
        xQueueGenericCreateStatic_IgnoreArg_pxStaticQueue();
    #else
        xQueueGenericCreate_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), 0, pxPointerToQueue );
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
    TEST_ASSERT_EQUAL( NULL, FreeRTOS_GetIPTaskHandle() );
}

void test_prvProcessIPEventsAndTimers_eSocketBindEvent_IPv4_only_but_IPv6_bind( void )
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
}

void test_vIPNetworkUpCalls_BackwardCompatible( void )
{
    NetworkEndPoint_t xEndPoint = { 0 };

    vApplicationIPNetworkEventHook_Expect( eNetworkUp );
    vDNSInitialise_Expect();
    vARPTimerReload_Expect( pdMS_TO_TICKS( 10000 ) );

    vIPNetworkUpCalls( &xEndPoint );

    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xEndPoint.bits.bEndPointUp );
}

void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeEqualToConfigBackwardCompatible( void )
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

void test_FreeRTOS_GetAddressConfiguration_HappyPath( void )
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

    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, &xEndPoint );
    FreeRTOS_GetAddressConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress );
    TEST_ASSERT_EQUAL( 1, ulIPAddress );
    TEST_ASSERT_EQUAL( 2, ulNetMask );
    TEST_ASSERT_EQUAL( 3, ulGatewayAddress );
    TEST_ASSERT_EQUAL( 4, ulDNSServerAddress );
}

void test_FreeRTOS_GetAddressConfiguration_NoEndpoint( void )
{
    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, NULL );
    FreeRTOS_GetAddressConfiguration( NULL, NULL, NULL, NULL );
}

void test_FreeRTOS_SetAddressConfiguration_HappyPath( void )
{
    uint32_t ulIPAddress = 1;
    uint32_t ulNetMask = 2;
    uint32_t ulGatewayAddress = 3;
    uint32_t ulDNSServerAddress = 4;
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xEndPoint.ipv4_settings.ulIPAddress = 1;
    xEndPoint.ipv4_settings.ulNetMask = 2;
    xEndPoint.ipv4_settings.ulGatewayAddress = 3;

    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, &xEndPoint );
    FreeRTOS_SetAddressConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress );
    TEST_ASSERT_EQUAL( 1, xEndPoint.ipv4_settings.ulIPAddress );
    TEST_ASSERT_EQUAL( 2, xEndPoint.ipv4_settings.ulNetMask );
    TEST_ASSERT_EQUAL( 3, xEndPoint.ipv4_settings.ulGatewayAddress );
    TEST_ASSERT_EQUAL( 4, xEndPoint.ipv4_settings.ulDNSServerAddresses[0] );
}

void test_FreeRTOS_SetAddressConfiguration_NoEndpoint( void )
{
    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, NULL );
    FreeRTOS_SetAddressConfiguration( NULL, NULL, NULL, NULL );
}

void test_FreeRTOS_SetIPAddress_ValidEndpoint( void )
{
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;
    uint32_t ulIPAddress = 0x00ABCDEFU;

    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );
    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, pxEndpoint );

    FreeRTOS_SetIPAddress( ulIPAddress );
    TEST_ASSERT_EQUAL( ulIPAddress, pxEndpoint->ipv4_settings.ulIPAddress );
}

void test_FreeRTOS_SetIPAddress_NullEndpoint( void )
{
    uint32_t ulIPAddress = 0x00ABCDEFU;

    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, NULL );

    FreeRTOS_SetIPAddress( ulIPAddress );
}

void test_FreeRTOS_GetGatewayAddress_ValidEndpoint( void )
{
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;
    uint32_t ulIPAddress = 0U;

    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );
    pxEndpoint->ipv4_settings.ulGatewayAddress = 0x00ABCDEF;
    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, pxEndpoint );

    ulIPAddress = FreeRTOS_GetGatewayAddress();
    TEST_ASSERT_EQUAL( pxEndpoint->ipv4_settings.ulGatewayAddress, ulIPAddress );
}

void test_FreeRTOS_GetGatewayAddress_NullEndpoint( void )
{
    uint32_t ulIPAddress = 0U;

    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, NULL );

    ulIPAddress = FreeRTOS_GetGatewayAddress();
    TEST_ASSERT_EQUAL( 0U, ulIPAddress );
}

void test_FreeRTOS_GetDNSServerAddress_ValidEndpoint( void )
{
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;
    uint32_t ulIPAddress = 0U;

    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );
    pxEndpoint->ipv4_settings.ulDNSServerAddresses[0] = 0x00ABCDEF;
    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, pxEndpoint );

    ulIPAddress = FreeRTOS_GetDNSServerAddress();
    TEST_ASSERT_EQUAL( pxEndpoint->ipv4_settings.ulDNSServerAddresses[0], ulIPAddress );
}

void test_FreeRTOS_GetDNSServerAddress_NullEndpoint( void )
{
    uint32_t ulIPAddress = 0U;

    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, NULL );

    ulIPAddress = FreeRTOS_GetDNSServerAddress();
    TEST_ASSERT_EQUAL( 0U, ulIPAddress );
}

void test_FreeRTOS_GetNetmask_ValidEndpoint( void )
{
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;
    uint32_t ulIPAddress = 0U;

    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );
    pxEndpoint->ipv4_settings.ulNetMask = 0x00ABCDEF;
    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, pxEndpoint );

    ulIPAddress = FreeRTOS_GetNetmask();
    TEST_ASSERT_EQUAL( pxEndpoint->ipv4_settings.ulNetMask, ulIPAddress );
}

void test_FreeRTOS_GetNetmask_NullEndpoint( void )
{
    uint32_t ulIPAddress = 0U;

    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, NULL );

    ulIPAddress = FreeRTOS_GetNetmask();
    TEST_ASSERT_EQUAL( 0U, ulIPAddress );
}

