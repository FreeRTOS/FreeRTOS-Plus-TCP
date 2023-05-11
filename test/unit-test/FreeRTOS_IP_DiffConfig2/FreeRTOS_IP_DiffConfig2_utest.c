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
#include "mock_IP_DiffConfig2_list_macros.h"
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

#include "FreeRTOS_IP.h"

/*#include "FreeRTOS_IP_stubs.c" */
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer );
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

extern BaseType_t xIPTaskInitialised;
extern BaseType_t xNetworkDownEventPending;
extern BaseType_t xNetworkUp;
extern UBaseType_t uxQueueMinimumSpace;

BaseType_t NetworkInterfaceOutputFunction_Stub_Called = 0;
BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
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


TaskHandle_t IPInItHappyPath_xTaskHandleToSet = ( TaskHandle_t ) 0xCDBA9087;
static BaseType_t StubxTaskCreate( TaskFunction_t pxTaskCode,
                                   const char * const pcName, /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
                                   const configSTACK_DEPTH_TYPE usStackDepth,
                                   void * const pvParameters,
                                   UBaseType_t uxPriority,
                                   TaskHandle_t * const pxCreatedTask )
{
    *pxCreatedTask = IPInItHappyPath_xTaskHandleToSet;
    return pdPASS;
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

    NetworkEndPoint_t xEndPoints = { 0 }, * xFirstEndPoint = &xEndPoints;

    /* Set the local IP to something other than 0. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD;

    /* Clear default values. */
    memset( &xDefaultAddressing, 0, sizeof( xDefaultAddressing ) );
    memset( xFirstEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    FreeRTOS_FillEndPoint_Ignore();
    FreeRTOS_FirstNetworkInterface_IgnoreAndReturn( pdTRUE );
    pxFillInterfaceDescriptor_IgnoreAndReturn( pdTRUE );

    vPreCheckConfigs_Expect();

    xQueueGenericCreate_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), 0U, ulPointerToQueue );

    #if ( configQUEUE_REGISTRY_SIZE > 0 )
        vQueueAddToRegistry_Expect( ulPointerToQueue, "NetEvnt" );
    #endif

    xNetworkBuffersInitialise_ExpectAndReturn( pdPASS );

    vNetworkSocketsInit_Expect();

    xTaskCreate_Stub( StubxTaskCreate );

    xReturn = FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    /*TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucIPAddress[ 0 ], ucIPAddress[ 1 ], ucIPAddress[ 2 ], ucIPAddress[ 3 ] ), xIPv4Addressing->ulIPAddress ); */
    /*TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucNetMask[ 0 ], ucNetMask[ 1 ], ucNetMask[ 2 ], ucNetMask[ 3 ] ), xIPv4Addressing->ulNetMask ); */
    /*TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucGatewayAddress[ 0 ], ucGatewayAddress[ 1 ], ucGatewayAddress[ 2 ], ucGatewayAddress[ 3 ] ), xIPv4Addressing->ulGatewayAddress ); */
    /*TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucDNSServerAddress[ 0 ], ucDNSServerAddress[ 1 ], ucDNSServerAddress[ 2 ], ucDNSServerAddress[ 3 ] ), xIPv4Addressing->ulDNSServerAddresses[ 0 ] ); */
    /*TEST_ASSERT_EQUAL( ( ( xIPv4Addressing->ulIPAddress & xIPv4Addressing->ulNetMask ) | ~xIPv4Addressing->ulNetMask ), xIPv4Addressing->ulBroadcastAddress ); */
    /* TEST_ASSERT_EQUAL_MEMORY( &xDefaultAddressing, &xNetworkAddressing, sizeof( xDefaultAddressing ) ); TODO: verify if xNetworkAddressing is used */
    /*TEST_ASSERT_EQUAL( 0, *ipLOCAL_IP_ADDRESS_POINTER ); */
    /*TEST_ASSERT_EQUAL_MEMORY( ucMACAddress, ipLOCAL_MAC_ADDRESS, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES ); */
    TEST_ASSERT_EQUAL( IPInItHappyPath_xTaskHandleToSet, FreeRTOS_GetIPTaskHandle() );
}
