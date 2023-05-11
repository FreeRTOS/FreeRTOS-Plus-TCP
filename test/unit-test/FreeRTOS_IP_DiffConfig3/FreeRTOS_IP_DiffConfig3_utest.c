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
#include "mock_IP_DiffConfig_list_macros.h"
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
#include "mock_FreeRTOS_DHCPv6.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_IPv4.h"

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

void test_prvProcessIPEventsAndTimers_eDHCPEvent_DHCPv4( void )
{
    IPStackEvent_t xReceivedEvent;
    uint32_t ulDHCPEvent = 0x1234;
    NetworkEndPoint_t xEndPoints, * pxEndPoints = &xEndPoints;
    BaseType_t xQueueReturn = 100;

    memset( pxEndPoints, 0, sizeof( NetworkEndPoint_t ) );
    pxEndPoints->bits.bWantDHCP = pdTRUE_UNSIGNED;

    xReceivedEvent.eEventType = eDHCPEvent;
    xReceivedEvent.pvData = pxEndPoints;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    vDHCPProcess_Expect( pdFALSE, pxEndPoints );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eDHCPEvent_DHCPv6( void )
{
    IPStackEvent_t xReceivedEvent;
    uint32_t ulDHCPEvent = 0x1234;
    NetworkEndPoint_t xEndPoints, * pxEndPoints = &xEndPoints;
    BaseType_t xQueueReturn = 100;

    memset( pxEndPoints, 0, sizeof( NetworkEndPoint_t ) );
    pxEndPoints->bits.bWantDHCP = pdTRUE_UNSIGNED;
    pxEndPoints->bits.bIPv6 = pdTRUE_UNSIGNED;

    xReceivedEvent.eEventType = eDHCPEvent;
    xReceivedEvent.pvData = pxEndPoints;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    vDHCPv6Process_Expect( pdFALSE, pxEndPoints );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eDHCPEvent_RA( void )
{
    IPStackEvent_t xReceivedEvent;
    uint32_t ulDHCPEvent = 0x1234;
    NetworkEndPoint_t xEndPoints, * pxEndPoints = &xEndPoints;
    BaseType_t xQueueReturn = 100;

    memset( pxEndPoints, 0, sizeof( NetworkEndPoint_t ) );
    pxEndPoints->bits.bWantRA = pdTRUE_UNSIGNED;
    pxEndPoints->bits.bIPv6 = pdTRUE_UNSIGNED;

    xReceivedEvent.eEventType = eDHCPEvent;
    xReceivedEvent.pvData = pxEndPoints;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    vRAProcess_Expect( pdFALSE, pxEndPoints );

    prvProcessIPEventsAndTimers();
}
