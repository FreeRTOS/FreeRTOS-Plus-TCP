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

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_IP_Timers_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Utils.h"
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
#include "mock_FreeRTOS_DNS_Callback.h"

#include "FreeRTOS_IP_Timers.h"

#include "FreeRTOS_IP_Timers_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

extern IPTimer_t xARPTimer;
#if ( ipconfigUSE_DHCP != 0 )
    /** @brief DHCP timer, to send requests and to renew a reservation.  */
    extern IPTimer_t xDHCPTimer;
#endif
#if ( ipconfigUSE_TCP != 0 )
    /** @brief TCP timer, to check for timeouts, resends. */
    extern IPTimer_t xTCPTimer;
#endif
#if ( ipconfigDNS_USE_CALLBACKS != 0 )
    /** @brief DNS timer, to check for timeouts when looking-up a domain. */
    extern IPTimer_t xDNSTimer;
#endif

#if ( ipconfigUSE_TCP != 0 )

/** @brief Set to a non-zero value if one or more TCP message have been processed
 *           within the last round. */
    extern BaseType_t xProcessedTCPMessage;
#endif

extern IPTimer_t xARPResolutionTimer;

void test_xCalculateSleepTime_AllTimersInactive( void )
{
    TickType_t uxTicks;

    xARPTimer.bActive = pdFALSE;
    xDHCPTimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME, uxTicks );
}

void test_xCalculateSleepTime_AllTimersActive_AllTimesGreater( void )
{
    TickType_t uxTicks;

    xARPTimer.bActive = pdTRUE;
    xDHCPTimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdTRUE;

    xARPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xDHCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xTCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xDNSTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME, uxTicks );
}

void test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptOne( void )
{
    TickType_t uxTicks;

    xARPTimer.bActive = pdTRUE;
    xDHCPTimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdTRUE;

    xARPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME - 10;
    xDHCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xTCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xDNSTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME - 10, uxTicks );
}

void test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptOne1( void )
{
    TickType_t uxTicks;

    xARPTimer.bActive = pdTRUE;
    xDHCPTimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdTRUE;

    xARPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xDHCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME - 10;
    xTCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xDNSTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME - 10, uxTicks );
}

void test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptOne2( void )
{
    TickType_t uxTicks;

    xARPTimer.bActive = pdTRUE;
    xDHCPTimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdTRUE;

    xARPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xDHCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xTCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME - 10;
    xDNSTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME - 10, uxTicks );
}

void test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptOne3( void )
{
    TickType_t uxTicks;

    xARPTimer.bActive = pdTRUE;
    xDHCPTimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdTRUE;

    xARPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xDHCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xTCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xDNSTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME - 10;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME - 10, uxTicks );
}

void test_vCheckNetworkTimers_AllTimersDisabled( void )
{
    xARPTimer.bActive = pdFALSE;
    xDHCPTimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

void test_vCheckNetworkTimers_ARPTimerActiveAndExpired( void )
{
    xARPTimer.bActive = pdTRUE;
    xDHCPTimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;

    xARPTimer.bExpired = pdTRUE;

    vTaskSetTimeOutState_Expect( &( xARPTimer.xTimeOut ) );

    xSendEventToIPTask_ExpectAndReturn( eARPTimerEvent, pdTRUE );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

void test_vCheckNetworkTimers_ARPResolutionTimerActiveAndExpired( void )
{
    xARPTimer.bActive = pdFALSE;
    xDHCPTimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdTRUE;

    xARPResolutionTimer.bExpired = pdTRUE;

    pxARPWaitingNetworkBuffer = NULL;

    vTaskSetTimeOutState_Expect( &( xARPResolutionTimer.xTimeOut ) );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

void test_vCheckNetworkTimers_ARPResolutionTimerActiveAndExpired2( void )
{
    xARPTimer.bActive = pdFALSE;
    xDHCPTimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdTRUE;

    xARPResolutionTimer.bExpired = pdTRUE;

    pxARPWaitingNetworkBuffer = ( NetworkBufferDescriptor_t * ) 0x1234ABCD;

    vTaskSetTimeOutState_Expect( &( xARPResolutionTimer.xTimeOut ) );

    vReleaseNetworkBufferAndDescriptor_Expect( pxARPWaitingNetworkBuffer );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();

    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xARPResolutionTimer.bActive );
    TEST_ASSERT_EQUAL_PTR( NULL, pxARPWaitingNetworkBuffer );
}

void test_vCheckNetworkTimers_DHCPTimerActiveAndExpired( void )
{
    xARPTimer.bActive = pdFALSE;
    xDHCPTimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdFALSE;

    xDHCPTimer.bExpired = pdTRUE;

    vTaskSetTimeOutState_Expect( &( xDHCPTimer.xTimeOut ) );

    xSendDHCPEvent_ExpectAndReturn( pdTRUE );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

void test_vCheckNetworkTimers_DNSTimerActiveAndExpired( void )
{
    xARPTimer.bActive = pdFALSE;
    xDHCPTimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdFALSE;

    xDNSTimer.bExpired = pdTRUE;

    vTaskSetTimeOutState_Expect( &( xDHCPTimer.xTimeOut ) );

    vDNSCheckCallBack_Expect( NULL );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

void test_vCheckNetworkTimers_AllTimersInactive_1( void )
{
    xARPTimer.bActive = pdFALSE;
    xDHCPTimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdFALSE;

    xProcessedTCPMessage = pdTRUE;

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

void test_vCheckNetworkTimers_AllTimersInactive_2( void )
{
    xARPTimer.bActive = pdFALSE;
    xDHCPTimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdFALSE;

    xProcessedTCPMessage = pdTRUE;

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdFALSE );

    xTCPTimerCheck_ExpectAndReturn( pdTRUE, 0x123 );

    vTaskSetTimeOutState_Expect( &( xTCPTimer.xTimeOut ) );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();

    TEST_ASSERT_EQUAL( 0, xProcessedTCPMessage );
    TEST_ASSERT_EQUAL( 0x123, xTCPTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xTCPTimer.bExpired );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xTCPTimer.bActive );
}

void test_prvIPTimerStart_NonZeroTime( void )
{
    IPTimer_t xTimer;
    TickType_t xTime = 0xABCD;

    vTaskSetTimeOutState_Expect( &xTimer.xTimeOut );

    prvIPTimerStart( &xTimer, xTime );

    TEST_ASSERT_EQUAL( xTime, xTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xTimer.bExpired );
}

void test_prvIPTimerStart_ZeroTime( void )
{
    IPTimer_t xTimer;
    TickType_t xTime = 0x00;

    vTaskSetTimeOutState_Expect( &xTimer.xTimeOut );

    prvIPTimerStart( &xTimer, xTime );

    TEST_ASSERT_EQUAL( xTime, xTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xTimer.bActive );
    TEST_ASSERT_EQUAL( pdTRUE, xTimer.bExpired );
}

void test_vIPTimerStartARPResolution( void )
{
    TickType_t xTime = 0x00;

    vTaskSetTimeOutState_Expect( &xARPResolutionTimer.xTimeOut );

    vIPTimerStartARPResolution( xTime );

    TEST_ASSERT_EQUAL( xTime, xARPResolutionTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xARPResolutionTimer.bActive );
    TEST_ASSERT_EQUAL( pdTRUE, xARPResolutionTimer.bExpired );
}

void test_vTCPTimerReload( void )
{
    TickType_t xTime = 0x12A;

    vTaskSetTimeOutState_Expect( &xTCPTimer.xTimeOut );

    vTCPTimerReload( xTime );

    TEST_ASSERT_EQUAL( 0x12A, xTCPTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( xTime, xTCPTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xTCPTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xTCPTimer.bExpired );
}

void test_vARPTimerReload( void )
{
    TickType_t xTime = 0x12A;

    vTaskSetTimeOutState_Expect( &xARPTimer.xTimeOut );

    vARPTimerReload( xTime );

    TEST_ASSERT_EQUAL( 0x12A, xARPTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( xTime, xARPTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xARPTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xARPTimer.bExpired );
}

void test_vDHCPTimerReload( void )
{
    TickType_t xTime = 0x12A;

    vTaskSetTimeOutState_Expect( &xDHCPTimer.xTimeOut );

    vDHCPTimerReload( xTime );

    TEST_ASSERT_EQUAL( 0x12A, xDHCPTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( xTime, xDHCPTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xDHCPTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xDHCPTimer.bExpired );
}

void test_vDNSTimerReload( void )
{
    TickType_t xTime = 0x12A;

    vTaskSetTimeOutState_Expect( &xDNSTimer.xTimeOut );

    vDNSTimerReload( xTime );

    TEST_ASSERT_EQUAL( 0x12A, xDNSTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( xTime, xDNSTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xDNSTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xDNSTimer.bExpired );
}

void test_prvIPTimerCheck_TimerDisabled( void )
{
    BaseType_t xResult;
    IPTimer_t xTimer;

    xTimer.bActive = pdFALSE;

    xResult = prvIPTimerCheck( &xTimer );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

void test_prvIPTimerCheck_TimerExpired( void )
{
    BaseType_t xResult;
    IPTimer_t xTimer;

    xTimer.bActive = pdTRUE;
    xTimer.bExpired = pdTRUE;
    xTimer.ulReloadTime = 0xAA;

    vTaskSetTimeOutState_Expect( &xTimer.xTimeOut );

    xResult = prvIPTimerCheck( &xTimer );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    TEST_ASSERT_EQUAL( 0xAA, xTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( 0xAA, xTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xTimer.bExpired );
}

void test_prvIPTimerCheck_TimerNotExpired( void )
{
    BaseType_t xResult;
    IPTimer_t xTimer;

    xTimer.bActive = pdTRUE;
    xTimer.bExpired = pdFALSE;
    xTimer.ulReloadTime = 0xAA;

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xResult = prvIPTimerCheck( &xTimer );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

void test_prvIPTimerCheck_TimerNotExpired1( void )
{
    BaseType_t xResult;
    IPTimer_t xTimer;

    xTimer.bActive = pdTRUE;
    xTimer.bExpired = pdFALSE;
    xTimer.ulReloadTime = 0xAA;

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    vTaskSetTimeOutState_Expect( &xTimer.xTimeOut );

    xResult = prvIPTimerCheck( &xTimer );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    TEST_ASSERT_EQUAL( 0xAA, xTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( 0xAA, xTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xTimer.bExpired );
}

void test_vIPSetTCPTimerExpiredState_False( void )
{
    BaseType_t xExpiredState = pdFALSE;

    vIPSetTCPTimerExpiredState( xExpiredState );

    TEST_ASSERT_EQUAL( xExpiredState, xTCPTimer.bExpired );
}

void test_vIPSetTCPTimerExpiredState_True( void )
{
    BaseType_t xExpiredState = pdTRUE;

    vIPSetTCPTimerExpiredState( xExpiredState );

    TEST_ASSERT_EQUAL( xExpiredState, xTCPTimer.bExpired );
}

void test_vIPSetARPTimerEnableState_False( void )
{
    BaseType_t xEnableState = pdFALSE;

    vIPSetARPTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xARPTimer.bActive );
}

void test_vIPSetARPTimerEnableState_True( void )
{
    BaseType_t xEnableState = pdTRUE;

    vIPSetARPTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xARPTimer.bActive );
}

void test_vIPSetARPResolutionTimerEnableState_False( void )
{
    BaseType_t xEnableState = pdFALSE;

    vIPSetARPResolutionTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xARPResolutionTimer.bActive );
}

void test_vIPSetARPResolutionTimerEnableState_True( void )
{
    BaseType_t xEnableState = pdTRUE;

    vIPSetARPResolutionTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xARPResolutionTimer.bActive );
}

void test_vIPSetDHCPTimerEnableState_False( void )
{
    BaseType_t xEnableState = pdFALSE;

    vIPSetDHCPTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xDHCPTimer.bActive );
}

void test_vIPSetDHCPTimerEnableState_True( void )
{
    BaseType_t xEnableState = pdTRUE;

    vIPSetDHCPTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xDHCPTimer.bActive );
}

void test_vIPSetDNSTimerEnableState_False( void )
{
    BaseType_t xEnableState = pdFALSE;

    vIPSetDNSTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xDNSTimer.bActive );
}

void test_vIPSetDNSTimerEnableState_True( void )
{
    BaseType_t xEnableState = pdTRUE;

    vIPSetDNSTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xDNSTimer.bActive );
}
