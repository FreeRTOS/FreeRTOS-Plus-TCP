/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_task.h"
#include "mock_queue.h"
#include "mock_semphr.h"

#include "mock_list.h"
#include "mock_TimerWork_list_macros.h"

#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_Stream_Buffer.h"

/* Private includes. */
#include "mock_FreeRTOS_TCP_IP_Reception.h"
#include "mock_FreeRTOS_TCP_IP_utils.h"
#include "mock_FreeRTOS_TCP_IP.h"
#include "mock_FreeRTOS_TCP_IP_StateHandling.h"
#include "mock_NetworkBufferManagement.h"

#include "mock_FreeRTOS_IP_Private.h"

#include "FreeRTOS_TCP_IP_TimerWork.h"

#include "FreeRTOS_TCP_IP_TimerWork_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

void test_prvTCPNextTimeout_AllZero( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    TickType_t uxReturn;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( 0 );

    uxReturn = prvTCPNextTimeout( pxSocket );

    TEST_ASSERT_EQUAL( ipMS_TO_MIN_TICKS( tcpMAXIMUM_TCP_WAKEUP_TIME_MS ), uxReturn );
    TEST_ASSERT_EQUAL( ipMS_TO_MIN_TICKS( tcpMAXIMUM_TCP_WAKEUP_TIME_MS ), pxSocket->u.xTCP.usTimeout );
}

void test_prvTCPNextTimeout_NonZeroTimeout( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    TickType_t uxReturn;
    uint16_t usTimeout = 0x123;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.usTimeout = usTimeout;

    uxReturn = prvTCPNextTimeout( pxSocket );

    TEST_ASSERT_EQUAL( usTimeout, uxReturn );
    TEST_ASSERT_EQUAL( usTimeout, pxSocket->u.xTCP.usTimeout );
}

void test_prvTCPNextTimeout_SYNState( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    TickType_t uxReturn;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;

    uxReturn = prvTCPNextTimeout( pxSocket );

    TEST_ASSERT_EQUAL( ipMS_TO_MIN_TICKS( 500 ), uxReturn );
    TEST_ASSERT_EQUAL( ipMS_TO_MIN_TICKS( 500 ), pxSocket->u.xTCP.usTimeout );
}

void test_prvTCPNextTimeout_SYNState_SockConn( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    TickType_t uxReturn;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;

    uxReturn = prvTCPNextTimeout( pxSocket );

    TEST_ASSERT_EQUAL( ipMS_TO_MIN_TICKS( 0 ), uxReturn );
    TEST_ASSERT_EQUAL( ipMS_TO_MIN_TICKS( 0 ), pxSocket->u.xTCP.usTimeout );
}

void test_prvTCPNextTimeout_SYNState_SockConn_RepCountMore( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    TickType_t uxReturn;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    pxSocket->u.xTCP.ucRepCount = 3;

    uxReturn = prvTCPNextTimeout( pxSocket );

    TEST_ASSERT_EQUAL( ipMS_TO_MIN_TICKS( 11000 ), uxReturn );
    TEST_ASSERT_EQUAL( ipMS_TO_MIN_TICKS( 11000 ), pxSocket->u.xTCP.usTimeout );
}

void test_prvTCPStatusAgeCheck_AllConnectedStates( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    BaseType_t xResult;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    /* Established can last forever with keep-alive messages */
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    xResult = prvTCPStatusAgeCheck( pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );

    /* Closed can last forever too. */
    pxSocket->u.xTCP.ucTCPState = eCLOSED;
    xResult = prvTCPStatusAgeCheck( pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );

    /* Server may listen forever. */
    pxSocket->u.xTCP.ucTCPState = eTCP_LISTEN;
    xResult = prvTCPStatusAgeCheck( pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );

    /* Waiting for close, up the the user. */
    pxSocket->u.xTCP.ucTCPState = eCLOSE_WAIT;
    xResult = prvTCPStatusAgeCheck( pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

void test_prvTCPStatusAgeCheck_eCONNECT_SYN( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    BaseType_t xResult;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;

    xTaskGetTickCount_ExpectAndReturn( 0 );

    xResult = prvTCPStatusAgeCheck( pxSocket );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

void test_prvTCPStatusAgeCheck_eCONNECT_SYN_AgeIsOverflowing( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    BaseType_t xResult;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;

    xTaskGetTickCount_ExpectAndReturn( ipconfigTCP_HANG_PROTECTION_TIME * ( TickType_t ) configTICK_RATE_HZ + 1 );

    vTCPStateChange_Expect( pxSocket, eCLOSE_WAIT );

    xResult = prvTCPStatusAgeCheck( pxSocket );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

void test_prvTCPStatusAgeCheck_eCONNECT_SYN_AgeIsOverflowing_SocketNotYetOwnedByApp( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    BaseType_t xResult;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;

    xTaskGetTickCount_ExpectAndReturn( ipconfigTCP_HANG_PROTECTION_TIME * ( TickType_t ) configTICK_RATE_HZ + 1 );

    vTCPStateChange_Expect( pxSocket, eCLOSE_WAIT );

    pxSocket->u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;

    xResult = prvTCPStatusAgeCheck( pxSocket );
    TEST_ASSERT_EQUAL( -1, xResult );
}

void test_prvTCPSendPacket_AllZeroedOut( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    int32_t lResult, lReturn = 0x123AB;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    prvTCPSendRepeated_ExpectAnyArgsAndReturn( lReturn );

    lResult = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( lReturn, lResult );
}

void test_prvTCPSendPacket_FunctionSendsPacket( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    int32_t lResult, lReturn = 0x123AB;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxNetworkBuffer = &xLocalNetworkBuffer;

    prvTCPSendRepeated_ExpectAndReturn( pxSocket, NULL, lReturn );
    prvTCPSendRepeated_IgnoreArg_ppxNetworkBuffer();
    /* Return a non-NULL value. */
    prvTCPSendRepeated_ReturnThruPtr_ppxNetworkBuffer( &pxNetworkBuffer );

    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    lResult = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( lReturn, lResult );
}

void test_prvTCPSendPacket_ConnectSynState( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    int32_t lResult, lReturn = 0x123AB;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 0 );

    lResult = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( 0, lResult );
}

void test_prvTCPSendPacket_ConnectSynState_RepCountGT3( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    int32_t lResult, lReturn = 0x123AB;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;

    pxSocket->u.xTCP.ucRepCount = 3;

    vTCPStateChange_Expect( pxSocket, eCLOSE_WAIT );

    lResult = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( 0, lResult );
}

void test_prvTCPSendPacket_ConnectSynState_ConnPrepedTrue( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    int32_t lResult, lReturn = 0x123AB;
    uint32_t uxOptionsLength = 0x12ABF;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;

    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;

    prvSetSynAckOptions_ExpectAnyArgsAndReturn( uxOptionsLength );
    prvTCPReturnPacket_ExpectAnyArgs();

    lResult = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lResult );
}

void test_prvTCPSendPacket_ConnectSynState_RNGSuccess( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    int32_t lResult, lReturn = 0x123AB;
    uint32_t uxOptionsLength = 0x12ABF;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 11 );

    prvSocketSetMSS_Expect( pxSocket );

    prvTCPCreateWindow_Expect( pxSocket );

    prvSetSynAckOptions_ExpectAnyArgsAndReturn( uxOptionsLength );
    prvTCPReturnPacket_ExpectAnyArgs();

    lResult = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lResult );
}

void test_prvTCPSendPacket_ConnectSynState_ARPCacheMiss( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    int32_t lResult, lReturn = 0x123AB;
    uint32_t uxOptionsLength = 0x12ABF;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );

    pxSocket->u.xTCP.ulRemoteIP = 0x1234;
    FreeRTOS_OutputARPRequest_Expect( FreeRTOS_htonl( pxSocket->u.xTCP.ulRemoteIP ) );

    lResult = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( 0, lResult );
}

void test_prvTCPSendPacket_ConnectSynState_ARPCantSendPacket( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    int32_t lResult, lReturn = 0x123AB;
    uint32_t uxOptionsLength = 0x12ABF;

    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eCantSendPacket );

    pxSocket->u.xTCP.ulRemoteIP = 0x1234;
    FreeRTOS_OutputARPRequest_Expect( FreeRTOS_htonl( pxSocket->u.xTCP.ulRemoteIP ) );

    lResult = prvTCPSendPacket( pxSocket );
    TEST_ASSERT_EQUAL( 0, lResult );
}
