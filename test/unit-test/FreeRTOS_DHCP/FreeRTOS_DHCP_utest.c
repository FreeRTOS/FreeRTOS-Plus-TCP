/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_task.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_DHCP_mock.h"

#include "FreeRTOS_DHCP.h"

#include "FreeRTOS_DHCP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

extern Socket_t xDHCPSocket;
extern DHCPData_t xDHCPData;

const char * pcHostName = "Unit-Test";

void test_xIsDHCPSocket(void)
{
    BaseType_t xReturn;
    struct xSOCKET xTestSocket;
    xDHCPSocket = &xTestSocket;

    /************************************/
    /* Test by NOT giving DHCP socket. */
    xReturn = xIsDHCPSocket( NULL );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    /************************************/
    /* Test by giving DHCP socket. */
    xReturn = xIsDHCPSocket( xDHCPSocket );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

void test_eGetDHCPState( void )
{
    DHCPData_t xTestData;
    eDHCPState_t eReturn;
    int i;

    for( i = 0; i < sizeof(xTestData.eDHCPState); i++ )
    {
        /* Modify the global state. */
        xDHCPData.eDHCPState = i;
        eReturn = eGetDHCPState();
        TEST_ASSERT_EQUAL( i, eReturn );
    }
}

NetworkBufferDescriptor_t * pxGlobalNetworkBuffer[10];
uint8_t GlobalBufferCounter = 0;
static NetworkBufferDescriptor_t * GetNetworkBuffer( size_t SizeOfEthBuf, long unsigned int xTimeToBlock, int callbacks )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = malloc( sizeof(NetworkBufferDescriptor_t) );
    pxNetworkBuffer->pucEthernetBuffer = malloc( SizeOfEthBuf );
    
    /* Ignore the callback count. */
    ( void ) callbacks;
    /* Ignore the timeout. */
    ( void ) xTimeToBlock;
    
    /* Set the global network buffer so that memory can be freed later on. */
    pxGlobalNetworkBuffer[ GlobalBufferCounter++ ] = pxNetworkBuffer;
    
    return pxNetworkBuffer;
}

static void ReleaseNetworkBuffer( void )
{
    /* Free the ethernet buffer. */
    free( pxGlobalNetworkBuffer[ --GlobalBufferCounter ]->pucEthernetBuffer );
    /* Free the network buffer. */
    free( pxGlobalNetworkBuffer[ GlobalBufferCounter ] );
}

static void ReleaseUDPBuffer( const void * temp, int callbacks )
{
   /* Should just call network buffer. */
   ReleaseNetworkBuffer();
}

#define xSizeofUDPBuffer 300
uint8_t pucUDPBuffer[ xSizeofUDPBuffer ];

static int32_t RecvFromStub( Socket_t xSocket,
                               void * pvBuffer,
                               size_t uxBufferLength,
                               BaseType_t xFlags,
                               struct freertos_sockaddr * pxSourceAddress,
                               socklen_t * pxSourceAddressLength,
                               int callbacks )
{    
    switch( callbacks )
    {
        case 0:
            memset( pucUDPBuffer, 0, xSizeofUDPBuffer );
            break;
        case 1:
            /* Put in correct DHCP cookie. */
            ( ( struct xDHCPMessage_IPv4 *) pucUDPBuffer )->ulDHCPCookie = dhcpCOOKIE;
            /* Put incorrect DHCP opcode. */
            ( ( struct xDHCPMessage_IPv4 *) pucUDPBuffer )->ucOpcode = dhcpREPLY_OPCODE+10;
            break;
    }
    
    if( xFlags == FREERTOS_ZERO_COPY )
    {
        *( ( uint8_t ** )pvBuffer ) = pucUDPBuffer;
    }
    
    return xSizeofUDPBuffer;
}

void test_vDHCPProcess_NotResetAndIncorrectState(void)
{
    xDHCPData.eDHCPState = eSendDHCPRequest;
    //vIPReloadDHCPTimer_Ignore();
    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    /* Since the expected state is incorrect, the state
     * should remain the same. */
    TEST_ASSERT_EQUAL( eSendDHCPRequest, xDHCPData.eDHCPState );
}

void test_vDHCPProcess_ResetAndIncorrectStateWithRNGFail(void)
{
    xDHCPData.eDHCPState = eSendDHCPRequest;
    /* Make random number generation fail. */
    xApplicationGetRandomNumber_ExpectAndReturn( &(xDHCPData.ulTransactionId), pdFALSE );
    vDHCPProcess( pdTRUE, eWaitingSendFirstDiscover );
    /* Expected state is incorrect, but we are trying to reset
     * the DHCP the state machine. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
}

void test_vDHCPProcess_ResetAndIncorrectStateWithRNGSuccessSocketCreationFail(void)
{   
    /* Test all the valid and invalid entries. */
    for( int i =0; i < ( eNotUsingLeasedAddress * 2 ); i++)
    {
        /* This should get assigned to a given value. */
        xDHCPSocket = NULL;
        /* Put any state. */
        xDHCPData.eDHCPState = eSendDHCPRequest;
        /* This should be reset to 0. */
        xDHCPData.xUseBroadcast = 1;
        /* This should be reset as well */
        xDHCPData.ulOfferedIPAddress = 0xAAAAAAAA;
        /* And this too. */
        xDHCPData.ulDHCPServerAddress = 0xABABABAB;
        
        
        /* Make random number generation pass. */
        xApplicationGetRandomNumber_ExpectAndReturn( &(xDHCPData.ulTransactionId), pdTRUE );
        /* return an invalid socket. */
        FreeRTOS_socket_ExpectAndReturn(FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP,FREERTOS_INVALID_SOCKET);
        /* See if the timer is reloaded. */
        vIPReloadDHCPTimer_Expect( dhcpINITIAL_TIMER_PERIOD );
        /* Try all kinds of states. */
        vDHCPProcess( pdTRUE, i );
        /* Expected state is incorrect, but we are trying to reset
         * the DHCP the state machine. */
        TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
        TEST_ASSERT_EQUAL( xDHCPSocket, NULL );
        TEST_ASSERT_EQUAL( xDHCPData.xUseBroadcast, 0);
        /* This should be reset as well */
        TEST_ASSERT_EQUAL( xDHCPData.ulOfferedIPAddress, 0);
        /* And this too. */
        TEST_ASSERT_EQUAL( xDHCPData.ulDHCPServerAddress, 0);
        
    }
    
}

void test_vDHCPProcess_ResetAndIncorrectStateWithRNGSuccessSocketBindFail(void)
{
    struct xSOCKET xTestSocket;
    
    /* Test all the valid and invalid entries. */
    for( int i =0; i < ( eNotUsingLeasedAddress * 2 ); i++)
    {
        /* This should get assigned to a given value. */
        xDHCPSocket = NULL;
        /* Put any state. */
        xDHCPData.eDHCPState = eSendDHCPRequest;
        /* This should be reset to 0. */
        xDHCPData.xUseBroadcast = 1;
        /* This should be reset as well */
        xDHCPData.ulOfferedIPAddress = 0xAAAAAAAA;
        /* And this too. */
        xDHCPData.ulDHCPServerAddress = 0xABABABAB;
        
        
        /* Make random number generation pass. */
        xApplicationGetRandomNumber_ExpectAndReturn( &(xDHCPData.ulTransactionId), pdTRUE );
        /* Return a valid socket. */
        FreeRTOS_socket_ExpectAndReturn(FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP,&xTestSocket);
        /* Ignore the inputs to setting the socket options. */
        FreeRTOS_setsockopt_IgnoreAndReturn( pdPASS );
        /* Make sure that binding fails. Return anything except zero. */
        vSocketBind_IgnoreAndReturn(pdTRUE);
        /* Then expect the socket to be closed. */
        vSocketClose_ExpectAndReturn( &xTestSocket, NULL );
        /* See if the timer is reloaded. */
        vIPReloadDHCPTimer_Expect( dhcpINITIAL_TIMER_PERIOD );
        /* Try all kinds of states. */
        vDHCPProcess( pdTRUE, i );
        /* Expected state is incorrect, but we are trying to reset
         * the DHCP the state machine. */
        TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
        TEST_ASSERT_EQUAL( xDHCPSocket, NULL );
        TEST_ASSERT_EQUAL( xDHCPData.xUseBroadcast, 0);
        /* This should be reset as well */
        TEST_ASSERT_EQUAL( xDHCPData.ulOfferedIPAddress, 0);
        /* And this too. */
        TEST_ASSERT_EQUAL( xDHCPData.ulDHCPServerAddress, 0);
        
    }
    
}

void test_vDHCPProcess_ResetAndIncorrectStateWithRNGSuccessSocketSuccess(void)
{
    struct xSOCKET xTestSocket;
    
    /* Test all the valid and invalid entries. */
    for( int i =0; i < ( eNotUsingLeasedAddress * 2 ); i++)
    {
        /* This should get assigned to a given value. */
        xDHCPSocket = NULL;
        /* Put any state. */
        xDHCPData.eDHCPState = eSendDHCPRequest;
        /* This should be reset to 0. */
        xDHCPData.xUseBroadcast = 1;
        /* This should be reset as well */
        xDHCPData.ulOfferedIPAddress = 0xAAAAAAAA;
        /* And this too. */
        xDHCPData.ulDHCPServerAddress = 0xABABABAB;
        
        
        /* Make random number generation pass. */
        xApplicationGetRandomNumber_ExpectAndReturn( &(xDHCPData.ulTransactionId), pdTRUE );
        /* Return a valid socket. */
        FreeRTOS_socket_ExpectAndReturn(FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP,&xTestSocket);
        /* Ignore the inputs to setting the socket options. */
        FreeRTOS_setsockopt_IgnoreAndReturn( pdPASS );
        /* Make sure that binding fails. Return anything except zero. */
        vSocketBind_IgnoreAndReturn(0);
        /* See if the timer is reloaded. */
        vIPReloadDHCPTimer_Expect( dhcpINITIAL_TIMER_PERIOD );
        /* Try all kinds of states. */
        vDHCPProcess( pdTRUE, i );
        /* Expected state is incorrect, but we are trying to reset
         * the DHCP the state machine. */
        TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
        TEST_ASSERT_EQUAL( xDHCPSocket, &xTestSocket );
        TEST_ASSERT_EQUAL( xDHCPData.xUseBroadcast, 0);
        /* This should be reset as well */
        TEST_ASSERT_EQUAL( xDHCPData.ulOfferedIPAddress, 0);
        /* And this too. */
        TEST_ASSERT_EQUAL( xDHCPData.ulDHCPServerAddress, 0);
        
    }
    
}

void test_vDHCPProcess_ResetAndIncorrectStateWithSocketAlreadyCreated(void)
{
    struct xSOCKET xTestSocket;
    
    /* Test all the valid and invalid entries. */
    for( int i =0; i < ( eNotUsingLeasedAddress * 2 ); i++)
    {
        /* This should remain unchanged. */
        xDHCPSocket = &xTestSocket;
        /* Put any state. */
        xDHCPData.eDHCPState = eSendDHCPRequest;
        /* This should be reset to 0. */
        xDHCPData.xUseBroadcast = 1;
        /* This should be reset as well */
        xDHCPData.ulOfferedIPAddress = 0xAAAAAAAA;
        /* And this too. */
        xDHCPData.ulDHCPServerAddress = 0xABABABAB;
        /* And this should be updated. */
        xDHCPData.xDHCPTxPeriod = 0;
        
        /* Make random number generation pass. */
        xApplicationGetRandomNumber_ExpectAndReturn( &(xDHCPData.ulTransactionId), pdTRUE );
        /* See if the timer is reloaded. */
        vIPReloadDHCPTimer_Expect( dhcpINITIAL_TIMER_PERIOD );
        /* Try all kinds of states. */
        vDHCPProcess( pdTRUE, i );
        /* Expected state is incorrect, but we are trying to reset
         * the DHCP the state machine. */
        TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
        TEST_ASSERT_EQUAL( xDHCPSocket, &xTestSocket );
        TEST_ASSERT_EQUAL( 0,xDHCPData.xUseBroadcast);
        /* This should be reset as well */
        TEST_ASSERT_EQUAL( 0,xDHCPData.ulOfferedIPAddress);
        /* And this too. */
        TEST_ASSERT_EQUAL( 0,xDHCPData.ulDHCPServerAddress);
        /* This should be updated. */
        TEST_ASSERT_EQUAL( dhcpINITIAL_DHCP_TX_PERIOD, xDHCPData.xDHCPTxPeriod );
        
    }
    
}

void test_vDHCPProcess_CorrectStateDHCPHookFailsDHCPSocketNULL(void)
{   
    /* The DHCP socket is NULL. */
    xDHCPSocket = NULL;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    /* Make sure that the local IP address is uninitialised. */
    *ipLOCAL_IP_ADDRESS_POINTER=0;
    /* Put a verifiable value. */
    xNetworkAddressing.ulDefaultIPAddress = 0x12345678;
    
    /* Make sure that the user indicates anything else than the desired options. */
    xApplicationDHCPHook_ExpectAndReturn(eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, (eDHCPContinue+eDHCPUseDefaults) << 2 );
    /* Expect the timer to be disabled. */
    vIPSetDHCPTimerEnableState_Expect(pdFALSE);
    vIPNetworkUpCalls_Ignore();
    
    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    
    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( NULL, xDHCPSocket );
    /* The state should indicate that we are not using leased address. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress,xDHCPData.eDHCPState);
    /* Make sure that the local IP address pointer indicates that. */
    TEST_ASSERT_EQUAL( xNetworkAddressing.ulDefaultIPAddress,*ipLOCAL_IP_ADDRESS_POINTER);
}

void test_vDHCPProcess_CorrectStateDHCPHookFailsDHCPSocketNonNULL(void)
{
    struct xSOCKET xTestSocket;
    
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    /* Make sure that the local IP address is uninitialised. */
    *ipLOCAL_IP_ADDRESS_POINTER=0;
    /* Put a verifiable value. */
    xNetworkAddressing.ulDefaultIPAddress = 0x12345678;
    
    /* Make sure that the user indicates anything else than the desired options. */
    xApplicationDHCPHook_ExpectAndReturn(eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, (eDHCPContinue+eDHCPUseDefaults) << 2 );
    /* Expect the timer to be disabled. */
    vIPSetDHCPTimerEnableState_Expect(pdFALSE);
    /* Ignore the call. */
    vIPNetworkUpCalls_Ignore();
    /* Expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( xDHCPSocket, NULL );
    
    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    
    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( NULL, xDHCPSocket );
    /* The state should indicate that we are not using leased address. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress,xDHCPData.eDHCPState);
    /* Make sure that the local IP address pointer indicates that. */
    TEST_ASSERT_EQUAL( xNetworkAddressing.ulDefaultIPAddress,*ipLOCAL_IP_ADDRESS_POINTER);
}

void test_vDHCPProcess_CorrectStateDHCPHookDefaultReturn(void)
{
    struct xSOCKET xTestSocket;
    
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    /* Make sure that the local IP address is uninitialised. */
    *ipLOCAL_IP_ADDRESS_POINTER=0;
    /* Put a verifiable value. */
    memset(&xNetworkAddressing, 0xAA, sizeof(xNetworkAddressing));
    /* Put a verifiable value. */
    memset(&xDefaultAddressing, 0xBB, sizeof(xDefaultAddressing));
    
    /* Make sure that the user indicates anything else than the desired options. */
    xApplicationDHCPHook_ExpectAndReturn( eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, eDHCPUseDefaults );
    /* Expect the timer to be disabled. */
    vIPSetDHCPTimerEnableState_Expect(pdFALSE);
    /* Ignore the call. */
    vIPNetworkUpCalls_Ignore();
    /* Expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( xDHCPSocket, NULL );
    
    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    
    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( NULL, xDHCPSocket );
    /* The state should indicate that we are not using leased address. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress,xDHCPData.eDHCPState);
    /* Make sure that the network addressing struct is updated to show that. */
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultAddressing,&xNetworkAddressing,sizeof(xDefaultAddressing));
    /* Make sure that the local IP address pointer indicates that. */
    TEST_ASSERT_EQUAL( xNetworkAddressing.ulDefaultIPAddress,*ipLOCAL_IP_ADDRESS_POINTER);
}

/* GNW = getNetworkBufferWithDescriptor */
void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnDHCPSocketNotNULLButGNWFails(void)
{
    struct xSOCKET xTestSocket;
    
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    
    /* Make sure that the user indicates anything else than the desired options. */
    xApplicationDHCPHook_ExpectAndReturn( eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, eDHCPContinue );
    xTaskGetTickCount_IgnoreAndReturn(100);
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning NULL will mean the prvSendDHCPDiscover fail. */
    pxGetNetworkBufferWithDescriptor_IgnoreAndReturn(NULL);
        
    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    
    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we are not using leased address. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover,xDHCPData.eDHCPState);
}

void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnDHCPSocketNULL(void)
{    
    /* This should remain unchanged. */
    xDHCPSocket = NULL;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    
    /* Make sure that the user indicates anything else than the desired options. */
    xApplicationDHCPHook_ExpectAndReturn( eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, eDHCPContinue );
    /* Expect the timer to be disabled. */
    vIPSetDHCPTimerEnableState_Expect(pdFALSE);
    /* Ignore the call. */
    vIPNetworkUpCalls_Ignore();
        
    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    
    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( NULL, xDHCPSocket );
    /* The state should indicate that we are not using leased address. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress,xDHCPData.eDHCPState);
}

void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnSendFailsNoBroadcast(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    /* Not using broadcast. */
    xDHCPData.xUseBroadcast = pdFALSE;
    
    /* Make sure that the user indicates anything else than the desired options. */
    xApplicationDHCPHook_ExpectAndReturn( eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, eDHCPContinue );
    /* Return the time value. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Make the call to FreeRTOS_send fail. */
    FreeRTOS_sendto_IgnoreAndReturn( 0 );
    /* Since the send failed, a call to release the buffer should be there. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Stub( ReleaseUDPBuffer );

    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    
    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover,xDHCPData.eDHCPState);
    /* The time value should be as expected. */
    TEST_ASSERT_EQUAL( xTimeValue,xDHCPData.xDHCPTxTime);
}

void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnSendFailsUseBroadCast(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    /* Not using broadcast. */
    xDHCPData.xUseBroadcast = pdTRUE;
    
    /* Make sure that the user indicates anything else than the desired options. */
    xApplicationDHCPHook_ExpectAndReturn( eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, eDHCPContinue );
    /* Return the time value. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Make the call to FreeRTOS_send fail. */
    FreeRTOS_sendto_IgnoreAndReturn( 0 );
    /* Since the send failed, a call to release the buffer should be there. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Stub( ReleaseUDPBuffer );

    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    
    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover,xDHCPData.eDHCPState);
    /* The time value should be as expected. */
    TEST_ASSERT_EQUAL( xTimeValue,xDHCPData.xDHCPTxTime);
}

void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnSendSucceedsUseBroadCast(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    /* Using broadcast. */
    xDHCPData.xUseBroadcast = pdTRUE;
    
    /* Make sure that the user indicates anything else than the desired options. */
    xApplicationDHCPHook_ExpectAndReturn( eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, eDHCPContinue );
    /* Return the time value. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Make the call to FreeRTOS_send succeed. */
    FreeRTOS_sendto_IgnoreAndReturn( 1 );

    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    
    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer,xDHCPData.eDHCPState);
    /* The time value should be as expected. */
    TEST_ASSERT_EQUAL( xTimeValue,xDHCPData.xDHCPTxTime);
    
    /* Free the allocated memory. */
    ReleaseNetworkBuffer();
}

void test_vDHCPProcess_eSendDHCPRequestCorrectStateGNWFails(void)
{
    struct xSOCKET xTestSocket;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eSendDHCPRequest;

    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Return NULL network buffer. */
    pxGetNetworkBufferWithDescriptor_IgnoreAndReturn( NULL );

    vDHCPProcess( pdFALSE, eSendDHCPRequest );
    
    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eSendDHCPRequest,xDHCPData.eDHCPState);
}

void test_vDHCPProcess_eSendDHCPRequestCorrectStateGNWSucceedsSendFails(void)
{
    struct xSOCKET xTestSocket;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eSendDHCPRequest;

    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Send fails. */
    FreeRTOS_sendto_IgnoreAndReturn(0);
    /* ReleaseUDPPayloadBuffer will be called. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Stub( ReleaseUDPBuffer );

    vDHCPProcess( pdFALSE, eSendDHCPRequest );
    
    /* DHCP socket should be still allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eSendDHCPRequest,xDHCPData.eDHCPState);
}


void test_vDHCPProcess_eSendDHCPRequestCorrectStateGNWSucceedsSendSucceeds(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eSendDHCPRequest;

    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Send succeeds. */
    FreeRTOS_sendto_IgnoreAndReturn( 1 );
    /* Return the time value. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );

    vDHCPProcess( pdFALSE, eSendDHCPRequest );
    
    /* DHCP socket should be still allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge,xDHCPData.eDHCPState);
    TEST_ASSERT_EQUAL( xTimeValue,xDHCPData.xDHCPTxTime);
    TEST_ASSERT_EQUAL( dhcpINITIAL_DHCP_TX_PERIOD,xDHCPData.xDHCPTxPeriod);
}

void test_vDHCPProcess_eWaitingOfferRecvfromFailsNoTimeout(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingOffer;
    /* Put some time values. */
    xDHCPData.xDHCPTxTime = 100;
    xDHCPData.xDHCPTxPeriod = 100;

    /* Expect these args. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPSocket, NULL, 0UL, FREERTOS_ZERO_COPY, NULL, NULL, 0 );
    /* Ignore the buffer arg though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    
    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod );
    

    vDHCPProcess( pdFALSE, eWaitingOffer );
    
    /* DHCP socket should be still allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer,xDHCPData.eDHCPState);
}

void test_vDHCPProcess_eWaitingOfferRecvfromFailsTimeoutGiveUp(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingOffer;
    /* Put some time values. */
    xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we exceed the period - and give up. */
    xDHCPData.xDHCPTxPeriod = ipconfigMAXIMUM_DISCOVER_TX_PERIOD;

    /* Expect these args. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPSocket, NULL, 0UL, FREERTOS_ZERO_COPY, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    
    /* Make sure that there is timeout. The expression is: xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference greater than the period. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod + 100 );
    
    /* Make all calls to the RNG succeed. */
    xApplicationGetRandomNumber_IgnoreAndReturn(pdTRUE);
    
    /* Closing the DHCP socket. */
    vSocketClose_ExpectAndReturn( xDHCPSocket, 0 );
    
    /* Ignore the call to this function. */
    vARPSendGratuitous_Ignore();

    vDHCPProcess( pdFALSE, eWaitingOffer );
    
    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eGetLinkLayerAddress,xDHCPData.eDHCPState);
}

void test_vDHCPProcess_eWaitingOfferRecvfromFailsTimeoutDontGiveUpRNGFail(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingOffer;
    /* Put some time values. */
    xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    xDHCPData.xDHCPTxPeriod = (ipconfigMAXIMUM_DISCOVER_TX_PERIOD>>1) - 1;

    /* Expect these args. Return a 0 to fail. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPSocket, NULL, 0UL, FREERTOS_ZERO_COPY, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    
    /* Make sure that there is timeout. The expression is: xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference greater than the period. */
    xTaskGetTickCount_ExpectAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod + 100 );
    
    /* Make all calls to the RNG fail. */
    xApplicationGetRandomNumber_IgnoreAndReturn(pdFALSE);

    vDHCPProcess( pdFALSE, eWaitingOffer );
    
    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer,xDHCPData.eDHCPState);
    /* make sure that the period is increased by a factor of two. */
    TEST_ASSERT_EQUAL( ((ipconfigMAXIMUM_DISCOVER_TX_PERIOD>>1) - 1) <<1,xDHCPData.xDHCPTxPeriod);
}

void test_vDHCPProcess_eWaitingOfferRecvfromFailsTimeoutDontGiveUpRNGPassUseBroadcast(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingOffer;
    /* Put some time values. */
    xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    xDHCPData.xDHCPTxPeriod = (ipconfigMAXIMUM_DISCOVER_TX_PERIOD>>1) - 1;
    /* Using broadcast. */
    xDHCPData.xUseBroadcast = pdTRUE;

    /* Expect these args. Return a 0 to fail. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPSocket, NULL, 0UL, FREERTOS_ZERO_COPY, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    
    /* Make sure that there is timeout. The expression is: xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference greater than the period. */
    xTaskGetTickCount_ExpectAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod + 100 );
    
    /* Make all calls to the RNG succeed. */
    xApplicationGetRandomNumber_IgnoreAndReturn(pdTRUE);
    
    xTaskGetTickCount_ExpectAndReturn(xTimeValue);
    
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Send succeeds. */
    FreeRTOS_sendto_IgnoreAndReturn( 1 );

    vDHCPProcess( pdFALSE, eWaitingOffer );
    
    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer,xDHCPData.eDHCPState);
    /* make sure that the period is increased by a factor of two. */
    TEST_ASSERT_EQUAL( ((ipconfigMAXIMUM_DISCOVER_TX_PERIOD>>1) - 1) <<1,xDHCPData.xDHCPTxPeriod);
}

void test_vDHCPProcess_eWaitingOfferRecvfromFailsTimeoutDontGiveUpRNGPassNoBroadcast(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingOffer;
    /* Put some time values. */
    xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    xDHCPData.xDHCPTxPeriod = (ipconfigMAXIMUM_DISCOVER_TX_PERIOD>>1) - 1;
    /* Not Using broadcast. */
    xDHCPData.xUseBroadcast = pdFALSE;

    /* Expect these args. Return a 0 to fail. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPSocket, NULL, 0UL, FREERTOS_ZERO_COPY, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    
    /* Make sure that there is timeout. The expression is: xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference greater than the period. */
    xTaskGetTickCount_ExpectAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod + 100 );
    
    /* Make all calls to the RNG succeed. */
    xApplicationGetRandomNumber_IgnoreAndReturn(pdTRUE);
    
    xTaskGetTickCount_ExpectAndReturn(xTimeValue);
    
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a NULL network buffer. */
    pxGetNetworkBufferWithDescriptor_IgnoreAndReturn( NULL );
    
    vDHCPProcess( pdFALSE, eWaitingOffer );
    
    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eInitialWait,xDHCPData.eDHCPState);
    /* make sure that the period is increased by a factor of two. */
    TEST_ASSERT_EQUAL( ((ipconfigMAXIMUM_DISCOVER_TX_PERIOD>>1) - 1) <<1,xDHCPData.xDHCPTxPeriod);
}

static int32_t FreeRTOS_recvfrom_eWaitingOfferRecvfromSucceedsFalseCookieNoTimeout( Socket_t xSocket,
                               void * pvBuffer,
                               size_t uxBufferLength,
                               BaseType_t xFlags,
                               struct freertos_sockaddr * pxSourceAddress,
                               socklen_t * pxSourceAddressLength,
                               int callbacks )
{
    if( xFlags == FREERTOS_ZERO_COPY )
    {
        *( ( uint8_t ** )pvBuffer ) = pucUDPBuffer;
    }
    
    memset( pucUDPBuffer, 0, xSizeofUDPBuffer );
    
    return xSizeofUDPBuffer;
}

void test_vDHCPProcess_eWaitingOfferRecvfromSucceedsFalseCookieNoTimeout(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingOffer;
    /* Put some time values. */
    xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    xDHCPData.xUseBroadcast = pdFALSE;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSucceedsFalseCookieNoTimeout );
    
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );
    
    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod );
    
    vDHCPProcess( pdFALSE, eWaitingOffer );
    
    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer,xDHCPData.eDHCPState);
}

static int32_t FreeRTOS_recvfrom_eWaitingOfferRecvfromSucceedsFalseOpcodeNoTimeout( Socket_t xSocket,
                               void * pvBuffer,
                               size_t uxBufferLength,
                               BaseType_t xFlags,
                               struct freertos_sockaddr * pxSourceAddress,
                               socklen_t * pxSourceAddressLength,
                               int callbacks )
{
    if( xFlags == FREERTOS_ZERO_COPY )
    {
        *( ( uint8_t ** )pvBuffer ) = pucUDPBuffer;
    }
    
    memset( pucUDPBuffer, 0, xSizeofUDPBuffer );
    /* Put in correct DHCP cookie. */
    ( ( struct xDHCPMessage_IPv4 *) pucUDPBuffer )->ulDHCPCookie = dhcpCOOKIE;
    
    return xSizeofUDPBuffer;
}

void test_vDHCPProcess_eWaitingOfferRecvfromSucceedsFalseOpcodeNoTimeout(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingOffer;
    /* Put some time values. */
    xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    xDHCPData.xUseBroadcast = pdFALSE;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSucceedsFalseOpcodeNoTimeout );
    
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );
    
    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod );
    
    vDHCPProcess( pdFALSE, eWaitingOffer );
    
    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer,xDHCPData.eDHCPState);
}

static int32_t FreeRTOS_recvfrom_eWaitingOfferRecvfromSucceedsCorrectCookieAndOpcodeNoTimeout( Socket_t xSocket,
                               void * pvBuffer,
                               size_t uxBufferLength,
                               BaseType_t xFlags,
                               struct freertos_sockaddr * pxSourceAddress,
                               socklen_t * pxSourceAddressLength,
                               int callbacks )
{
    if( xFlags == FREERTOS_ZERO_COPY )
    {
        *( ( uint8_t ** )pvBuffer ) = pucUDPBuffer;
    }
    
    memset( pucUDPBuffer, 0, xSizeofUDPBuffer );
    /* Put in correct DHCP cookie. */
    ( ( struct xDHCPMessage_IPv4 *) pucUDPBuffer )->ulDHCPCookie = dhcpCOOKIE;
    /* Put incorrect DHCP opcode. */
    ( ( struct xDHCPMessage_IPv4 *) pucUDPBuffer )->ucOpcode = dhcpREPLY_OPCODE;
    
    return xSizeofUDPBuffer;
}

void test_vDHCPProcess_eWaitingOfferRecvfromSucceedsCorrectCookieAndOpcodeNoTimeout(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingOffer;
    /* Put some time values. */
    xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which won't match. */
    xDHCPData.ulTransactionId = 0x01ABCDEF;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSucceedsCorrectCookieAndOpcodeNoTimeout );
    
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );
    
    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod );
    
    vDHCPProcess( pdFALSE, eWaitingOffer );
    
    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer,xDHCPData.eDHCPState);
}

static int32_t FreeRTOS_recvfrom_eWaitingOfferRecvfromLessBytesNoTimeout( Socket_t xSocket,
                               void * pvBuffer,
                               size_t uxBufferLength,
                               BaseType_t xFlags,
                               struct freertos_sockaddr * pxSourceAddress,
                               socklen_t * pxSourceAddressLength,
                               int callbacks )
{
    if( xFlags == FREERTOS_ZERO_COPY )
    {
        *( ( uint8_t ** )pvBuffer ) = pucUDPBuffer;
    }
    
    memset( pucUDPBuffer, 0, xSizeofUDPBuffer );
    
    return sizeof( DHCPMessage_IPv4_t ) - 1;
}

void test_vDHCPProcess_eWaitingOfferRecvfromLessBytesNoTimeout(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingOffer;
    /* Put some time values. */
    xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    xDHCPData.xUseBroadcast = pdFALSE;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromLessBytesNoTimeout );
    
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );
    
    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod );
    
    vDHCPProcess( pdFALSE, eWaitingOffer );
    
    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer,xDHCPData.eDHCPState);
}

static int32_t FreeRTOS_recvfrom_eWaitingOfferRecvfromSuccessCorrectTxID( Socket_t xSocket,
                               void * pvBuffer,
                               size_t uxBufferLength,
                               BaseType_t xFlags,
                               struct freertos_sockaddr * pxSourceAddress,
                               socklen_t * pxSourceAddressLength,
                               int callbacks )
{
    if( xFlags == FREERTOS_ZERO_COPY )
    {
        *( ( uint8_t ** )pvBuffer ) = pucUDPBuffer;
    }
    
    memset( pucUDPBuffer, 0, xSizeofUDPBuffer );
    /* Put in correct DHCP cookie. */
    ( ( struct xDHCPMessage_IPv4 *) pucUDPBuffer )->ulDHCPCookie = dhcpCOOKIE;
    /* Put in correct DHCP opcode. */
    ( ( struct xDHCPMessage_IPv4 *) pucUDPBuffer )->ucOpcode = dhcpREPLY_OPCODE;
    /* Put in correct DHCP Tx ID. */
    ( ( struct xDHCPMessage_IPv4 *) pucUDPBuffer )->ulTransactionID = FreeRTOS_htonl( EP_DHCPData.ulTransactionId );
    
    return xSizeofUDPBuffer;
}

void test_vDHCPProcess_eWaitingOfferRecvfromSuccessCorrectTxID(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
     
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingOffer;
    /* Put some time values. */
    xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    xDHCPData.ulTransactionId = 0x01ABCDEF;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSuccessCorrectTxID );
    
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );
    
    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod );
    
    vDHCPProcess( pdFALSE, eWaitingOffer );
    
    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer,xDHCPData.eDHCPState);
}

uint8_t DHCP_header[] = {
        dhcpREPLY_OPCODE,                                                      /**< Operation Code: Specifies the general type of message. */
        0x01,                                                 /**< Hardware type used on the local network. */
        0x06,                                               /**< Hardware Address Length: Specifies how long hardware
                                                                                * addresses are in this message. */
        0x02,                                                        /**< Hops. */
        0x01,0xAB, 0xCD,0xEF,                                              /**< A 32-bit identification field generated by the client,
                                                                                * to allow it to match up the request with replies received
                                                                                * from DHCP servers. */
        0x01,                                                /**< Number of seconds elapsed since a client began an attempt to acquire or renew a lease. */
        0x00,                                                      /**< Just one bit used to indicate broadcast. */
        0x00,0xAA,0xAA,0xAA,                                     /**< Client's IP address if it has one or 0 is put in this field. */
        0x00,0xAA,0xAA,0xAA,                                       /**< The IP address that the server is assigning to the client. */
        0x00,0xAA,0xAA,0xAA,                                     /**< The DHCP server address that the client should use. */
        0x00,0xAA,0xAA,0xAA                                 /**< Gateway IP address in case the server client are on different subnets. */
    };

uint8_t * ucGenericPtr;
int32_t ulGenericLength;
static int32_t FreeRTOS_recvfrom_Generic( Socket_t xSocket,
                               void * pvBuffer,
                               size_t uxBufferLength,
                               BaseType_t xFlags,
                               struct freertos_sockaddr * pxSourceAddress,
                               socklen_t * pxSourceAddressLength,
                               int callbacks )
{
    if( xFlags == FREERTOS_ZERO_COPY )
    {
        *( ( uint8_t ** )pvBuffer ) = ucGenericPtr;
    }
    
    return ulGenericLength;
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageWithoutOptionsNoTimeout(void)
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    uint8_t DHCPMsg[ sizeof(struct xDHCPMessage_IPv4) ];
    DHCPMessage_IPv4_t * pxDHCPMessage = (DHCPMessage_IPv4_t *)DHCPMsg;
        
    memset( DHCPMsg, 0, sizeof(DHCPMsg) );
    memcpy( DHCPMsg, DHCP_header, sizeof(DHCP_header) );
    memcpy( pxDHCPMessage->ucClientHardwareAddress, ipLOCAL_MAC_ADDRESS, sizeof( MACAddress_t ) );
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof(DHCPMsg);
    
    /* This should remain unchanged. */
    xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    xDHCPData.eDHCPState = eWaitingOffer;
    /* Put some time values. */
    xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    xDHCPData.ulTransactionId = 0x01ABCDEF;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );
    
    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod );
    
    vDHCPProcess( pdFALSE, eWaitingOffer );
    
    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer,xDHCPData.eDHCPState);
}

void test_vDHCPProcess(void)
{
    BaseType_t xReset;
    eDHCPState_t eExpectedState;
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthBuffer[ipUDP_PAYLOAD_OFFSET_IPv4];
    uint8_t pucUDPBuffer[ 300 ];
    uint32_t ulTicksReturned;

    #if 0
    
    /*************************************************************************/    
    /*************************************************************************/
    /* DHCP State: eWaitingOffer. */
    /*************************************************************************/
    /*************************************************************************/
  
    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. Get the default values from the Application hook. */
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = &xTestSocket;
    ulTicksReturned = 235;
    /* Mark the broadcast as true. */
    xDHCPData.xUseBroadcast = pdTRUE;
    xDHCPData.eDHCPState = eWaitingOffer;
    xDHCPData.xDHCPTxTime = ulTicksReturned;
    /* Set the DHCP period. */
    xDHCPData.xDHCPTxPeriod = 100;
    /* Make sure nothing is received. */
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    /* Returning a proper network buffer. */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod );
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingOffer );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eWaitingOffer, xDHCPData.eDHCPState );
    /* Make sure that DHCP socket is still NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /*************************************************************************/

    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. Get the default values from the Application hook. */
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = &xTestSocket;
    ulTicksReturned = 235;
    /* Mark the broadcast as true. */
    xDHCPData.xUseBroadcast = pdTRUE;
    xDHCPData.eDHCPState = eWaitingOffer;
    xDHCPData.xDHCPTxTime = ulTicksReturned;
    /* Set the DHCP period. */
    xDHCPData.xDHCPTxPeriod = 100;
    /* Make sure nothing is received. */
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    /* Returning a proper network buffer. */
    /* Return a value which makes the difference greater than the period so
     * that the process times out. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod + 100 );
    /* For DHCP we need random numbers, but what if it fails? */
    xApplicationGetRandomNumber_IgnoreAndReturn( pdFALSE );
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingOffer );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eWaitingOffer, xDHCPData.eDHCPState );
    /* Make sure that DHCP socket is still NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /*************************************************************************/

    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. Get the default values from the Application hook. */
    /* Make sure that DHCP socket is created */
    xDHCPSocket = &xTestSocket;
    ulTicksReturned = 235;
    /* Mark the broadcast as true. */
    xDHCPData.xUseBroadcast = pdTRUE;
    xDHCPData.eDHCPState = eWaitingOffer;
    xDHCPData.xDHCPTxTime = ulTicksReturned;
    /* Set the DHCP period. */
    xDHCPData.xDHCPTxPeriod = 100;
    /* Make sure nothing is received. */
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    /* Returning a proper network buffer. */
    /* Return a value which makes the difference greater than the period so
     * that the process times out. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod + 100 );
    /* For DHCP we need random numbers, make it pass. */
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );
    /* Return the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Make freertos send fail. */
    FreeRTOS_sendto_IgnoreAndReturn( 0 );
    /* Since the send failed, a call to release the buffer should be there. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Stub( ReleaseUDPBuffer );
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingOffer );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eInitialWait, xDHCPData.eDHCPState );
    /* Make sure that DHCP socket is still NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /* Clean the stub */
    FreeRTOS_ReleaseUDPPayloadBuffer_Stub(NULL);
    /*************************************************************************/

    
    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. Get the default values from the Application hook. */
    ulTicksReturned = 235;
    /* Mark the broadcast as true. */
    xDHCPData.xUseBroadcast = pdTRUE;
    xDHCPData.eDHCPState = eWaitingOffer;
    xDHCPData.xDHCPTxTime = ulTicksReturned;
    /* Set the DHCP period. */
    xDHCPData.xDHCPTxPeriod = 100;
    /* Make sure nothing is received. */
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    /* Returning a proper network buffer. */
    /* Return a value which makes the difference greater than the period so
     * that the process times out. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod + 100 );
    /* For DHCP we need random numbers, make it pass. */
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );
    /* Return the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Make freertos send pass. */
    FreeRTOS_sendto_IgnoreAndReturn( 1 );
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingOffer );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eWaitingOffer, xDHCPData.eDHCPState );
    /*************************************************************************/

    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. Get the default values from the Application hook. */
    ulTicksReturned = 235;
    /* Mark the broadcast as true. */
    xDHCPData.xUseBroadcast = pdFALSE;
    xDHCPData.eDHCPState = eWaitingOffer;
    xDHCPData.xDHCPTxTime = ulTicksReturned;
    /* Set the DHCP period. */
    xDHCPData.xDHCPTxPeriod = 100;
    /* Make sure nothing is received. */
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    /* Returning a proper network buffer. */
    /* Return a value which makes the difference greater than the period so
     * that the process times out. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod + 100 );
    /* For DHCP we need random numbers, make it pass. */
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );
    /* Return the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Make freertos send pass. */
    FreeRTOS_sendto_IgnoreAndReturn( 1 );
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingOffer );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eWaitingOffer, xDHCPData.eDHCPState );
    /*************************************************************************/

    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. */
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = &xTestSocket;
    ulTicksReturned = 235;
    /* Mark the broadcast as true. */
    xDHCPData.xUseBroadcast = pdFALSE;
    xDHCPData.eDHCPState = eWaitingOffer;
    xDHCPData.xDHCPTxTime = ulTicksReturned;
    /* Set the DHCP period to be greater than the configured value. */
    xDHCPData.xDHCPTxPeriod = ipconfigMAXIMUM_DISCOVER_TX_PERIOD + 20;
    /* Make sure nothing is received. */
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    /* Return a value which makes the difference greater than the period so
     * that the process times out. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod + 100 );
    /* For DHCP we need random numbers, make it pass. */
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Make freertos send pass. */
    FreeRTOS_sendto_IgnoreAndReturn( 1 );
    /* Closing the DHCP socket. */
    vSocketClose_ExpectAndReturn( xDHCPSocket, 0 );
    /* Ignore the call to this function. */
    vARPSendGratuitous_Ignore();
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingOffer );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eGetLinkLayerAddress, xDHCPData.eDHCPState );
    /*************************************************************************/


    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. */
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = &xTestSocket;
    ulTicksReturned = 235;
    /* Mark the broadcast as true. */
    xDHCPData.xUseBroadcast = pdFALSE;
    xDHCPData.eDHCPState = eWaitingOffer;
    xDHCPData.xDHCPTxTime = ulTicksReturned;
    /* Set the DHCP period to be greater than the configured value. */
    xDHCPData.xDHCPTxPeriod = ipconfigMAXIMUM_DISCOVER_TX_PERIOD + 20;
    /* Make sure we have received data less than sizeof( DHCPMessage_IPv4_t ). */
    FreeRTOS_recvfrom_IgnoreAndReturn( 239 );
    
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( NULL );
    /* Return a value which makes the difference greater than the period so
     * that the process times out. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod + 100 );
    /* For DHCP we need random numbers, make it pass. */
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Make freertos send pass. */
    FreeRTOS_sendto_IgnoreAndReturn( 1 );
    /* Closing the DHCP socket. */
    vSocketClose_ExpectAndReturn( xDHCPSocket, 0 );
    /* Ignore the call to this function. */
    vARPSendGratuitous_Ignore();
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingOffer );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eGetLinkLayerAddress, xDHCPData.eDHCPState );
    /*************************************************************************/

    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. */
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = &xTestSocket;
    ulTicksReturned = 235;
    /* Mark the broadcast as true. */
    xDHCPData.xUseBroadcast = pdFALSE;
    xDHCPData.eDHCPState = eWaitingOffer;
    xDHCPData.xDHCPTxTime = ulTicksReturned;
    /* Set the DHCP period to be greater than the configured value. */
    xDHCPData.xDHCPTxPeriod = ipconfigMAXIMUM_DISCOVER_TX_PERIOD + 20;
    /* Make sure we have received data less than sizeof( DHCPMessage_IPv4_t ). */
    FreeRTOS_recvfrom_Stub( RecvFromStub );
    printf( "%08x\n", pucUDPBuffer );
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );
    /* Return a value which makes the difference equal to the period so
     * that the process doesn't time out. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod );
    /* For DHCP we need random numbers, make it pass. */
    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );

    /* Ignore the call to this function. */
    vARPSendGratuitous_Ignore();
    
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingOffer );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eWaitingOffer, xDHCPData.eDHCPState );
    /*************************************************************************/

    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. */
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = &xTestSocket;
    ulTicksReturned = 235;
    /* Mark the broadcast as true. */
    xDHCPData.xUseBroadcast = pdFALSE;
    xDHCPData.eDHCPState = eWaitingOffer;
    xDHCPData.xDHCPTxTime = ulTicksReturned;
    /* Set the DHCP period to be greater than the configured value. */
    xDHCPData.xDHCPTxPeriod = ipconfigMAXIMUM_DISCOVER_TX_PERIOD + 20;
    FreeRTOS_recvfrom_Stub( RecvFromStub );
    FreeRTOS_ReleaseUDPPayloadBuffer_Stub(NULL);
    printf( "%08x\n", pucUDPBuffer );
    FreeRTOS_ReleaseUDPPayloadBuffer_Ignore();
    /* Return a value which makes the difference equal to the period so
     * that the process doesn't time out. */
    xTaskGetTickCount_IgnoreAndReturn( xDHCPData.xDHCPTxTime + xDHCPData.xDHCPTxPeriod );
    /* For DHCP we need random numbers, make it pass. */
    //xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );
    /* Closing the DHCP socket. */
    //vSocketClose_ExpectAndReturn( xDHCPSocket, 0 );
    /* Ignore the call to this function. */
    //vARPSendGratuitous_Ignore();
    
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingOffer );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eWaitingOffer, xDHCPData.eDHCPState );
    /*************************************************************************/
    #endif
    
}







































