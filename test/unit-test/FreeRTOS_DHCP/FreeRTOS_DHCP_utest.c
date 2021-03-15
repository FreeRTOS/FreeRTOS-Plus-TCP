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

void test_vDHCPProcess(void)
{
    BaseType_t xReset;
    eDHCPState_t eExpectedState;
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue;

    #if 1
    /*************************************************************************/
    /* Test resetting DHCP state machine, but make the expected state
     * different than the current one. The expected state should be ignored
     * since the DHCP state machine is being reset.*/
    /* Make sure that DHCP socket is created. */
    xDHCPSocket = &xTestSocket;
    xDHCPData.eDHCPState = eSendDHCPRequest;
    xApplicationGetRandomNumber_ExpectAndReturn( &(xDHCPData.ulTransactionId), pdTRUE );
    vIPReloadDHCPTimer_Ignore();
    vDHCPProcess( pdTRUE, eWaitingSendFirstDiscover );
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
    /*************************************************************************/

    /*************************************************************************/
    /* Test resetting DHCP state machine, but make the expected state
     * different than the current one. The expected state should be ignored
     * since the DHCP state machine is being reset.*/
    /* Make sure that DHCP socket is created. */
    xDHCPSocket = &xTestSocket;
    xDHCPData.eDHCPState = eSendDHCPRequest;
    /* Make random number generation fail. */
    xApplicationGetRandomNumber_ExpectAndReturn( &(xDHCPData.ulTransactionId), pdFALSE );
    vDHCPProcess( pdTRUE, eWaitingSendFirstDiscover );
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
    /*************************************************************************/

    /*************************************************************************/
    /* Test resetting DHCP state machine, but make the expected state
     * different than the current one. The expected state should be ignored
     * since the DHCP state machine is being reset.*/
    /* Make sure that DHCP socket is not created. */
    xDHCPSocket = NULL;
    xDHCPData.eDHCPState = eSendDHCPRequest;
    /* Make random number generation succeeds. */
    xApplicationGetRandomNumber_ExpectAndReturn( &(xDHCPData.ulTransactionId), pdTRUE );
    FreeRTOS_socket_ExpectAndReturn(FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP,FREERTOS_INVALID_SOCKET);
    vIPReloadDHCPTimer_Ignore();
    vDHCPProcess( pdTRUE, eWaitingSendFirstDiscover );
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
    /* Make sure that DHCP socket is still NULL since socket creation failed. */
    TEST_ASSERT_EQUAL( NULL, xDHCPSocket );
    /*************************************************************************/
    
    /*************************************************************************/
    /* Test resetting DHCP state machine, but make the expected state
     * different than the current one. The expected state should be ignored
     * since the DHCP state machine is being reset.*/
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = NULL;
    xDHCPData.eDHCPState = eSendDHCPRequest;
    /* Make sure that the random number generation succeeds. */
    xApplicationGetRandomNumber_ExpectAndReturn( &(xDHCPData.ulTransactionId), pdTRUE );
    FreeRTOS_socket_ExpectAndReturn(FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP,&xTestSocket);
    FreeRTOS_setsockopt_IgnoreAndReturn( pdPASS );
    /* Make sure that binding fails. Return anything except zero. */
    vSocketBind_IgnoreAndReturn(pdTRUE);
    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );
    vDHCPProcess( pdTRUE, eWaitingSendFirstDiscover );
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
    /* Make sure that DHCP socket is still NULL since binding failed. */
    TEST_ASSERT_EQUAL( NULL, xDHCPSocket );
    /*************************************************************************/
    
    /*************************************************************************/
    /* Test resetting DHCP state machine, but make the expected state
     * different than the current one. The expected state should be ignored
     * since the DHCP state machine is being reset.*/
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = NULL;
    xDHCPData.eDHCPState = eSendDHCPRequest;
    /* Make sure that the random number generation succeeds. */
    xApplicationGetRandomNumber_ExpectAndReturn( &(xDHCPData.ulTransactionId), pdTRUE );
    FreeRTOS_socket_ExpectAndReturn(FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP,&xTestSocket);
    FreeRTOS_setsockopt_IgnoreAndReturn( pdPASS );
    /* Make sure that binding succeeds. */
    vSocketBind_IgnoreAndReturn(0);
    vDHCPProcess( pdTRUE, eWaitingSendFirstDiscover );
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
    /* Make sure that DHCP socket is allocated since all socket related steps
     * succeeded. */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /*************************************************************************/
    
    /*************************************************************************/
    /* Test resetting DHCP state machine, and provide the correct expected
     * state. The expected state should be ignored since the DHCP state
     * machine is being reset. */
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = NULL;
    xDHCPData.eDHCPState = eSendDHCPRequest;
    /* Make sure that the random number generation succeeds. */
    xApplicationGetRandomNumber_ExpectAndReturn( &(xDHCPData.ulTransactionId), pdTRUE );
    FreeRTOS_socket_ExpectAndReturn(FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP,&xTestSocket);
    FreeRTOS_setsockopt_IgnoreAndReturn( pdPASS );
    /* Make sure that binding succeeds. */
    vSocketBind_IgnoreAndReturn(0);
    vDHCPProcess( pdTRUE, eInitialWait );
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
    /* Make sure that DHCP socket is allocated since all socket related steps
     * succeeded. */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPSocket );
    /*************************************************************************/
    
    /*************************************************************************/
    /* Test without resetting DHCP state machine, and do not provide the
     * expected state. This should cause the state machine to detect an
     * error. */
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = NULL;
    xDHCPData.eDHCPState = eSendDHCPRequest;
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eInitialWait );
    /* Since DHCP state machine should not process this, make sure that the
     * state is unchanged. */
    TEST_ASSERT_EQUAL( eSendDHCPRequest, xDHCPData.eDHCPState );
    /* Make sure that DHCP socket is still NULL */
    TEST_ASSERT_EQUAL( NULL, xDHCPSocket );
    /*************************************************************************/
    
    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. */
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = NULL;
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    /* Return anything else than eDHCPContinue and eDHCPUseDefaults. */
    xApplicationDHCPHook_ExpectAndReturn( eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, eDHCPContinue+eDHCPUseDefaults+10 );
    /* Make sure that the code disables the DHCP timer. */
    vIPSetDHCPTimerEnableState_Expect( pdFALSE );
    /* Make sure that since DHCP failed, the code tries to enable the
     * network. */
    vIPNetworkUpCalls_Ignore();
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xDHCPData.eDHCPState );
    /* Make sure that DHCP socket is still NULL */
    TEST_ASSERT_EQUAL( NULL, xDHCPSocket );
    /* Make sure that values are copied over. */
    TEST_ASSERT_EQUAL_MEMORY( &( xNetworkAddressing ), &( xDefaultAddressing ), sizeof( xNetworkAddressing ) );
    /*************************************************************************/
    
    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. */
    /* Make sure that DHCP socket is not created */
    xDHCPSocket = NULL;
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    /* Return eDHCPContinue. */
    xApplicationDHCPHook_ExpectAndReturn( eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, eDHCPContinue );
    /* Make sure that the code disables the DHCP timer. */
    vIPSetDHCPTimerEnableState_Expect( pdFALSE );
    /* Make sure that since DHCP failed, the code tries to enable the
     * network. */
    vIPNetworkUpCalls_Ignore();
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xDHCPData.eDHCPState );
    /* Make sure that DHCP socket is still NULL */
    TEST_ASSERT_EQUAL( NULL, xDHCPSocket );
 
    /*************************************************************************/

    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. */
    /* Make sure that DHCP socket is created */
    xDHCPSocket = &xTestSocket;
    /* This should be changed. Tested later. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x12345678;
    /* Time value to be stored in the DHCP state machine. */
    xTimeValue = 1234;
    
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    /* Return eDHCPContinue. */
    xApplicationDHCPHook_ExpectAndReturn( eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, eDHCPContinue );
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    
    /* Returning NULL will mean the prvSendDHCPDiscover fail. */
    pxGetNetworkBufferWithDescriptor_IgnoreAndReturn(NULL);
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
    /*************************************************************************/
    #endif
    
    /*************************************************************************/
    /* Test without resetting DHCP state machine, and provide the expected
     * state. */
    /* Make sure that DHCP socket is created */
    xDHCPSocket = &xTestSocket;
    /* This should be changed. Tested later. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x12345678;
    /* Time value to be stored in the DHCP state machine. */
    xTimeValue = 1234;
    
    xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    /* Return eDHCPContinue. */
    xApplicationDHCPHook_ExpectAndReturn( eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress, eDHCPContinue );
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    
    /* Returning NULL will mean the prvSendDHCPDiscover fail. */
    pxGetNetworkBufferWithDescriptor_IgnoreAndReturn(NULL);
    /* Do not reset the state machine. */
    vDHCPProcess( pdFALSE, eWaitingSendFirstDiscover );
    /* Since DHCP state machine should not process this, make sure that the
     * state shows that. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xDHCPData.eDHCPState );
    /*************************************************************************/


}







































