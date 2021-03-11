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

#include "FreeRTOS_DHCP.h"

#include "FreeRTOS_DHCP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

extern Socket_t xDHCPSocket;
extern DHCPData_t xDHCPData;

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
    
    /*************************************************************************/
    /* Test resetting DHCP state machine, but make the expected state
     * different than the current one. */
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
     * different than the current one. */
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
     * different than the current one. */
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
     * different than the current one. */
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
     * different than the current one. */
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
    
}
