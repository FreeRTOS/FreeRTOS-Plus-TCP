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
#include "mock_list_macros.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_TCP_WIN.h"

/* Private includes. */
#include "mock_FreeRTOS_TCP_IP_StateHandling.h"
#include "mock_FreeRTOS_TCP_IP_utils.h"
#include "mock_FreeRTOS_TCP_IP_Reception.h"
#include "mock_FreeRTOS_TCP_IP_TimerWork.h"
#include "mock_NetworkBufferManagement.h"

#include "mock_FreeRTOS_IP_Private.h"

#include "FreeRTOS_TCP_IP.h"

#include "FreeRTOS_TCP_IP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/*
 * @brief: Call the function with a NULL socket.
 */
void test_vSocketCloseNextTime_NULLSocket( void )
{
    vSocketCloseNextTime( NULL );
}

/*
 * @brief Call the function with a non-NULL socket.
 */
void test_vSocketCloseNextTime_NonNULLSocket( void )
{
    FreeRTOS_Socket_t xLocalSocket;

    vSocketCloseNextTime( &xLocalSocket );
}

/*
 * @brief Call the function twice with different
 *       sockets so that a call to vSocketClose is made.
 */
void test_vSocketCloseNextTime_NonNULLSocket_CallTwice_DifferentSockets( void )
{
    uintptr_t ulSocketAddr = 0x1234;

    /* This is a stateful function, clean it up. */
    vSocketClose_ExpectAnyArgsAndReturn( NULL );
    vSocketCloseNextTime( NULL );

    /* The actual test. */

    vSocketCloseNextTime( ( FreeRTOS_Socket_t * ) ulSocketAddr );

    /* Expect this to be called with previous socket value. */
    vSocketClose_ExpectAndReturn( ( FreeRTOS_Socket_t * ) ulSocketAddr, NULL );

    /* Call the function with a different socket (essentially a different address). */
    vSocketCloseNextTime( ( FreeRTOS_Socket_t * ) ( ulSocketAddr + 10 ) );
}

/*
 * @brief Call the function twice with same
 *       socket so that a call to vSocketClose is not made.
 */
void test_vSocketCloseNextTime_NonNULLSocket_CallTwice_SameSocket( void )
{
    uintptr_t ulSocketAddr = 0x4321;

    /* This is a stateful function, clean it up. */
    vSocketClose_ExpectAnyArgsAndReturn( NULL );
    vSocketCloseNextTime( NULL );

    /* Now the actual test. */

    vSocketCloseNextTime( ( FreeRTOS_Socket_t * ) ulSocketAddr );
    vSocketCloseNextTime( ( FreeRTOS_Socket_t * ) ulSocketAddr );
}

void test_xTCPSocketCheck_NotEstablishedButSYNTxStreamNULL_ErrorReturned( void )
{
    FreeRTOS_Socket_t xLocalSocket;
    BaseType_t xReturn = -0x12;
    BaseType_t xResult;

    /* The socket is still not in established state. */
    xLocalSocket.u.xTCP.ucTCPState = eCONNECT_SYN;
    xLocalSocket.u.xTCP.txStream = NULL;

    xLocalSocket.u.xTCP.pxAckMessage = NULL;

    /* Return value doesn't matter since it is going to be ignored. */
    prvTCPSendPacket_ExpectAndReturn( &xLocalSocket, 0 );

    /* Return value doesn't matter since it is going to be ignored. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

    prvTCPStatusAgeCheck_ExpectAndReturn( &xLocalSocket, xReturn );

    xResult = xTCPSocketCheck( &xLocalSocket );

    TEST_ASSERT_EQUAL( xResult, xReturn );
}

void test_xTCPSocketCheck_NotEstablishedTxStreamNonNULL_ErrorReturned( void )
{
    FreeRTOS_Socket_t xLocalSocket;
    BaseType_t xReturn = -0x12;
    BaseType_t xResult;

    /* The socket is still not in established state. */
    xLocalSocket.u.xTCP.ucTCPState = eSYN_RECEIVED;
    /* Anything except NULL */
    xLocalSocket.u.xTCP.txStream = NULL + 1;
    xLocalSocket.u.xTCP.pxAckMessage = NULL;

    /* Return value doesn't matter since it is going to be ignored. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

    prvTCPStatusAgeCheck_ExpectAndReturn( &xLocalSocket, xReturn );

    xResult = xTCPSocketCheck( &xLocalSocket );

    TEST_ASSERT_EQUAL( xResult, xReturn );
}

void test_xTCPSocketCheck_EstablishedTxStreamNULL_ErrorReturned( void )
{
    FreeRTOS_Socket_t xLocalSocket;
    BaseType_t xReturn = -0x12;
    BaseType_t xResult;

    /* The socket is still not in established state. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED;
    xLocalSocket.u.xTCP.txStream = NULL;

    xLocalSocket.u.xTCP.pxAckMessage = NULL;

    /* Return value doesn't matter since it is going to be ignored. */
    prvTCPSendPacket_ExpectAndReturn( &xLocalSocket, 0 );

    /* Return value doesn't matter since it is going to be ignored. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

    prvTCPStatusAgeCheck_ExpectAndReturn( &xLocalSocket, xReturn );

    xResult = xTCPSocketCheck( &xLocalSocket );

    TEST_ASSERT_EQUAL( xResult, xReturn );
}

void test_xTCPSocketCheck_EstablishedTxStreamNonNULL_ErrorReturned( void )
{
    FreeRTOS_Socket_t xLocalSocket;
    BaseType_t xReturn = -0x12;
    BaseType_t xResult;

    /* The socket is in established state. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED;
    /* Anything except NULL */
    xLocalSocket.u.xTCP.txStream = NULL + 1;

    xLocalSocket.u.xTCP.pxAckMessage = NULL;

    /* Since the connection is established and the Tx stream is non-NULL,
     * so add it for transmission. */
    prvTCPAddTxData_Expect( &xLocalSocket );

    /* Return value doesn't matter since it is going to be ignored. */
    prvTCPSendPacket_ExpectAndReturn( &xLocalSocket, 0 );

    /* Return value doesn't matter since it is going to be ignored. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

    prvTCPStatusAgeCheck_ExpectAndReturn( &xLocalSocket, xReturn );

    xResult = xTCPSocketCheck( &xLocalSocket );

    TEST_ASSERT_EQUAL( xResult, xReturn );
}

void test_xTCPSocketCheck_NonNULLACKMsg_UserShutdown( void )
{
    FreeRTOS_Socket_t xLocalSocket;
    BaseType_t xReturn = -0x12;
    BaseType_t xResult;

    /* The socket is still not in established state. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED - 1;
    /* Tx stream is NULL. */
    xLocalSocket.u.xTCP.txStream = NULL;

    /* Non-NULL Ack message. */
    xLocalSocket.u.xTCP.pxAckMessage = NULL + 1;
    /* User wants a shutdown. */
    xLocalSocket.u.xTCP.bits.bUserShutdown = pdTRUE_UNSIGNED;

    /* Expect the network buffer to be released. */
    vReleaseNetworkBufferAndDescriptor_Expect( xLocalSocket.u.xTCP.pxAckMessage );

    /* Return value doesn't matter since it is going to be ignored. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

    prvTCPStatusAgeCheck_ExpectAndReturn( &xLocalSocket, xReturn );

    xResult = xTCPSocketCheck( &xLocalSocket );

    TEST_ASSERT_EQUAL( xResult, xReturn );
    TEST_ASSERT_EQUAL( NULL, xLocalSocket.u.xTCP.pxAckMessage );
}

void test_xTCPSocketCheck_NonNULLACKMsg_NoUserShutdown_ClosedConn( void )
{
    FreeRTOS_Socket_t xLocalSocket;
    BaseType_t xReturn = -0x12;
    BaseType_t xResult;

    /* The socket is still not in established state. */
    xLocalSocket.u.xTCP.ucTCPState = eCLOSED;
    /* Tx stream is NULL. */
    xLocalSocket.u.xTCP.txStream = NULL;

    /* Non-NULL Ack message. */
    xLocalSocket.u.xTCP.pxAckMessage = NULL + 1;
    /* User wants a shutdown. */
    xLocalSocket.u.xTCP.bits.bUserShutdown = pdFALSE_UNSIGNED;

    /* Return a value greater than 1. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 2 );

    /* Expect the network buffer to be released. */
    vReleaseNetworkBufferAndDescriptor_Expect( xLocalSocket.u.xTCP.pxAckMessage );

    xResult = xTCPSocketCheck( &xLocalSocket );

    TEST_ASSERT_EQUAL( 0, xResult );
    TEST_ASSERT_EQUAL( NULL, xLocalSocket.u.xTCP.pxAckMessage );
}

void test_xTCPSocketCheck_NonNULLACKMsg_NoUserShutdown_NotClosedConn_NoLogging( void )
{
    FreeRTOS_Socket_t xLocalSocket;
    BaseType_t xReturn = -0x12;
    BaseType_t xResult;

    xTCPWindowLoggingLevel = 0;

    /* Try all states except the closed connection. */
    for( uint8_t i = eCLOSED + 1; i <= eTIME_WAIT; i++ )
    {
        /* The socket is still not in established state. */
        xLocalSocket.u.xTCP.ucTCPState = i;
        /* Tx stream is NULL. This prevents a call to prvTCPAddTxData. */
        xLocalSocket.u.xTCP.txStream = NULL;

        /* Non-NULL Ack message. */
        xLocalSocket.u.xTCP.pxAckMessage = NULL + 1;
        /* User wants a shutdown. */
        xLocalSocket.u.xTCP.bits.bUserShutdown = pdFALSE_UNSIGNED;

        prvTCPReturnPacket_Expect( &xLocalSocket, xLocalSocket.u.xTCP.pxAckMessage, ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER, ipconfigZERO_COPY_TX_DRIVER );

        /* Return a value greater than 1. */
        prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 2 );

        xResult = xTCPSocketCheck( &xLocalSocket );

        TEST_ASSERT_EQUAL( 0, xResult );
        TEST_ASSERT_EQUAL( NULL, xLocalSocket.u.xTCP.pxAckMessage );
    }
}

void test_xTCPSocketCheck_NonNULLACKMsg_NoUserShutdown_NotClosedConn_LoggingEnabled( void )
{
    FreeRTOS_Socket_t xLocalSocket;
    BaseType_t xReturn = -0x12;
    BaseType_t xResult;

    xTCPWindowLoggingLevel = 2;

    /* Try all states except the closed connection. */
    for( uint8_t i = eCLOSED + 1; i <= eTIME_WAIT; i++ )
    {
        /* The socket is still not in established state. */
        xLocalSocket.u.xTCP.ucTCPState = i;
        /* Tx stream is NULL. This prevents a call to prvTCPAddTxData. */
        xLocalSocket.u.xTCP.txStream = NULL;

        /* Non-NULL Ack message. */
        xLocalSocket.u.xTCP.pxAckMessage = NULL + 1;
        /* User wants a shutdown. */
        xLocalSocket.u.xTCP.bits.bUserShutdown = pdFALSE_UNSIGNED;

        prvTCPReturnPacket_Expect( &xLocalSocket, xLocalSocket.u.xTCP.pxAckMessage, ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER, ipconfigZERO_COPY_TX_DRIVER );

        /* Return a value greater than 1. */
        prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 1 );

        if( ( xLocalSocket.u.xTCP.ucTCPState >= ( uint8_t ) eESTABLISHED ) ||
            ( xLocalSocket.u.xTCP.ucTCPState == ( uint8_t ) eCONNECT_SYN ) )
        {
            /* Return value doesn't matter since it is going to be ignored. */
            prvTCPSendPacket_ExpectAndReturn( &xLocalSocket, 0 );
        }

        /* Return value doesn't matter since it is going to be ignored. */
        prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

        prvTCPStatusAgeCheck_ExpectAndReturn( &xLocalSocket, xReturn );

        xResult = xTCPSocketCheck( &xLocalSocket );

        TEST_ASSERT_EQUAL( xReturn, xResult );
        TEST_ASSERT_EQUAL( NULL, xLocalSocket.u.xTCP.pxAckMessage );
    }
}

void test_xProcessReceivedTCPPacket_CatchAssert( void )
{
    NetworkBufferDescriptor_t xNetDescriptor;

    xNetDescriptor.pucEthernetBuffer = NULL;

    /* Network buffer should not be NULL. */
    catch_assert( xProcessReceivedTCPPacket( NULL ) );
    /* The ethernet buffer cannot be NULL. */
    catch_assert( xProcessReceivedTCPPacket( &xNetDescriptor ) );
}

void test_xProcessReceivedTCPPacket_MinimumPacketSize( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;

    pxNetworkBuffer = &xNetDescriptor;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];

    /* Any non-NULL value. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    for( uint32_t i = 0; i < ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER ); i++ )
    {
        pxNetworkBuffer->xDataLength = i;

        xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

        /* All the packet data lengths smaller than the acceptable length should be rejected. */
        TEST_ASSERT_EQUAL( pdFAIL, xResult );
    }
}

void test_xProcessReceivedTCPPacket_NoSocket_IncorrectFlags1( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;

    pxNetworkBuffer = &xNetDescriptor;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;

    /* Any non-NULL value. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, NULL );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Since socket is not found, this test should fail. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_NoSocket_IncorrectFlags2( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;

    pxNetworkBuffer = &xNetDescriptor;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;

    /* Any non-NULL value. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_ACK;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, NULL );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Since socket is not found, this test should fail. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_NoSocket_CorrectFlags( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;

    pxNetworkBuffer = &xNetDescriptor;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;

    /* Any non-NULL value. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_URG;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, NULL );

    /* The return value doesn't matter since it is ignored. */
    prvTCPSendReset_ExpectAndReturn( pxNetworkBuffer, 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Since socket is not found, this test should fail. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_SocketNotConnected_CorrectFlags( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;

    pxNetworkBuffer = &xNetDescriptor;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    /* Any non-NULL value. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_URG;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket disconnected. */
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdFALSE );

    /* The return value doesn't matter since it is ignored. */
    prvTCPSendReset_ExpectAndReturn( pxNetworkBuffer, 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Since socket is not found, this test should fail. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_SocketConnected_CorrectFlags_NoOpt_NoReturn( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_URG;

    /* No options. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = 0;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Expect the socket timers to be updated since the connection is established. */
    prvTCPTouchSocket_Expect( &xLocalSocket );

    /* Since the connection is established, expect this call. Also, return a 0 saying nothing to return. */
    prvTCPHandleState_ExpectAndReturn( &xLocalSocket, NULL, 0 );
    prvTCPHandleState_IgnoreArg_ppxNetworkBuffer();

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    /* Return value is ignored. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Connection established. Processing should be successful. */
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    /* Test whether the TCP header is copied over. */
    TEST_ASSERT_EQUAL_MEMORY( &( ucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ),
                              &( xLocalSocket.u.xTCP.xPacket.u.ucLastPacket[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ),
                              ipSIZE_OF_TCP_HEADER );
}

int32_t stub1( FreeRTOS_Socket_t * Socket,
               NetworkBufferDescriptor_t ** ppxBuffer,
               int callbacks )
{
    *ppxBuffer = NULL;

    return 0;
}

void test_xProcessReceivedTCPPacket_SocketConnected_CorrectFlags_NoOpt_Return_( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_URG;

    /* No options. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = 0;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Expect the socket timers to be updated since the connection is established. */
    prvTCPTouchSocket_Expect( &xLocalSocket );

    /* Since the connection is established, expect this call. Also, return a 0 saying nothing to return. */
    prvTCPHandleState_ExpectAndReturn( &xLocalSocket, NULL, 1 );
    prvTCPHandleState_IgnoreArg_ppxNetworkBuffer();

    /* Ignore the second parameter. The return value is ignored. */
    prvTCPSendRepeated_Stub( stub1 );

    /* Return value is ignored. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Connection established. Processing should be successful. */
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    /* Test whether the TCP header is copied over. */
    TEST_ASSERT_EQUAL_MEMORY( &( ucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ),
                              &( xLocalSocket.u.xTCP.xPacket.u.ucLastPacket[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ),
                              ipSIZE_OF_TCP_HEADER );
}

void test_xProcessReceivedTCPPacket_SocketConnected_CorrectFlags_OptionsPresent_NoReturn( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_URG;

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Expect the socket timers to be updated since the connection is established. */
    prvTCPTouchSocket_Expect( &xLocalSocket );

    /* Expect the options to be processed. */
    prvCheckOptions_Expect( &xLocalSocket, pxNetworkBuffer );

    /* Since the connection is established, expect this call. Also, return a 0 saying nothing to return. */
    prvTCPHandleState_ExpectAndReturn( &xLocalSocket, NULL, 0 );
    prvTCPHandleState_IgnoreArg_ppxNetworkBuffer();

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    /* Return value is ignored. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Connection established. Processing should be successful. */
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    /* Test whether the TCP header is copied over. */
    TEST_ASSERT_EQUAL_MEMORY( &( ucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ),
                              &( xLocalSocket.u.xTCP.xPacket.u.ucLastPacket[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ),
                              ipSIZE_OF_TCP_HEADER );
}

void test_xProcessReceivedTCPPacket_SocketConnected_CorrectFlags_OptionsPresent_ReturnToPeer( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    /* Make sure this is same as the data in ethernet buffer as that will
     * overwrite the TCP header. */
    const uint32_t ulWindowSize = 0xAAAA;

    /* Make the window scale is set. */
    xLocalSocket.u.xTCP.ucPeerWinScaleFactor = 2;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_URG;

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Expect the socket timers to be updated since the connection is established. */
    prvTCPTouchSocket_Expect( &xLocalSocket );

    /* Expect the options to be processed. */
    prvCheckOptions_Expect( &xLocalSocket, pxNetworkBuffer );

    /* Since the connection is established, expect this call. Also, return a 0 saying nothing to return. */
    prvTCPHandleState_ExpectAndReturn( &xLocalSocket, NULL, 1 );
    prvTCPHandleState_IgnoreArg_ppxNetworkBuffer();

    /* Expect the message to be sent to the peer. Return valus is ignored. */
    prvTCPSendRepeated_ExpectAndReturn( &xLocalSocket, NULL, 0 );
    prvTCPSendRepeated_IgnoreArg_ppxNetworkBuffer();

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    /* Return value is ignored. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Connection established. Processing should be successful. */
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    /* Test whether the TCP header is copied over. */
    TEST_ASSERT_EQUAL_MEMORY( &( ucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ),
                              &( xLocalSocket.u.xTCP.xPacket.u.ucLastPacket[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ),
                              ipSIZE_OF_TCP_HEADER );
    /* Make sure that the window size is updated. */
    TEST_ASSERT_EQUAL( ulWindowSize << xLocalSocket.u.xTCP.ucPeerWinScaleFactor, xLocalSocket.u.xTCP.ulWindowSize );
}

void test_xProcessReceivedTCPPacket_SocketDisconnected_CorrectFlags_OptionsPresent_ReturnToPeer( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eSYN_RECEIVED;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Expect the socket timers to be updated since the connection is established. */
    prvTCPTouchSocket_Expect( &xLocalSocket );

    /* Expect the options to be processed. */
    prvCheckOptions_Expect( &xLocalSocket, pxNetworkBuffer );

    /* Since the connection is established, expect this call. Also, return a 0 saying nothing to return. */
    prvTCPHandleState_ExpectAndReturn( &xLocalSocket, NULL, 1 );
    prvTCPHandleState_IgnoreArg_ppxNetworkBuffer();

    /* Expect the message to be sent to the peer. Return valus is ignored. */
    prvTCPSendRepeated_ExpectAndReturn( &xLocalSocket, NULL, 0 );
    prvTCPSendRepeated_IgnoreArg_ppxNetworkBuffer();

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    /* Return value is ignored. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Connection established. Processing should be successful. */
    TEST_ASSERT_EQUAL( pdPASS, xResult );
    /* Test whether the TCP header is copied over. */
    TEST_ASSERT_EQUAL_MEMORY( &( ucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ),
                              &( xLocalSocket.u.xTCP.xPacket.u.ucLastPacket[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ),
                              ipSIZE_OF_TCP_HEADER );
}

void test_xProcessReceivedTCPPacket_SocketListening_SYNFlag( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eTCP_LISTEN;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Expect the socket and reutrn NULL (maybe due to a malloc failure). */
    prvHandleListen_ExpectAndReturn( &xLocalSocket, pxNetworkBuffer, NULL );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Check the output. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_SocketListening_SYNFlag_ProperSockReturned( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eTCP_LISTEN;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Expect the socket and return the current socket. */
    prvHandleListen_ExpectAndReturn( &xLocalSocket, pxNetworkBuffer, &xLocalSocket );

    /* Expect the socket timers to be updated since the connection is established. */
    prvTCPTouchSocket_Expect( &xLocalSocket );

    /* Expect the options to be processed. */
    prvCheckOptions_Expect( &xLocalSocket, pxNetworkBuffer );

    /* Since the connection is established, expect this call. Also, return a 0 saying nothing to return. */
    prvTCPHandleState_ExpectAndReturn( &xLocalSocket, NULL, 1 );
    prvTCPHandleState_IgnoreArg_ppxNetworkBuffer();

    /* Expect the message to be sent to the peer. Return valus is ignored. */
    prvTCPSendRepeated_ExpectAndReturn( &xLocalSocket, NULL, 0 );
    prvTCPSendRepeated_IgnoreArg_ppxNetworkBuffer();

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    /* Return value is ignored. */
    prvTCPNextTimeout_ExpectAndReturn( &xLocalSocket, 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Connection established. Processing should be successful. */
    TEST_ASSERT_EQUAL( pdPASS, xResult );
}

void test_xProcessReceivedTCPPacket_SocketListening_NotSYNFlag( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_URG;

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eTCP_LISTEN;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Expect reset due to a RST flag. */
    prvTCPSendReset_ExpectAndReturn( pxNetworkBuffer, 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Check the output. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_SocketListening_RSTFlag( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eTCP_LISTEN;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Check the connection. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_SocketConnected_RSTFlag_1( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Ignore the arguments and return various values. */
    xSequenceGreaterThan_ExpectAnyArgsAndReturn( 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Check the connection. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_SocketConnected_RSTFlag_2( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Ignore the arguments and return various values. */
    xSequenceGreaterThan_ExpectAnyArgsAndReturn( 1 );
    xSequenceLessThan_ExpectAnyArgsAndReturn( 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Check the connection. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_SocketConnected_RSTFlag_3_SeqWithinRange( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Ignore the arguments and return various values. */
    xSequenceGreaterThan_ExpectAnyArgsAndReturn( 1 );
    xSequenceLessThan_ExpectAnyArgsAndReturn( 1 );

    /* Since the sequence number is in range, we should expect this call. The
     * return value is ignored. */
    prvTCPSendChallengeAck_ExpectAndReturn( pxNetworkBuffer, 0 );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Check the connection. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_SocketConnected_RSTFlag_SeqNumMatch( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;
    uint32_t ulSequenceNumber = 0x123AB;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;
    pxProtocolHeaders->xTCPHeader.ulSequenceNumber = FreeRTOS_htonl( ulSequenceNumber );

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Make the sequence numbers match */
    xLocalSocket.u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;
    vTCPStateChange_Expect( &xLocalSocket, eCLOSED );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Check the connection. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_SocketeCONNECTSYN_RSTFlag( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eCONNECT_SYN;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Check the connection. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_SocketeCONNECTSYN_RSTFlag_RFC5961( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;
    uint32_t ulAckNum = 0x1212AB;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;
    pxProtocolHeaders->xTCPHeader.ulAckNr = FreeRTOS_htonl( ulAckNum );

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eCONNECT_SYN;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    /* Expect the seq num to match. */
    xLocalSocket.u.xTCP.xTCPWindow.ulOurSequenceNumber = ulAckNum - 1;
    vTCPStateChange_Expect( &xLocalSocket, eCLOSED );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Check the connection. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_xProcessReceivedTCPPacket_SocketeConnected_SYNFlag( void )
{
    NetworkBufferDescriptor_t xNetDescriptor, * pxNetworkBuffer;
    BaseType_t xResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    uint32_t ulLocalIP = 0x1234, ulRemoteIP = 0x3241;
    uint16_t xLocalPort = 0x12, xRemotePort = 0x21;
    ProtocolHeaders_t * pxProtocolHeaders;
    FreeRTOS_Socket_t xLocalSocket;
    uint32_t ulAckNum = 0x1212AB;

    pxNetworkBuffer = &xNetDescriptor;

    /* Add the buffer. */
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    /* Add data to the buffer which can be verified. */
    memset( ucEthernetBuffer, 0xAA, ipconfigTCP_MSS );

    /* Get the IP header and fill the struct. */
    pxIPHeader = ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_ntohl( ulLocalIP );
    pxIPHeader->ulSourceIPAddress = FreeRTOS_ntohl( ulRemoteIP );

    /* Get the protocol header and fill the struct. */
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxProtocolHeaders->xTCPHeader.usDestinationPort = FreeRTOS_ntohs( xLocalPort );
    pxProtocolHeaders->xTCPHeader.usSourcePort = FreeRTOS_ntohs( xRemotePort );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;
    pxProtocolHeaders->xTCPHeader.ulAckNr = FreeRTOS_htonl( ulAckNum );

    /* Options present. */
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = tcpTCP_OFFSET_LENGTH_BITS;

    pxNetworkBuffer->xDataLength = ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER );

    pxTCPSocketLookup_ExpectAndReturn( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort, &xLocalSocket );

    /* Make the socket connected. */
    xLocalSocket.u.xTCP.ucTCPState = eESTABLISHED;
    prvTCPSocketIsActive_ExpectAndReturn( xLocalSocket.u.xTCP.ucTCPState, pdTRUE );

    xResult = xProcessReceivedTCPPacket( pxNetworkBuffer );

    /* Check the output. */
    TEST_ASSERT_EQUAL( pdFAIL, xResult );
}

void test_FreeRTOS_GetTCPStateName( void )
{
    static const char * const pcLocalStateNames[] =
    {
        "eCLOSED",
        "eTCP_LISTEN",
        "eCONNECT_SYN",
        "eSYN_FIRST",
        "eSYN_RECEIVED",
        "eESTABLISHED",
        "eFIN_WAIT_1",
        "eFIN_WAIT_2",
        "eCLOSE_WAIT",
        "eCLOSING",
        "eLAST_ACK",
        "eTIME_WAIT",
        "eUNKNOWN"
    };

    size_t uxTotalStates = 13;

    for( uint8_t i = 0; i < 100; i++ )
    {
        if( i < uxTotalStates )
        {
            TEST_ASSERT_EQUAL_STRING( pcLocalStateNames[ i ], FreeRTOS_GetTCPStateName( i ) );
        }
        else
        {
            TEST_ASSERT_EQUAL_STRING( pcLocalStateNames[ uxTotalStates - 1 ], FreeRTOS_GetTCPStateName( i ) );
        }
    }

    for( uint8_t i = 0; i < 100; i++ )
    {
        static uint64_t temp = 0;
        temp--;

        TEST_ASSERT_EQUAL_STRING( pcLocalStateNames[ uxTotalStates - 1 ], FreeRTOS_GetTCPStateName( temp ) );
    }
}

void test_xTCPCheckNewClient_NotFound( void )
{
    FreeRTOS_Socket_t xLocalSocket1, xLocalSocket2;
    BaseType_t xResult;
    uint16_t usLocalPort = 0x12AB;
    ListItem_t xLocalList1, xListLocalEnd, xListLocalStart;

    listGET_END_MARKER_ExpectAndReturn( &xBoundTCPSocketsList, &xListLocalEnd );

    listGET_HEAD_ENTRY_ExpectAndReturn( ( ListItem_t * ) &xBoundTCPSocketsList, &xListLocalStart );

    xLocalSocket1.usLocalPort = FreeRTOS_ntohs( usLocalPort );
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &xListLocalStart, usLocalPort );

    /* Get the socket as the owner. */
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xListLocalStart, &xLocalSocket2 );

    listGET_NEXT_ExpectAndReturn( &xListLocalStart, &xListLocalEnd );

    xResult = xTCPCheckNewClient( &xLocalSocket1 );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

void test_xTCPCheckNewClient_Found_NoMatchingBits( void )
{
    FreeRTOS_Socket_t xLocalSocket1, xLocalSocket2;
    BaseType_t xResult;
    uint16_t usLocalPort = 0x12AB;
    ListItem_t xLocalList1, xListLocalEnd, xListLocalStart;

    listGET_END_MARKER_ExpectAndReturn( &xBoundTCPSocketsList, &xListLocalEnd );

    listGET_HEAD_ENTRY_ExpectAndReturn( ( ListItem_t * ) &xBoundTCPSocketsList, &xListLocalStart );

    xLocalSocket1.usLocalPort = FreeRTOS_ntohs( usLocalPort );
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &xListLocalStart, usLocalPort );

    /* Make the protocol as TCP. */
    xLocalSocket2.ucProtocol = FREERTOS_IPPROTO_TCP;
    xLocalSocket2.u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;
    /* Get the socket as the owner. */
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xListLocalStart, &xLocalSocket2 );

    listGET_NEXT_ExpectAndReturn( &xListLocalStart, &xListLocalEnd );

    xResult = xTCPCheckNewClient( &xLocalSocket1 );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

void test_xTCPCheckNewClient_Found_MatchingBits( void )
{
    FreeRTOS_Socket_t xLocalSocket1, xLocalSocket2;
    BaseType_t xResult;
    uint16_t usLocalPort = 0x12AB;
    ListItem_t xLocalList1, xListLocalEnd, xListLocalStart;

    listGET_END_MARKER_ExpectAndReturn( &xBoundTCPSocketsList, &xListLocalEnd );

    listGET_HEAD_ENTRY_ExpectAndReturn( ( ListItem_t * ) &xBoundTCPSocketsList, &xListLocalStart );

    xLocalSocket1.usLocalPort = FreeRTOS_ntohs( usLocalPort );
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &xListLocalStart, usLocalPort );

    /* Make the protocol as TCP. */
    xLocalSocket2.ucProtocol = FREERTOS_IPPROTO_TCP;
    xLocalSocket2.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    /* Get the socket as the owner. */
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xListLocalStart, &xLocalSocket2 );

    xResult = xTCPCheckNewClient( &xLocalSocket1 );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

void test_xTCPCheckNewClient_UnmatchingPort( void )
{
    FreeRTOS_Socket_t xLocalSocket1, xLocalSocket2;
    BaseType_t xResult;
    uint16_t usLocalPort = 0x12AB;
    ListItem_t xLocalList1, xListLocalEnd, xListLocalStart;

    listGET_END_MARKER_ExpectAndReturn( &xBoundTCPSocketsList, &xListLocalEnd );

    listGET_HEAD_ENTRY_ExpectAndReturn( ( ListItem_t * ) &xBoundTCPSocketsList, &xListLocalStart );

    xLocalSocket1.usLocalPort = FreeRTOS_ntohs( usLocalPort );
    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &xListLocalStart, usLocalPort + 1 );

    listGET_NEXT_ExpectAndReturn( &xListLocalStart, &xListLocalEnd );

    xResult = xTCPCheckNewClient( &xLocalSocket1 );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}
