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
#include "mock_StateHandling_list_macros.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_Stream_Buffer.h"

/* Private includes. */
#include "mock_FreeRTOS_TCP_IP_Reception.h"
#include "mock_FreeRTOS_TCP_IP_utils.h"
#include "mock_FreeRTOS_TCP_IP.h"
#include "mock_FreeRTOS_TCP_IP_TimerWork.h"
#include "mock_NetworkBufferManagement.h"

#include "mock_FreeRTOS_IP_Private.h"

#include "FreeRTOS_TCP_IP_StateHandling.h"

#include "FreeRTOS_TCP_IP_StateHandling_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

void test_prvCheckRxData_ReceiveLengthEqualToReportedLen(void)
{
    NetworkBufferDescriptor_t xLocalNetBuffer, * pxNetworkBuffer;
    uint8_t ucLocalBuffer[ipconfigTCP_MSS], *pucRecvData;
    uint8_t ucIntermediateResult = 0;
    int32_t lReceiveLength = 0x123;
    int32_t lLength = 0x123;
    BaseType_t xReturn;
    /* Make this a multiple of 4 and >20. */
    uint8_t lTCPHeaderLength = 20;
    
    pucRecvData = NULL;
    pxNetworkBuffer = &xLocalNetBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                                                                                xIPHeaderSize( pxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    
    /* Map the buffer onto an IPHeader_t struct for easy access to fields. */
    IPHeader_t * pxIPHeader = ( IPHeader_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    
    pxNetworkBuffer->xDataLength = lReceiveLength + ipSIZE_OF_ETH_HEADER;
    pxIPHeader->usLength = FreeRTOS_ntohs( lLength );
    /* The TCP header is represented as 4-byte word lengths in the upper 4 bits. */
    pxTCPHeader->ucTCPOffset = (lTCPHeaderLength/4) <<4;
    
    pxTCPHeader->ucTCPFlags = 0;
    
    xReturn = prvCheckRxData( pxNetworkBuffer, &pucRecvData );
    
    TEST_ASSERT_EQUAL( lReceiveLength - ( lTCPHeaderLength + ipSIZE_OF_IPv4_HEADER ), xReturn );
    TEST_ASSERT_EQUAL( &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                              ipSIZE_OF_IPv4_HEADER +
                                                              ( size_t ) lTCPHeaderLength ] ),
                                                              pucRecvData );
}

void test_prvCheckRxData_ReceiveLengthLessThanReportedLen(void)
{
    NetworkBufferDescriptor_t xLocalNetBuffer, * pxNetworkBuffer;
    uint8_t ucLocalBuffer[ipconfigTCP_MSS], *pucRecvData;
    uint8_t ucIntermediateResult = 0;
    int32_t lReceiveLength = 0x123;
    int32_t lLength = lReceiveLength + 4;
    BaseType_t xReturn;
    /* Make this a multiple of 4 and >20. */
    uint8_t lTCPHeaderLength = 20;
    
    pucRecvData = NULL;
    pxNetworkBuffer = &xLocalNetBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                                                                                xIPHeaderSize( pxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    
    /* Map the buffer onto an IPHeader_t struct for easy access to fields. */
    IPHeader_t * pxIPHeader = ( IPHeader_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    
    pxNetworkBuffer->xDataLength = lReceiveLength + ipSIZE_OF_ETH_HEADER;
    pxIPHeader->usLength = FreeRTOS_ntohs( lLength );
    /* The TCP header is represented as 4-byte word lengths in the upper 4 bits. */
    pxTCPHeader->ucTCPOffset = (lTCPHeaderLength/4) <<4;
    
    pxTCPHeader->ucTCPFlags = 0;
    
    xReturn = prvCheckRxData( pxNetworkBuffer, &pucRecvData );
    
    TEST_ASSERT_EQUAL( lReceiveLength - ( lTCPHeaderLength + ipSIZE_OF_IPv4_HEADER ), xReturn );
    TEST_ASSERT_EQUAL( &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                              ipSIZE_OF_IPv4_HEADER +
                                                              ( size_t ) lTCPHeaderLength ] ),
                                                              pucRecvData );
}

void test_prvCheckRxData_ReceiveLengthGreaterThanReportedLen(void)
{
    NetworkBufferDescriptor_t xLocalNetBuffer, * pxNetworkBuffer;
    uint8_t ucLocalBuffer[ipconfigTCP_MSS], *pucRecvData;
    uint8_t ucIntermediateResult = 0;
    int32_t lReceiveLength = 0x123;
    int32_t lLength = lReceiveLength - 4;
    BaseType_t xReturn;
    /* Make this a multiple of 4 and >20. */
    uint8_t lTCPHeaderLength = 20;
    
    pucRecvData = NULL;
    pxNetworkBuffer = &xLocalNetBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                                                                                xIPHeaderSize( pxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    
    /* Map the buffer onto an IPHeader_t struct for easy access to fields. */
    IPHeader_t * pxIPHeader = ( IPHeader_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    
    pxNetworkBuffer->xDataLength = lReceiveLength + ipSIZE_OF_ETH_HEADER;
    pxIPHeader->usLength = FreeRTOS_ntohs( lLength );
    /* The TCP header is represented as 4-byte word lengths in the upper 4 bits. */
    pxTCPHeader->ucTCPOffset = (lTCPHeaderLength/4) <<4;
    
    pxTCPHeader->ucTCPFlags = 0;
    
    xReturn = prvCheckRxData( pxNetworkBuffer, &pucRecvData );
    
    TEST_ASSERT_EQUAL( lLength - ( lTCPHeaderLength + ipSIZE_OF_IPv4_HEADER ), xReturn );
    TEST_ASSERT_EQUAL( &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                              ipSIZE_OF_IPv4_HEADER +
                                                              ( size_t ) lTCPHeaderLength ] ),
                                                              pucRecvData );
}

void test_prvCheckRxData_ReceiveLengthLessThanTCPLen(void)
{
    NetworkBufferDescriptor_t xLocalNetBuffer, * pxNetworkBuffer;
    uint8_t ucLocalBuffer[ipconfigTCP_MSS], *pucRecvData;
    uint8_t ucIntermediateResult = 0;
    int32_t lReceiveLength = 40 /* 20+20 */ - 2;
    int32_t lLength = lReceiveLength;
    BaseType_t xReturn;
    /* Make this a multiple of 4 and >20. */
    uint8_t lTCPHeaderLength = 20;
    
    pucRecvData = NULL;
    pxNetworkBuffer = &xLocalNetBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                                                                                xIPHeaderSize( pxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    
    /* Map the buffer onto an IPHeader_t struct for easy access to fields. */
    IPHeader_t * pxIPHeader = ( IPHeader_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    
    pxNetworkBuffer->xDataLength = lReceiveLength + ipSIZE_OF_ETH_HEADER;
    pxIPHeader->usLength = FreeRTOS_ntohs( lLength );
    /* The TCP header is represented as 4-byte word lengths in the upper 4 bits. */
    pxTCPHeader->ucTCPOffset = (lTCPHeaderLength/4) <<4;
    
    pxTCPHeader->ucTCPFlags = 0;
    
    xReturn = prvCheckRxData( pxNetworkBuffer, &pucRecvData );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                              ipSIZE_OF_IPv4_HEADER +
                                                              ( size_t ) lTCPHeaderLength ] ),
                                                              pucRecvData );
}

void test_prvCheckRxData_ReceiveLengthEqualTCPLen(void)
{
    NetworkBufferDescriptor_t xLocalNetBuffer, * pxNetworkBuffer;
    uint8_t ucLocalBuffer[ipconfigTCP_MSS], *pucRecvData;
    uint8_t ucIntermediateResult = 0;
    int32_t lReceiveLength = 40 /* 20+20 */;
    int32_t lLength = lReceiveLength;
    BaseType_t xReturn;
    /* Make this a multiple of 4 and >20. */
    uint8_t lTCPHeaderLength = 20;
    
    pucRecvData = NULL;
    pxNetworkBuffer = &xLocalNetBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                                                                                xIPHeaderSize( pxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    
    /* Map the buffer onto an IPHeader_t struct for easy access to fields. */
    IPHeader_t * pxIPHeader = ( IPHeader_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    
    pxNetworkBuffer->xDataLength = lReceiveLength + ipSIZE_OF_ETH_HEADER;
    pxIPHeader->usLength = FreeRTOS_ntohs( lLength );
    /* The TCP header is represented as 4-byte word lengths in the upper 4 bits. */
    pxTCPHeader->ucTCPOffset = (lTCPHeaderLength/4) <<4;
    
    pxTCPHeader->ucTCPFlags = 0; 
    
    xReturn = prvCheckRxData( pxNetworkBuffer, &pucRecvData );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                              ipSIZE_OF_IPv4_HEADER +
                                                              ( size_t ) lTCPHeaderLength ] ),
                                                              pucRecvData );
}

int32_t FreeRTOS_min_int32( int32_t a, int32_t b )
{
    if( a > b )
    {
        return b;
    }
    else
    {
        return a;
    }
}

void test_prvCheckRxData_ReceiveLengthProper_HasURGData(void)
{
    NetworkBufferDescriptor_t xLocalNetBuffer, * pxNetworkBuffer;
    uint8_t ucLocalBuffer[ipconfigTCP_MSS], *pucRecvData;
    uint8_t ucIntermediateResult = 0;
    int32_t lReceiveLength = 0x123;
    int32_t lLength = lReceiveLength;
    BaseType_t xReturn;
    /* Make this a multiple of 4 and >20. */
    uint8_t lTCPHeaderLength = 20;
    uint8_t ucUrgentLen = 21;
    
    pucRecvData = NULL;
    pxNetworkBuffer = &xLocalNetBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                                                                                xIPHeaderSize( pxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    
    /* Map the buffer onto an IPHeader_t struct for easy access to fields. */
    IPHeader_t * pxIPHeader = ( IPHeader_t *) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    
    pxNetworkBuffer->xDataLength = lReceiveLength + ipSIZE_OF_ETH_HEADER;
    pxIPHeader->usLength = FreeRTOS_ntohs( lLength );
    /* The TCP header is represented as 4-byte word lengths in the upper 4 bits. */
    pxTCPHeader->ucTCPOffset = (lTCPHeaderLength/4) <<4;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_URG;
    pxTCPHeader->usUrgent = FreeRTOS_ntohs(ucUrgentLen);
    
    xReturn = prvCheckRxData( pxNetworkBuffer, &pucRecvData );
    
    TEST_ASSERT_EQUAL( lReceiveLength - ( lTCPHeaderLength + ipSIZE_OF_IPv4_HEADER )- ucUrgentLen, xReturn );
    TEST_ASSERT_EQUAL( &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER +
                                                              ipSIZE_OF_IPv4_HEADER +
                                                              ( size_t ) lTCPHeaderLength ] ) + ucUrgentLen,
                                                              pucRecvData );
}



void test_prvHandleEstablished_WorstCase(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    /**/
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    
    pxSocket = &xLocalSocket;
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = 0;
    
    pxSocket->u.xTCP.txStream = NULL;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE_UNSIGNED;
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
}

void test_prvHandleEstablished_TCPFlagACK_WindowReturnZero(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    /**/
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    
    pxSocket = &xLocalSocket;
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 0 );
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x1234;
    
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE_UNSIGNED;
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
}

void test_prvHandleEstablished_TCPFlagACK_TxStreamNULL(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    
    pxSocket = &xLocalSocket;
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
        
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 2 );
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = NULL;
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE_UNSIGNED;
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
}

void test_prvHandleEstablished_TCPFlagACK_WindowReturnNonZero(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    /**/
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    
    pxSocket = &xLocalSocket;
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
        
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 2 );
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x1234;
    
    /* Make stream buffer return nothing. */
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 0 );
    
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE_UNSIGNED;
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
}

void test_prvHandleEstablished_TCPFlagACK_WindowReturnNonZero_StreamBufferSuccess(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    /**/
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    
    pxSocket = &xLocalSocket;
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
        
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 2 );
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x1234;
    
    /* Make stream buffer return something. */
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 1 );
    
    pxSocket->xSelectBits = 0;
    
    pxSocket->u.xTCP.pxHandleSent = NULL;
    
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE_UNSIGNED;
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_NOT_EQUAL( 0, pxSocket->xEventBits & ( ( EventBits_t ) eSOCKET_SEND ) );
}

static int pxHandleSentCount;
static void pxHandleSentFunc( Socket_t xSocket, size_t xLength )
{
    pxHandleSentCount++;
}

void test_prvHandleEstablished_TCPFlagACK_WindowReturnNonZero_StreamBufferSuccess1(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    /**/
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    
    pxSocket = &xLocalSocket;
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
        
    ulTCPWindowTxAck_ExpectAnyArgsAndReturn( 2 );
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x1234;
    
    /* Make stream buffer return something. */
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 1 );
    
    pxSocket->xSelectBits = eSELECT_WRITE;
    
    pxHandleSentCount = 0;
    pxSocket->u.xTCP.pxHandleSent = pxHandleSentFunc;
    
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE_UNSIGNED;
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_NOT_EQUAL( 0, pxSocket->xEventBits & ( ( EventBits_t ) eSOCKET_SEND ) );
    TEST_ASSERT_EQUAL( 1, pxHandleSentCount );
}

void test_prvHandleEstablished_TCPFlagFIN_FINNotAcceptedButSent(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    /**/
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    
    pxSocket = &xLocalSocket;
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;

    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream =(StreamBuffer_t *) 0x1234;
    
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulFINSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE_UNSIGNED;
    
    pxTCPWindow->ucOptionLength = 0x12;
    
    vTCPStateChange_Expect( pxSocket, eLAST_ACK );
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + pxTCPWindow->ucOptionLength, xReturn );
    TEST_ASSERT_EQUAL( ( uint8_t ) tcpTCP_FLAG_ACK | ( uint8_t ) tcpTCP_FLAG_FIN, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAccepted );
}

void test_prvHandleEstablished_TCPFlagFIN_FINAcceptedAndSent(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    /**/
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    
    pxSocket = &xLocalSocket;
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;

    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x1234;   
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulFINSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdTRUE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE_UNSIGNED;
    
    pxTCPWindow->ucOptionLength = 0x12;
    
    vTCPStateChange_Expect( pxSocket, eLAST_ACK );
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + pxTCPWindow->ucOptionLength, xReturn );
    TEST_ASSERT_EQUAL( ( uint8_t ) tcpTCP_FLAG_ACK | ( uint8_t ) tcpTCP_FLAG_FIN, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAccepted );
}

void test_prvHandleEstablished_TCPFlagFIN_FINAcceptedButNotSent(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    /**/
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    
    pxSocket = &xLocalSocket;
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
     
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream =(StreamBuffer_t *) 0x1234;       
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulFINSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdTRUE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    
    xTCPWindowRxEmpty_ExpectAnyArgsAndReturn( 0 );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( 0 );
    
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE_UNSIGNED;
    
    pxTCPWindow->ucOptionLength = 0x12;
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAccepted );
}

void test_prvHandleEstablished_TCPFlagFIN_FINAcceptedButNotSent1(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    /**/
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    
    pxSocket = &xLocalSocket;
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x1234;        
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulFINSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdTRUE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    
    /* Return values to show that the FIN is being refused. */
    xTCPWindowRxEmpty_ExpectAnyArgsAndReturn( 1 );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( 0 );
    
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE_UNSIGNED;
    
    pxTCPWindow->ucOptionLength = 0x12;
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAccepted );
}


void test_prvHandleEstablished_TCPFlagFIN_FINAcceptedButNotSent2(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    /**/
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    uint32_t TCPHeaderSeqNumber = 10;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( TCPHeaderSeqNumber );
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x1234;     
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulFINSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdTRUE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    
    /* FIN is not being refused. */
    xTCPWindowRxEmpty_ExpectAnyArgsAndReturn( 1 );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( 1 );
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulSeqNumber;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 0;
    
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE_UNSIGNED;
        
    pxTCPWindow->ucOptionLength = 0x12;
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAccepted );
}

void test_prvHandleEstablished_TCPFlagFIN_FINAcceptedButNotSent3(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    uint32_t ulReceiveLength = 0;
    /**/
    UBaseType_t uxOptionsLength = 1;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    uint32_t TCPHeaderSeqNumber = 1;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;

    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( TCPHeaderSeqNumber );
    
    /* No flag set. */
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x1234;     
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulFINSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdTRUE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    
    /* FIN is not being refused. */
    xTCPWindowRxEmpty_ExpectAnyArgsAndReturn( 1 );
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( 1 );
    
    vTCPStateChange_Expect( pxSocket, eLAST_ACK );
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulSeqNumber;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 0;
    
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE_UNSIGNED;
        
    pxTCPWindow->ucOptionLength = 0x12;
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + pxTCPWindow->ucOptionLength, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAccepted );
}
