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

void test_prvHandleEstablished_TCPFlagFIN_FINAcceptedButNotSent_RecvLenNonZero(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    /* Non zero receive length. */
    uint32_t ulReceiveLength = 2;
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
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAccepted );
    TEST_ASSERT_EQUAL( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2, pxTCPHeader->ucTCPOffset );
}

void test_prvHandleEstablished_TCPFlagFIN_FINAcceptedAndSent_RecvLenNonZero(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    /* Non zero receive length. */
    uint32_t ulReceiveLength = 2;
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
    
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
    
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
    TEST_ASSERT_EQUAL( ( ipSIZE_OF_TCP_HEADER + pxTCPWindow->ucOptionLength ) << 2, pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxTCPWindow->tx.ulCurrentSequenceNumber );
}

void test_prvHandleEstablished_TCPFlagNotFIN_FINNotAcceptedAndSent_RecvLenNonZero(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    /* Non zero receive length. */
    uint32_t ulReceiveLength = 2;
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
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_URG;
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x1234;     
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulFINSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulSeqNumber;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 0;
    
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE_UNSIGNED;
        
    pxTCPWindow->ucOptionLength = 0x12;
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAccepted );
    TEST_ASSERT_EQUAL( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2, pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxTCPWindow->tx.ulCurrentSequenceNumber );
}

void test_prvHandleEstablished_TCPFlagURG_FINNotAcceptedAndSent_RecvLenNon0_OptionLen0_NothingToSend(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    /* Non zero receive length. */
    uint32_t ulReceiveLength = 2;
    /**/
    UBaseType_t uxOptionsLength = 0;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    uint32_t TCPHeaderSeqNumber = 10;
    int32_t lSendLen = -1;
    
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
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_URG;
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x1234;     
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulFINSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulSeqNumber;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 0;
    
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE_UNSIGNED;
        
    pxTCPWindow->ucOptionLength = 0x12;
    
    prvTCPPrepareSend_ExpectAndReturn( pxSocket, ppxNetworkBuffer, uxOptionsLength, lSendLen );
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAccepted );
    TEST_ASSERT_EQUAL( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2, pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxTCPWindow->tx.ulCurrentSequenceNumber );
}

void test_prvHandleEstablished_TCPFlagURG_FINNotAcceptedAndSent_RecvLenNon0_OptionLen0_Send(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    /* Non zero receive length. */
    uint32_t ulReceiveLength = 2;
    /**/
    UBaseType_t uxOptionsLength = 0;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    uint32_t TCPHeaderSeqNumber = 10;
    int32_t lSendLen = 10;
    
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
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_URG;
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.txStream = (StreamBuffer_t *)0x1234;     
    /* Since the stream is non-NULL, expect a call. */
    prvTCPAddTxData_Expect( pxSocket );
    
    pxTCPWindow->tx.ulFINSequenceNumber = ulSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinAccepted = pdFALSE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulSeqNumber;
    pxTCPWindow->rx.ulCurrentSequenceNumber = 0;
    
    pxSocket->u.xTCP.bits.bFinAcked = pdFALSE_UNSIGNED;
        
    pxTCPWindow->ucOptionLength = 0x12;
    
    prvTCPPrepareSend_ExpectAndReturn( pxSocket, ppxNetworkBuffer, uxOptionsLength, lSendLen );
    
    xReturn = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( lSendLen, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAccepted );
    TEST_ASSERT_EQUAL( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2, pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxTCPWindow->tx.ulCurrentSequenceNumber );
}

void test_prvTCPHandleFin(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulCurrentSeqNumber = 0x123, lFinSeqNumber = 0xABC;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulCurrentSeqNumber;
    pxTCPWindow->tx.ulFINSequenceNumber = lFinSeqNumber;
    
    vTCPStateChange_Expect( pxSocket, eLAST_ACK );
    
    xReturn = prvTCPHandleFin( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + pxTCPWindow->ucOptionLength, xReturn );
    TEST_ASSERT_EQUAL( ulCurrentSeqNumber, pxTCPWindow->tx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinSent );
    TEST_ASSERT_EQUAL( ulCurrentSeqNumber, pxTCPWindow->tx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN, pxTCPHeader->ucTCPFlags );
}

void test_prvTCPHandleFin1(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulCurrentSeqNumber = 0x123, lFinSeqNumber = 0xABC;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
    pxTCPHeader->ulAckNr = FreeRTOS_htonl( lFinSeqNumber + 1 );
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulCurrentSeqNumber;
    pxTCPWindow->tx.ulFINSequenceNumber = lFinSeqNumber;
    
    xReturn = prvTCPHandleFin( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( lFinSeqNumber, pxTCPWindow->tx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinSent );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAcked );
    TEST_ASSERT_EQUAL( lFinSeqNumber + 1, pxTCPWindow->tx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, pxTCPHeader->ucTCPFlags );
}

void test_prvTCPHandleFin2(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulCurrentSeqNumber = 0x123, lFinSeqNumber = 0xABC;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
    pxTCPHeader->ulAckNr = FreeRTOS_htonl( lFinSeqNumber + 1 );
    
    pxSocket->u.xTCP.bits.bFinAcked = pdTRUE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE_UNSIGNED;
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulCurrentSeqNumber;
    pxTCPWindow->tx.ulFINSequenceNumber = lFinSeqNumber;
    
    vTCPStateChange_Expect( pxSocket, eCLOSE_WAIT );
    
    xReturn = prvTCPHandleFin( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + pxTCPWindow->ucOptionLength, xReturn );
    TEST_ASSERT_EQUAL( lFinSeqNumber, pxTCPWindow->tx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinSent );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAcked );
    TEST_ASSERT_EQUAL( lFinSeqNumber + 1, pxTCPWindow->tx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
}

void test_prvTCPHandleFin3(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulCurrentSeqNumber = 0x123, lFinSeqNumber = 0xABC;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
    pxTCPHeader->ulAckNr = FreeRTOS_htonl( lFinSeqNumber + 1 );
    
    pxSocket->u.xTCP.bits.bFinAcked = pdTRUE_UNSIGNED;
    
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE_UNSIGNED;
    
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulCurrentSeqNumber;
    pxTCPWindow->tx.ulFINSequenceNumber = lFinSeqNumber;
    
    pxSocket->u.xTCP.bits.bFinLast = pdTRUE_UNSIGNED;
    
    vTCPStateChange_Expect( pxSocket, eCLOSE_WAIT );
    
    xReturn = prvTCPHandleFin( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( lFinSeqNumber, pxTCPWindow->tx.ulFINSequenceNumber );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinSent );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinAcked );
    TEST_ASSERT_EQUAL( lFinSeqNumber + 1, pxTCPWindow->tx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, pxTCPHeader->ucTCPFlags );
}

void test_prvHandleSynReceived_AllSetToZero(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    /* Non zero receive length. */
    uint32_t ulReceiveLength = 2;
    UBaseType_t uxOptionsLength = 0;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    uint32_t TCPHeaderSeqNumber = 10;
    int32_t lSendLen = 10;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulSeqNumber );
    
    vTCPStateChange_Expect( pxSocket, eCLOSE_WAIT );
    
    xReturn = prvHandleSynReceived( pxSocket, pxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_RST, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 ), pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxTCPWindow->rx.ulCurrentSequenceNumber );
}

void test_prvHandleSynReceived_FlagACK(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    /* Non zero receive length. */
    uint32_t ulReceiveLength = 2;
    UBaseType_t uxOptionsLength = 0;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    uint32_t TCPHeaderSeqNumber = 10;
    int32_t lSendLen = 10;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulSeqNumber );
    
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0x12;
    pxSocket->u.xTCP.ucPeerWinScaleFactor = 0x34;
    vTCPStateChange_Expect( pxSocket, eESTABLISHED );
    
    xReturn = prvHandleSynReceived( pxSocket, pxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 ), pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, pxSocket->u.xTCP.ucMyWinScaleFactor );
    TEST_ASSERT_EQUAL( 0, pxSocket->u.xTCP.ucPeerWinScaleFactor );
}

void test_prvHandleSynReceived_FlagSYN(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    /* Non zero receive length. */
    uint32_t ulReceiveLength = 2;
    UBaseType_t uxOptionsLength = 0;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB;
    uint32_t TCPHeaderSeqNumber = 10;
    int32_t lSendLen = 10;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulSeqNumber );
    
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0x12;
    pxSocket->u.xTCP.ucPeerWinScaleFactor = 0x34;
    vTCPStateChange_Expect( pxSocket, eCLOSE_WAIT );
    
    xReturn = prvHandleSynReceived( pxSocket, pxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK | tcpTCP_FLAG_RST, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 ), pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxTCPWindow->rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0x12, pxSocket->u.xTCP.ucMyWinScaleFactor );
    TEST_ASSERT_EQUAL( 0x34, pxSocket->u.xTCP.ucPeerWinScaleFactor );
}

void test_prvHandleSynReceived_FlagACKAndSYN(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    /* Non zero receive length. */
    uint32_t ulReceiveLength = 2;
    UBaseType_t uxOptionsLength = 0;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB, ulTxSeqNumber = 0xFAFB;
    uint32_t TCPHeaderSeqNumber = 10;
    int32_t lSendLen = 10;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = eCONNECT_SYN;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_SYN;
    
    vTCPWindowInit_ExpectAnyArgs();
    
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulSeqNumber );
    
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0x12;
    pxSocket->u.xTCP.ucPeerWinScaleFactor = 0x34;
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulTxSeqNumber;
    
    vTCPStateChange_Expect( pxSocket, eESTABLISHED );
    
    xReturn = prvHandleSynReceived( pxSocket, pxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 ), pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EQUAL( ulSeqNumber + 1, pxTCPWindow->rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( ulSeqNumber + 1, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( ulTxSeqNumber+1, pxTCPWindow->tx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, pxSocket->u.xTCP.ucMyWinScaleFactor );
    TEST_ASSERT_EQUAL( 0, pxSocket->u.xTCP.ucPeerWinScaleFactor );
}

void test_prvHandleSynReceived_FlagACKAndStateClosed_Non0RxLength(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    /* Non zero receive length. */
    uint32_t ulReceiveLength = 0;
    UBaseType_t uxOptionsLength = 0;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB, ulTxSeqNumber = 0xFAFB;
    uint32_t TCPHeaderSeqNumber = 10;
    int32_t lSendLen = 10;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = eCLOSED;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulSeqNumber );
    
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0x12;
    pxSocket->u.xTCP.ucPeerWinScaleFactor = 0x34;
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulTxSeqNumber;
    
    vTCPStateChange_Expect( pxSocket, eESTABLISHED );
    
    xReturn = prvHandleSynReceived( pxSocket, pxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( 0, pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxTCPWindow->rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( ulTxSeqNumber, pxTCPWindow->tx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, pxSocket->u.xTCP.ucMyWinScaleFactor );
    TEST_ASSERT_EQUAL( 0, pxSocket->u.xTCP.ucPeerWinScaleFactor );
}

void test_prvHandleSynReceived_FlagACKAndStateClosed_Non0RxLength_WinScalingEnabled(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    /* Non zero receive length. */
    uint32_t ulReceiveLength = 0;
    UBaseType_t uxOptionsLength = 0;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulSeqNumber = 0xFFAB, ulTxSeqNumber = 0xFAFB;
    uint32_t TCPHeaderSeqNumber = 10;
    int32_t lSendLen = 10;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = eCLOSED;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulSeqNumber );
    
    pxSocket->u.xTCP.ucMyWinScaleFactor = 0x12;
    pxSocket->u.xTCP.ucPeerWinScaleFactor = 0x34;
    pxTCPWindow->tx.ulCurrentSequenceNumber = ulTxSeqNumber;
    pxSocket->u.xTCP.bits.bWinScaling = pdTRUE_UNSIGNED;
    
    vTCPStateChange_Expect( pxSocket, eESTABLISHED );
    
    xReturn = prvHandleSynReceived( pxSocket, pxNetworkBuffer, ulReceiveLength, uxOptionsLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( tcpTCP_FLAG_ACK, pxTCPHeader->ucTCPFlags );
    TEST_ASSERT_EQUAL( 0, pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EQUAL( ulSeqNumber, pxTCPWindow->rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->rx.ulHighestSequenceNumber );
    TEST_ASSERT_EQUAL( ulTxSeqNumber, pxTCPWindow->tx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0x12, pxSocket->u.xTCP.ucMyWinScaleFactor );
    TEST_ASSERT_EQUAL( 0x34, pxSocket->u.xTCP.ucPeerWinScaleFactor );
}

void test_prvSetOptions_AllZeroedOut(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;    
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxReturn;
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    uxReturn = prvSetOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( 0, uxReturn );
}

void test_prvSetOptions_NonZeroOptions(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;    
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint8_t ucOptionsLength = 0x10;
    
    /* Cannot set the options more than 16 bytes since that is what +TCP supports. */
    TEST_ASSERT_LESS_OR_EQUAL( 16, ucOptionsLength );
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxTCPWindow->ucOptionLength = ucOptionsLength;
    
    memset( pxTCPWindow->ulOptionsData, 0xAB, ucOptionsLength );
    
    uxReturn = prvSetOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( ucOptionsLength, uxReturn );
    TEST_ASSERT_EQUAL( ( ipSIZE_OF_TCP_HEADER + ucOptionsLength ) << 2, pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, pxTCPHeader->ucOptdata, ucOptionsLength );
}

void test_prvSetOptions_ZeroOptions_StateEstablished(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;    
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint8_t ucOptionsLength = 0;
    
    /* Cannot set the options more than 16 bytes since that is what +TCP supports. */
    TEST_ASSERT_LESS_OR_EQUAL( 16, ucOptionsLength );
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxTCPWindow->ucOptionLength = ucOptionsLength;
    
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    
    memset( pxTCPWindow->ulOptionsData, 0xAB, ucOptionsLength );
    
    uxReturn = prvSetOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( ucOptionsLength, uxReturn );
    TEST_ASSERT_EQUAL( 0, pxTCPHeader->ucTCPOffset );
}

void test_prvSetOptions_ZeroOptions_StateEstablished_MSSChange(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;    
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint8_t ucOptionsLength = 0;
    
    /* Cannot set the options more than 16 bytes since that is what +TCP supports. */
    TEST_ASSERT_LESS_OR_EQUAL( 16, ucOptionsLength );
    
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxTCPWindow->ucOptionLength = ucOptionsLength;
    
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    pxSocket->u.xTCP.bits.bMssChange = pdTRUE_UNSIGNED;
    pxSocket->u.xTCP.usCurMSS = 1024;
    
    memset( pxTCPWindow->ulOptionsData, 0xAB, ucOptionsLength );
    
    uxReturn = prvSetOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( 4, uxReturn );
    TEST_ASSERT_EQUAL( ( ipSIZE_OF_TCP_HEADER + 4 ) << 2, pxTCPHeader->ucTCPOffset );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxSocket->u.xTCP.bits.bMssChange );
    TEST_ASSERT_EQUAL( tcpTCP_OPT_MSS, pxTCPHeader->ucOptdata[ 0 ] );
    TEST_ASSERT_EQUAL( tcpTCP_OPT_MSS_LEN, pxTCPHeader->ucOptdata[ 1 ] );
    TEST_ASSERT_EQUAL( pxSocket->u.xTCP.usCurMSS >> 8, pxTCPHeader->ucOptdata[ 2 ] );
    TEST_ASSERT_EQUAL( pxSocket->u.xTCP.usCurMSS & 0xffU, pxTCPHeader->ucOptdata[ 3 ] );
}

void test_prvSendData_AllZero(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 0;
    BaseType_t xByteCount = 0;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;

    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_prvSendData_ReceiveLenGTZero_CurrMSSNonZero(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    BaseType_t xByteCount = 0;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxSocket->u.xTCP.usCurMSS = 1;

    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_prvSendData_ReceiveLenGTZero_FinSent(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    BaseType_t xByteCount = 0;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;

    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_prvSendData_ReceiveLenGTZero_NonZeroByteCount(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    BaseType_t xByteCount = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );    
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    prvTCPReturnPacket_ExpectAnyArgs();
    
    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( xByteCount, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
}

void test_prvSendData_ReceiveLenGTZero_NonZeroByteCount_PortCanLog(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    BaseType_t xByteCount = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxSocket->usLocalPort = 3;
    xTCPWindowLoggingLevel = 2;
    
    prvTCPReturnPacket_ExpectAnyArgs();
    
    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( xByteCount, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
}

void test_prvSendData_ReceiveLenGTZero_NonZeroByteCount_StateEstablished(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    BaseType_t xByteCount = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    
    prvTCPReturnPacket_ExpectAnyArgs();
    
    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( xByteCount, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
}

void test_prvSendData_ReceiveLenGTZero_NonZeroByteCount_StateEstablished_FlagACK(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    BaseType_t xByteCount = 0x12;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    
    prvTCPReturnPacket_ExpectAnyArgs();
    
    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( xByteCount, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
}

void test_prvSendData_AllConditionsMet_LoggingEnabled(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    BaseType_t xByteCount = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    
    xTCPWindowLoggingLevel = 2;
    
    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( &xLocalNetworkBuffer, pxSocket->u.xTCP.pxAckMessage );
}

void test_prvSendData_AllConditionsMet(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    BaseType_t xByteCount = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;    
    
    xTCPWindowLoggingLevel = 0;
    
    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( &xLocalNetworkBuffer, pxSocket->u.xTCP.pxAckMessage );
}

void test_prvSendData_AllConditionsMet_DelayedAckPresentButNotCurrent(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    BaseType_t xByteCount = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.pxAckMessage = (NetworkBufferDescriptor_t *)0x1234;
    /* Expect removal of old ACK message */
    vReleaseNetworkBufferAndDescriptor_Expect( pxSocket->u.xTCP.pxAckMessage );
    
    xTCPWindowLoggingLevel = 0;
    
    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( &xLocalNetworkBuffer, pxSocket->u.xTCP.pxAckMessage );
}

void test_prvSendData_AllConditionsMet_DelayedAckPresentAndCurrent(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    BaseType_t xByteCount = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.pxAckMessage = pxNetworkBuffer;
    
    xTCPWindowLoggingLevel = 0;
    
    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( &xLocalNetworkBuffer, pxSocket->u.xTCP.pxAckMessage );
}

void test_prvSendData_AllConditionsMet_DelayedAckPresentAndCurrent_MSSGT(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    BaseType_t xByteCount = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.pxAckMessage = pxNetworkBuffer;
    
    pxSocket->u.xTCP.ulHighestRxAllowed = 200;
    
    pxSocket->u.xTCP.usCurMSS = 20;
    
    xTCPWindowLoggingLevel = 0;
    
    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( &xLocalNetworkBuffer, pxSocket->u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( tcpDELAYED_ACK_SHORT_DELAY_MS, pxSocket->u.xTCP.usTimeout );
}

void test_prvSendData_AllConditionsMet_DelayedAckPresentAndCurrent1(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 0;
    BaseType_t xByteCount = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.pxAckMessage = (NetworkBufferDescriptor_t *) 0x123A;
    
    pxSocket->u.xTCP.ulHighestRxAllowed = 30;
    
    pxSocket->u.xTCP.usCurMSS = 20;
    
    xTCPWindowLoggingLevel = 0;
    
    vReleaseNetworkBufferAndDescriptor_Expect( pxSocket->u.xTCP.pxAckMessage );
    prvTCPReturnPacket_ExpectAnyArgs();
    
    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( xByteCount, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 0, pxSocket->u.xTCP.usTimeout );
}

void test_prvSendData_AllConditionsMet_DelayedAckPresentAndCurrent2(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer, **ppxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 0;
    BaseType_t xByteCount = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = eESTABLISHED;
    
    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
    
    /* Any non-NULL value */
    pxSocket->u.xTCP.pxAckMessage = &xLocalNetworkBuffer;
    
    pxSocket->u.xTCP.ulHighestRxAllowed = 30;
    
    pxSocket->u.xTCP.usCurMSS = 20;
    
    xTCPWindowLoggingLevel = 0;
    
    prvTCPReturnPacket_ExpectAnyArgs();
    
    xReturn = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xByteCount );
    
    TEST_ASSERT_EQUAL( xByteCount, xReturn );
    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 0, pxSocket->u.xTCP.usTimeout );
}

void test_prvStoreRxData_AllSetTo0(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 0;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    xReturn = prvStoreRxData( pxSocket, ucBuffer, pxNetworkBuffer, ulReceiveLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->ucOptionLength );
}

void test_prvStoreRxData_RxLenGT0(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    xReturn = prvStoreRxData( pxSocket, ucBuffer, pxNetworkBuffer, ulReceiveLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->ucOptionLength );
}

void test_prvStoreRxData_RxLenGT0_TCPStateSYNRxed(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    int32_t lOffset = 0, lStored = 0;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eSYN_RECEIVED;
    
    lTCPWindowRxCheck_ExpectAnyArgsAndReturn( lOffset );
    lTCPAddRxdata_ExpectAnyArgsAndReturn( lStored );
    prvTCPSendReset_ExpectAndReturn( pxNetworkBuffer, 0 );
    
    xReturn = prvStoreRxData( pxSocket, ucBuffer, pxNetworkBuffer, ulReceiveLength );
    
    TEST_ASSERT_EQUAL( -1, xReturn );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->ucOptionLength );
}

void test_prvStoreRxData_RxLenGT0_TCPStateSYNRxed1(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    int32_t lOffset = 0, lStored = ulReceiveLength;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eSYN_RECEIVED;
    
    lTCPWindowRxCheck_ExpectAnyArgsAndReturn( lOffset );
    lTCPAddRxdata_ExpectAnyArgsAndReturn( lStored );
    
    xReturn = prvStoreRxData( pxSocket, ucBuffer, pxNetworkBuffer, ulReceiveLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->ucOptionLength );
}

void test_prvStoreRxData_RxLenGT0_TCPStateSYNRxed2(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    int32_t lOffset = 0, lStored = ulReceiveLength;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eSYN_RECEIVED;
    
    lTCPWindowRxCheck_ExpectAnyArgsAndReturn( lOffset );
    lTCPAddRxdata_ExpectAnyArgsAndReturn( lStored );
    
    pxTCPWindow->ulUserDataLength = 10;
    
    /* Return value is ignored */
    lTCPAddRxdata_ExpectAnyArgsAndReturn( 0 );
    
    xReturn = prvStoreRxData( pxSocket, ucBuffer, pxNetworkBuffer, ulReceiveLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->ucOptionLength );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->ulUserDataLength );
}

void test_prvStoreRxData_RxLenGT0_TCPStateSYNRxed3(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    int32_t lOffset = 0, lStored = ulReceiveLength;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eSYN_RECEIVED;
    
    pxSocket->u.xTCP.rxStream = (StreamBuffer_t *)0xFFAB;
    uxStreamBufferGetSpace_ExpectAndReturn( pxSocket->u.xTCP.rxStream, 0 );
    
    lTCPWindowRxCheck_ExpectAnyArgsAndReturn( lOffset );
    lTCPAddRxdata_ExpectAnyArgsAndReturn( lStored );
    
    pxTCPWindow->ulUserDataLength = 10;
    
    /* Return value is ignored */
    lTCPAddRxdata_ExpectAnyArgsAndReturn( 0 );
    
    xReturn = prvStoreRxData( pxSocket, ucBuffer, pxNetworkBuffer, ulReceiveLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->ucOptionLength );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->ulUserDataLength );
}

void test_prvStoreRxData_RxLenGT0_TCPStateSYNRxed_OffssetLT0(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, *pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    BaseType_t xReturn;
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    TCPWindow_t * pxTCPWindow;
    uint32_t ulReceiveLength = 10;
    int32_t lOffset = -10, lStored = ulReceiveLength;
        
    pxSocket = &xLocalSocket;
    memset( pxSocket, 0, sizeof( xLocalSocket ) );
    pxNetworkBuffer = &xLocalNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) ); 
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    memset( ucBuffer, 0, ipconfigTCP_MSS );
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );
    pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    
    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eSYN_RECEIVED;
    
    pxSocket->u.xTCP.rxStream = (StreamBuffer_t *)0xFFAB;
    uxStreamBufferGetSpace_ExpectAndReturn( pxSocket->u.xTCP.rxStream, 0 );
    
    lTCPWindowRxCheck_ExpectAnyArgsAndReturn( lOffset );
    
    pxTCPWindow->ulUserDataLength = 10;
    
    /* Return value is ignored */
    lTCPAddRxdata_ExpectAnyArgsAndReturn( 0 );
    
    xReturn = prvStoreRxData( pxSocket, ucBuffer, pxNetworkBuffer, ulReceiveLength );
    
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->ucOptionLength );
    TEST_ASSERT_EQUAL( 0, pxTCPWindow->ulUserDataLength );
}













