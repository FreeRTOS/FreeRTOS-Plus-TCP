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
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_UDP_IP.h"

#include "FreeRTOS_IP.h"

#include "FreeRTOS_IP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer );
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );
eFrameProcessingResult_t prvAllowIPPacket( const IPPacket_t * const pxIPPacket,
                                           const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                           UBaseType_t uxHeaderLength );

extern BaseType_t xIPTaskInitialised;
extern BaseType_t xNetworkDownEventPending;
extern BaseType_t xNetworkUp;
extern UBaseType_t uxQueueMinimumSpace;

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

void test_prvProcessIPEventsAndTimers_NoEventReceived( void )
{
    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    /* No event received. */
    xQueueReceive_ExpectAnyArgsAndReturn( pdFALSE );

    prvProcessIPEventsAndTimers();
}

void test_prvProcessIPEventsAndTimers_eNetworkDownEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    BaseType_t xQueueReturn = 100;

    xReceivedEvent.eEventType = eNetworkDownEvent;

    xNetworkUp = pdTRUE;

    uxQueueMinimumSpace = xQueueReturn - 10;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    prvProcessNetworkDownEvent_Expect();

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( pdFALSE, xNetworkUp );
    TEST_ASSERT_EQUAL( xQueueReturn - 10, uxQueueMinimumSpace );
}

void test_prvProcessIPEventsAndTimers_eNetworkRxEventNULL_LessSpace( void )
{
    IPStackEvent_t xReceivedEvent;
    BaseType_t xQueueReturn = 100;

    xReceivedEvent.eEventType = eNetworkRxEvent;
    xReceivedEvent.pvData = NULL;

    uxQueueMinimumSpace = xQueueReturn - 10;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( xQueueReturn - 10, uxQueueMinimumSpace );
}

void test_prvProcessIPEventsAndTimers_eNetworkRxEvent_MoreSpace( void )
{
    IPStackEvent_t xReceivedEvent;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    BaseType_t xQueueReturn = 100;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t ) - 1;
    pxNetworkBuffer->pxNextBuffer = NULL;

    xReceivedEvent.eEventType = eNetworkRxEvent;
    xReceivedEvent.pvData = pxNetworkBuffer;

    uxQueueMinimumSpace = xQueueReturn + 10;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( xQueueReturn, uxQueueMinimumSpace );
}

void test_prvProcessIPEventsAndTimers_eSocketSelectEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    SocketSelectMessage_t xData;
    BaseType_t xQueueReturn = 100;

    memset( &xData, 0, sizeof( xData ) );
    xData.pxSocketSet = ( void * ) 0xFFAABBCC;
    xData.xTaskhandle = ( void * ) 0xABCDABCD;

    xReceivedEvent.eEventType = eSocketSelectEvent;
    xReceivedEvent.pvData = ( void * ) &xData;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    vSocketSelect_Expect( ( SocketSelect_t * ) 0xFFAABBCC );
    xTaskGenericNotify_ExpectAndReturn( ( TaskHandle_t ) 0xABCDABCD, 0, ( 0 ), eIncrement, NULL, pdPASS );

    prvProcessIPEventsAndTimers();
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


    /* Set the local IP to something other than 0. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD;

    /* Clear default values. */
    memset( &xDefaultAddressing, 0, sizeof( xDefaultAddressing ) );
    memset( &xNetworkAddressing, 0, sizeof( xDefaultAddressing ) );

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
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucIPAddress[ 0 ], ucIPAddress[ 1 ], ucIPAddress[ 2 ], ucIPAddress[ 3 ] ), xNetworkAddressing.ulDefaultIPAddress );
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucNetMask[ 0 ], ucNetMask[ 1 ], ucNetMask[ 2 ], ucNetMask[ 3 ] ), xNetworkAddressing.ulNetMask );
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucGatewayAddress[ 0 ], ucGatewayAddress[ 1 ], ucGatewayAddress[ 2 ], ucGatewayAddress[ 3 ] ), xNetworkAddressing.ulGatewayAddress );
    TEST_ASSERT_EQUAL( FreeRTOS_inet_addr_quick( ucDNSServerAddress[ 0 ], ucDNSServerAddress[ 1 ], ucDNSServerAddress[ 2 ], ucDNSServerAddress[ 3 ] ), xNetworkAddressing.ulDNSServerAddress );
    TEST_ASSERT_EQUAL( ( ( xNetworkAddressing.ulDefaultIPAddress & xNetworkAddressing.ulNetMask ) | ~xNetworkAddressing.ulNetMask ), xNetworkAddressing.ulBroadcastAddress );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultAddressing, &xNetworkAddressing, sizeof( xDefaultAddressing ) );
    TEST_ASSERT_EQUAL( 0, *ipLOCAL_IP_ADDRESS_POINTER );
    TEST_ASSERT_EQUAL_MEMORY( ucMACAddress, ipLOCAL_MAC_ADDRESS, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( IPInItHappyPath_xTaskHandleToSet, FreeRTOS_GetIPTaskHandle() );
}

void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBufferAssert( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xByteCount = 100, xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnBadAddress );

    xReturn = FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, xByteCount );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectSizeAssert( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnIncorrectSize );

    xReturn = FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, ReleaseTCPPayloadBufferxByteCount );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBytesReleasedAssert( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnCorrectVals );

    FreeRTOS_recv_ExpectAndReturn( &xSocket, NULL, ReleaseTCPPayloadBufferxByteCount, FREERTOS_MSG_DONTWAIT, ( ReleaseTCPPayloadBufferxByteCount >> 1 ) );

    xReturn = FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, ReleaseTCPPayloadBufferxByteCount );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_FreeRTOS_ReleaseTCPPayloadBuffer_HappyPath( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnCorrectVals );

    FreeRTOS_recv_ExpectAndReturn( &xSocket, NULL, ReleaseTCPPayloadBufferxByteCount, FREERTOS_MSG_DONTWAIT, ReleaseTCPPayloadBufferxByteCount );

    xReturn = FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, ReleaseTCPPayloadBufferxByteCount );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

void test_prvAllowIPPacket_BroadcastSourceIP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_IncorrectSizeFields( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_UDPCheckSumZero( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t );
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( UDPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_prvAllowIPPacket_UDP_HappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t );
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( UDPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    pxProtPack = ( ( ProtocolPacket_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxHeaderLength - ipSIZE_OF_IPv4_HEADER ] ) );

    /* Non-zero checksum. */
    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0xFF12;

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

void test_prvAllowIPPacket_TCP_HappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    /* Set correct length. */
    pxNetworkBuffer->xDataLength = sizeof( TCPPacket_t );
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( UDPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

void test_prvProcessIPPacket_( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x46;
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_xCheckSizeFields_BufferLengthLess( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength = 0;
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x46;
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    for( uint32_t i = 0; i < sizeof( IPPacket_t ); i++ )
    {
        uxBufferLength = i;
        xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

        TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    }
}

void test_xCheckSizeFields_HeaderLengthLess( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength = sizeof( IPPacket_t );
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    /* Value less than 0x45. */
    pxIPHeader->ucVersionHeaderLength = 0x45 - 2;
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xCheckSizeFields_HeaderLengthMore( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength = sizeof( IPPacket_t );
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    /* Value more than 4F. */
    pxIPHeader->ucVersionHeaderLength = 0x4F + 2;
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xCheckSizeFields_HeaderLengthMoreThanTotalLength( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength;
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    /* Value more than 4F. */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    uxBufferLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 );

    xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xCheckSizeFields_IPPacketLengthMoreThanTotalLength( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength;
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    /* Value more than 4F. */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    uxBufferLength = FreeRTOS_ntohs( pxIPHeader->usLength ) - 1;

    xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xCheckSizeFields_UDP_IncorrectPacketLen( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength;
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    /* Value more than 4F. */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    uxBufferLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER - 1;

    pxIPHeader->usLength = FreeRTOS_htons( uxBufferLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xCheckSizeFields_TCP_IncorrectPacketLen( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength;
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    /* Value more than 4F. */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    uxBufferLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_TCP_HEADER - 1;

    pxIPHeader->usLength = FreeRTOS_htons( uxBufferLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xCheckSizeFields_ICMP_IncorrectPacketLen( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength;
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    /* Value more than 4F. */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPHeader->ucProtocol = ipPROTOCOL_ICMP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    uxBufferLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMP_HEADER - 1;

    pxIPHeader->usLength = FreeRTOS_htons( uxBufferLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xCheckSizeFields_IGMP_IncorrectPacketLen( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength;
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    /* Value more than 4F. */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPHeader->ucProtocol = ipPROTOCOL_IGMP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    uxBufferLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMP_HEADER - 1;

    pxIPHeader->usLength = FreeRTOS_htons( uxBufferLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xCheckSizeFields_NoProt( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength;
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    /* Value more than 4F. */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPHeader->ucProtocol = 0;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    uxBufferLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMP_HEADER - 1;

    pxIPHeader->usLength = FreeRTOS_htons( uxBufferLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xCheckSizeFields_UDP_LengthLess( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength;
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    /* Value more than 4F. */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    uxBufferLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER;

    pxIPHeader->usLength = FreeRTOS_ntohs( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( pxProtPack->xUDPPacket.xUDPHeader ) - 1 );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xCheckSizeFields_UDP_LengthMore( void )
{
    BaseType_t xReturn;
    size_t uxBufferLength;
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) ucEthBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xFFFFFFFF;

    /* Value more than 4F. */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    uxBufferLength = ipconfigNETWORK_MTU + 20;

    pxIPHeader->usLength = FreeRTOS_ntohs( ipconfigNETWORK_MTU + 1 );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    xReturn = xCheckSizeFields( ucEthBuffer, uxBufferLength );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_vReturnEthernetFrame_DuplicationFailed( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdFALSE;

    xNetworkBuffer.xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;

    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( &xNetworkBuffer, xNetworkBuffer.xDataLength, NULL );
    vReturnEthernetFrame( &xNetworkBuffer, xReleaseAfterSend );
}

void test_vReturnEthernetFrame_DuplicationSuccess( void )
{
    NetworkBufferDescriptor_t xDuplicateNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdFALSE;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xDuplicateNetworkBuffer, 0, sizeof( xDuplicateNetworkBuffer ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    xDuplicateNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;

    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( &xNetworkBuffer, xNetworkBuffer.xDataLength, &xDuplicateNetworkBuffer );

    xNetworkInterfaceOutput_ExpectAndReturn( &xDuplicateNetworkBuffer, pdTRUE, pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, xDuplicateNetworkBuffer.xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( ipLOCAL_MAC_ADDRESS, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
}

void test_vReturnEthernetFrame( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdTRUE;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10;

    xNetworkInterfaceOutput_ExpectAndReturn( pxNetworkBuffer, xReleaseAfterSend, pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( ipLOCAL_MAC_ADDRESS, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
}

void test_vReturnEthernetFrame_DataLenMoreThanRequired( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdTRUE;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;

    xNetworkInterfaceOutput_ExpectAndReturn( pxNetworkBuffer, xReleaseAfterSend, pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAA, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( ipLOCAL_MAC_ADDRESS, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
}

void test_uxGetMinimumIPQueueSpace( void )
{
    UBaseType_t uxReturn;

    uxQueueMinimumSpace = 10;

    uxReturn = uxGetMinimumIPQueueSpace();

    TEST_ASSERT_EQUAL( 10, uxReturn );
}
