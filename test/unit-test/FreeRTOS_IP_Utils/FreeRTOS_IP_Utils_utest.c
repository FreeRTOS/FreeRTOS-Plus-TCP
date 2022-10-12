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
#include "mock_IP_Utils_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP.h"
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

#include "FreeRTOS_IP_Utils.h"

#include "FreeRTOS_IP_Utils_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"


#if ( ipconfigUSE_NETWORK_EVENT_HOOK == 1 )
    extern BaseType_t xCallEventHook;
#endif

extern UBaseType_t uxLastMinBufferCount;
extern size_t uxMinLastSize;

void test_xSendDHCPEvent( void )
{
    BaseType_t xReturn, xResult = 0x123;

    eGetDHCPState_ExpectAndReturn( 12 );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( xResult );

    xReturn = xSendDHCPEvent();

    TEST_ASSERT_EQUAL( xResult, xReturn );
}

void test_vSetMultiCastIPv4MacAddress( void )
{
    uint32_t ulIP = 0xABCDEF12;
    MACAddress_t xMACAddress;

    vSetMultiCastIPv4MacAddress( ulIP, &xMACAddress );

    TEST_ASSERT_EQUAL( ( uint8_t ) 0x01U, xMACAddress.ucBytes[ 0 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) 0x00U, xMACAddress.ucBytes[ 1 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) 0x5EU, xMACAddress.ucBytes[ 2 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) ( ( FreeRTOS_ntohl( ulIP ) >> 16 ) & 0x7fU ), xMACAddress.ucBytes[ 3 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) ( ( FreeRTOS_ntohl( ulIP ) >> 8 ) & 0xffU ), xMACAddress.ucBytes[ 4 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) ( ( FreeRTOS_ntohl( ulIP ) ) & 0xffU ), xMACAddress.ucBytes[ 5 ] );
}

void test_pxDuplicateNetworkBufferWithDescriptor_NULLReturned( void )
{
    NetworkBufferDescriptor_t * pxReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    size_t uxNewLength;

    pxNetworkBuffer = &xNetworkBuffer;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNewLength, 0, NULL );

    pxReturn = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, uxNewLength );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

void test_pxDuplicateNetworkBufferWithDescriptor_LargerBufferReturned( void )
{
    NetworkBufferDescriptor_t * pxReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer, xNetworkBuffer2;
    size_t uxNewLength = 0x345;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    uint8_t ucEthBuffer2[ ipconfigTCP_MSS ];

    pxNetworkBuffer = &xNetworkBuffer;
    memset( &xNetworkBuffer2, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAB, ipconfigTCP_MSS );
    xNetworkBuffer2.pucEthernetBuffer = ucEthBuffer2;
    memset( ucEthBuffer2, 0x00, ipconfigTCP_MSS );

    pxNetworkBuffer->xDataLength = 0x123;
    pxNetworkBuffer->ulIPAddress = 0xABCDEF56;
    pxNetworkBuffer->usPort = 0x1234;
    pxNetworkBuffer->usBoundPort = 0xFFAA;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNewLength, 0, &xNetworkBuffer2 );

    pxReturn = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, uxNewLength );

    TEST_ASSERT_EQUAL( &xNetworkBuffer2, pxReturn );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.xDataLength, uxNewLength );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.ulIPAddress, pxNetworkBuffer->ulIPAddress );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.usPort, pxNetworkBuffer->usPort );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.usBoundPort, pxNetworkBuffer->usBoundPort );
    TEST_ASSERT_EQUAL_MEMORY( pxNetworkBuffer->pucEthernetBuffer, xNetworkBuffer2.pucEthernetBuffer, pxNetworkBuffer->xDataLength );
}

void test_pxDuplicateNetworkBufferWithDescriptor_SmallerBufferReturned( void )
{
    NetworkBufferDescriptor_t * pxReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer, xNetworkBuffer2;
    size_t uxNewLength = 0x34;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    uint8_t ucEthBuffer2[ ipconfigTCP_MSS ];

    pxNetworkBuffer = &xNetworkBuffer;
    memset( &xNetworkBuffer2, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAB, ipconfigTCP_MSS );
    xNetworkBuffer2.pucEthernetBuffer = ucEthBuffer2;
    memset( ucEthBuffer2, 0x00, ipconfigTCP_MSS );

    pxNetworkBuffer->xDataLength = 0x123;
    pxNetworkBuffer->ulIPAddress = 0xABCDEF56;
    pxNetworkBuffer->usPort = 0x1234;
    pxNetworkBuffer->usBoundPort = 0xFFAA;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNewLength, 0, &xNetworkBuffer2 );

    pxReturn = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, uxNewLength );

    TEST_ASSERT_EQUAL( &xNetworkBuffer2, pxReturn );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.xDataLength, uxNewLength );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.ulIPAddress, pxNetworkBuffer->ulIPAddress );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.usPort, pxNetworkBuffer->usPort );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.usBoundPort, pxNetworkBuffer->usBoundPort );
    TEST_ASSERT_EQUAL_MEMORY( pxNetworkBuffer->pucEthernetBuffer, xNetworkBuffer2.pucEthernetBuffer, uxNewLength );
}

void test_prvPacketBuffer_to_NetworkBuffer_NULLParam( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    const void * pvBuffer = NULL;
    size_t uxOffset;

    pxNetworkBuffer = prvPacketBuffer_to_NetworkBuffer( pvBuffer, uxOffset );

    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
}

void test_prvPacketBuffer_to_NetworkBuffer_Unalligned( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetBufferToReturn;
    const void * pvBuffer;
    size_t uxOffset = 12;
    uint8_t ucEthBuf[ ipconfigTCP_MSS ];
    uintptr_t uxAddrOfNetBuffer = &xNetBufferToReturn;

    memcpy( ucEthBuf, &uxAddrOfNetBuffer, sizeof( uintptr_t ) );
    pvBuffer = ucEthBuf[ uxOffset + ipBUFFER_PADDING ];

    pxNetworkBuffer = prvPacketBuffer_to_NetworkBuffer( pvBuffer, uxOffset );

    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
}

void test_prvPacketBuffer_to_NetworkBuffer_Alligned( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetBufferToReturn;
    const void * pvBuffer;
    size_t uxOffset = 20;
    uint8_t ucEthBuf[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t * pxAddrOfNetBuffer = &xNetBufferToReturn;

    pxAddrOfNetBuffer->pucEthernetBuffer = ucEthBuf;

    *( ( NetworkBufferDescriptor_t ** ) pxAddrOfNetBuffer->pucEthernetBuffer ) = pxAddrOfNetBuffer;

    pxAddrOfNetBuffer->pucEthernetBuffer += ( uxOffset + ipBUFFER_PADDING );

    pxNetworkBuffer = prvPacketBuffer_to_NetworkBuffer( pxAddrOfNetBuffer->pucEthernetBuffer, uxOffset );

    TEST_ASSERT_EQUAL( ( uint32_t ) pxAddrOfNetBuffer, ( uint32_t ) pxNetworkBuffer );
}

void test_pxUDPPayloadBuffer_to_NetworkBuffer( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetBufferToReturn;
    const void * pvBuffer;
    size_t uxOffset = sizeof( UDPPacket_t );
    uint8_t ucEthBuf[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t * pxAddrOfNetBuffer = &xNetBufferToReturn;

    pxAddrOfNetBuffer->pucEthernetBuffer = ucEthBuf;

    *( ( NetworkBufferDescriptor_t ** ) pxAddrOfNetBuffer->pucEthernetBuffer ) = pxAddrOfNetBuffer;

    pxAddrOfNetBuffer->pucEthernetBuffer += ( uxOffset + ipBUFFER_PADDING );

    pxNetworkBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pxAddrOfNetBuffer->pucEthernetBuffer );

    TEST_ASSERT_EQUAL( ( uint32_t ) pxAddrOfNetBuffer, ( uint32_t ) pxNetworkBuffer );
}

void test_xIsCallingFromIPTask_NotCallingFromIPTask( void )
{
    BaseType_t xReturn;
    TaskHandle_t xHandleOfIPTask = 0xAABBCCDD, xHandleOfNotIPTask = 0xAABBCCDE;

    xTaskGetCurrentTaskHandle_ExpectAndReturn( xHandleOfNotIPTask );
    FreeRTOS_GetIPTaskHandle_ExpectAndReturn( xHandleOfIPTask );

    xReturn = xIsCallingFromIPTask();

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_xIsCallingFromIPTask_IsCallingFromIPTask( void )
{
    BaseType_t xReturn;
    TaskHandle_t xHandleOfIPTask = 0xAABBCCDD;

    xTaskGetCurrentTaskHandle_ExpectAndReturn( xHandleOfIPTask );
    FreeRTOS_GetIPTaskHandle_ExpectAndReturn( xHandleOfIPTask );

    xReturn = xIsCallingFromIPTask();

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

void test_prvProcessNetworkDownEvent_Pass( void )
{
    xCallEventHook = pdFALSE;

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_ClearARP_Expect();

    xNetworkInterfaceInitialise_ExpectAndReturn( pdPASS );

    vDHCPProcess_Expect( pdTRUE, eInitialWait );

    prvProcessNetworkDownEvent();

    /* Run again to trigger a different path in the code. */

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    vApplicationIPNetworkEventHook_Expect( eNetworkDown );

    FreeRTOS_ClearARP_Expect();

    xNetworkInterfaceInitialise_ExpectAndReturn( pdPASS );

    vDHCPProcess_Expect( pdTRUE, eInitialWait );

    prvProcessNetworkDownEvent();
}

void test_prvProcessNetworkDownEvent_Fail( void )
{
    xCallEventHook = pdFALSE;

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_ClearARP_Expect();

    xNetworkInterfaceInitialise_ExpectAndReturn( pdFAIL );

    vTaskDelay_ExpectAnyArgs();

    FreeRTOS_NetworkDown_Expect();

    prvProcessNetworkDownEvent();
}

void test_vPreCheckConfigs_CatchAssert1( void )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    catch_assert( vPreCheckConfigs() );
}

void test_vPreCheckConfigs_CatchAssert2( void )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );
    xNetworkEventQueue = 0xAABBCCDD;

    catch_assert( vPreCheckConfigs() );
}

void test_vPreCheckConfigs_CatchAssert3( void )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );
    xNetworkEventQueue = NULL;
    FreeRTOS_GetIPTaskHandle_ExpectAndReturn( ( TaskHandle_t ) 0xAABBCCDD );

    catch_assert( vPreCheckConfigs() );
}

void test_vPreCheckConfigs( void )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );
    xNetworkEventQueue = NULL;
    FreeRTOS_GetIPTaskHandle_ExpectAndReturn( ( TaskHandle_t ) 0x00 );

    vPreCheckConfigs();
}

void test_usGenerateProtocolChecksum_AllZeroedInput( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = ipconfigTCP_MSS;
    BaseType_t xOutgoingPacket;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( usReturn, ipUNHANDLED_PROTOCOL );
}

void test_usGenerateProtocolChecksum_InvalidLength( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = sizeof( IPPacket_t ) - 1;
    BaseType_t xOutgoingPacket;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( usReturn, ipINVALID_LENGTH );
}

void test_usGenerateProtocolChecksum_InvalidLength2( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = sizeof( IPPacket_t );
    BaseType_t xOutgoingPacket;
    uint8_t ucVersionHeaderLength = 24;
    IPPacket_t * pxIPPacket;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( usReturn, ipINVALID_LENGTH );
}

void test_usGenerateProtocolChecksum_InvalidLength3( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 30;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + usLength - 1;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( usReturn, ipINVALID_LENGTH );
}

void test_usGenerateProtocolChecksum_UDPWrongCRCIncomingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
}

void test_usGenerateProtocolChecksum_UDPInvalidLength( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER - 1;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_UDPOutgoingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 10;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_UDPNonZeroChecksum( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 10;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x1234;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_UDPCorrectCRCOutgoingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    /* This is the checksum with zeroed out data. Fill it in to make the checksum 0. */
    *( ( uint32_t * ) &pucEthernetBuffer[ usLength - sizeof( uint32_t ) ] ) = FreeRTOS_htonl( 0xFF9E );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x00;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
    TEST_ASSERT_EQUAL( 0xFFFF, pxProtPack->xUDPPacket.xUDPHeader.usChecksum );
}

void test_usGenerateProtocolChecksum_UDPCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x1234;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
    TEST_ASSERT_EQUAL( 40703, pxProtPack->xUDPPacket.xUDPHeader.usChecksum );
}

void test_usGenerateProtocolChecksum_UDPIncorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x01;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
}

void test_usGenerateProtocolChecksum_TCPCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x1234;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
    TEST_ASSERT_EQUAL( 4660, pxProtPack->xUDPPacket.xUDPHeader.usChecksum );
}

void test_usGenerateProtocolChecksum_TCPCorrectCRCOutgoingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    /* This is the checksum with zeroed out data. Fill it in to make the checksum 0. */
    *( ( uint32_t * ) &pucEthernetBuffer[ usLength - sizeof( uint32_t ) ] ) = FreeRTOS_htonl( 0xFFA9 );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x0000;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
    TEST_ASSERT_EQUAL( 0, pxProtPack->xUDPPacket.xUDPHeader.usChecksum );
}

void test_usGenerateProtocolChecksum_TCPCorrectCRC_IncomingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0xa9ff;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

void test_usGenerateProtocolChecksum_TCPIncorrectCRC_IncomingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x1234;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
}

void test_usGenerateProtocolChecksum_TCPInvalidLength( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength + ipSIZE_OF_TCP_HEADER - 1;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_TCP_HEADER - 1;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x1234;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_TCPInvalidLength2( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_TCP_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x1234;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_TCPInvalidLength3( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ipconfigNETWORK_MTU * 2;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + usLength;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x1234;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_ICMPInvalidLength( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ipconfigNETWORK_MTU * 2;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + usLength;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_ICMPInvalidLength2( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ( size_t ) usLength - 1;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_ICMPInvalidLength3( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength; /* + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMP_HEADER - 1; */
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMP_HEADER - 1;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_ICMPOutgoingChecksum( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
    TEST_ASSERT_EQUAL( 65535, pxProtPack->xICMPPacket.xICMPHeader.usChecksum );
}

void test_usGenerateProtocolChecksum_ICMPIncomingIncorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
    TEST_ASSERT_EQUAL( 0, pxProtPack->xICMPPacket.xICMPHeader.usChecksum );
}

void test_usGenerateProtocolChecksum_ICMPIncomingCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    /* Fill in the checksum. */
    pxProtPack->xICMPPacket.xICMPHeader.usChecksum = FreeRTOS_htons( 0xFFFF );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

void test_usGenerateProtocolChecksum_IGMPInvalidLength( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ipconfigNETWORK_MTU * 2;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + usLength;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_IGMP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_IGMPInvalidLength2( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ( size_t ) usLength - 1;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_IGMP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_IGMPInvalidLength3( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMP_HEADER - 1;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_IGMP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

void test_usGenerateProtocolChecksum_IGMPOutgoingChecksum( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_IGMP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
    TEST_ASSERT_EQUAL( 65535, pxProtPack->xICMPPacket.xICMPHeader.usChecksum );
}

void test_usGenerateProtocolChecksum_IGMPIncomingIncorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_IGMP;

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
    TEST_ASSERT_EQUAL( 0, pxProtPack->xICMPPacket.xICMPHeader.usChecksum );
}

void test_usGenerateProtocolChecksum_IGMPIncomingCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_IGMP;

    /* Fill in the checksum. */
    pxProtPack->xICMPPacket.xICMPHeader.usChecksum = FreeRTOS_htons( 0xFFFF );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

void test_usGenerateChecksum_UnallignedAccess( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 10;
    size_t uxUnalligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnalligned = 0; uxUnalligned < 4; uxUnalligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnalligned ] ) & 0x01U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnalligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 23130, usResult );
}

void test_usGenerateChecksum_OneByteToChecksum( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 1;
    size_t uxUnalligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnalligned = 0; uxUnalligned < 4; uxUnalligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnalligned ] ) & 0x01U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnalligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 43776, usResult );
}

void test_usGenerateChecksum_OneByteAllignedButZeroLength( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 0;
    size_t uxUnalligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnalligned = 0; uxUnalligned < 4; uxUnalligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnalligned ] ) & 0x01U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnalligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 0, usResult );
}

void test_usGenerateChecksum_TwoByteAlligned( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 1;
    size_t uxUnalligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnalligned = 0; uxUnalligned < 4; uxUnalligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnalligned ] ) & 0x02U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnalligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 43776, usResult );
}

void test_usGenerateChecksum_TwoByteAllignedTwoLength( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 2;
    size_t uxUnalligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnalligned = 0; uxUnalligned < 4; uxUnalligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnalligned ] ) & 0x02U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnalligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 43947, usResult );
}

void test_usGenerateChecksum_FourByteAlligned( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 2;
    size_t uxUnalligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnalligned = 0; uxUnalligned < 4; uxUnalligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnalligned ] ) & 0x04U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnalligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 43947, usResult );
}

void test_usGenerateChecksum_FourByteAllignedSumOverflow( void )
{
    uint16_t usResult;
    uint16_t usSum = FreeRTOS_htons( 0xFFFF - 0xAB );
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 20;
    size_t uxUnalligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnalligned = 0; uxUnalligned < 4; uxUnalligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnalligned ] ) & 0x04U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnalligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 2484, usResult );
}

void test_usGenerateChecksum_FourByteAllignedSumOverflow2( void )
{
    uint16_t usResult;
    uint16_t usSum = FreeRTOS_htons( 0xFFFF - 0xAB );
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 20;
    size_t uxUnalligned = 0;

    memset( pucNextData, 0xFF, ipconfigTCP_MSS );

    for( uxUnalligned = 0; uxUnalligned < 4; uxUnalligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnalligned ] ) & 0x04U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnalligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 21759, usResult );
}

void test_vPrintResourceStats_BufferCountMore( void )
{
    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS + 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 2 );

    vPrintResourceStats();
}

void test_vPrintResourceStats_BufferCountLess( void )
{
    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 2 );

    vPrintResourceStats();
}

void test_vPrintResourceStats_LastBuffer_NE_0( void )
{
    uxLastMinBufferCount = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
    uxMinLastSize = 10u;

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 2 );

    vPrintResourceStats();

    TEST_ASSERT_EQUAL( 2, uxMinLastSize );
}

void test_vPrintResourceStats_MinSizeIsBigger( void )
{
    uxLastMinBufferCount = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
    uxMinLastSize = 10u;

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 1024U * 1025U );

    vPrintResourceStats();

    TEST_ASSERT_EQUAL( 10, uxMinLastSize );
}

void test_FreeRTOS_strerror_r_Invalid( void )
{
    const char * pucResult;
    BaseType_t xErrnum = 0;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "Errno 0", pcBuffer );
}

void test_FreeRTOS_strerror_r_EADDRINUSE( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EADDRINUSE;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EADDRINUSE", pcBuffer );
}

void test_FreeRTOS_strerror_r_ENOMEM( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ENOMEM;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ENOMEM", pcBuffer );
}

void test_FreeRTOS_strerror_r_EADDRNOTAVAIL( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EADDRNOTAVAIL;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EADDRNOTAVAIL", pcBuffer );
}

void test_FreeRTOS_strerror_r_ENOPROTOOPT( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ENOPROTOOPT;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ENOPROTOOPT", pcBuffer );
}

void test_FreeRTOS_strerror_r_EBADF( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EBADF;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EBADF", pcBuffer );
}

void test_FreeRTOS_strerror_r_ENOSPC( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ENOSPC;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ENOSPC", pcBuffer );
}

void test_FreeRTOS_strerror_r_ECANCELED( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ECANCELED;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ECANCELED", pcBuffer );
}

void test_FreeRTOS_strerror_r_ENOTCONN( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ENOTCONN;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ENOTCONN", pcBuffer );
}

void test_FreeRTOS_strerror_r_EINPROGRESS( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EINPROGRESS;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EINPROGRESS", pcBuffer );
}

void test_FreeRTOS_strerror_r_EOPNOTSUPP( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EOPNOTSUPP;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EOPNOTSUPP", pcBuffer );
}

void test_FreeRTOS_strerror_r_EINTR( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EINTR;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EINTR", pcBuffer );
}

void test_FreeRTOS_strerror_r_ETIMEDOUT( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ETIMEDOUT;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ETIMEDOUT", pcBuffer );
}

void test_FreeRTOS_strerror_r_EINVAL( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EINVAL;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EINVAL", pcBuffer );
}

void test_FreeRTOS_strerror_r_EWOULDBLOCK( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EWOULDBLOCK;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EWOULDBLOCK", pcBuffer );
}

void test_FreeRTOS_strerror_r_EISCONN( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EISCONN;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EISCONN", pcBuffer );
}

void test_FreeRTOS_strerror_r_ZeroLengthBuffer( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EISCONN;
    char pcBuffer[ 100 ];
    size_t uxLength = 0;

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "", pcBuffer );
}

void test_FreeRTOS_max_int32( void )
{
    int32_t smaller, bigger, lResult;

    for( int i = -100; i < 100; i++ )
    {
        for( int j = -100; j <= i; j++ )
        {
            lResult = FreeRTOS_max_int32( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }

    for( int i = ( 0x6FFFFFFF - 100 ); i < ( 0x6FFFFFFF + 100 ); i++ )
    {
        for( int j = ( 0x6FFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_max_int32( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }
}

void test_FreeRTOS_max_uint32( void )
{
    uint32_t smaller, bigger, lResult;

    for( uint32_t i = 0; i < 100; i++ )
    {
        for( uint32_t j = 0; j <= i; j++ )
        {
            lResult = FreeRTOS_max_uint32( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }

    for( uint32_t i = ( 0xDFFFFFFF - 100 ); i < ( 0xDFFFFFFF + 100 ); i++ )
    {
        for( uint32_t j = ( 0xDFFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_max_uint32( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }
}

void test_FreeRTOS_max_size_t( void )
{
    uint32_t smaller, bigger, lResult;

    for( uint32_t i = 0; i < 100; i++ )
    {
        for( uint32_t j = 0; j <= i; j++ )
        {
            lResult = FreeRTOS_max_size_t( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }

    for( uint32_t i = ( 0xDFFFFFFF - 100 ); i < ( 0xDFFFFFFF + 100 ); i++ )
    {
        for( uint32_t j = ( 0xDFFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_max_size_t( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }
}

void test_FreeRTOS_min_int32( void )
{
    int32_t smaller, bigger, lResult;

    for( int i = -100; i < 100; i++ )
    {
        for( int j = -100; j <= i; j++ )
        {
            lResult = FreeRTOS_min_int32( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }

    for( int i = ( 0x6FFFFFFF - 100 ); i < ( 0x6FFFFFFF + 100 ); i++ )
    {
        for( int j = ( 0x6FFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_min_int32( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }
}

void test_FreeRTOS_min_uint32( void )
{
    uint32_t smaller, bigger, lResult;

    for( uint32_t i = 0; i < 100; i++ )
    {
        for( uint32_t j = 0; j <= i; j++ )
        {
            lResult = FreeRTOS_min_uint32( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }

    for( uint32_t i = ( 0xDFFFFFFF - 100 ); i < ( 0xDFFFFFFF + 100 ); i++ )
    {
        for( uint32_t j = ( 0xDFFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_min_uint32( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }
}

void test_FreeRTOS_min_size_t( void )
{
    uint32_t smaller, bigger, lResult;

    for( uint32_t i = 0; i < 100; i++ )
    {
        for( uint32_t j = 0; j <= i; j++ )
        {
            lResult = FreeRTOS_min_size_t( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }

    for( uint32_t i = ( 0xDFFFFFFF - 100 ); i < ( 0xDFFFFFFF + 100 ); i++ )
    {
        for( uint32_t j = ( 0xDFFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_min_size_t( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }
}

void test_FreeRTOS_round_up( void )
{
    uint32_t ulResult;
    uint32_t a, d;

    a = 0;
    d = 0;
    catch_assert( FreeRTOS_round_up( a, d ) );

    a = 32;
    d = 5;
    ulResult = FreeRTOS_round_up( a, d );
    TEST_ASSERT_EQUAL( 35, ulResult );

    a = 0xFFFFFFF7;
    d = 3;
    ulResult = FreeRTOS_round_up( a, d );
    TEST_ASSERT_EQUAL( 0xFFFFFFF9, ulResult );

    a = 0x123AB;
    d = 7;
    ulResult = FreeRTOS_round_up( a, d );
    TEST_ASSERT_EQUAL( 0x123AD, ulResult );

    a = 0x123AD;
    d = 7;
    ulResult = FreeRTOS_round_up( a, d );
    TEST_ASSERT_EQUAL( 0x123AD, ulResult );
}

void test_FreeRTOS_round_down( void )
{
    uint32_t ulResult;
    uint32_t a, d;

    a = 0;
    d = 0;
    catch_assert( FreeRTOS_round_down( a, d ) );

    a = 32;
    d = 5;
    ulResult = FreeRTOS_round_down( a, d );
    TEST_ASSERT_EQUAL( 30, ulResult );

    a = 0xFFFFFFF7;
    d = 3;
    ulResult = FreeRTOS_round_down( a, d );
    TEST_ASSERT_EQUAL( 0xFFFFFFF6, ulResult );

    a = 0x123AB;
    d = 7;
    ulResult = FreeRTOS_round_down( a, d );
    TEST_ASSERT_EQUAL( 0x123A6, ulResult );

    a = 0x123AD;
    d = 7;
    ulResult = FreeRTOS_round_down( a, d );
    TEST_ASSERT_EQUAL( 0x123AD, ulResult );
}

void test_ulChar2u32( void )
{
    uint32_t ulResult;
    uint8_t pucPtr[] = { 0xAA, 0x00, 0x12, 0xEF };

    ulResult = ulChar2u32( pucPtr );

    TEST_ASSERT_EQUAL_UINT32( 0xAA0012EF, ulResult );
}

void test_usChar2u16( void )
{
    uint16_t usResult;
    uint8_t pucPtr[] = { 0xAA, 0x00, 0x12, 0xEF };

    usResult = usChar2u16( pucPtr );

    TEST_ASSERT_EQUAL_UINT16( 0xAA00, usResult );

    usResult = usChar2u16( &pucPtr[ 2 ] );

    TEST_ASSERT_EQUAL_UINT16( 0x12EF, usResult );
}
