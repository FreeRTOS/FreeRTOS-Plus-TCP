/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IPv4.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_IPv4_Utils.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_task.h"
#include "mock_NetworkBufferManagement.h"

#include "FreeRTOS_ARP.h"

#include "FreeRTOS_ARP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

extern ARPCacheRow_t xARPCache[ ipconfigARP_CACHE_ENTRIES ];

extern NetworkBufferDescriptor_t * pxARPWaitingNetworkBuffer;

extern BaseType_t xARPHadIPClash;

/* Helper function to reset the uxARPClashCounter variable before a test is run. It
 * cannot be directly reset since it is declared as static. */
static void vResetARPClashCounter( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;
    struct xNetworkEndPoint xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    /* Different protocol length. */
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES + 1;

    xNetworkBuffer.pucEthernetBuffer = &xARPFrame;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    /* Regardless of whether this is called or not, the test should not fail. */
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );

    eResult = eARPProcessPacket( &xNetworkBuffer );

    /* Stop ignoring after the helper function is called. */
    xTaskCheckForTimeOut_StopIgnore();
}

void test_xCheckLoopback_IncorrectFrameType( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    BaseType_t xResult;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( IPPacket_t );

    IPPacket_t * pxIPPacket = ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );

    /* =================================================== */
    /* Let the frame-type be anything else than IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE + 1;
    /* bReleaseAfterSend parameter doesn't matter here. */
    xResult = xCheckLoopback( pxNetworkBuffer, pdFALSE );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );
    /* =================================================== */
}

void test_xCheckLoopback_IncorrectMACAddress( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    BaseType_t xResult;
    NetworkEndPoint_t xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( IPPacket_t );

    IPPacket_t * pxIPPacket = ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );

    /* =================================================== */
    /* Let the frame-type be IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* But let the MAC address be different. */
    memset( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, 0xAA, ipMAC_ADDRESS_LENGTH_BYTES );
    /* bReleaseAfterSend parameter doesn't matter here. */
    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( &xEndPoint );
    xResult = xCheckLoopback( pxNetworkBuffer, pdFALSE );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );
    /* =================================================== */
}

void test_xCheckLoopback_HappyCase( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    BaseType_t xResult;
    NetworkEndPoint_t xEndPoint;
    uint8_t ucBytes[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x22, 0x33, 0x44, 0x55, 0x66 };

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( IPPacket_t );


    IPPacket_t * pxIPPacket = ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );

    /* =================================================== */
    /* Let the frame-type be IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( &xEndPoint );
    /* Make the MAC address same. */
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
    memcpy( xEndPoint.xMACAddress.ucBytes, ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( pxNetworkBuffer, pxNetworkBuffer->xDataLength, pxNetworkBuffer );
    xSendEventStructToIPTask_IgnoreAndReturn( pdTRUE );

    xResult = xCheckLoopback( pxNetworkBuffer, pdFALSE );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    /* =================================================== */
}

void test_xCheckLoopback_DuplicationFails( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    BaseType_t xResult;
    NetworkEndPoint_t xEndPoint;
    uint8_t ucBytes[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x22, 0x33, 0x44, 0x55, 0x66 };

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( IPPacket_t );

    IPPacket_t * pxIPPacket = ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( &xEndPoint );
    /* =================================================== */
    /* Let the frame-type be IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* Make the MAC address same. */
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
    /* Make buffer duplication fail. */
    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( pxNetworkBuffer, pxNetworkBuffer->xDataLength, NULL );
    xResult = xCheckLoopback( pxNetworkBuffer, pdFALSE );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    /* =================================================== */
}


void test_xCheckLoopback_SendEventToIPTaskFails( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    BaseType_t xResult;
    NetworkEndPoint_t xEndPoint;
    uint8_t ucBytes[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x22, 0x33, 0x44, 0x55, 0x66 };

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( IPPacket_t );

    IPPacket_t * pxIPPacket = ( IPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );


    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( &xEndPoint );
    /* =================================================== */
    /* Let the frame-type be IPv4. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* Make the MAC address same. */
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );

    xSendEventStructToIPTask_IgnoreAndReturn( pdFALSE );
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    xResult = xCheckLoopback( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    /* =================================================== */
}

void test_eARPProcessPacket_DifferentHardwareAddress( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Different Hardware address. */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET + 1;
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;

    /* When the local IP address is 0, we should not process any ARP Packets. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0UL;
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_DifferentProtocolType( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    /* Different protocol type */
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE + 1;
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;

    /* When the local IP address is 0, we should not process any ARP Packets. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0UL;
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_DifferentHardwareLength( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    /* Different MAC address length. */
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES + 1;
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;

    /* When the local IP address is 0, we should not process any ARP Packets. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0UL;
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_DifferentProtocolLength( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    /* Different protocol length. */
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES + 1;
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;

    /* When the local IP address is 0, we should not process any ARP Packets. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0UL;
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_SourceMACIsBroadcast( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;

    /* Copy the broadcast MAC address into the sender hardware address. */
    memcpy( &( xARPFrame.xARPHeader.xSenderHardwareAddress ), &xBroadcastMACAddress, sizeof( MACAddress_t ) );
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_SourceMACIsMulticast( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    xARPFrame.xARPHeader.xSenderHardwareAddress.ucBytes[ 0 ] = 0x01;
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );

    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_IPIsLocalLoopBack( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    uint32_t ulSenderProtocolAddress = FreeRTOS_htonl( ipFIRST_LOOPBACK_IPv4 + 10 );
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress,
            &ulSenderProtocolAddress,
            sizeof( ulSenderProtocolAddress ) );
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_SenderIPLessThanLoopBack( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    uint32_t ulSenderProtocolAddress = FreeRTOS_htonl( ipFIRST_LOOPBACK_IPv4 - 10 );
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress,
            &ulSenderProtocolAddress,
            sizeof( ulSenderProtocolAddress ) );
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_LocalIPisZero( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;

    /* When the local IP address is 0, we should not process any ARP Packets. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0UL;
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_InvalidOperation( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    /* What if some invalid option is sent in the ARP Packet? */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Add invalid operation */
    xARPFrame.xARPHeader.usOperation = ipARP_REQUEST | ipARP_REPLY;
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

void test_eARPProcessPacket_Request_DifferentIP( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* Process an ARP request, but not meant for this node. */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REQUEST;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER + 0x11;
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );
    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( 1 );
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReturnEthernetFrame, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_Request_SenderMACSameAsLocalMAC( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* Process an ARP request, but not meant for this node. */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    memset( ipLOCAL_MAC_ADDRESS, 0x22, sizeof( MACAddress_t ) );
    memcpy( &( xARPFrame.xARPHeader.xSenderHardwareAddress ), ipLOCAL_MAC_ADDRESS, sizeof( MACAddress_t ) );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REQUEST;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    pxNetworkBuffer->pucEthernetBuffer = &xARPFrame;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );
    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( 1 );
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReturnEthernetFrame, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_Request_SenderAndTargetDifferent( void )
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucBuffer[ sizeof( IPPacket_t ) + ipBUFFER_PADDING ];
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    /* Process an ARP request - meant for this node with target and source different. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REQUEST;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress, &( xARPFrame.xARPHeader.ulTargetProtocolAddress ), sizeof( xARPFrame.xARPHeader.ulTargetProtocolAddress ) );
    /* Make sure the the destination and source IP addresses are different. */
    xARPFrame.xARPHeader.ucSenderProtocolAddress[ 0 ]++;

    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;
    xNetworkBuffer.pucEthernetBuffer = &xARPFrame;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );
    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( 1 );
    eResult = eARPProcessPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( eReturnEthernetFrame, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_Request_SenderAndTargetSame( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;
    NetworkInterface_t xInterface;
    struct xNetworkEndPoint xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    /* Process an ARP request - meant for this node with target and source same. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REQUEST;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress, &( xARPFrame.xARPHeader.ulTargetProtocolAddress ), sizeof( xARPFrame.xARPHeader.ulTargetProtocolAddress ) );

    /* Reset the private variable uxARPClashCounter. */
    vResetARPClashCounter();

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAndReturn( *ipLOCAL_IP_ADDRESS_POINTER, 2, &xEndPoint );
    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( 1 );

    xNetworkBuffer.pucEthernetBuffer = &xARPFrame;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;

    eResult = eARPProcessPacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( eReturnEthernetFrame, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_Reply_TargetIPSameAsLocalIP( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;
    NetworkInterface_t xInterface;
    struct xNetworkEndPoint xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );
    memset( xARPCache, 0, sizeof( xARPCache ) );

    /* Process an ARP request, but not meant for this node. */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    memset( ipLOCAL_MAC_ADDRESS, 0x22, sizeof( MACAddress_t ) );
    memcpy( &( xARPFrame.xARPHeader.xSenderHardwareAddress ), ipLOCAL_MAC_ADDRESS, sizeof( MACAddress_t ) );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REPLY;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER;

    uint32_t ulSenderProtocolAddress = 0xFFAAEEBB;
    memcpy( &( xARPFrame.xARPHeader.ucSenderProtocolAddress ), &ulSenderProtocolAddress, sizeof( uint32_t ) );

    /* Reset the private variable uxARPClashCounter. */
    vResetARPClashCounter();

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAndReturn( ulSenderProtocolAddress, 2, &xEndPoint );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );

    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;
    xEndPoint.ipv4_settings.ulIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    xNetworkBuffer.pucEthernetBuffer = &xARPFrame;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    eResult = eARPProcessPacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    TEST_ASSERT_EQUAL( pdTRUE, xIsIPInARPCache( ulSenderProtocolAddress ) );
    /* =================================================== */
}

void test_eARPProcessPacket_Reply_TargetIPNotSameAsLocalIP_ButEntryInCache( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;
    NetworkInterface_t xInterface;
    struct xNetworkEndPoint xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );
    memset( xARPCache, 0, sizeof( xARPCache ) );

    /* Process an ARP request, but not meant for this node. */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    memset( ipLOCAL_MAC_ADDRESS, 0x22, sizeof( MACAddress_t ) );
    memcpy( &( xARPFrame.xARPHeader.xSenderHardwareAddress ), ipLOCAL_MAC_ADDRESS, sizeof( MACAddress_t ) );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REPLY;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER + 1;

    uint32_t ulSenderProtocolAddress = 0xFFAAEEBB;
    memcpy( &( xARPFrame.xARPHeader.ucSenderProtocolAddress ), &ulSenderProtocolAddress, sizeof( uint32_t ) );

    xARPCache[ 0 ].ulIPAddress = ulSenderProtocolAddress;
    xARPCache[ 0 ].ucAge = 1;
    xARPCache[ 0 ].ucValid = 1;

    /* Reset the private variable uxARPClashCounter. */
    vResetARPClashCounter();

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAndReturn( ulSenderProtocolAddress, 2, &xEndPoint );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );

    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;
    xNetworkBuffer.pucEthernetBuffer = &xARPFrame;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    eResult = eARPProcessPacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    TEST_ASSERT_EQUAL( pdTRUE, xIsIPInARPCache( ulSenderProtocolAddress ) );
    TEST_ASSERT_EQUAL( ipconfigMAX_ARP_AGE, xARPCache[ 0 ].ucAge );
    /* =================================================== */
}


void test_eARPProcessPacket_Reply_SenderAndTargetSame( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;
    NetworkInterface_t xInterface;
    struct xNetworkEndPoint xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    /* Process an ARP reply - meant for this node with target and source same. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REPLY;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = 0xAABBCCDD;
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress, &( xARPFrame.xARPHeader.ulTargetProtocolAddress ), sizeof( xARPFrame.xARPHeader.ulTargetProtocolAddress ) );

    /* Reset the private variable uxARPClashCounter. */
    vResetARPClashCounter();

    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;
    xEndPoint.ipv4_settings.ulIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    xNetworkBuffer.pucEthernetBuffer = &xARPFrame;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );
    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( 1 );

    /* Reset the flag. */
    xARPHadIPClash = pdFALSE;

    eResult = eARPProcessPacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    TEST_ASSERT_EQUAL( pdTRUE, xARPHadIPClash );
    /* =================================================== */

    /* Reset the flag. */
    xARPHadIPClash = pdFALSE;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );
    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( 1 );

    /* Call it again and do not expect the task functions to be called. */
    eResult = eARPProcessPacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    TEST_ASSERT_EQUAL( pdTRUE, xARPHadIPClash );
}

void test_eARPProcessPacket_Reply_DifferentIP( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;
    NetworkInterface_t xInterface;
    struct xNetworkEndPoint xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    /* Process an ARP reply - not meant for this node. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REPLY;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER + 0x11;
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress, &( xARPFrame.xARPHeader.ulTargetProtocolAddress ), sizeof( xARPFrame.xARPHeader.ulTargetProtocolAddress ) );

    /* Reset the private variable uxARPClashCounter. */
    vResetARPClashCounter();

    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;
    xNetworkBuffer.pucEthernetBuffer = &xARPFrame;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );

    eResult = eARPProcessPacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_Reply_DifferentIP_WaitingBufferNonNull( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t xLocalBuffer;
    uint8_t pucLocalEthernetBuffer[ 1500 ];
    NetworkInterface_t xInterface;
    struct xNetworkEndPoint xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* Clear the buffer. */
    memset( pucLocalEthernetBuffer, 0, sizeof( pucLocalEthernetBuffer ) );

    xLocalBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    pxARPWaitingNetworkBuffer = &xLocalBuffer;

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    /* Process an ARP reply - not meant for this node. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REPLY;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER + 0x11;
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress, &( xARPFrame.xARPHeader.ulTargetProtocolAddress ), sizeof( xARPFrame.xARPHeader.ulTargetProtocolAddress ) );

    /* Reset the private variable uxARPClashCounter. */
    vResetARPClashCounter();

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );

    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;
    xNetworkBuffer.pucEthernetBuffer = &xARPFrame;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    eResult = eARPProcessPacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    /* =================================================== */
}

void test_eARPProcessPacket_Reply_WaitingBufferNonNull_MatchingAddress1( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t xLocalBuffer;
    NetworkInterface_t xInterface;
    struct xNetworkEndPoint xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;

    uint8_t pucLocalEthernetBuffer[ 1500 ];
    IPPacket_t * pxARPWaitingIPPacket = ( ( IPPacket_t * ) pucLocalEthernetBuffer );
    IPHeader_t * pxARPWaitingIPHeader = &( pxARPWaitingIPPacket->xIPHeader );

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* Clear the buffer. */
    memset( pucLocalEthernetBuffer, 0, sizeof( pucLocalEthernetBuffer ) );

    xLocalBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    pxARPWaitingNetworkBuffer = &xLocalBuffer;

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    /* Process an ARP reply - not meant for this node. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REPLY;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER + 0x11;
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress, &( xARPFrame.xARPHeader.ulTargetProtocolAddress ), sizeof( xARPFrame.xARPHeader.ulTargetProtocolAddress ) );

    memcpy( &( pxARPWaitingIPHeader->ulSourceIPAddress ), xARPFrame.xARPHeader.ucSenderProtocolAddress, sizeof( pxARPWaitingIPHeader->ulSourceIPAddress ) );

    /* Reset the private variable uxARPClashCounter. */
    vResetARPClashCounter();

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );

    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;
    xNetworkBuffer.pucEthernetBuffer = &xARPFrame;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    xSendEventStructToIPTask_IgnoreAndReturn( pdFAIL );
    vReleaseNetworkBufferAndDescriptor_Ignore();
    vIPSetARPResolutionTimerEnableState_Expect( pdFALSE );

    eResult = eARPProcessPacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    TEST_ASSERT_EQUAL( NULL, pxARPWaitingNetworkBuffer );
    /* =================================================== */
}

void test_eARPProcessPacket_Reply_WaitingBufferNonNull_MatchingAddress2( void )
{
    ARPPacket_t xARPFrame;
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t xLocalBuffer;
    uint8_t pucLocalEthernetBuffer[ 1500 ];
    NetworkInterface_t xInterface;
    struct xNetworkEndPoint xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;

    IPPacket_t * pxARPWaitingIPPacket = ( ( IPPacket_t * ) pucLocalEthernetBuffer );
    IPHeader_t * pxARPWaitingIPHeader = &( pxARPWaitingIPPacket->xIPHeader );

    memset( &xARPFrame, 0, sizeof( ARPPacket_t ) );

    /* Clear the buffer. */
    memset( pucLocalEthernetBuffer, 0, sizeof( pucLocalEthernetBuffer ) );

    xLocalBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    pxARPWaitingNetworkBuffer = &xLocalBuffer;

    /* =================================================== */
    /* Add settings required for ARP header to pass checks */
    xARPFrame.xARPHeader.usHardwareType = ipARP_HARDWARE_TYPE_ETHERNET;
    xARPFrame.xARPHeader.usProtocolType = ipARP_PROTOCOL_TYPE;
    xARPFrame.xARPHeader.ucHardwareAddressLength = ipMAC_ADDRESS_LENGTH_BYTES;
    xARPFrame.xARPHeader.ucProtocolAddressLength = ipIP_ADDRESS_LENGTH_BYTES;

    /* Process an ARP reply - not meant for this node. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCDD;
    /* Fill in the request option. */
    xARPFrame.xARPHeader.usOperation = ipARP_REPLY;
    xARPFrame.xARPHeader.ulTargetProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER + 0x11;
    memcpy( xARPFrame.xARPHeader.ucSenderProtocolAddress, &( xARPFrame.xARPHeader.ulTargetProtocolAddress ), sizeof( xARPFrame.xARPHeader.ulTargetProtocolAddress ) );

    memcpy( &( pxARPWaitingIPHeader->ulSourceIPAddress ), xARPFrame.xARPHeader.ucSenderProtocolAddress, sizeof( pxARPWaitingIPHeader->ulSourceIPAddress ) );

    /* Reset the private variable uxARPClashCounter. */
    vResetARPClashCounter();

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );

    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;
    xNetworkBuffer.pucEthernetBuffer = &xARPFrame;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    xSendEventStructToIPTask_IgnoreAndReturn( pdPASS );
    vIPSetARPResolutionTimerEnableState_Expect( pdFALSE );

    eResult = eARPProcessPacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    TEST_ASSERT_EQUAL( NULL, pxARPWaitingNetworkBuffer );
    /* =================================================== */
}

void test_xIsIPInARPCache_NoMatchingIP( void )
{
    uint32_t ulIPAddress = 0x1234ABCD;
    BaseType_t xResult;

    for( uint16_t x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        xARPCache[ x ].ulIPAddress = 0;
    }

    xResult = xIsIPInARPCache( ulIPAddress );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

void test_xIsIPInARPCache_MatchingIPButEntryInvalid( void )
{
    uint32_t ulIPAddress = 0x1234ABCD;
    BaseType_t xResult;

    for( uint16_t x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        xARPCache[ x ].ulIPAddress = 0;
        xARPCache[ x ].ucValid = ( uint8_t ) pdFALSE;
    }

    xARPCache[ 0 ].ulIPAddress = ulIPAddress;

    xResult = xIsIPInARPCache( ulIPAddress );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

void test_xIsIPInARPCache_MatchingIP1( void )
{
    uint32_t ulIPAddress = 0x1234ABCD;
    BaseType_t xResult;

    for( uint16_t x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        xARPCache[ x ].ulIPAddress = 0;
        xARPCache[ x ].ucValid = ( uint8_t ) pdTRUE;
    }

    xARPCache[ 0 ].ulIPAddress = ulIPAddress;

    xResult = xIsIPInARPCache( ulIPAddress );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

void test_xIsIPInARPCache_MatchingIP2( void )
{
    uint32_t ulIPAddress = 0x1234ABCD;
    BaseType_t xResult;

    for( uint16_t x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        xARPCache[ x ].ulIPAddress = 0;
        xARPCache[ x ].ucValid = ( uint8_t ) pdTRUE;
    }

    xARPCache[ ipconfigARP_CACHE_ENTRIES - 1 ].ulIPAddress = ulIPAddress;

    xResult = xIsIPInARPCache( ulIPAddress );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

void test_xCheckRequiresARPResolution_NotOnLocalNetwork( void )
{
    struct xNetworkEndPoint xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];
    BaseType_t xResult;
    NetworkInterface_t xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    IPPacket_t * pxIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    IPHeader_t * pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD1234;

    xEndPoint.ipv4_settings.ulNetMask = 0xFFFFFF00;
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    /* Make sure there is no match. */
    pxIPHeader->ulSourceIPAddress = ~( *ipLOCAL_IP_ADDRESS_POINTER & xEndPoint.ipv4_settings.ulNetMask );

    xResult = xCheckRequiresARPResolution( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

void test_xCheckRequiresARPResolution_OnLocalNetwork_NotInCache( void )
{
    struct xNetworkEndPoint xEndPoint;
    NetworkInterface_t xInterface;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];
    BaseType_t xResult;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    IPPacket_t * pxIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    IPHeader_t * pxIPHeader = &( pxIPPacket->xIPHeader );

    *ipLOCAL_IP_ADDRESS_POINTER = 0xABCD1234;

    xEndPoint.ipv4_settings.ulNetMask = 0xFFFFFF00;
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    /* Make sure there is a match. */
    pxIPHeader->ulSourceIPAddress = *ipLOCAL_IP_ADDRESS_POINTER & xEndPoint.ipv4_settings.ulNetMask;
    xEndPoint.ipv4_settings.ulIPAddress = *ipLOCAL_IP_ADDRESS_POINTER & xEndPoint.ipv4_settings.ulNetMask;
    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;

    /* And that the IP is not in ARP cache. */
    for( uint16_t x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        xARPCache[ x ].ulIPAddress = 0;
    }

    FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);

    /* For this unit-test, we do not concern ourselves with whether the ARP request
     * is actually sent or not. Effort is all that matters. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    
    FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);

    xResult = xCheckRequiresARPResolution( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

void test_xCheckRequiresARPResolution_OnLocalNetwork_InCache( void )
{
    struct xNetworkEndPoint xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];
    BaseType_t xResult;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    IPPacket_t * pxIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    IPHeader_t * pxIPHeader = &( pxIPPacket->xIPHeader );

    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    xEndPoint.ipv4_settings.ulNetMask = 0xFFFFFF00;

    /* Make sure there is a match. */
    pxIPHeader->ulSourceIPAddress = xEndPoint.ipv4_settings.ulIPAddress & xEndPoint.ipv4_settings.ulNetMask;

    xNetworkBuffer.pxEndPoint = &xEndPoint;

    /* And that the IP is not in ARP cache. */
    for( uint16_t x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        xARPCache[ x ].ulIPAddress = pxIPHeader->ulSourceIPAddress;
        xARPCache[ x ].ucValid = ( uint8_t ) pdTRUE;
    }

    xResult = xCheckRequiresARPResolution( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}


void test_ulARPRemoveCacheEntryByMac_NoMatch( void )
{
    uint32_t ulResult;
    const MACAddress_t xMACAddress = { 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA };
    int i;
    BaseType_t xEntryToCheck;
    uint8_t ucBuffer[ sizeof( xARPCache[ 0 ] ) ];

    /* Catch some asserts. */
    catch_assert( ulARPRemoveCacheEntryByMac( NULL ) );

    /* =================================================== */
    /* Make sure no entry matches. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    }

    ulResult = ulARPRemoveCacheEntryByMac( &xMACAddress );
    TEST_ASSERT_EQUAL( 0, ulResult );
    /* =================================================== */
}

void test_ulARPRemoveCacheEntryByMac_OneMatchingEntry( void )
{
    uint32_t ulResult;
    const MACAddress_t xMACAddress = { 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA };
    int i;
    BaseType_t xEntryToCheck;
    uint8_t ucBuffer[ sizeof( xARPCache[ 0 ] ) ];

    /* =================================================== */
    /* Make sure only one entry matches. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    }

    xEntryToCheck = 1;
    xARPCache[ xEntryToCheck ].ulIPAddress = 0xAABBCCEE;
    memset( xARPCache[ xEntryToCheck ].xMACAddress.ucBytes, 0xAA, sizeof( xMACAddress.ucBytes ) );
    memset( ucBuffer, 0, sizeof( xARPCache[ 0 ] ) );
    ulResult = ulARPRemoveCacheEntryByMac( &xMACAddress );
    TEST_ASSERT_EQUAL( 0xAABBCCEE, ulResult );
    TEST_ASSERT_EQUAL( 0, memcmp( ucBuffer, &xARPCache[ xEntryToCheck ], sizeof( xARPCache[ 0 ] ) ) );
}

void test_vARPRefreshCacheEntry_NULLMAC_NoMatchingEntry( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;
    struct xNetworkEndPoint xEndPoint;

    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = 255;
        xARPCache[ i ].ucValid = pdTRUE;
    }

    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );

    ulIPAddress = 0x00;
    /* Pass a NULL MAC Address and an IP address which will not match. */
    vARPRefreshCacheEntry( NULL, ulIPAddress, &xEndPoint );

    /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
    TEST_ASSERT_EQUAL( xARPCache[ 0 ].ucAge, ( uint8_t ) ipconfigMAX_ARP_RETRANSMISSIONS );
    TEST_ASSERT_EQUAL( xARPCache[ 0 ].ucValid, ( uint8_t ) pdFALSE );
    /* =================================================== */
}

void test_vARPRefreshCacheEntry_NULLMAC_MatchingEntry( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;
    struct xNetworkEndPoint xEndPoint;

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = 255;
        xARPCache[ i ].ucValid = pdTRUE;
    }

    xARPCache[ 1 ].ulIPAddress = 0xAABBCCEE;

    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );

    ulIPAddress = 0xAABBCCEE;
    /* Pass a NULL MAC Address and an IP address which will match. */
    vARPRefreshCacheEntry( NULL, ulIPAddress, &xEndPoint );

    /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
    TEST_ASSERT_EQUAL( xARPCache[ 1 ].ucAge, 255 );
    TEST_ASSERT_EQUAL( xARPCache[ 1 ].ucValid, ( uint8_t ) pdTRUE );
    /* =================================================== */
}

void test_vARPRefreshCacheEntry_MACWontMatch_IPWillMatch( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;
    struct xNetworkEndPoint xEndPoint;

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = 255;
        xARPCache[ i ].ucValid = pdTRUE;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x34, sizeof( xMACAddress.ucBytes ) );
    }

    xUseEntry = 1;
    xARPCache[ xUseEntry ].ulIPAddress = 0xAABBCCEE;

    ulIPAddress = 0xAABBCCEE;
    memset( xMACAddress.ucBytes, 0x11, ipMAC_ADDRESS_LENGTH_BYTES );
    /* Pass a MAC Address which won't match and an IP address which will match. */

    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );

    vARPRefreshCacheEntry( &xMACAddress, ulIPAddress, &xEndPoint );

    /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
    TEST_ASSERT_EQUAL_MESSAGE( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry ].ucAge, "Test 3" );
    TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry ].ucValid );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xARPCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( xMACAddress.ucBytes ) );
    /* =================================================== */
}

void test_vARPRefreshCacheEntry_MACAndIPWillMatch( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;
    struct xNetworkEndPoint xEndPoint;

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = 255;
        xARPCache[ i ].ucValid = pdFALSE;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x34, sizeof( xMACAddress.ucBytes ) );
    }

    xUseEntry = 1;
    xARPCache[ xUseEntry ].ulIPAddress = 0xAABBCCEE;
    /* Set a MAC address which will match */
    memset( xARPCache[ xUseEntry ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );

    ulIPAddress = 0xAABBCCEE;
    memset( xMACAddress.ucBytes, 0x11, ipMAC_ADDRESS_LENGTH_BYTES );

    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );

    /* Pass a MAC Address which will match and an IP address which will match too. */
    vARPRefreshCacheEntry( &xMACAddress, ulIPAddress, &xEndPoint );

    /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
    TEST_ASSERT_EQUAL_MESSAGE( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry ].ucAge, "Test 4" );
    TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry ].ucValid );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xARPCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( xMACAddress.ucBytes ) );
    /* =================================================== */
}


void test_vARPRefreshCacheEntry_IPOnADifferentSubnet( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;
    struct xNetworkEndPoint xEndPoint;

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = 255;
        xARPCache[ i ].ucValid = pdFALSE;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x34, sizeof( xMACAddress.ucBytes ) );
    }

    xUseEntry = 1;
    xARPCache[ xUseEntry ].ulIPAddress = 0xAABBCCEE;
    /* Set a MAC address which will match */
    memset( xARPCache[ xUseEntry ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    /* Set a local IP address */
    *ipLOCAL_IP_ADDRESS_POINTER = 0xAABBCCEF;

    /* The IP address being passed should not be on the same subnet. */
    ulIPAddress = 0x00BBCCEE;
    memset( xMACAddress.ucBytes, 0x11, ipMAC_ADDRESS_LENGTH_BYTES );
    /* Pass a MAC Address which will match and an IP address which will match too. */

    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( ( void * ) 124 );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );

    vARPRefreshCacheEntry( &xMACAddress, ulIPAddress, &xEndPoint );

    /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
    TEST_ASSERT_EQUAL_MESSAGE( ipconfigMAX_ARP_AGE, xARPCache[ 0 ].ucAge, "Test 5" );
    TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ 0 ].ucValid );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xARPCache[ 0 ].xMACAddress.ucBytes, sizeof( xMACAddress.ucBytes ) );
    /* =================================================== */
}

void test_vARPRefreshCacheEntry_IPAndMACInDifferentLocations( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;
    struct xNetworkEndPoint xEndPoint;

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = i + 1;
        xARPCache[ i ].ucValid = pdFALSE;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x34, sizeof( xMACAddress.ucBytes ) );
    }

    xUseEntry = 0;

    /* Make sure an entry matches. */
    xARPCache[ xUseEntry ].ulIPAddress = 0xAABBCCEE;
    ulIPAddress = 0xAABBCCEE;

    /* Also make sure that a MAC address matches. But a different one. */
    memset( xARPCache[ xUseEntry + 1 ].xMACAddress.ucBytes, 0x22, sizeof( xMACAddress.ucBytes ) );
    memset( xMACAddress.ucBytes, 0x22, ipMAC_ADDRESS_LENGTH_BYTES );

    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( ( void * ) 124 );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( ( void * ) 124 );

    /* Pass a MAC and IP Address which won't match, but age is now a factor. */
    vARPRefreshCacheEntry( &xMACAddress, ulIPAddress, &xEndPoint );

    /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
    TEST_ASSERT_EQUAL( xARPCache[ xUseEntry + 1 ].ulIPAddress, ulIPAddress );
    TEST_ASSERT_EQUAL_MESSAGE( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry + 1 ].ucAge, "Test 9" );
    TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry + 1 ].ucValid );

    uint8_t MemoryCompare[ sizeof( ARPCacheRow_t ) ];
    memset( MemoryCompare, 0, sizeof( ARPCacheRow_t ) );
    TEST_ASSERT_EQUAL_MEMORY( MemoryCompare, &xARPCache[ xUseEntry ], sizeof( ARPCacheRow_t ) );
    /* =================================================== */
}

void test_vARPRefreshCacheEntry_IPAndMACInDifferentLocations1( void )
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;
    int i;
    BaseType_t xUseEntry;
    struct xNetworkEndPoint xEndPoint;

    /* =================================================== */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        xARPCache[ i ].ucAge = i + 1;
        xARPCache[ i ].ucValid = pdFALSE;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x34, sizeof( xMACAddress.ucBytes ) );
    }

    xUseEntry = 0;

    /* Make sure an entry matches. */
    xARPCache[ xUseEntry ].ulIPAddress = 0xAABBCCEA;
    ulIPAddress = 0xAABBCCEE;

    /* Also make sure that a MAC address matches. But a different one. */
    memset( xARPCache[ xUseEntry + 1 ].xMACAddress.ucBytes, 0x22, sizeof( xMACAddress.ucBytes ) );
    memset( xMACAddress.ucBytes, 0x22, ipMAC_ADDRESS_LENGTH_BYTES );

    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn((void *) 0x1234);
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn((void *) 0x1234);

    /* Pass a MAC and IP Address which won't match, but age is now a factor. */
    vARPRefreshCacheEntry( &xMACAddress, ulIPAddress, &xEndPoint );

    /* Since no matching entry will be found with smallest age (i.e. oldest), 0th entry will be updated to have the below details. */
    TEST_ASSERT_EQUAL( xARPCache[ xUseEntry + 1 ].ulIPAddress, ulIPAddress );
    TEST_ASSERT_EQUAL_MESSAGE( ipconfigMAX_ARP_AGE, xARPCache[ xUseEntry + 1 ].ucAge, "Test 9" );
    TEST_ASSERT_EQUAL( ( uint8_t ) pdTRUE, xARPCache[ xUseEntry + 1 ].ucValid );
}

void test_eARPGetCacheEntryByMac_catchAssert( void )
{
    uint32_t ulIPAddress = 0x12345678, ulEntryToTest;
    eARPLookupResult_t eResult;
    MACAddress_t xMACAddress = { 0x22, 0x22, 0x22, 0x22, 0x22, 0x22 };
    int i;
    struct xNetworkInterface * xInterface;

    /* Hit some asserts */
    catch_assert( eARPGetCacheEntryByMac( NULL, &ulIPAddress, &xInterface ) );
    catch_assert( eARPGetCacheEntryByMac( &xMACAddress, NULL, &xInterface ) );
}

void test_eARPGetCacheEntryByMac_NoMatchingEntries( void )
{
    uint32_t ulIPAddress = 0x12345678, ulEntryToTest;
    eARPLookupResult_t eResult;
    MACAddress_t xMACAddress = { 0x22, 0x22, 0x22, 0x22, 0x22, 0x22 };
    int i;
    struct xNetworkInterface * xInterface;

    /* =================================================== */
    /* Make sure no entry matches. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    }

    eResult = eARPGetCacheEntryByMac( &xMACAddress, &ulIPAddress, &xInterface );
    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
    TEST_ASSERT_EQUAL( 0x12345678, ulIPAddress );
    /* =================================================== */
}

void test_eARPGetCacheEntryByMac_OneMatchingEntry( void )
{
    uint32_t ulIPAddress = 0x12345678, ulEntryToTest;
    eARPLookupResult_t eResult;
    MACAddress_t xMACAddress = { 0x22, 0x22, 0x22, 0x22, 0x22, 0x22 };
    int i;
    struct xNetworkInterface * xInterface;

    /* =================================================== */
    /* Make sure one entry matches. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAABBCCDD;
        memset( xARPCache[ i ].xMACAddress.ucBytes, 0x11, sizeof( xMACAddress.ucBytes ) );
    }

    ulEntryToTest = 1;
    memset( xARPCache[ ulEntryToTest ].xMACAddress.ucBytes, 0x22, sizeof( xMACAddress.ucBytes ) );
    xARPCache[ ulEntryToTest ].ulIPAddress = 0xAABBCCEE;
    eResult = eARPGetCacheEntryByMac( &xMACAddress, &ulIPAddress, &xInterface );
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    TEST_ASSERT_EQUAL( xARPCache[ ulEntryToTest ].ulIPAddress, ulIPAddress );
    /* =================================================== */
}

void test_eARPGetCacheEntry_CatchAssert( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    struct xNetworkInterface * xInterface;

    catch_assert( eARPGetCacheEntry( NULL, &xMACAddress, &xInterface ) );
    catch_assert( eARPGetCacheEntry( &ulIPAddress, NULL, &xInterface ) );
}

void test_eARPGetCacheEntry_IPMatchesBroadcastAddr( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;
    struct xNetworkEndPoint * pxEndPoint, xEndPoint;

    /* =================================================== */
    ulIPAddress = FreeRTOS_ntohl( xNetworkAddressing.ulBroadcastAddress );
    /* Not worried about what these functions do. */
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( &xEndPoint );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 3" );
    TEST_ASSERT_EQUAL( pxEndPoint, &xEndPoint );
    TEST_ASSERT_EQUAL_MEMORY_MESSAGE( &xBroadcastMACAddress, &xMACAddress, sizeof( xMACAddress ), "Test 3" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_IPMatchesOtherBroadcastAddr( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;
    struct xNetworkInterface * xInterface;
    struct xNetworkEndPoint * pxEndPoint, xEndPoint;

    /* =================================================== */
    ulIPAddress = FreeRTOS_ntohl( ipBROADCAST_IP_ADDRESS );
    /* Not worried about what these functions do. */
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( &xEndPoint );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress, &xInterface );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 3" );
    TEST_ASSERT_EQUAL_MEMORY_MESSAGE( &xBroadcastMACAddress, &xMACAddress, sizeof( xMACAddress ), "Test 3" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_LocalIPIsZero( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;
    struct xNetworkInterface * xInterface;
    struct xNetworkEndPoint * pxEndPoint, xEndPoint;

    /* =================================================== */
    *ipLOCAL_IP_ADDRESS_POINTER = 0;
    ulIPAddress = 0x1234;
    /* Not worried about what these functions do. */
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAndReturn( ulIPAddress, 4, ( void * ) 0x1234 );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress, &pxEndPoint );
    TEST_ASSERT_EQUAL_MESSAGE( eCantSendPacket, eResult, "Test 4" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_LocalIPMatchesReceivedIP( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;
    struct xNetworkInterface * xInterface;
    struct xNetworkEndPoint * pxEndPoint, xEndPoint;

    /* =================================================== */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    ulIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    /* Not worried about what these functions do. */
    xEndPoint.ipv4_settings.ulIPAddress = 0x1234;
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAndReturn( ulIPAddress, 4, ( void * ) 0x1234 );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress, &pxEndPoint );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 5" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_MatchingInvalidEntry( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;
    struct xNetworkInterface * xInterface;
    struct xNetworkEndPoint * pxEndPoint, xEndPoint;

    /* =================================================== */
    ulIPAddress = 0x4321;
    /* Make both values (IP address and local IP pointer) different. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    /* Add the IP address in the cache so that we'll have a cache hit. */
    xARPCache[ 1 ].ulIPAddress = xNetworkAddressing.ulGatewayAddress;
    /* But reset the valid bit. */
    xARPCache[ 1 ].ucValid = pdFALSE;
    /* Not worried about what these functions do. */
    xEndPoint.ipv4_settings.ulGatewayAddress = xNetworkAddressing.ulGatewayAddress;
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( &xEndPoint );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress, &xInterface );
    TEST_ASSERT_EQUAL_MESSAGE( eCantSendPacket, eResult, "Test 6" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_MatchingValidEntry( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;
    struct xNetworkInterface * xInterface;
    struct xNetworkEndPoint * pxEndPoint, xEndPoint;

    /* =================================================== */
    ulIPAddress = 0x4321;
    /* Make both values (IP address and local IP pointer) different. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    /* Add the IP address in the cache so that we'll have a cache hit. */
    xARPCache[ 1 ].ulIPAddress = xNetworkAddressing.ulGatewayAddress;
    /* Now try with a set valid bit. */
    xARPCache[ 1 ].ucValid = pdTRUE;
    /* Not worried about what these functions do. */
    xEndPoint.ipv4_settings.ulGatewayAddress = xNetworkAddressing.ulGatewayAddress;
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( &xEndPoint );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress, &xInterface );
    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheHit, eResult, "Test 7" );
    TEST_ASSERT_EQUAL_MEMORY_MESSAGE( &xARPCache[ 1 ].xMACAddress, &xMACAddress, sizeof( xMACAddress ), "Test 7" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_GatewayAddressZero( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;
    struct xNetworkInterface * xInterface;
    struct xNetworkEndPoint * pxEndPoint, xEndPoint;

    /* =================================================== */
    for( int i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ucValid = ( uint8_t ) pdFALSE;
    }

    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;

    ulIPAddress = 0x4321;
    /* Not worried about what these functions do. */
    xEndPoint.ipv4_settings.ulGatewayAddress = 0;
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( NULL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress, &xInterface );

    TEST_ASSERT_EQUAL_MESSAGE( eARPCacheMiss, eResult, "Test 9" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_AddressNotOnLocalAddress( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;
    struct xNetworkInterface * xInterface;

    /* =================================================== */
    ulIPAddress = 0;
    /* Make both values (IP address and local IP pointer) different. */
    /* Get any address on the same netmask. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x00000034;

    /* Not worried about what these functions do. */
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( NULL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress, &xInterface );
    TEST_ASSERT_EQUAL_MESSAGE( eCantSendPacket, eResult, "Test 11" );
    /* =================================================== */
}

void test_eARPGetCacheEntry_NoCacheHit( void )
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;
    eARPLookupResult_t eResult;
    uint32_t ulSavedGatewayAddress;
    struct xNetworkInterface * xInterface;

    /* =================================================== */
    for( int i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0;
        xARPCache[ i ].ucValid = ( uint8_t ) pdTRUE;
    }

    ulSavedGatewayAddress = xNetworkAddressing.ulGatewayAddress;
    xNetworkAddressing.ulGatewayAddress = 0;
    /* Make IP address param == 0 */
    ulIPAddress = 0;

    /* Make both values (IP address and local IP pointer) different
     * and on different net masks. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x1234;
    /* Not worried about what these functions do. */
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL );
    eResult = eARPGetCacheEntry( &ulIPAddress, &xMACAddress, &xInterface );
    xNetworkAddressing.ulGatewayAddress = ulSavedGatewayAddress;
    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    /* =================================================== */
}

void test_vARPAgeCache( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkInterface_t xInterface;

    xEndPoint.pxNext = NULL;
    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;

    /* Invalidate the first cache entry. */
    for( int i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ucAge = 0;
    }

    uint8_t ucEntryToCheck = 1;

    pxNetworkEndPoints = &xEndPoint;
    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;
    xEndPoint.ipv4_settings.ulIPAddress = 0x1234;

    /* =================================================== */
    /* Let the value returned first time be 0 such that the variable is reset. */
    xTaskGetTickCount_ExpectAndReturn( 0 );

    pxNetworkEndPoints = &xEndPoint;

    FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);

    /* The function which calls 'pxGetNetworkBufferWithDescriptor' is 'FreeRTOS_OutputARPRequest'.
     * It doesn't return anything and will be tested separately. */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );

    FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);

    vARPAgeCache();
    /* =================================================== */

    /* / * =================================================== * / */
    /* / * Make second entry invalid but with age > 1. * / */
    xARPCache[ ucEntryToCheck ].ucAge = 1;
    xARPCache[ ucEntryToCheck ].ucValid = pdFALSE;
    /* Set an IP address */
    xARPCache[ ucEntryToCheck ].ulIPAddress = 0xAAAAAAAA;
    
    FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);

    /* The function which calls 'pxGetNetworkBufferWithDescriptor' is 'FreeRTOS_OutputARPRequest'.
     * It doesn't return anything and will be tested separately. */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );

    FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);

    /* Let the value returned first time be 100. */
    xTaskGetTickCount_ExpectAndReturn( 100 );

    FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);

    /* The function which calls 'pxGetNetworkBufferWithDescriptor' is 'FreeRTOS_OutputARPRequest'.
     * It doesn't return anything and will be tested separately. */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );

    FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);

    vARPAgeCache();
    /* =================================================== */

    /* =================================================== */
    /* Make second entry invalid but with age > 1. */
    xARPCache[ ucEntryToCheck ].ucAge = 1;
    xARPCache[ ucEntryToCheck ].ucValid = pdTRUE;
    /* Set an IP address */
    xARPCache[ ucEntryToCheck ].ulIPAddress = 0xAAAAAAAA;

    FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);

    /* The function which calls 'pxGetNetworkBufferWithDescriptor' is 'FreeRTOS_OutputARPRequest'.
     * It doesn't return anything and will be tested separately. */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );

    FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);

    /* Let the value returned first time be 100. */
    xTaskGetTickCount_ExpectAndReturn( 100 );

    vARPAgeCache();
    /* =================================================== */

    /* =================================================== */
    /* Make second entry invalid but with age > 1. */
    xARPCache[ ucEntryToCheck ].ucAge = 100;
    xARPCache[ ucEntryToCheck ].ucValid = pdTRUE;
    /* Set an IP address */
    xARPCache[ ucEntryToCheck ].ulIPAddress = 0xAAAAAAAA;

    /* This time the pxGetNetworkBuffer will be called. */
    /* Let the value returned third time be 100000. */
    xTaskGetTickCount_ExpectAndReturn( 100000 );

    FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);

    /* The function which calls 'pxGetNetworkBufferWithDescriptor' is 'FreeRTOS_OutputARPRequest'.
     * It doesn't return anything and will be tested separately. */
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );

    FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);

    vARPAgeCache();
    /* =================================================== */
}

void test_vARPSendGratuitous( void )
{
    /* The output is ignored. But we should check the input though. */
    xSendEventToIPTask_ExpectAndReturn( eARPTimerEvent, 0 );
    vARPSendGratuitous();
}

uint32_t xNetworkInterfaceOutput_ARP_STUB_CallCount = 0;
BaseType_t xNetworkInterfaceOutput_ARP_STUB( NetworkInterface_t * pxInterface,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                             BaseType_t bReleaseAfterSend )
{
    xNetworkInterfaceOutput_ARP_STUB_CallCount++;
    return pdTRUE_UNSIGNED;
}

void test_FreeRTOS_OutputARPRequest( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkInterface_t xInterface;
    uint8_t ucBuffer[ sizeof( ARPPacket_t ) + ipBUFFER_PADDING + ipconfigETHERNET_MINIMUM_PACKET_BYTES ];
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulIPAddress = 0xAAAAAAAA;

    xNetworkBuffer.pucEthernetBuffer = ucBuffer;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );

    xEndPoint.bits.bEndPointUp = pdTRUE_UNSIGNED;
    xEndPoint.ipv4_settings.ulIPAddress = 0x1234;
    xEndPoint.pxNetworkInterface = &xInterface;
    xEndPoint.pxNetworkInterface->pfOutput = xNetworkInterfaceOutput_ARP_STUB;

    /* =================================================== */
    xNetworkInterfaceOutput_ARP_STUB_CallCount = 0;

    FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);
    
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, &xNetworkBuffer );

    xIsCallingFromIPTask_IgnoreAndReturn( pdTRUE );

    FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);
    
    FreeRTOS_OutputARPRequest( ulIPAddress );
    TEST_ASSERT_EQUAL( xNetworkInterfaceOutput_ARP_STUB_CallCount, 1 );
    /* =================================================== */

    /* =================================================== */
    xNetworkInterfaceOutput_ARP_STUB_CallCount = 0;

    FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);
    
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, &xNetworkBuffer );

    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    xSendEventStructToIPTask_IgnoreAndReturn( pdFALSE );
    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );
    FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);

    FreeRTOS_OutputARPRequest( ulIPAddress );
    TEST_ASSERT_EQUAL( xNetworkInterfaceOutput_ARP_STUB_CallCount, 0 );
    /* =================================================== */

    /* =================================================== */
    xNetworkInterfaceOutput_ARP_STUB_CallCount = 0;
    FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, &xNetworkBuffer );
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    xSendEventStructToIPTask_IgnoreAndReturn( pdPASS );
    FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);

    FreeRTOS_OutputARPRequest( ulIPAddress );

    TEST_ASSERT_EQUAL( xNetworkInterfaceOutput_ARP_STUB_CallCount, 0 );
    /* =================================================== */
}


void vStoreTimeValue( TimeOut_t * const timeout,
                      int32_t callbacks )
{
    timeout->xOverflowCount = 0;
    timeout->xTimeOnEntering = 100;
}

void test_xARPWaitResolution_PrivateFunctionReturnsHit( void )
{
    uint32_t ulIPAddress = 0xAAAAAAAA;
    BaseType_t xResult;
    int i;
    struct xNetworkInterface * xInterface;
    NetworkEndPoint_t xEndPoint;

    /* Catch the assertion for calling from IP task. */
    /* =================================================== */
    /* Assertion on calling from IP-task */
    xIsCallingFromIPTask_IgnoreAndReturn( pdTRUE );
    catch_assert( xARPWaitResolution( ulIPAddress, 0 ) );
    /* =================================================== */


    /* Make the resolution pass without any attempt by making
     * eARPGetCacheEntry return eARPCacheHit. */
    /* =================================================== */
    /* Assertion on calling from IP-task */
    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    /* Not worried about what these functions do. */
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 1UL );
    vSetMultiCastIPv4MacAddress_Ignore();
    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, &xEndPoint );

    xResult = xARPWaitResolution( ulIPAddress, 0 );
    TEST_ASSERT_EQUAL( xResult, 0 );
    /* =================================================== */
}

void test_xARPWaitResolution_GNWFailsNoTimeout( void )
{
    uint32_t ulIPAddress = 0xAAAAAAAA;
    NetworkEndPoint_t xEndPoint;
    NetworkInterface_t xInterface;
    BaseType_t xResult;
    int i;

    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;
    /* Make the resolution fail with maximum tryouts. */
    /* =================================================== */
    /* Make sure that no address matches the IP address. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAAAAAAAA;
    }

    ulIPAddress = 0x00000031;
    /* Make both values (IP address and local IP pointer) different. */
    /* Get any address on the same netmask. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x00000034;

    /* Assertion on calling from IP-task */
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( ( void * ) 1234 );

    vTaskSetTimeOutState_Stub( vStoreTimeValue );

    /* Make sure that there are enough stubs for all the repetitive calls. */
    for( i = 0; i < ipconfigMAX_ARP_RETRANSMISSIONS; i++ )
    {
        FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);
        pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
        FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);
        vTaskDelay_Expect( pdMS_TO_TICKS( 250U ) );
        FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
        xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
        FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( ( void * ) 1234 );
        xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    }

    xResult = xARPWaitResolution( ulIPAddress, 0 );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRNOTAVAIL, xResult );
    /* =================================================== */
}

void test_xARPWaitResolution( void )
{
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint;
    uint32_t ulIPAddress = 0xAAAAAAAA;
    BaseType_t xResult;
    int i;

    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;
    /* Make the resolution fail after some attempts due to timeout. */
    /* =================================================== */
    /* Make sure that no address matches the IP address. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAAAAAAAA;
    }

    ulIPAddress = 0x00000031;
    /* Make both values (IP address and local IP pointer) different. */
    /* Get any address on the same netmask. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x00000034;

    /* Assertion on calling from IP-task */
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( ( void * ) 1234 );

    vTaskSetTimeOutState_Stub( vStoreTimeValue );

    /* Make sure that there are enough stubs for all the repetitive calls. */
    for( i = 0; i < ( ipconfigMAX_ARP_RETRANSMISSIONS - 1 ); i++ )
    {
        FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);
        pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
        FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);
        vTaskDelay_Expect( pdMS_TO_TICKS( 250U ) );
        FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
        xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
        FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( ( void * ) 1234 );
        xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    }

    FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
    FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);
    vTaskDelay_Expect( pdMS_TO_TICKS( 250U ) );
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( ( void * ) 1234 );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );

    xResult = xARPWaitResolution( ulIPAddress, 0 );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRNOTAVAIL, xResult );
    /* =================================================== */

    /* Make the resolution pass after some attempts. */
    /* =================================================== */
    xEndPoint.bits.bIPv6 = 0;

    /* Make sure that no address matches the IP address. */
    for( i = 0; i < ipconfigARP_CACHE_ENTRIES; i++ )
    {
        xARPCache[ i ].ulIPAddress = 0xAAAAAAAA;
    }

    ulIPAddress = 0x00000031;
    /* Make both values (IP address and local IP pointer) different. */
    /* Get any address on the same netmask. */
    *ipLOCAL_IP_ADDRESS_POINTER = 0x00000034;

    /* Assertion on calling from IP-task */
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    /* Not worried about what these functions do. */
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( ( void * ) 1234 );

    vTaskSetTimeOutState_Stub( vStoreTimeValue );

    /* Make sure that there are enough stubs for all the repetitive calls. */
    for( i = 0; i < ( ipconfigMAX_ARP_RETRANSMISSIONS - 2 ); i++ )
    {
        FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);
        pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
        FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);
        vTaskDelay_Expect( pdMS_TO_TICKS( 250U ) );
        FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
        xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 0UL );
        FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( ( void * ) 1234 );
        xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    }

    FreeRTOS_FirstEndPoint_ExpectAndReturn(NULL, &xEndPoint);
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, NULL );
    FreeRTOS_NextEndPoint_ExpectAndReturn(NULL, &xEndPoint, NULL);
    vTaskDelay_Expect( pdMS_TO_TICKS( 250U ) );
    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );
    xIsIPv4Multicast_ExpectAndReturn( ulIPAddress, 1UL );
    vSetMultiCastIPv4MacAddress_Ignore();
    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, &xEndPoint );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );

    xResult = xARPWaitResolution( ulIPAddress, 0 );
    TEST_ASSERT_EQUAL( 0, xResult );
    /* =================================================== */
}

void test_vARPGenerateRequestPacket( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;

    NetworkBufferDescriptor_t * const pxNetworkBuffer = &xNetworkBuffer;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    uint8_t ucBuffer[ sizeof( ARPPacket_t ) + ipBUFFER_PADDING ];

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    pxNetworkBuffer->xDataLength = sizeof( ARPPacket_t );

    /* Catch some asserts. */
    catch_assert( vARPGenerateRequestPacket( NULL ) );

    pxNetworkBuffer->xDataLength = sizeof( ARPPacket_t ) - 10;
    catch_assert( vARPGenerateRequestPacket( pxNetworkBuffer ) );

    pxNetworkBuffer->xDataLength = sizeof( ARPPacket_t );
    vARPGenerateRequestPacket( pxNetworkBuffer );
}


void test_FreeRTOS_ClearARP( void )
{
    struct xNetworkEndPoint xEndPoint;
    uint8_t ucArray[ sizeof( xARPCache ) ];

    memset( ucArray, 0, sizeof( xARPCache ) );

    FreeRTOS_ClearARP( NULL );
    TEST_ASSERT_EQUAL_MEMORY( ucArray, xARPCache, sizeof( xARPCache ) );
}



void test_FreeRTOS_PrintARPCache( void )
{
    int x;

    for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        /* Anything except 0. */
        xARPCache[ x ].ulIPAddress = 0xAA;
        /* Anything except 0. */
        xARPCache[ x ].ucAge = x;
    }

    /* Nothing to actually unit-test here. */
    FreeRTOS_PrintARPCache();

    for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        /* Anything except 0. */
        xARPCache[ x ].ulIPAddress = 0x00;
        /* Anything except 0. */
        xARPCache[ x ].ucAge = x;
    }

    /* Nothing to actually unit-test here. */
    FreeRTOS_PrintARPCache();
}