/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_task.h"
#include "mock_list.h"
/* This must come after list.h is included. */
#include "mock_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_DNS.h"

#include "FreeRTOS_UDP_IP.h"

#include "FreeRTOS_UDP_IP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

void test_vProcessGeneratedUDPPacket_CantSendPacket(void)
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    UDPPacket_t * pxUDPPacket;
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    eARPGetCacheEntry_ExpectAnyArgsAndReturn(eCantSendPacket);
    vReleaseNetworkBufferAndDescriptor_Expect( &xLocalNetworkBuffer );
    
    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );
}

void test_vProcessGeneratedUDPPacket_CacheMiss_PacketSmaller(void)
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    UDPPacket_t * pxUDPPacket;
    uint32_t ulIPAddr = 0x1234ABCD;
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    xLocalNetworkBuffer.ulIPAddress = ulIPAddr;
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t *) pucLocalEthernetBuffer;
    
    eARPGetCacheEntry_ExpectAnyArgsAndReturn(eARPCacheMiss);
    
    vARPRefreshCacheEntry_Expect(NULL, ulIPAddr);
    vARPGenerateRequestPacket_Expect( &xLocalNetworkBuffer );
    
    xNetworkInterfaceOutput_ExpectAndReturn( &xLocalNetworkBuffer, pdTRUE, pdTRUE );
    
    xLocalNetworkBuffer.xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES - 2;
    
    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );
}

void test_vProcessGeneratedUDPPacket_CacheMiss_PacketNotSmaller(void)
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    UDPPacket_t * pxUDPPacket;
    uint32_t ulIPAddr = 0x1234ABCD;
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    xLocalNetworkBuffer.ulIPAddress = ulIPAddr;
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t *) pucLocalEthernetBuffer;
    
    eARPGetCacheEntry_ExpectAnyArgsAndReturn(eARPCacheMiss);
    
    vARPRefreshCacheEntry_Expect(NULL, ulIPAddr);
    vARPGenerateRequestPacket_Expect( &xLocalNetworkBuffer );
    
    xNetworkInterfaceOutput_ExpectAndReturn( &xLocalNetworkBuffer, pdTRUE, pdTRUE );
    
    xLocalNetworkBuffer.xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES+2;
    
    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );
}

void test_vProcessGeneratedUDPPacket_UnknownARPReturn(void)
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    UDPPacket_t * pxUDPPacket;
    uint32_t ulIPAddr = 0x1234ABCD;
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    xLocalNetworkBuffer.ulIPAddress = ulIPAddr;
    xLocalNetworkBuffer.usPort = ipPACKET_CONTAINS_ICMP_DATA;
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t *) pucLocalEthernetBuffer;
    
    eARPGetCacheEntry_ExpectAnyArgsAndReturn(eCantSendPacket+1);
    
    vReleaseNetworkBufferAndDescriptor_Expect( &xLocalNetworkBuffer );
    
    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );
}

void test_vProcessGeneratedUDPPacket_CacheHit_NoICMP(void)
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    UDPPacket_t * pxUDPPacket;
    uint32_t ulIPAddr = 0x1234ABCD;
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    xLocalNetworkBuffer.ulIPAddress = ulIPAddr;
    xLocalNetworkBuffer.usPort = ipPACKET_CONTAINS_ICMP_DATA+1;
    xLocalNetworkBuffer.xDataLength = sizeof( UDPPacket_t );
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t *) pucLocalEthernetBuffer;
    
    eARPGetCacheEntry_ExpectAnyArgsAndReturn(eARPCacheHit);
    
    usGenerateChecksum_ExpectAndReturn( 0U, NULL, ipSIZE_OF_IPv4_HEADER, 0 );
    usGenerateChecksum_IgnoreArg_pucNextData();
    
    xNetworkInterfaceOutput_ExpectAndReturn( &xLocalNetworkBuffer, pdTRUE, pdTRUE );
    
    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );
}

void test_vProcessGeneratedUDPPacket_CacheHit_ICMPPacket_LLMNR_UDPChkSumOption(void)
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    UDPPacket_t * pxUDPPacket;
    uint32_t ulIPAddr = ipLLMNR_IP_ADDR;
    uint8_t ucSocketOptions=FREERTOS_SO_UDPCKSUM_OUT;
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    xLocalNetworkBuffer.pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ]= ucSocketOptions;
    
    xLocalNetworkBuffer.ulIPAddress = ulIPAddr;
    xLocalNetworkBuffer.usPort = ipPACKET_CONTAINS_ICMP_DATA;
    xLocalNetworkBuffer.xDataLength = sizeof( UDPPacket_t );
    
    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( UDPPacket_t *) pucLocalEthernetBuffer;
    
    eARPGetCacheEntry_ExpectAnyArgsAndReturn(eARPCacheHit);
    
    usGenerateChecksum_ExpectAndReturn( 0U, NULL, ipSIZE_OF_IPv4_HEADER, 0 );
    usGenerateChecksum_IgnoreArg_pucNextData();
    
    usGenerateProtocolChecksum_ExpectAndReturn( pucLocalEthernetBuffer, xLocalNetworkBuffer.xDataLength, pdTRUE, 0 );
    
    xNetworkInterfaceOutput_ExpectAndReturn( &xLocalNetworkBuffer, pdTRUE, pdTRUE );
    
    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );
}

void test_xProcessReceivedUDPPacket_catchAsserts( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    
    catch_assert( xProcessReceivedUDPPacket(NULL,0) );
    
    xLocalNetworkBuffer.pucEthernetBuffer = NULL;
    catch_assert( xProcessReceivedUDPPacket(&xLocalNetworkBuffer,0) );
}

void test_xProcessReceivedUDPPacket_NoListeningSocket_NotForThisNode( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort=0;
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, NULL);
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdFAIL, xResult);
}

void test_xProcessReceivedUDPPacket_NoListeningSocket_DelayedDNSResponse( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = 0;
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    UDPPacket_t * pxUDPPacket;
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usSourcePort=FreeRTOS_htons(ipDNS_PORT);
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, NULL);
    
    vARPRefreshCacheEntry_Expect(&( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    ulDNSHandlePacket_ExpectAndReturn(&xLocalNetworkBuffer, pdPASS);
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdPASS, xResult);
}

void test_xProcessReceivedUDPPacket_NoListeningSocket_LLMNRResponse( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipLLMNR_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    UDPPacket_t * pxUDPPacket;
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usSourcePort=FreeRTOS_ntohs( ipLLMNR_PORT );
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, NULL);
    
    vARPRefreshCacheEntry_Expect(&( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    ulDNSHandlePacket_ExpectAndReturn(&xLocalNetworkBuffer, pdPASS);
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdPASS, xResult);
}

void test_xProcessReceivedUDPPacket_NoListeningSocket_LLMNRResponse_MismatchingPorts( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipLLMNR_PORT+1 );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    UDPPacket_t * pxUDPPacket;
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usSourcePort=FreeRTOS_ntohs( ipLLMNR_PORT );
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, NULL);
    
    vARPRefreshCacheEntry_Expect(&( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    ulDNSHandlePacket_ExpectAndReturn(&xLocalNetworkBuffer, pdPASS);
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdPASS, xResult);
}

void test_xProcessReceivedUDPPacket_NoListeningSocket_NBNSResponse( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    UDPPacket_t * pxUDPPacket;
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usSourcePort=FreeRTOS_ntohs( ipNBNS_PORT );
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, NULL);
    
    vARPRefreshCacheEntry_Expect(&( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    ulNBNSHandlePacket_ExpectAndReturn(&xLocalNetworkBuffer, pdPASS);
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdPASS, xResult);
}

void test_xProcessReceivedUDPPacket_NoListeningSocket_NBNSResponse_MismatchingPorts( void )
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT+1 );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    UDPPacket_t * pxUDPPacket;
    
    /* Cleanup the ethernet buffer. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usSourcePort=FreeRTOS_ntohs( ipNBNS_PORT );
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, NULL);
    
    vARPRefreshCacheEntry_Expect(&( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    ulNBNSHandlePacket_ExpectAndReturn(&xLocalNetworkBuffer, pdPASS);
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdPASS, xResult);
}

void test_xProcessReceivedUDPPacket_SocketFound_NoHandler_BufferFull(void)
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    
    /* Cleanup. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    memset(&xLocalSocket, 0, sizeof(xLocalSocket));
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    
    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, &xLocalSocket);
    
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdFAIL, xResult);
}

void test_xProcessReceivedUDPPacket_SocketFound_NoHandler_NoEventGroupSocketSetUSemaphore(void)
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    
    /* Cleanup. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    memset(&xLocalSocket, 0, sizeof(xLocalSocket));
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    
    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = NULL;
    xLocalSocket.pxSocketSet = NULL;
    xLocalSocket.pxUserSemaphore = NULL;
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, &xLocalSocket);
    
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    
    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn(pdPASS);
    
    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 0 );
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdPASS, xResult);
}

void test_xProcessReceivedUDPPacket_SocketFound_NoHandler_ValidEventGroupUSemaphore(void)
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    
    /* Cleanup. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    memset(&xLocalSocket, 0, sizeof(xLocalSocket));
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    
    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = (void*)1;
    xLocalSocket.pxSocketSet = NULL;
    xLocalSocket.pxUserSemaphore = (void*)1;
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, &xLocalSocket);
    
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    
    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn(pdPASS);
    
    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore,NULL, semGIVE_BLOCK_TIME,queueSEND_TO_BACK, pdPASS );
    
    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn(pdPASS);
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdPASS, xResult);
}

void test_xProcessReceivedUDPPacket_SocketFound_NoHandler_ValidEventGroupUSemaphoreSocketSet_InvalidSelectBits(void)
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    
    /* Cleanup. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    memset(&xLocalSocket, 0, sizeof(xLocalSocket));
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    
    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = (void*)1;
    xLocalSocket.pxSocketSet = (void *)1;
    xLocalSocket.pxUserSemaphore = (void*)1;
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, &xLocalSocket);
    
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    
    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn(pdPASS);
    
    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore,NULL, semGIVE_BLOCK_TIME,queueSEND_TO_BACK, pdPASS );
    
    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn(pdPASS);
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdPASS, xResult);
}

void test_xProcessReceivedUDPPacket_SocketFound_NoHandler_ValidEventGroupUSemaphoreSocketSet_ValidSelectBits(void)
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    SocketSelect_t xLocalSocketSet;
    
    /* Cleanup. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    memset(&xLocalSocket, 0, sizeof(xLocalSocket));
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    
    xLocalSocket.u.xUDP.pxHandleReceive = NULL;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = (void*)1;
    xLocalSocket.pxSocketSet = &xLocalSocketSet;
    xLocalSocket.pxUserSemaphore = (void*)1;
    xLocalSocket.xSelectBits = eSELECT_READ;
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, &xLocalSocket);
    
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    
    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn(pdPASS);
    
    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore,NULL, semGIVE_BLOCK_TIME,queueSEND_TO_BACK, pdPASS );
    
    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn(pdPASS);
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdPASS, xResult);
}

uint32_t ulFunctionCalled = 0;
BaseType_t xFunctionReturn;
static BaseType_t xLocalHandler( Socket_t pxSocket, void* pvData, size_t xLength, const struct freertos_sockaddr * pxFrom, const struct freertos_sockaddr * pxTo )
{
    TEST_ASSERT( pxSocket != NULL );
    TEST_ASSERT( pvData != NULL );
    TEST_ASSERT( pxFrom != NULL );
    TEST_ASSERT( pxTo != NULL );
    
    ulFunctionCalled++;
    
    return xFunctionReturn;
}

void test_xProcessReceivedUDPPacket_SocketFound_HandlerFoundReturnZero_ValidEventGroupUSemaphoreSocketSet_ValidSelectBits(void)
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    SocketSelect_t xLocalSocketSet;
    
    /* Cleanup. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    memset(&xLocalSocket, 0, sizeof(xLocalSocket));
    ulFunctionCalled = 0;
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    
    xLocalSocket.u.xUDP.pxHandleReceive = xLocalHandler;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = (void*)1;
    xLocalSocket.pxSocketSet = &xLocalSocketSet;
    xLocalSocket.pxUserSemaphore = (void*)1;
    xLocalSocket.xSelectBits = eSELECT_READ;
    
    xFunctionReturn = 0;
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, &xLocalSocket);
    
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    
    vTaskSuspendAll_Expect();
    vListInsertEnd_Expect( &( xLocalSocket.u.xUDP.xWaitingPacketsList ), &( xLocalNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn(pdPASS);
    
    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdPASS );
    xEventGroupSetBits_ExpectAndReturn( xLocalSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );
    xQueueGenericSend_ExpectAndReturn( xLocalSocket.pxUserSemaphore,NULL, semGIVE_BLOCK_TIME,queueSEND_TO_BACK, pdPASS );
    
    xIsDHCPSocket_ExpectAndReturn( &xLocalSocket, 1 );
    xSendDHCPEvent_ExpectAndReturn(pdPASS);
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdPASS, xResult);
    TEST_ASSERT_EQUAL(1,ulFunctionCalled);
}

void test_xProcessReceivedUDPPacket_SocketFound_HandlerFoundReturnNonZero(void)
{
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint16_t usPort = FreeRTOS_ntohs( ipNBNS_PORT );
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xResult;
    FreeRTOS_Socket_t xLocalSocket;
    UDPPacket_t * pxUDPPacket;
    SocketSelect_t xLocalSocketSet;
    
    /* Cleanup. */
    memset(pucLocalEthernetBuffer, 0, ipconfigTCP_MSS);
    memset(&xLocalSocket, 0, sizeof(xLocalSocket));
    ulFunctionCalled = 0;
    
    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;
    
    pxUDPPacket = ( UDPPacket_t *) xLocalNetworkBuffer.pucEthernetBuffer;
    
    xLocalSocket.u.xUDP.pxHandleReceive = xLocalHandler;
    /* Since we have memset this to 0, anything bigger than 0 should suffice. */
    xLocalSocket.u.xUDP.uxMaxPackets = 1;
    xLocalSocket.xEventGroup = (void*)1;
    xLocalSocket.pxSocketSet = &xLocalSocketSet;
    xLocalSocket.pxUserSemaphore = (void*)1;
    xLocalSocket.xSelectBits = eSELECT_READ;
    
    xFunctionReturn = 1;
    
    pxUDPSocketLookup_ExpectAndReturn(usPort, &xLocalSocket);
    
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
    
    xResult = xProcessReceivedUDPPacket( &xLocalNetworkBuffer, usPort );
    TEST_ASSERT_EQUAL(pdFAIL, xResult);
    TEST_ASSERT_EQUAL(1,ulFunctionCalled);
}
