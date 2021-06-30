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
#include "mock_FreeRTOS_TCP_IP.h"
#include "mock_FreeRTOS_TCP_IP_TimerWork.h"
#include "mock_NetworkBufferManagement.h"

#include "mock_FreeRTOS_IP_Private.h"

#include "FreeRTOS_TCP_IP_Reception.h"

#include "FreeRTOS_TCP_IP_Reception_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"


void test_prvCheckOptions_SmallHeader(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    
    for( pxTCPHeader->ucTCPOffset = 0; pxTCPHeader->ucTCPOffset <= ( 5U << 4U ); pxTCPHeader->ucTCPOffset++ )
    {
        prvCheckOptions( pxSocket, pxNetworkBuffer );
    }
}

uint8_t temp[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */
    /****** IPv4 ******/
    0x45,                                /* Version (4) Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    
};

void test_prvCheckOptions_AptHeader_InvalidDataLen(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    ProtocolHeaders_t * pxProtocolHeaders;
    TCPHeader_t * pxTCPHeader;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    
    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] );
    pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    
    /* Set a known pattern in the ethernet buffer. */
    
    
    pxTCPHeader->ucTCPOffset = (5U << 4U) + 1;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = 0;
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ( sizeof( TCPHeader_t ) - sizeof( pxTCPHeader->ucOptdata ) );
    prvCheckOptions( pxSocket, pxNetworkBuffer );
}
