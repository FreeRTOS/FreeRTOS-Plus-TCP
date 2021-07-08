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
#include "mock_Reception_list_macros.h"

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

uint8_t IP_Packet_AptHeader_InvalidDataLen[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x60, 0x10,                          /* TCP header size 4-bits (20) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00                           /* Urgent point if flag set */
    
};

void test_prvCheckOptions_AptHeader_InvalidDataLen(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_InvalidDataLen, sizeof(IP_Packet_AptHeader_InvalidDataLen) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_InvalidDataLen );
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_InvalidDataLen, ucLocalBuffer, sizeof( IP_Packet_AptHeader_InvalidDataLen ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_InvalidOptLen[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x60, 0x10,                          /* TCP header size 4-bits (20) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00                           /* Urgent point if flag set */
    
};

void test_prvCheckOptions_AptHeader_ValidDataLen_InvalidOptLen(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_InvalidOptLen, sizeof(IP_Packet_AptHeader_ValidDataLen_InvalidOptLen) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_InvalidOptLen ) + 3 /* Any value less than 4. */;
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_InvalidOptLen, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_InvalidOptLen ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x60, 0x10,                          /* TCP header size 4-bits (20) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00                           /* Urgent point if flag set */
    
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_1(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1 ) + 5 /* Any value greater than 4. */;
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x60, 0x02,                          /* TCP header size 4-bits (24) (other flags SYN set) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00                           /* Urgent point if flag set */
    
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_2(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2 ) + 5 /* Any value greater than 4. */;
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x60, 0x02,                          /* TCP header size 4-bits (24) (other flags SYN set) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP                  /* No-op option */
    
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_3(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x60, 0x02,                          /* TCP header size 4-bits (24) (other flags SYN set) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,                   /* No-op option */
    tcpTCP_OPT_MSS, tcpTCP_OPT_MSS           /* MSS option - will be invalid */
    
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_4(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x02,                          /* TCP header size 4-bits (28) (other flags SYN set) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_WSOPT, tcpTCP_OPT_MSS_LEN,  /* Window scaling option with incorrect length */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,   /* No-op option */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP    /* No-op option */
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_5(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x02,                          /* TCP header size 4-bits (28) (other flags SYN set) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */ 
    tcpTCP_OPT_WSOPT, tcpTCP_OPT_WSOPT_LEN
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_6(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x02,                          /* TCP header size 4-bits (28) (other flags SYN set) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_WSOPT, tcpTCP_OPT_WSOPT_LEN,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP    /* No-op option */ 
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_7(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_8[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x00,                          /* TCP header size 4-bits (28) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_WSOPT, tcpTCP_OPT_WSOPT_LEN,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP    /* No-op option */ 
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_8(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_8, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_8) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_8 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_8, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_8 ) );
    TEST_ASSERT_EQUAL( tcpTCP_OPT_NOOP, pxSocket->u.xTCP.ucPeerWinScaleFactor );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bWinScaling );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_9[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x00,                          /* TCP header size 4-bits (28) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_MSS, tcpTCP_OPT_WSOPT_LEN,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP    /* No-op option */ 
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_9(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_9, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_9) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_9 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_9, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_9 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x60, 0x00,                          /* TCP header size 4-bits (28) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_MSS, tcpTCP_OPT_WSOPT_LEN
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_10(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x60, 0x00,                          /* TCP header size 4-bits (28) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_MSS, tcpTCP_OPT_MSS_LEN
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_11(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x00,                          /* TCP header size 4-bits (28) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_MSS, tcpTCP_OPT_MSS_LEN,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_12(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    uint16_t usMSSLocal = 0xAB56;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12 );
    
    usChar2u16_ExpectAndReturn( &ucLocalBuffer[ sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12 ) - 4 ], usMSSLocal );
    
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_13[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x00,                          /* TCP header size 4-bits (28) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_MSS, tcpTCP_OPT_MSS_LEN,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_13(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    uint16_t usMSSLocal = 0xAB56;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_13, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_13) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_13 );
    
    usChar2u16_ExpectAndReturn( &ucLocalBuffer[ sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_13 ) - 4 ], usMSSLocal );
    
    pxSocket->u.xTCP.usInitMSS = usMSSLocal + 2;
    
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_13, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_13 ) );
    TEST_ASSERT_EQUAL( usMSSLocal, pxSocket->u.xTCP.usInitMSS );
    TEST_ASSERT_EQUAL( usMSSLocal, pxSocket->u.xTCP.usCurMSS );
    TEST_ASSERT_EQUAL( usMSSLocal, pxSocket->u.xTCP.xTCPWindow.usMSSInit );
    TEST_ASSERT_EQUAL( usMSSLocal, pxSocket->u.xTCP.xTCPWindow.usMSS );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x00,                          /* TCP header size 4-bits (28) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_MSS, tcpTCP_OPT_MSS_LEN,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_14(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    uint16_t usMSSLocal = 0;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14 );
    
    usChar2u16_ExpectAndReturn( &ucLocalBuffer[ sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14 ) - 4 ], usMSSLocal );
    
    pxSocket->u.xTCP.usInitMSS = usMSSLocal + 2;
    
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14 ) );
}

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_14_1(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    uint16_t usMSSLocal = 0;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14, sizeof(IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14 );
    
    usChar2u16_ExpectAndReturn( &ucLocalBuffer[ sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14 ) - 4 ], usMSSLocal );
    
    pxSocket->u.xTCP.usInitMSS = usMSSLocal;
    
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14 ) );
    TEST_ASSERT_EQUAL( usMSSLocal, pxSocket->u.xTCP.usInitMSS );
}

uint8_t IP_Packet_AptHeader_SACK_Permitted[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x00,                          /* TCP header size 4-bits (28) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_SACK_P, tcpTCP_OPT_MSS_LEN,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_SACK_Permitted(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_SACK_Permitted, sizeof(IP_Packet_AptHeader_SACK_Permitted) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_SACK_Permitted );
    
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_SACK_Permitted, ucLocalBuffer, sizeof( IP_Packet_AptHeader_SACK_Permitted ) );
}

uint8_t IP_Packet_AptHeader_SACK_Permitted_1[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x00,                          /* TCP header size 4-bits (28) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_SACK_P, 0,                /* Zero length option */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_SACK_Permitted_1(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_SACK_Permitted_1, sizeof(IP_Packet_AptHeader_SACK_Permitted_1) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_SACK_Permitted_1 );
    
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_SACK_Permitted_1, ucLocalBuffer, sizeof( IP_Packet_AptHeader_SACK_Permitted_1 ) );
}

uint8_t IP_Packet_AptHeader_SACK_Permitted_2[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x00,                          /* TCP header size 4-bits (28) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_SACK_P, 7,                /* More length than remaining bytes */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_SACK_Permitted_2(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_SACK_Permitted_2, sizeof(IP_Packet_AptHeader_SACK_Permitted_2) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_SACK_Permitted_2 );
    
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_SACK_Permitted_2, ucLocalBuffer, sizeof( IP_Packet_AptHeader_SACK_Permitted_2 ) );
}

uint8_t IP_Packet_AptHeader_SACK_Set[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x70, 0x00,                          /* TCP header size 4-bits (28) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_SACK_A, 3,                /* Smaller length of option */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_SACK_Set(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_SACK_Set, sizeof(IP_Packet_AptHeader_SACK_Set) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_SACK_Set );
    
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_SACK_Set, ucLocalBuffer, sizeof( IP_Packet_AptHeader_SACK_Set ) );
}

uint8_t IP_Packet_AptHeader_SACK_Send[] = 
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76,  /* Source MAC */
    0x80, 0x00,                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                /* Version (4). Header length 4*(5) */
    0x00,                                /* Unused */
    0x12, 0x34,                          /* Total length */
    0xAA, 0xBB,                          /* Identification */
    0x00, 0x00,                          /* Flags: 3 bits, offset: 13 bits */
    0x12,                                /* Time to live */
    0x06,                                /* Protocol: TCP */
    0xAB, 0x12,                          /* Header checksum */
    192, 168, 0, 2,                      /* Source IP - not in hex since it is easy to manipulate */
    192, 168, 0, 10,                     /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,                          /* Source port */
    0xAB, 0xCD,                          /* Destination port */
    0x00, 0x00, 0x00, 0x01,              /* Sequence Number */
    0x12, 0x34, 0x56, 0x67,              /* ACK number */
    0x80, 0x00,                          /* TCP header size 4-bits (32) (other flags) */
    0x00, 0x23,                          /* Window size */
    0xff, 0xff,                          /* Checksum */
    0x00, 0x00,                          /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_SACK_A, 10,               /* Smaller length of option */
    0x00, 0x00,                          /* Start segment - 1 */
    0x00, 0xff,                          /* Start Segment - 2 */
    0x00, 0x00,                          /* End segment - 1 */
    0x01, 0xff                           /* End Segment - 2 */
};

void test_prvCheckOptions_AptHeader_SACK_Send(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];
    
    memcpy( ucLocalBuffer, IP_Packet_AptHeader_SACK_Send, sizeof(IP_Packet_AptHeader_SACK_Send) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;
    
    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_SACK_Send );
    
    prvReadSackOption_Expect( &ucLocalBuffer[ sizeof(IP_Packet_AptHeader_SACK_Send) - 10 ], 2, pxSocket );
    
    prvCheckOptions( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_SACK_Send, ucLocalBuffer, sizeof( IP_Packet_AptHeader_SACK_Send ) );
}


void test_prvTCPSendChallengeAck(void)
{
    NetworkBufferDescriptor_t xLocalBuffer;
    BaseType_t xTemp = 0x1234, xReturn;
 
    prvTCPSendSpecialPacketHelper_ExpectAndReturn( &xLocalBuffer, tcpTCP_FLAG_ACK, xTemp );
    
    xReturn = prvTCPSendChallengeAck( &xLocalBuffer );
    
    TEST_ASSERT_EQUAL( xTemp, xReturn );
}

void test_prvTCPSendReset(void)
{
    NetworkBufferDescriptor_t xLocalBuffer;
    BaseType_t xTemp = 0x1234, xReturn;
 
    prvTCPSendSpecialPacketHelper_ExpectAndReturn( &xLocalBuffer, ( uint8_t ) tcpTCP_FLAG_ACK | ( uint8_t ) tcpTCP_FLAG_RST, xTemp );
    
    xReturn = prvTCPSendReset( &xLocalBuffer );
    
    TEST_ASSERT_EQUAL( xTemp, xReturn );
}

void test_prvHandleListen_SequenceNumberZero( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket, * pxResultSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalBuffer;
    
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 0 );
    
    pxResultSocket = prvHandleListen( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( NULL, pxResultSocket );
}

void test_prvHandleListen_SequenceNumberNonZero( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket, * pxResultSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    TCPPacket_t * pxTCPPacket;
    uint32_t xSeqNumber = 12;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalBuffer;
    
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxTCPPacket = ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    
    
    
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( xSeqNumber );
    
    pxSocket->u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
    
    prvSocketSetMSS_Expect( pxSocket );
    prvTCPCreateWindow_Expect( pxSocket );
    vTCPStateChange_Expect( pxSocket, eSYN_FIRST );
    
    memset( pxSocket->u.xTCP.xPacket.u.ucLastPacket, 0x00, sizeof( pxSocket->u.xTCP.xPacket.u.ucLastPacket ) );
    memset( pxNetworkBuffer->pucEthernetBuffer, 0xAA, ipconfigTCP_MSS );
    
    pxResultSocket = prvHandleListen( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( pxSocket, pxResultSocket );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bPassQueued );
    TEST_ASSERT_EQUAL( pxSocket, pxSocket->u.xTCP.pxPeerSocket );
    TEST_ASSERT_EQUAL( FreeRTOS_htons( pxTCPPacket->xTCPHeader.usSourcePort ), pxSocket->u.xTCP.usRemotePort );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( pxTCPPacket->xIPHeader.ulSourceIPAddress ), pxSocket->u.xTCP.ulRemoteIP );
    TEST_ASSERT_EQUAL( xSeqNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );
}

void test_prvHandleListen_SequenceNumberNonZero_SocketNotToBeReused( void )
{
    FreeRTOS_Socket_t xLocalSocket, xLocalSocketToReturn, * pxSocket, * pxResultSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    TCPPacket_t * pxTCPPacket;
    uint32_t xSeqNumber = 12;
    
    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalBuffer;
    
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    pxTCPPacket = ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    
    
    
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( xSeqNumber );
    
    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.usBacklog = 13;
    pxSocket->u.xTCP.usChildCount = pxSocket->u.xTCP.usBacklog - 10;
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP, &xLocalSocketToReturn );
    
    prvTCPSocketCopy_ExpectAndReturn( &xLocalSocketToReturn, &xLocalSocket, pdFALSE );
    
    pxResultSocket = prvHandleListen( pxSocket, pxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( NULL, pxResultSocket );
}

void test_prvHandleListen_SequenceNumberNonZero_SocketNotToBeReused_ChildCountMoreThanBacklog( void )
{
    FreeRTOS_Socket_t xLocalSocket, xLocalSocketToReturn, * pxSocket, * pxResultSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    TCPPacket_t * pxTCPPacket;
    uint32_t xSeqNumber = 12;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxTCPPacket = ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;



    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( xSeqNumber );

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.usBacklog = 13;
    pxSocket->u.xTCP.usChildCount = pxSocket->u.xTCP.usBacklog + 10;

    /* Return value is ignored. */
    prvTCPSendSpecialPacketHelper_ExpectAndReturn( &xLocalBuffer, ( uint8_t ) tcpTCP_FLAG_ACK | ( uint8_t ) tcpTCP_FLAG_RST, 0 );

    pxResultSocket = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxResultSocket );
}

void test_prvHandleListen_SequenceNumberNonZero_SocketNotToBeReused_ChildCountLessThanBacklog_NoSocket( void )
{
    FreeRTOS_Socket_t xLocalSocket, xLocalSocketToReturn, * pxSocket, * pxResultSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    TCPPacket_t * pxTCPPacket;
    uint32_t xSeqNumber = 12;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxTCPPacket = ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( xSeqNumber );

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.usBacklog = 13;
    pxSocket->u.xTCP.usChildCount = pxSocket->u.xTCP.usBacklog - 10;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP, NULL );

    /* Return value is ignored. */
    prvTCPSendSpecialPacketHelper_ExpectAndReturn( &xLocalBuffer, ( uint8_t ) tcpTCP_FLAG_ACK | ( uint8_t ) tcpTCP_FLAG_RST, 0 );

    pxResultSocket = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxResultSocket );
}

void test_prvHandleListen_SequenceNumberNonZero_SocketNotToBeReused_ChildCountLessThanBacklog_InvalidSocket( void )
{
    FreeRTOS_Socket_t xLocalSocket, xLocalSocketToReturn, * pxSocket, * pxResultSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    TCPPacket_t * pxTCPPacket;
    uint32_t xSeqNumber = 12;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxTCPPacket = ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( xSeqNumber );

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.usBacklog = 13;
    pxSocket->u.xTCP.usChildCount = pxSocket->u.xTCP.usBacklog - 10;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP, FREERTOS_INVALID_SOCKET );

    /* Return value is ignored. */
    prvTCPSendSpecialPacketHelper_ExpectAndReturn( &xLocalBuffer, ( uint8_t ) tcpTCP_FLAG_ACK | ( uint8_t ) tcpTCP_FLAG_RST, 0 );

    pxResultSocket = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxResultSocket );
}

void test_prvHandleListen_SequenceNumberNonZero_SocketNotToBeReused_ChildCountLessThanBacklog_ProperSocket( void )
{
    FreeRTOS_Socket_t xLocalSocket, xLocalSocketToReturn, * pxSocket, * pxResultSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    TCPPacket_t * pxTCPPacket;
    uint32_t xSeqNumber = 12;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxTCPPacket = ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( xSeqNumber );

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.usBacklog = 13;
    pxSocket->u.xTCP.usChildCount = pxSocket->u.xTCP.usBacklog - 10;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP, &xLocalSocketToReturn );

    prvTCPSocketCopy_ExpectAndReturn( &xLocalSocketToReturn, &xLocalSocket, pdTRUE );

    prvSocketSetMSS_Expect( &xLocalSocketToReturn );
    prvTCPCreateWindow_Expect( &xLocalSocketToReturn );
    vTCPStateChange_Expect( &xLocalSocketToReturn, eSYN_FIRST );

    pxResultSocket = prvHandleListen( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( &xLocalSocketToReturn, pxResultSocket );
}

void test_prvTCPHandleState_CannotStoreData(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn;
    uint8_t ucReceiveLength = 0;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    
    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();
    
    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;
    
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, -1 );
    prvStoreRxData_IgnoreArg_pucRecvData();
    
    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( -1, xReturn );
}

void test_prvTCPHandleState_StoreData(void)
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, *pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    
    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;
    
    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();
    
    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;
    
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();
    
    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );
    
    prvHandleEstablished_ExpectAndReturn( pxSocket, ppxNetworkBuffer, ucReceiveLength, xOptionLength, 0x34AB );
    
    prvSendData_ExpectAnyArgsAndReturn( 0xAB );
    
    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );
    
    TEST_ASSERT_EQUAL( 0xAB, xReturn );
}



































