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
#include "mock_FreeRTOS_Stream_Buffer.h"

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


void test_prvCheckOptions_SmallHeader( void )
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
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80, 0x00,                         /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                 /* Version (4). Header length 4*(5) */
    0x00,                 /* Unused */
    0x12, 0x34,           /* Total length */
    0xAA, 0xBB,           /* Identification */
    0x00, 0x00,           /* Flags: 3 bits, offset: 13 bits */
    0x12,                 /* Time to live */
    0x06,                 /* Protocol: TCP */
    0xAB, 0x12,           /* Header checksum */
    192,  168,  0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,  168,  0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,             /* Source port */
    0xAB, 0xCD,             /* Destination port */
    0x00, 0x00, 0x00, 0x01, /* Sequence Number */
    0x12, 0x34, 0x56, 0x67, /* ACK number */
    0x60, 0x10,             /* TCP header size 4-bits (20) (other flags) */
    0x00, 0x23,             /* Window size */
    0xff, 0xff,             /* Checksum */
    0x00, 0x00              /* Urgent point if flag set */
};

void test_prvCheckOptions_AptHeader_InvalidDataLen( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_InvalidDataLen, sizeof( IP_Packet_AptHeader_InvalidDataLen ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_InvalidDataLen );
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_InvalidDataLen, ucLocalBuffer, sizeof( IP_Packet_AptHeader_InvalidDataLen ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_InvalidOptLen[] =
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80, 0x00,                         /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                 /* Version (4). Header length 4*(5) */
    0x00,                 /* Unused */
    0x12, 0x34,           /* Total length */
    0xAA, 0xBB,           /* Identification */
    0x00, 0x00,           /* Flags: 3 bits, offset: 13 bits */
    0x12,                 /* Time to live */
    0x06,                 /* Protocol: TCP */
    0xAB, 0x12,           /* Header checksum */
    192,  168,  0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,  168,  0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,             /* Source port */
    0xAB, 0xCD,             /* Destination port */
    0x00, 0x00, 0x00, 0x01, /* Sequence Number */
    0x12, 0x34, 0x56, 0x67, /* ACK number */
    0x60, 0x10,             /* TCP header size 4-bits (20) (other flags) */
    0x00, 0x23,             /* Window size */
    0xff, 0xff,             /* Checksum */
    0x00, 0x00              /* Urgent point if flag set */
};

void test_prvCheckOptions_AptHeader_ValidDataLen_InvalidOptLen( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_InvalidOptLen, sizeof( IP_Packet_AptHeader_ValidDataLen_InvalidOptLen ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_InvalidOptLen ) + 3 /* Any value less than 4. */;
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_InvalidOptLen, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_InvalidOptLen ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1[] =
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80, 0x00,                         /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                 /* Version (4). Header length 4*(5) */
    0x00,                 /* Unused */
    0x12, 0x34,           /* Total length */
    0xAA, 0xBB,           /* Identification */
    0x00, 0x00,           /* Flags: 3 bits, offset: 13 bits */
    0x12,                 /* Time to live */
    0x06,                 /* Protocol: TCP */
    0xAB, 0x12,           /* Header checksum */
    192,  168,  0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,  168,  0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,             /* Source port */
    0xAB, 0xCD,             /* Destination port */
    0x00, 0x00, 0x00, 0x01, /* Sequence Number */
    0x12, 0x34, 0x56, 0x67, /* ACK number */
    0x60, 0x10,             /* TCP header size 4-bits (20) (other flags) */
    0x00, 0x23,             /* Window size */
    0xff, 0xff,             /* Checksum */
    0x00, 0x00              /* Urgent point if flag set */
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_1( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1 ) + 5 /* Any value greater than 4. */;
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_1 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2[] =
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21, 0x32, 0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80, 0x00,                         /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                 /* Version (4). Header length 4*(5) */
    0x00,                 /* Unused */
    0x12, 0x34,           /* Total length */
    0xAA, 0xBB,           /* Identification */
    0x00, 0x00,           /* Flags: 3 bits, offset: 13 bits */
    0x12,                 /* Time to live */
    0x06,                 /* Protocol: TCP */
    0xAB, 0x12,           /* Header checksum */
    192,  168,  0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,  168,  0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12, 0x23,             /* Source port */
    0xAB, 0xCD,             /* Destination port */
    0x00, 0x00, 0x00, 0x01, /* Sequence Number */
    0x12, 0x34, 0x56, 0x67, /* ACK number */
    0x60, 0x02,             /* TCP header size 4-bits (24) (other flags SYN set) */
    0x00, 0x23,             /* Window size */
    0xff, 0xff,             /* Checksum */
    0x00, 0x00              /* Urgent point if flag set */
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_2( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2 ) + 5 /* Any value greater than 4. */;
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_2 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3[] =
{
    0x11,            0x22,            0x33,            0x44,            0x55, 0x66, /* Destination MAC */
    0x21,            0x32,            0x43,            0x54,            0x65, 0x76, /* Source MAC */
    0x80,            0x00,                                                          /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                                  /* Version (4). Header length 4*(5) */
    0x00,                                                  /* Unused */
    0x12,            0x34,                                 /* Total length */
    0xAA,            0xBB,                                 /* Identification */
    0x00,            0x00,                                 /* Flags: 3 bits, offset: 13 bits */
    0x12,                                                  /* Time to live */
    0x06,                                                  /* Protocol: TCP */
    0xAB,            0x12,                                 /* Header checksum */
    192,             168,             0,               2,  /* Source IP - not in hex since it is easy to manipulate */
    192,             168,             0,               10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,            0x23,                                                              /* Source port */
    0xAB,            0xCD,                                                              /* Destination port */
    0x00,            0x00,            0x00,            0x01,                            /* Sequence Number */
    0x12,            0x34,            0x56,            0x67,                            /* ACK number */
    0x60,            0x02,                                                              /* TCP header size 4-bits (24) (other flags SYN set) */
    0x00,            0x23,                                                              /* Window size */
    0xff,            0xff,                                                              /* Checksum */
    0x00,            0x00,                                                              /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP /* No-op option */
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_3( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_3 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4[] =
{
    0x11,            0x22,            0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,            0x32,            0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,            0x00,                                    /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                       /* Version (4). Header length 4*(5) */
    0x00,                                       /* Unused */
    0x12,            0x34,                      /* Total length */
    0xAA,            0xBB,                      /* Identification */
    0x00,            0x00,                      /* Flags: 3 bits, offset: 13 bits */
    0x12,                                       /* Time to live */
    0x06,                                       /* Protocol: TCP */
    0xAB,            0x12,                      /* Header checksum */
    192,             168,             0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,             168,             0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,            0x23,                             /* Source port */
    0xAB,            0xCD,                             /* Destination port */
    0x00,            0x00,            0x00, 0x01,      /* Sequence Number */
    0x12,            0x34,            0x56, 0x67,      /* ACK number */
    0x60,            0x02,                             /* TCP header size 4-bits (24) (other flags SYN set) */
    0x00,            0x23,                             /* Window size */
    0xff,            0xff,                             /* Checksum */
    0x00,            0x00,                             /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP, /* No-op option */
    tcpTCP_OPT_MSS,  tcpTCP_OPT_MSS                    /* MSS option - will be invalid */
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_4( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_4 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5[] =
{
    0x11,             0x22, 0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,             0x32, 0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,             0x00,                         /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                             /* Version (4). Header length 4*(5) */
    0x00,                             /* Unused */
    0x12,             0x34,           /* Total length */
    0xAA,             0xBB,           /* Identification */
    0x00,             0x00,           /* Flags: 3 bits, offset: 13 bits */
    0x12,                             /* Time to live */
    0x06,                             /* Protocol: TCP */
    0xAB,             0x12,           /* Header checksum */
    192,              168,  0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,              168,  0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,             0x23,               /* Source port */
    0xAB,             0xCD,               /* Destination port */
    0x00,             0x00, 0x00, 0x01,   /* Sequence Number */
    0x12,             0x34, 0x56, 0x67,   /* ACK number */
    0x70,             0x02,               /* TCP header size 4-bits (28) (other flags SYN set) */
    0x00,             0x23,               /* Window size */
    0xff,             0xff,               /* Checksum */
    0x00,             0x00,               /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_WSOPT, tcpTCP_OPT_MSS_LEN, /* Window scaling option with incorrect length */
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP,    /* No-op option */
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP     /* No-op option */
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_5( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_5 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6[] =
{
    0x11,             0x22,            0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,             0x32,            0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,             0x00,                                    /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                        /* Version (4). Header length 4*(5) */
    0x00,                                        /* Unused */
    0x12,             0x34,                      /* Total length */
    0xAA,             0xBB,                      /* Identification */
    0x00,             0x00,                      /* Flags: 3 bits, offset: 13 bits */
    0x12,                                        /* Time to live */
    0x06,                                        /* Protocol: TCP */
    0xAB,             0x12,                      /* Header checksum */
    192,              168,             0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,              168,             0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,             0x23,                        /* Source port */
    0xAB,             0xCD,                        /* Destination port */
    0x00,             0x00,            0x00, 0x01, /* Sequence Number */
    0x12,             0x34,            0x56, 0x67, /* ACK number */
    0x70,             0x02,                        /* TCP header size 4-bits (28) (other flags SYN set) */
    0x00,             0x23,                        /* Window size */
    0xff,             0xff,                        /* Checksum */
    0x00,             0x00,                        /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP, /* No-op option */
    tcpTCP_OPT_WSOPT, tcpTCP_OPT_WSOPT_LEN
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_6( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_6 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7[] =
{
    0x11,             0x22,                 0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,             0x32,                 0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,             0x00,                                         /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                             /* Version (4). Header length 4*(5) */
    0x00,                                             /* Unused */
    0x12,             0x34,                           /* Total length */
    0xAA,             0xBB,                           /* Identification */
    0x00,             0x00,                           /* Flags: 3 bits, offset: 13 bits */
    0x12,                                             /* Time to live */
    0x06,                                             /* Protocol: TCP */
    0xAB,             0x12,                           /* Header checksum */
    192,              168,                  0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,              168,                  0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,             0x23,                             /* Source port */
    0xAB,             0xCD,                             /* Destination port */
    0x00,             0x00,                 0x00, 0x01, /* Sequence Number */
    0x12,             0x34,                 0x56, 0x67, /* ACK number */
    0x70,             0x02,                             /* TCP header size 4-bits (28) (other flags SYN set) */
    0x00,             0x23,                             /* Window size */
    0xff,             0xff,                             /* Checksum */
    0x00,             0x00,                             /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP,
    tcpTCP_OPT_WSOPT, tcpTCP_OPT_WSOPT_LEN,
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP   /* No-op option */
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_7( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_7 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_8[] =
{
    0x11,             0x22,                 0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,             0x32,                 0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,             0x00,                                         /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                             /* Version (4). Header length 4*(5) */
    0x00,                                             /* Unused */
    0x12,             0x34,                           /* Total length */
    0xAA,             0xBB,                           /* Identification */
    0x00,             0x00,                           /* Flags: 3 bits, offset: 13 bits */
    0x12,                                             /* Time to live */
    0x06,                                             /* Protocol: TCP */
    0xAB,             0x12,                           /* Header checksum */
    192,              168,                  0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,              168,                  0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,             0x23,                             /* Source port */
    0xAB,             0xCD,                             /* Destination port */
    0x00,             0x00,                 0x00, 0x01, /* Sequence Number */
    0x12,             0x34,                 0x56, 0x67, /* ACK number */
    0x70,             0x00,                             /* TCP header size 4-bits (28) (other flags) */
    0x00,             0x23,                             /* Window size */
    0xff,             0xff,                             /* Checksum */
    0x00,             0x00,                             /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP,
    tcpTCP_OPT_WSOPT, tcpTCP_OPT_WSOPT_LEN,
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP,  tcpTCP_OPT_NOOP   /* No-op option */
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_8( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_8, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_8 ) );
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
    0x11,            0x22,                 0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,            0x32,                 0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,            0x00,                                         /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                            /* Version (4). Header length 4*(5) */
    0x00,                                            /* Unused */
    0x12,            0x34,                           /* Total length */
    0xAA,            0xBB,                           /* Identification */
    0x00,            0x00,                           /* Flags: 3 bits, offset: 13 bits */
    0x12,                                            /* Time to live */
    0x06,                                            /* Protocol: TCP */
    0xAB,            0x12,                           /* Header checksum */
    192,             168,                  0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,             168,                  0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,            0x23,                             /* Source port */
    0xAB,            0xCD,                             /* Destination port */
    0x00,            0x00,                 0x00, 0x01, /* Sequence Number */
    0x12,            0x34,                 0x56, 0x67, /* ACK number */
    0x70,            0x00,                             /* TCP header size 4-bits (28) (other flags) */
    0x00,            0x23,                             /* Window size */
    0xff,            0xff,                             /* Checksum */
    0x00,            0x00,                             /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_MSS,  tcpTCP_OPT_WSOPT_LEN,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP /* No-op option */
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_9( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_9, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_9 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_9 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_9, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_9 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10[] =
{
    0x11,            0x22, 0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,            0x32, 0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,            0x00,                         /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                            /* Version (4). Header length 4*(5) */
    0x00,                            /* Unused */
    0x12,            0x34,           /* Total length */
    0xAA,            0xBB,           /* Identification */
    0x00,            0x00,           /* Flags: 3 bits, offset: 13 bits */
    0x12,                            /* Time to live */
    0x06,                            /* Protocol: TCP */
    0xAB,            0x12,           /* Header checksum */
    192,             168,  0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,             168,  0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,            0x23,             /* Source port */
    0xAB,            0xCD,             /* Destination port */
    0x00,            0x00, 0x00, 0x01, /* Sequence Number */
    0x12,            0x34, 0x56, 0x67, /* ACK number */
    0x60,            0x00,             /* TCP header size 4-bits (28) (other flags) */
    0x00,            0x23,             /* Window size */
    0xff,            0xff,             /* Checksum */
    0x00,            0x00,             /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,  /* No-op option */
    tcpTCP_OPT_MSS,  tcpTCP_OPT_WSOPT_LEN
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_10( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_10 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11[] =
{
    0x11,            0x22, 0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,            0x32, 0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,            0x00,                         /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                            /* Version (4). Header length 4*(5) */
    0x00,                            /* Unused */
    0x12,            0x34,           /* Total length */
    0xAA,            0xBB,           /* Identification */
    0x00,            0x00,           /* Flags: 3 bits, offset: 13 bits */
    0x12,                            /* Time to live */
    0x06,                            /* Protocol: TCP */
    0xAB,            0x12,           /* Header checksum */
    192,             168,  0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,             168,  0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,            0x23,             /* Source port */
    0xAB,            0xCD,             /* Destination port */
    0x00,            0x00, 0x00, 0x01, /* Sequence Number */
    0x12,            0x34, 0x56, 0x67, /* ACK number */
    0x60,            0x00,             /* TCP header size 4-bits (28) (other flags) */
    0x00,            0x23,             /* Window size */
    0xff,            0xff,             /* Checksum */
    0x00,            0x00,             /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,  /* No-op option */
    tcpTCP_OPT_MSS,  tcpTCP_OPT_MSS_LEN
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_11( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11 );
    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_11 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12[] =
{
    0x11,            0x22,               0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,            0x32,               0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,            0x00,                                       /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                          /* Version (4). Header length 4*(5) */
    0x00,                                          /* Unused */
    0x12,            0x34,                         /* Total length */
    0xAA,            0xBB,                         /* Identification */
    0x00,            0x00,                         /* Flags: 3 bits, offset: 13 bits */
    0x12,                                          /* Time to live */
    0x06,                                          /* Protocol: TCP */
    0xAB,            0x12,                         /* Header checksum */
    192,             168,                0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,             168,                0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,            0x23,                           /* Source port */
    0xAB,            0xCD,                           /* Destination port */
    0x00,            0x00,               0x00, 0x01, /* Sequence Number */
    0x12,            0x34,               0x56, 0x67, /* ACK number */
    0x70,            0x00,                           /* TCP header size 4-bits (28) (other flags) */
    0x00,            0x23,                           /* Window size */
    0xff,            0xff,                           /* Checksum */
    0x00,            0x00,                           /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,                /* No-op option */
    tcpTCP_OPT_MSS,  tcpTCP_OPT_MSS_LEN,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_12( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    uint16_t usMSSLocal = 0xAB56;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12 );

    usChar2u16_ExpectAndReturn( &ucLocalBuffer[ sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12 ) - 4 ], usMSSLocal );

    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_12 ) );
}

uint8_t IP_Packet_AptHeader_ValidDataLen_ValidOptLen_13[] =
{
    0x11,            0x22,               0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,            0x32,               0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,            0x00,                                       /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                          /* Version (4). Header length 4*(5) */
    0x00,                                          /* Unused */
    0x12,            0x34,                         /* Total length */
    0xAA,            0xBB,                         /* Identification */
    0x00,            0x00,                         /* Flags: 3 bits, offset: 13 bits */
    0x12,                                          /* Time to live */
    0x06,                                          /* Protocol: TCP */
    0xAB,            0x12,                         /* Header checksum */
    192,             168,                0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,             168,                0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,            0x23,                           /* Source port */
    0xAB,            0xCD,                           /* Destination port */
    0x00,            0x00,               0x00, 0x01, /* Sequence Number */
    0x12,            0x34,               0x56, 0x67, /* ACK number */
    0x70,            0x00,                           /* TCP header size 4-bits (28) (other flags) */
    0x00,            0x23,                           /* Window size */
    0xff,            0xff,                           /* Checksum */
    0x00,            0x00,                           /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,                /* No-op option */
    tcpTCP_OPT_MSS,  tcpTCP_OPT_MSS_LEN,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_13( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    uint16_t usMSSLocal = 0xAB56;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_13, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_13 ) );
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
    0x11,            0x22,               0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,            0x32,               0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,            0x00,                                       /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                          /* Version (4). Header length 4*(5) */
    0x00,                                          /* Unused */
    0x12,            0x34,                         /* Total length */
    0xAA,            0xBB,                         /* Identification */
    0x00,            0x00,                         /* Flags: 3 bits, offset: 13 bits */
    0x12,                                          /* Time to live */
    0x06,                                          /* Protocol: TCP */
    0xAB,            0x12,                         /* Header checksum */
    192,             168,                0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,             168,                0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,            0x23,                           /* Source port */
    0xAB,            0xCD,                           /* Destination port */
    0x00,            0x00,               0x00, 0x01, /* Sequence Number */
    0x12,            0x34,               0x56, 0x67, /* ACK number */
    0x70,            0x00,                           /* TCP header size 4-bits (28) (other flags) */
    0x00,            0x23,                           /* Window size */
    0xff,            0xff,                           /* Checksum */
    0x00,            0x00,                           /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,                /* No-op option */
    tcpTCP_OPT_MSS,  tcpTCP_OPT_MSS_LEN,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP, tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_14( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    uint16_t usMSSLocal = 0;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14 );

    usChar2u16_ExpectAndReturn( &ucLocalBuffer[ sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14 ) - 4 ], usMSSLocal );

    pxSocket->u.xTCP.usInitMSS = usMSSLocal + 2;

    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14, ucLocalBuffer, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14 ) );
}

void test_prvCheckOptions_AptHeader_ValidDataLen_ValidOptLen_14_1( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;
    uint16_t usMSSLocal = 0;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14, sizeof( IP_Packet_AptHeader_ValidDataLen_ValidOptLen_14 ) );
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
    0x11,              0x22,               0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,              0x32,               0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,              0x00,                                       /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                            /* Version (4). Header length 4*(5) */
    0x00,                                            /* Unused */
    0x12,              0x34,                         /* Total length */
    0xAA,              0xBB,                         /* Identification */
    0x00,              0x00,                         /* Flags: 3 bits, offset: 13 bits */
    0x12,                                            /* Time to live */
    0x06,                                            /* Protocol: TCP */
    0xAB,              0x12,                         /* Header checksum */
    192,               168,                0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,               168,                0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,              0x23,                           /* Source port */
    0xAB,              0xCD,                           /* Destination port */
    0x00,              0x00,               0x00, 0x01, /* Sequence Number */
    0x12,              0x34,               0x56, 0x67, /* ACK number */
    0x70,              0x00,                           /* TCP header size 4-bits (28) (other flags) */
    0x00,              0x23,                           /* Window size */
    0xff,              0xff,                           /* Checksum */
    0x00,              0x00,                           /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP,                /* No-op option */
    tcpTCP_OPT_SACK_P, tcpTCP_OPT_MSS_LEN,
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_SACK_Permitted( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_SACK_Permitted, sizeof( IP_Packet_AptHeader_SACK_Permitted ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_SACK_Permitted );

    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_SACK_Permitted, ucLocalBuffer, sizeof( IP_Packet_AptHeader_SACK_Permitted ) );
}

uint8_t IP_Packet_AptHeader_SACK_Permitted_1[] =
{
    0x11,              0x22,            0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,              0x32,            0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,              0x00,                                    /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                         /* Version (4). Header length 4*(5) */
    0x00,                                         /* Unused */
    0x12,              0x34,                      /* Total length */
    0xAA,              0xBB,                      /* Identification */
    0x00,              0x00,                      /* Flags: 3 bits, offset: 13 bits */
    0x12,                                         /* Time to live */
    0x06,                                         /* Protocol: TCP */
    0xAB,              0x12,                      /* Header checksum */
    192,               168,             0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,               168,             0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,              0x23,                        /* Source port */
    0xAB,              0xCD,                        /* Destination port */
    0x00,              0x00,            0x00, 0x01, /* Sequence Number */
    0x12,              0x34,            0x56, 0x67, /* ACK number */
    0x70,              0x00,                        /* TCP header size 4-bits (28) (other flags) */
    0x00,              0x23,                        /* Window size */
    0xff,              0xff,                        /* Checksum */
    0x00,              0x00,                        /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP,             /* No-op option */
    tcpTCP_OPT_SACK_P, 0,                           /* Zero length option */
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_SACK_Permitted_1( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_SACK_Permitted_1, sizeof( IP_Packet_AptHeader_SACK_Permitted_1 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_SACK_Permitted_1 );

    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_SACK_Permitted_1, ucLocalBuffer, sizeof( IP_Packet_AptHeader_SACK_Permitted_1 ) );
}

uint8_t IP_Packet_AptHeader_SACK_Permitted_2[] =
{
    0x11,              0x22,            0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,              0x32,            0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,              0x00,                                    /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                         /* Version (4). Header length 4*(5) */
    0x00,                                         /* Unused */
    0x12,              0x34,                      /* Total length */
    0xAA,              0xBB,                      /* Identification */
    0x00,              0x00,                      /* Flags: 3 bits, offset: 13 bits */
    0x12,                                         /* Time to live */
    0x06,                                         /* Protocol: TCP */
    0xAB,              0x12,                      /* Header checksum */
    192,               168,             0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,               168,             0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,              0x23,                        /* Source port */
    0xAB,              0xCD,                        /* Destination port */
    0x00,              0x00,            0x00, 0x01, /* Sequence Number */
    0x12,              0x34,            0x56, 0x67, /* ACK number */
    0x70,              0x00,                        /* TCP header size 4-bits (28) (other flags) */
    0x00,              0x23,                        /* Window size */
    0xff,              0xff,                        /* Checksum */
    0x00,              0x00,                        /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP,             /* No-op option */
    tcpTCP_OPT_SACK_P, 7,                           /* More length than remaining bytes */
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_SACK_Permitted_2( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_SACK_Permitted_2, sizeof( IP_Packet_AptHeader_SACK_Permitted_2 ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_SACK_Permitted_2 );

    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_SACK_Permitted_2, ucLocalBuffer, sizeof( IP_Packet_AptHeader_SACK_Permitted_2 ) );
}

uint8_t IP_Packet_AptHeader_SACK_Set[] =
{
    0x11,              0x22,            0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,              0x32,            0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,              0x00,                                    /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                                         /* Version (4). Header length 4*(5) */
    0x00,                                         /* Unused */
    0x12,              0x34,                      /* Total length */
    0xAA,              0xBB,                      /* Identification */
    0x00,              0x00,                      /* Flags: 3 bits, offset: 13 bits */
    0x12,                                         /* Time to live */
    0x06,                                         /* Protocol: TCP */
    0xAB,              0x12,                      /* Header checksum */
    192,               168,             0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,               168,             0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,              0x23,                        /* Source port */
    0xAB,              0xCD,                        /* Destination port */
    0x00,              0x00,            0x00, 0x01, /* Sequence Number */
    0x12,              0x34,            0x56, 0x67, /* ACK number */
    0x70,              0x00,                        /* TCP header size 4-bits (28) (other flags) */
    0x00,              0x23,                        /* Window size */
    0xff,              0xff,                        /* Checksum */
    0x00,              0x00,                        /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP,             /* No-op option */
    tcpTCP_OPT_SACK_A, 3,                           /* Smaller length of option */
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP,
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP
};

void test_prvCheckOptions_AptHeader_SACK_Set( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_SACK_Set, sizeof( IP_Packet_AptHeader_SACK_Set ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_SACK_Set );

    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_SACK_Set, ucLocalBuffer, sizeof( IP_Packet_AptHeader_SACK_Set ) );
}

uint8_t IP_Packet_AptHeader_SACK_Send[] =
{
    0x11,              0x22, 0x33, 0x44, 0x55, 0x66, /* Destination MAC */
    0x21,              0x32, 0x43, 0x54, 0x65, 0x76, /* Source MAC */
    0x80,              0x00,                         /* Type: IPv4 */

    /****** IPv4 ******/
    0x45,                              /* Version (4). Header length 4*(5) */
    0x00,                              /* Unused */
    0x12,              0x34,           /* Total length */
    0xAA,              0xBB,           /* Identification */
    0x00,              0x00,           /* Flags: 3 bits, offset: 13 bits */
    0x12,                              /* Time to live */
    0x06,                              /* Protocol: TCP */
    0xAB,              0x12,           /* Header checksum */
    192,               168,  0,    2,  /* Source IP - not in hex since it is easy to manipulate */
    192,               168,  0,    10, /* Destination IP - not in hex since it is easy to manipulate */

    /****** TCP *******/
    0x12,              0x23,             /* Source port */
    0xAB,              0xCD,             /* Destination port */
    0x00,              0x00, 0x00, 0x01, /* Sequence Number */
    0x12,              0x34, 0x56, 0x67, /* ACK number */
    0x80,              0x00,             /* TCP header size 4-bits (32) (other flags) */
    0x00,              0x23,             /* Window size */
    0xff,              0xff,             /* Checksum */
    0x00,              0x00,             /* Urgent point if flag set */
    /* Options */
    tcpTCP_OPT_NOOP,   tcpTCP_OPT_NOOP,  /* No-op option */
    tcpTCP_OPT_SACK_A, 10,               /* Smaller length of option */
    0x00,              0x00,             /* Start segment - 1 */
    0x00,              0xff,             /* Start Segment - 2 */
    0x00,              0x00,             /* End segment - 1 */
    0x01,              0xff              /* End Segment - 2 */
};

void test_prvCheckOptions_AptHeader_SACK_Send( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer, * pxNetworkBuffer;

    pxSocket = &xLocalSocket;
    pxNetworkBuffer = &xLocalNetworkBuffer;
    uint8_t ucLocalBuffer[ ipconfigTCP_MSS ];

    memcpy( ucLocalBuffer, IP_Packet_AptHeader_SACK_Send, sizeof( IP_Packet_AptHeader_SACK_Send ) );
    pxNetworkBuffer->pucEthernetBuffer = ucLocalBuffer;

    /* Make the data length invalid. */
    pxNetworkBuffer->xDataLength = sizeof( IP_Packet_AptHeader_SACK_Send );

    prvReadSackOption_Expect( &ucLocalBuffer[ sizeof( IP_Packet_AptHeader_SACK_Send ) - 10 ], 2, pxSocket );

    prvCheckOptions( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL_MEMORY( IP_Packet_AptHeader_SACK_Send, ucLocalBuffer, sizeof( IP_Packet_AptHeader_SACK_Send ) );
}


void test_prvTCPSendChallengeAck( void )
{
    NetworkBufferDescriptor_t xLocalBuffer;
    BaseType_t xTemp = 0x1234, xReturn;

    prvTCPSendSpecialPacketHelper_ExpectAndReturn( &xLocalBuffer, tcpTCP_FLAG_ACK, xTemp );

    xReturn = prvTCPSendChallengeAck( &xLocalBuffer );

    TEST_ASSERT_EQUAL( xTemp, xReturn );
}

void test_prvTCPSendReset( void )
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

void test_prvTCPHandleState_CannotStoreData( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
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

void test_prvTCPHandleState_CanStoreData( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
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

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    prvHandleEstablished_ExpectAndReturn( pxSocket, ppxNetworkBuffer, ucReceiveLength, xOptionLength, 0x34AB );

    prvSendData_ExpectAnyArgsAndReturn( 0xAB );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0xAB, xReturn );
}

void test_prvTCPHandleState_CanStoreData_KeepAliveSeq( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    prvHandleEstablished_ExpectAndReturn( pxSocket, ppxNetworkBuffer, ucReceiveLength, xOptionLength, 0x34AB );

    prvSendData_ExpectAnyArgsAndReturn( 0xAB );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0xAB, xReturn );
}

void test_prvTCPHandleState_SynFirst( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eSYN_FIRST;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );


    prvSetSynAckOptions_ExpectAnyArgsAndReturn( uxOptionsLength );
    vTCPStateChange_Expect( pxSocket, eSYN_RECEIVED );

    prvSendData_ExpectAnyArgsAndReturn( 0xAB );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0xAB, xReturn );
}

void test_prvTCPHandleState_eClosed( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eCLOSED;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_prvTCPHandleState_eTCPListen( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eTCP_LISTEN;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

void test_prvTCPHandleState_eConnectSyn( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eCONNECT_SYN;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    prvHandleSynReceived_ExpectAnyArgsAndReturn( xSendLength );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( xSendLength, xReturn );
}

void test_prvTCPHandleState_eSynReceived_FlagNotSyn( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eSYN_RECEIVED;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    prvHandleSynReceived_ExpectAnyArgsAndReturn( xSendLength );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( xSendLength, xReturn );
}

void test_prvTCPHandleState_eSynReceived_FlagSyn( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eSYN_RECEIVED;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_SYN;
    vTCPStateChange_Expect( pxSocket, eSYN_FIRST );

    prvHandleSynReceived_ExpectAnyArgsAndReturn( xSendLength );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( xSendLength, xReturn );
}

void test_prvTCPHandleState_eSynReceived_FlagFIN_FinRecvFalse( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eSYN_RECEIVED;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.bits.bFinRecv = pdTRUE_UNSIGNED;
    pxTCPWindow->rx.ulFINSequenceNumber = 0x12;

    prvHandleSynReceived_ExpectAnyArgsAndReturn( xSendLength );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( xSendLength, xReturn );
    TEST_ASSERT_EQUAL( 0x12, pxTCPWindow->rx.ulFINSequenceNumber );
}

void test_prvTCPHandleState_eSynReceived_FlagFIN_FinRecvTrue_FinSentTrue( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eSYN_RECEIVED;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;

    prvHandleSynReceived_ExpectAnyArgsAndReturn( xSendLength );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( xSendLength, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxSocket->u.xTCP.bits.bFinLast );
}

void test_prvTCPHandleState_eSynReceived_FlagFIN_FinRecvTrue_FinSentFalse( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eSYN_RECEIVED;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;

    prvHandleSynReceived_ExpectAnyArgsAndReturn( xSendLength );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( xSendLength, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinLast );
}

void test_prvTCPHandleState_eLastAck( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eLAST_ACK;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;

    prvTCPHandleFin_ExpectAnyArgsAndReturn( xSendLength );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( xSendLength, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinLast );
}

void test_prvTCPHandleState_eFinWait1( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eFIN_WAIT_1;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;

    prvTCPHandleFin_ExpectAnyArgsAndReturn( xSendLength );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( xSendLength, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinLast );
}

void test_prvTCPHandleState_eFinWait2( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eFIN_WAIT_2;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;

    prvTCPHandleFin_ExpectAnyArgsAndReturn( xSendLength );

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( xSendLength, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinLast );
}

void test_prvTCPHandleState_eCloseWait( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eCLOSE_WAIT;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinLast );
}

void test_prvTCPHandleState_eClosing( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eCLOSING;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinLast );
}

void test_prvTCPHandleState_eTimeWait( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eTIME_WAIT;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinLast );
}

void test_prvTCPHandleState_eDefault( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    BaseType_t xReturn, xSendLength = -2;
    uint8_t ucReceiveLength = 0;
    BaseType_t xOptionLength = 0x1234;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0x1234;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER +
                                                                                                                 xIPHeaderSize( *ppxNetworkBuffer ) ] );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
    TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

    uint32_t ulNextSequenceNumber = 0xABCD;

    prvCheckRxData_ExpectAndReturn( pxNetworkBuffer, NULL, ucReceiveLength );
    prvCheckRxData_IgnoreArg_ppucRecvData();

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eTIME_WAIT + 1;

    /* Add a sequence number. */
    pxTCPHeader->ulSequenceNumber = FreeRTOS_htonl( ulNextSequenceNumber );
    /* Add next sequence in the window */
    pxTCPWindow->rx.ulCurrentSequenceNumber = ulNextSequenceNumber + 1;

    /* Make the highest sequence number smaller. */
    pxTCPWindow->rx.ulHighestSequenceNumber = ulNextSequenceNumber - 100;

    /* Return a positive value to show that storing data was successful */
    prvStoreRxData_ExpectAndReturn( pxSocket, NULL, *ppxNetworkBuffer, ucReceiveLength, 1 );
    prvStoreRxData_IgnoreArg_pucRecvData();

    prvSetOptions_ExpectAndReturn( pxSocket, *ppxNetworkBuffer, xOptionLength );

    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_FIN;
    pxSocket->u.xTCP.bits.bFinLast = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinRecv = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;

    xReturn = prvTCPHandleState( pxSocket, ppxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinLast );
}

void test_prvTCPSendRepeated_MaxOutLoop( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxLocalBuffer, ** ppxLocalBuffer;
    int32_t ulReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];

    pxSocket = &xLocalSocket;

    pxLocalBuffer = &xLocalBuffer;
    ppxLocalBuffer = &pxLocalBuffer;
    pxLocalBuffer->pucEthernetBuffer = ucBuffer;

    pxSocket->u.xTCP.txStream = NULL;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED - 1;

    for( int i = 0; i < SEND_REPEATED_COUNT; i++ )
    {
        prvTCPReturnPacket_ExpectAnyArgs();
    }

    ulReturn = prvTCPSendRepeated( pxSocket, ppxLocalBuffer );

    TEST_ASSERT_EQUAL( 40 * SEND_REPEATED_COUNT, ulReturn );
}

void test_prvTCPSendRepeated_BufferResizeFail( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxLocalBuffer, ** ppxLocalBuffer;
    int32_t ulReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];

    pxSocket = &xLocalSocket;

    pxLocalBuffer = &xLocalBuffer;
    ppxLocalBuffer = &pxLocalBuffer;
    pxLocalBuffer->pucEthernetBuffer = ucBuffer;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;
    /* Anything greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2U;
    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED - 1;
    pxSocket->u.xTCP.bits.bWinChange = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;

    /* Get 100 bytes in the Tx window. */
    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( 100 );

    /* Buffer resize fail. */
    prvTCPBufferResize_ExpectAnyArgsAndReturn( NULL );

    ulReturn = prvTCPSendRepeated( pxSocket, ppxLocalBuffer );

    TEST_ASSERT_EQUAL( 0, ulReturn );
}

void test_prvTCPPrepareSend_WinChangeFalse_KeepAliveFalse( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    pxSocket->u.xTCP.usCurMSS = 0;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eCLOSE_WAIT;

    pxSocket->u.xTCP.bits.bWinChange = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( 0, lReturn );
}

void test_prvTCPPrepareSend_WinChangeFalse_KeepAliveTrue( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    pxSocket->u.xTCP.usCurMSS = 0;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eCLOSE_WAIT;

    pxSocket->u.xTCP.bits.bWinChange = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
}

void test_prvTCPPrepareSend_WinChangeTrue_KeepAliveFalse( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    pxSocket->u.xTCP.usCurMSS = 0;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eCLOSE_WAIT;

    pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
}

void test_prvTCPPrepareSend_CloseWaitState( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x123;
    size_t uxOffset = 0xFEDC;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );
    /* Return a stream buffer which is valid */
    prvTCPBufferResize_ExpectAnyArgsAndReturn( pxNetworkBuffer );


    uxStreamBufferDistance_ExpectAndReturn( pxSocket->u.xTCP.txStream, pxSocket->u.xTCP.txStream->uxTail, 0, uxOffset );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( ulDataGot );

    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eCLOSE_WAIT;

    pxSocket->u.xTCP.bits.bWinChange = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( lDataLength + uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
}

void test_prvTCPPrepareSend_EstablishedState_UserShutdownFalse_RepCount3( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x123;
    size_t uxOffset = 0xFEDC;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );
    /* Return a stream buffer which is valid */
    prvTCPBufferResize_ExpectAnyArgsAndReturn( pxNetworkBuffer );


    uxStreamBufferDistance_ExpectAndReturn( pxSocket->u.xTCP.txStream, pxSocket->u.xTCP.txStream->uxTail, 0, uxOffset );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( ulDataGot );

    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Stop User shutdown */
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.ucKeepRepCount = 3U;

    pxSocket->u.xTCP.bits.bWinChange = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( lDataLength + uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
}

void test_prvTCPPrepareSend_EstablishedState_UserShutdownFalse_RepCountGreaterThan3( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x123;
    size_t uxOffset = 0xFEDC;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );
    /* Return a stream buffer which is valid */
    prvTCPBufferResize_ExpectAnyArgsAndReturn( pxNetworkBuffer );

    uxStreamBufferDistance_ExpectAndReturn( pxSocket->u.xTCP.txStream, pxSocket->u.xTCP.txStream->uxTail, 0, uxOffset );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( ulDataGot );

    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Stop User shutdown */
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.ucKeepRepCount = 4U;

    vTCPStateChange_Expect( pxSocket, eCLOSE_WAIT );

    pxSocket->u.xTCP.bits.bWinChange = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( -1 + uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
}

void test_prvTCPPrepareSend_EstablishedState_RepCountNonZeroButPositive( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x00;
    size_t uxOffset = 0xFEDC;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );

    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Stop User shutdown */
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.ucKeepRepCount = 3U;

    pxSocket->u.xTCP.xLastAliveTime = 0x123;
    xTaskGetTickCount_ExpectAndReturn( pxSocket->u.xTCP.xLastAliveTime + 0x12 );

    pxSocket->u.xTCP.bits.bWinChange = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
}

void test_prvTCPPrepareSend_EstablishedState_RepCountZero( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x00;
    size_t uxOffset = 0xFEDC;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );

    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Stop User shutdown */
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.ucKeepRepCount = 0U;

    pxSocket->u.xTCP.xLastAliveTime = 0x123;
    xTaskGetTickCount_ExpectAndReturn( pxSocket->u.xTCP.xLastAliveTime + 0x12 );

    pxSocket->u.xTCP.bits.bWinChange = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
}

void test_prvTCPPrepareSend_EstablishedState_RepCountZero_AgeExceeds( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x00;
    size_t uxOffset = 0xFEDC, uxTickCount = 0x12AB;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );

    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Stop User shutdown */
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.ucKeepRepCount = 0U;

    pxSocket->u.xTCP.xLastAliveTime = 0x123;
    xTaskGetTickCount_ExpectAndReturn( pxSocket->u.xTCP.xLastAliveTime + ( ipconfigTCP_KEEP_ALIVE_INTERVAL * ( TickType_t ) configTICK_RATE_HZ ) + 1 );

    xTaskGetTickCount_ExpectAndReturn( uxTickCount );

    pxSocket->u.xTCP.bits.bWinChange = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( uxTickCount, pxSocket->u.xTCP.xLastAliveTime );
}

void test_prvTCPPrepareSend_EstablishedState_RepCountZero_AgeExceeds_WinChangeTrue( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x00;
    size_t uxOffset = 0xFEDC, uxTickCount = 0x12AB;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );

    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Stop User shutdown */
    pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.ucKeepRepCount = 0U;

    pxSocket->u.xTCP.xLastAliveTime = 0x123;

    pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxSocket->u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0x123, pxSocket->u.xTCP.xLastAliveTime );
}

void test_prvTCPPrepareSend_EstablishedState_RepCountZero_AgeExceeds_WinChangeTrue1( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x00;
    size_t uxOffset = 0xFEDC, uxTickCount = 0x12AB;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );

    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Stop User shutdown */
    pxSocket->u.xTCP.bits.bUserShutdown = pdTRUE_UNSIGNED;
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdFALSE );
    pxSocket->u.xTCP.ucKeepRepCount = 0U;

    pxSocket->u.xTCP.xLastAliveTime = 0x123;

    pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxSocket->u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0x123, pxSocket->u.xTCP.xLastAliveTime );
}

void test_prvTCPPrepareSend_EstablishedState_RepCountZero_AgeExceeds_WinChangeTrue2( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x00;
    size_t uxOffset = 0xFEDC, uxTickCount = 0x12AB;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );

    pxSocket->u.xTCP.bits.bCloseRequested = pdFALSE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Stop User shutdown */
    pxSocket->u.xTCP.bits.bUserShutdown = pdTRUE_UNSIGNED;
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdTRUE );
    vTCPStateChange_Expect( pxSocket, eFIN_WAIT_1 );

    pxSocket->u.xTCP.ucKeepRepCount = 0U;

    pxSocket->u.xTCP.xLastAliveTime = 0x123;

    pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxSocket->u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0x123, pxSocket->u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bUserShutdown );
}

void test_prvTCPPrepareSend_EstablishedState_RepCountZero_AgeExceeds_WinChangeTrue3( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x01;
    size_t uxOffset = 0xFEDC, uxTickCount = 0x12AB;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );

    prvTCPBufferResize_ExpectAnyArgsAndReturn( pxNetworkBuffer );

    uxStreamBufferDistance_ExpectAndReturn( pxSocket->u.xTCP.txStream, pxSocket->u.xTCP.txStream->uxTail, 0, uxOffset );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( ulDataGot );

    pxSocket->u.xTCP.bits.bCloseRequested = pdTRUE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Stop User shutdown */
    pxSocket->u.xTCP.bits.bUserShutdown = pdTRUE_UNSIGNED;
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdTRUE );
    vTCPStateChange_Expect( pxSocket, eFIN_WAIT_1 );

    pxSocket->u.xTCP.ucKeepRepCount = 0U;

    pxSocket->u.xTCP.xLastAliveTime = 0x123;

    pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( lDataLength + uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxSocket->u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0x123, pxSocket->u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bUserShutdown );
}

void test_prvTCPPrepareSend_EstablishedState_RepCountZero_AgeExceeds_WinChangeTrue4( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x01;
    size_t uxOffset = 0xFEDC, uxTickCount = 0x12AB;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );

    prvTCPBufferResize_ExpectAnyArgsAndReturn( pxNetworkBuffer );

    uxStreamBufferDistance_ExpectAndReturn( pxSocket->u.xTCP.txStream, pxSocket->u.xTCP.txStream->uxTail, 0, uxOffset );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( ulDataGot );

    uxStreamBufferDistance_ExpectAnyArgsAndReturn( ulDataGot + 1 );

    pxSocket->u.xTCP.bits.bCloseRequested = pdTRUE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Stop User shutdown */
    pxSocket->u.xTCP.bits.bUserShutdown = pdTRUE_UNSIGNED;
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdTRUE );
    vTCPStateChange_Expect( pxSocket, eFIN_WAIT_1 );

    pxSocket->u.xTCP.ucKeepRepCount = 0U;

    pxSocket->u.xTCP.xLastAliveTime = 0x123;

    pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( lDataLength + uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxSocket->u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0x123, pxSocket->u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bUserShutdown );
}

void test_prvTCPPrepareSend_EstablishedState_RepCountZero_AgeExceeds_WinChangeTrue5( void )
{
    FreeRTOS_Socket_t xLocalSocket, * pxSocket;
    NetworkBufferDescriptor_t xLocalBuffer, * pxNetworkBuffer, ** ppxNetworkBuffer;
    int32_t lReturn;
    uint8_t ucBuffer[ ipconfigTCP_MSS ];
    uint8_t ucStream[ ipconfigTCP_MSS ];
    UBaseType_t uxOptionsLength = 0xAB;
    int32_t lDataLength = 0x01;
    size_t uxOffset = 0xFEDC, uxTickCount = 0x12AB;
    uint32_t ulDataGot = 0xBAC;
    ProtocolHeaders_t * pxProtocolHeaders;

    pxSocket = &xLocalSocket;

    pxNetworkBuffer = &xLocalBuffer;
    ppxNetworkBuffer = &pxNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucBuffer;

    pxProtocolHeaders = ( ProtocolHeaders_t * ) &( ucBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] );

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    /* Any value greater than 1 */
    pxSocket->u.xTCP.usCurMSS = 2;

    ulTCPWindowTxGet_ExpectAnyArgsAndReturn( lDataLength );

    prvTCPBufferResize_ExpectAnyArgsAndReturn( pxNetworkBuffer );

    uxStreamBufferDistance_ExpectAndReturn( pxSocket->u.xTCP.txStream, pxSocket->u.xTCP.txStream->uxTail, 0, uxOffset );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( ulDataGot );

    uxStreamBufferDistance_ExpectAnyArgsAndReturn( ulDataGot );

    pxSocket->u.xTCP.bits.bCloseRequested = pdTRUE_UNSIGNED;

    pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eESTABLISHED;

    /* Stop User shutdown */
    pxSocket->u.xTCP.bits.bUserShutdown = pdTRUE_UNSIGNED;
    xTCPWindowTxDone_ExpectAnyArgsAndReturn( pdTRUE );
    vTCPStateChange_Expect( pxSocket, eFIN_WAIT_1 );

    pxSocket->u.xTCP.ucKeepRepCount = 0U;

    pxSocket->u.xTCP.xLastAliveTime = 0x123;

    pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
    pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;
    pxSocket->u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;

    lReturn = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

    TEST_ASSERT_EQUAL( lDataLength + uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength, lReturn );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_ACK );
    TEST_ASSERT_NOT_EQUAL( 0, pxProtocolHeaders->xTCPHeader.ucTCPFlags & tcpTCP_FLAG_FIN );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxSocket->u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0x123, pxSocket->u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( pdFALSE, pxSocket->u.xTCP.bits.bUserShutdown );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxSocket->u.xTCP.bits.bFinSent );
}
