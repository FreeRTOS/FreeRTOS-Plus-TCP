/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
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

#include "FreeRTOSIPConfig.h"

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */

#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
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
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_Utils.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_IPv4_Private.h"
#include "mock_FreeRTOS_ND.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IPv4.h"

#include "FreeRTOS_TCP_Transmission.h"
#include "FreeRTOS_TCP_Transmission_IPV6_stubs.c"

#include "catch_assert.h"


#define PACKET_LENGTH    100

BaseType_t NetworkInterfaceOutputFunction_Stub_Called = 0;

BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    NetworkInterfaceOutputFunction_Stub_Called++;
    return 0;
}

/* ============================ Test Cases ============================ */

/**
 * @brief This function verify handling when both
 *        'pxNetworkBuffer' or 'pxSocket' is not defined.
 *        while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_BufferSocketNULL( void )
{
    FreeRTOS_Socket_t * pxSocket = NULL;
    NetworkBufferDescriptor_t * pxDescriptor = NULL;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdFALSE;

    prvTCPReturnPacket_IPV6( pxSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify handling case when
 *        only pxNetworkBuffer is NULL while
 *        returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_BufferNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t * pxDescriptor = NULL;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdFALSE;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify handling case when
 *        only xSocket is NULL while
 *        returning a packet.
 */
/* void test_prvTCPReturnPacket_IPV6_pucEthernetBuffer_Assert( void ) */
/*  { */
/*     FreeRTOS_Socket_t *pxSocket=NULL; */
/*     NetworkBufferDescriptor_t xDescriptor; */
/*     uint32_t ulLen = PACKET_LENGTH; */
/*     BaseType_t xReleaseAfterSend = pdFALSE; */
/*     NetworkEndPoint_t xEndPoint; */

/*     memset(&xDescriptor, 0, sizeof(NetworkBufferDescriptor_t)); */
/*     memset(&xEndPoint, 0, sizeof(NetworkEndPoint_t)); */
/*     xDescriptor.pxEndPoint = &xEndPoint; */
/*     xDescriptor.pucEthernetBuffer = NULL; */

/*    catch_assert(prvTCPReturnPacket_IPV6( pxSocket, &xDescriptor, ulLen, xReleaseAfterSend )); */
/*  } */

/**
 * @brief This function verify handling case when
 *        only xSocket is NULL while
 *        returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_SocketNULL( void )
{
    FreeRTOS_Socket_t * pxSocket = NULL;
    NetworkBufferDescriptor_t xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdFALSE;
    NetworkEndPoint_t xEndPoint;
    TCPPacket_IPv6_t xTCPPacket;

    memset( &xDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    xDescriptor.pxEndPoint = &xEndPoint;
    xDescriptor.pucEthernetBuffer = &xTCPPacket;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    prvTCPReturnPacket_IPV6( pxSocket, &xDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point is NULL while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_NoEP_NoReleaseAfterSend( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdFALSE;
    TCPPacket_IPv6_t xTCPPacket;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );

    xDescriptor.pucEthernetBuffer = &xTCPPacket;
    xDescriptor.pxEndPoint = NULL;

    prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point is NULL while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_NoEP_ReleaseAfterSend( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdTRUE;
    TCPPacket_IPv6_t xTCPPacket;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );

    xDescriptor.pucEthernetBuffer = &xTCPPacket;
    xDescriptor.pxEndPoint = NULL;

    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point does not have a valid NetworkInterface
 *        while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_Assert1( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdTRUE;
    NetworkEndPoint_t xEndPoint;
    TCPPacket_IPv6_t xTCPPacket;


    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xTCPPacket, 0, sizeof( TCPPacket_IPv6_t ) );

    pxDescriptor->pucEthernetBuffer = &xTCPPacket;
    pxDescriptor->pxEndPoint = &xEndPoint;
    pxDescriptor->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    pxDescriptor->pxEndPoint->pxNetworkInterface = NULL;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    catch_assert( prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend ) );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point does not have a valid NetworkInterface
 *        while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_Assert2( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdTRUE;
    NetworkEndPoint_t xEndPoint;
    TCPPacket_IPv6_t xTCPPacket;


    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xTCPPacket, 0, sizeof( TCPPacket_IPv6_t ) );

    pxDescriptor->pucEthernetBuffer = &xTCPPacket;
    pxDescriptor->pxEndPoint = &xEndPoint;
    pxDescriptor->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    pxDescriptor->pxEndPoint->pxNetworkInterface = NULL;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );

    catch_assert( prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend ) );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point does not have a valid NetworkInterface output
 *        function, while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_Assert3( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdTRUE;
    NetworkEndPoint_t xEndPoint;
    TCPPacket_IPv6_t xTCPPacket;
    NetworkInterface_t xNetworkInterfaces;


    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xTCPPacket, 0, sizeof( TCPPacket_IPv6_t ) );
    memset( &xNetworkInterfaces, 0, sizeof( NetworkInterface_t ) );

    pxDescriptor->pucEthernetBuffer = &xTCPPacket;
    pxDescriptor->pxEndPoint = &xEndPoint;
    pxDescriptor->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    pxDescriptor->pxEndPoint->pxNetworkInterface = &xNetworkInterfaces;
    pxDescriptor->pxEndPoint->pxNetworkInterface->pfOutput = NULL;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    catch_assert( prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend ) );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point does not have a valid NetworkInterface,
 *        while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_HappyPath_ReleaseAfterSend( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    BaseType_t xReleaseAfterSend = pdTRUE;
    NetworkEndPoint_t xEndPoint;
    TCPPacket_IPv6_t xTCPPacket;
    NetworkInterface_t xNetworkInterfaces;


    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xTCPPacket, 0, sizeof( TCPPacket_IPv6_t ) );
    memset( &xNetworkInterfaces, 0, sizeof( NetworkInterface_t ) );

    pxDescriptor->pucEthernetBuffer = &xTCPPacket;
    pxDescriptor->pxEndPoint = &xEndPoint;
    pxDescriptor->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    xEndPoint.pxNetworkInterface = &xNetworkInterfaces;
    xEndPoint.pxNetworkInterface->pfOutput = NULL;
    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point does not have a valid NetworkInterface,
 *        while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_HappyPath_NoReleaseAfterSend( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdFALSE;
    NetworkEndPoint_t xEndPoint;
    TCPPacket_IPv6_t xTCPPacket;
    NetworkInterface_t xNetworkInterfaces;


    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xTCPPacket, 0, sizeof( TCPPacket_IPv6_t ) );
    memset( &xNetworkInterfaces, 0, sizeof( NetworkInterface_t ) );

    pxDescriptor->pucEthernetBuffer = &xTCPPacket;
    pxDescriptor->pxEndPoint = &xEndPoint;
    pxDescriptor->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    xEndPoint.pxNetworkInterface = &xNetworkInterfaces;
    xEndPoint.pxNetworkInterface->pfOutput = NULL;
    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}
