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
#include <unity.h>

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"


const BaseType_t xBufferAllocFixedSize = pdTRUE;

struct freertos_addrinfo pucAddrBuffer[ 2 ];

struct freertos_sockaddr pucSockAddrBuffer[ 1 ];

void vPortEnterCritical( void )
{
}

void vPortExitCritical( void )
{
}

BaseType_t xApplicationDNSQueryHook_Multi( struct xNetworkEndPoint * pxEndPoint,
                                           const char * pcName )
{
    return pdFALSE;
}

struct freertos_addrinfo * xStub_pxNew_AddrInfo( const char * pcName,
                                                 BaseType_t xFamily,
                                                 const uint8_t * pucAddress,
                                                 int numCalls )
{
    struct freertos_addrinfo * pxAddrInfo = NULL;
    void * pvBuffer;
    /* ulChar2u32 reads from big-endian to host-endian. */
    uint32_t ulIPAddress = ( ( ( uint32_t ) pucAddress[ 0 ] ) << 24 ) |
                           ( ( ( uint32_t ) pucAddress[ 1 ] ) << 16 ) |
                           ( ( ( uint32_t ) pucAddress[ 2 ] ) << 8 ) |
                           ( ( ( uint32_t ) pucAddress[ 3 ] ) );

    /* Translate to network-endian. */

    /* 'xFamily' might not be used when IPv6 is disabled. */
    ( void ) xFamily;
    pvBuffer = &pucAddrBuffer[ 0 ];

    if( ( pvBuffer != NULL ) && ( strcmp( pcName, "helloman" ) != 0 ) )
    {
        pxAddrInfo = ( struct freertos_addrinfo * ) pvBuffer;

        ( void ) memset( pxAddrInfo, 0, sizeof( *pxAddrInfo ) );
        pxAddrInfo->ai_canonname = pxAddrInfo->xPrivateStorage.ucName;
        ( void ) strncpy( pxAddrInfo->xPrivateStorage.ucName, pcName, sizeof( pxAddrInfo->xPrivateStorage.ucName ) );

        pxAddrInfo->ai_addr = ( ( struct freertos_sockaddr * ) &( pxAddrInfo->xPrivateStorage.sockaddr ) );

        switch( xFamily )
        {
            #if ( ipconfigUSE_IPv4 != 0 )
                case FREERTOS_AF_INET4:
                    pxAddrInfo->ai_addr->sin_address.ulIP_IPv4 = FreeRTOS_htonl( ulIPAddress );
                    pxAddrInfo->ai_family = FREERTOS_AF_INET4;
                    pxAddrInfo->ai_addrlen = ipSIZE_OF_IPv4_ADDRESS;
                    break;
            #endif /* ( ipconfigUSE_IPv4 != 0 ) */

            #if ( ipconfigUSE_IPv6 != 0 )
                case FREERTOS_AF_INET6:
                    pxAddrInfo->ai_family = FREERTOS_AF_INET6;
                    pxAddrInfo->ai_addrlen = ipSIZE_OF_IPv6_ADDRESS;
                    ( void ) memcpy( pxAddrInfo->xPrivateStorage.sockaddr.sin_address.xIP_IPv6.ucBytes, pucAddress, ipSIZE_OF_IPv6_ADDRESS );
                    break;
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */

            default:
                /* MISRA 16.4 Compliance */
                FreeRTOS_debug_printf( ( "pxNew_AddrInfo: Undefined xFamily Type \n" ) );
                break;
        }
    }

    return pxAddrInfo;
}

#define ipIP_VERSION_AND_HEADER_LENGTH_BYTE    ( ( uint8_t ) 0x45 )
UDPPacketHeader_t xDefaultPartUDPPacketHeader =
{
    /* .ucBytes : */
    {
        0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Ethernet source MAC address. */
        0x08, 0x00,                          /* Ethernet frame type. */
        ipIP_VERSION_AND_HEADER_LENGTH_BYTE, /* ucVersionHeaderLength. */
        0x00,                                /* ucDifferentiatedServicesCode. */
        0x00, 0x00,                          /* usLength. */
        0x00, 0x00,                          /* usIdentification. */
        0x00, 0x00,                          /* usFragmentOffset. */
        ipconfigUDP_TIME_TO_LIVE,            /* ucTimeToLive */
        ipPROTOCOL_UDP,                      /* ucProtocol. */
        0x00, 0x00,                          /* usHeaderChecksum. */
        0x00, 0x00, 0x00, 0x00               /* Source IP address. */
    }
};
