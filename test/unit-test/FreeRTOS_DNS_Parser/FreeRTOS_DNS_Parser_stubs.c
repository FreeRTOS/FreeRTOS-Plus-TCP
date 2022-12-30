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


BaseType_t xBufferAllocFixedSize = pdFALSE;


void vPortEnterCritical( void )
{
}

void vPortExitCritical( void )
{
}

uint16_t usPacketIdentifier;

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

struct freertos_addrinfo * pxNew_AddrInfo( const char * pcName,
                                            BaseType_t xFamily,
                                            const uint8_t * pucAddress ) 
{
    struct freertos_addrinfo * pxAddrInfo = NULL;
    void * pvBuffer;

    /* 'xFamily' might not be used when IPv6 is disabled. */
    ( void ) xFamily;
    pvBuffer = malloc( sizeof( *pxAddrInfo ) );

    // if( pvBuffer != NULL )
    // {
    //     pxAddrInfo = ( struct freertos_addrinfo * ) pvBuffer;

    //     ( void ) memset( pxAddrInfo, 0, sizeof( *pxAddrInfo ) );
    //     pxAddrInfo->ai_canonname = pxAddrInfo->xPrivateStorage.ucName;
    //     ( void ) strncpy( pxAddrInfo->xPrivateStorage.ucName, pcName, sizeof( pxAddrInfo->xPrivateStorage.ucName ) );

    //     #if ( ipconfigUSE_IPv6 == 0 )
    //         pxAddrInfo->ai_addr = &( pxAddrInfo->xPrivateStorage.sockaddr );
    //     #else
    //         pxAddrInfo->ai_addr = ( ( xFreertosSocAddr * ) &( pxAddrInfo->xPrivateStorage.sockaddr ) );

    //         if( xFamily == ( BaseType_t ) FREERTOS_AF_INET6 )
    //         {
    //             pxAddrInfo->ai_family = FREERTOS_AF_INET6;
    //             pxAddrInfo->ai_addrlen = ipSIZE_OF_IPv6_ADDRESS;
    //             ( void ) memcpy( pxAddrInfo->xPrivateStorage.sockaddr.sin_addrv6.ucBytes, pucAddress, ipSIZE_OF_IPv6_ADDRESS );
    //         }
    //         else
    //     #endif /* ( ipconfigUSE_IPv6 == 0 ) */
    //     {
    //         /* ulChar2u32 reads from big-endian to host-endian. */
    //         uint32_t ulIPAddress = ulChar2u32( pucAddress );
    //         /* Translate to network-endian. */
    //         pxAddrInfo->ai_addr->sin_addr.xIP_IPv4 = FreeRTOS_htonl( ulIPAddress );
    //         pxAddrInfo->ai_family = FREERTOS_AF_INET4;
    //         pxAddrInfo->ai_addrlen = ipSIZE_OF_IPv4_ADDRESS;
    //     }
    // }

    return pxAddrInfo;

}
