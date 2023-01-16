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
#include "FreeRTOS_DNS_Globals.h"
#include "FreeRTOS_IP_Private.h"


const BaseType_t xBufferAllocFixedSize = pdTRUE;


void vPortEnterCritical( void )
{
}

void vPortExitCritical( void )
{
}

BaseType_t xApplicationDNSQueryHook( struct xNetworkEndPoint * pxEndPoint,
                                     const char * pcName )
{
    return pdFALSE;
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

void * pvPortMalloc( size_t xNeeded )
{
    return malloc( xNeeded );
}

void vPortFree( void * ptr )
{
    free( ptr );
}

/*
 * Convert a string like 'fe80::8d11:cd9b:8b66:4a80'
 * to a 16-byte IPv6 address
 */
BaseType_t FreeRTOS_inet_pton6( const char * pcSource,
                                void * pvDestination )
{
}

/*
 * Get the first end-point belonging to a given interface.  When pxInterface is
 * NULL, the very first end-point will be returned.
 */
NetworkEndPoint_t * FreeRTOS_FirstEndPoint( const NetworkInterface_t * pxInterface )
{
}

/*
 * Get the next end-point.  When pxInterface is null, all end-points can be
 * iterated.
 */
NetworkEndPoint_t * FreeRTOS_NextEndPoint( const NetworkInterface_t * pxInterface,
                                           NetworkEndPoint_t * pxEndPoint )
{
}

/**
 * @brief Bind the socket to a port number.
 * @param[in] xSocket: the socket that must be bound.
 * @param[in] usPort: the port number to bind to.
 * @return The created socket - or NULL if the socket could not be created or could not be bound.
 */
BaseType_t DNS_BindSocket( Socket_t xSocket,
                           uint16_t usPort )
{
}
