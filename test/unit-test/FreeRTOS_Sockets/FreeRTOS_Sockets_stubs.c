/*
 * FreeRTOS+TCP V2.4.0
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

volatile BaseType_t xInsideInterrupt = pdFALSE;

/** @brief The expected IP version and header length coded into the IP header itself. */
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

ipDECL_CAST_PTR_FUNC_FOR_TYPE( FreeRTOS_Socket_t )
{
    return ( FreeRTOS_Socket_t * ) pvArgument;
}

ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( FreeRTOS_Socket_t )
{
    return ( FreeRTOS_Socket_t * ) pvArgument;
}

ipDECL_CAST_PTR_FUNC_FOR_TYPE( SocketSelect_t )
{
    return ( SocketSelect_t * ) pvArgument;
}

ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( UDPPacket_t )
{
    return ( const UDPPacket_t * ) pvArgument;
}

ipDECL_CAST_PTR_FUNC_FOR_TYPE( NetworkBufferDescriptor_t )
{
    return ( NetworkBufferDescriptor_t * ) pvArgument;
}

ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( ListItem_t )
{
    return ( const ListItem_t * ) pvArgument;
}

void vPortEnterCritical( void )
{
}
void vPortExitCritical( void )
{
}

void * pvPortMalloc( size_t xNeeded )
{
    return malloc( xNeeded );
}

void vPortFree( void * ptr )
{
    free( ptr );
}
