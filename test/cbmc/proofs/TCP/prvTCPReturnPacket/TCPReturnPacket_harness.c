/*
 * FreeRTOS memory safety proofs with CBMC.
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_TCP_IP.h"

#include "../../utility/memory_assignments.c"

#include "cbmc.h"

/* This proof assumes that pxDuplicateNetworkBufferWithDescriptor is implemented correctly. */
void publicTCPReturnPacket( FreeRTOS_Socket_t * pxSocket,
                            NetworkBufferDescriptor_t * pxNetworkBuffer,
                            uint32_t ulLen,
                            BaseType_t xReleaseAfterSend );

/* Abstraction of pxDuplicateNetworkBufferWithDescriptor*/
NetworkBufferDescriptor_t * pxDuplicateNetworkBufferWithDescriptor( const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                    size_t xNewLength )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = ensure_FreeRTOS_NetworkBuffer_is_allocated();

    if( ensure_memory_is_valid( pxNetworkBuffer, sizeof( *pxNetworkBuffer ) ) )
    {
        pxNetworkBuffer->pucEthernetBuffer = safeMalloc( sizeof( TCPPacket_t ) );
        __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer );
    }

    return pxNetworkBuffer;
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * pxDescriptor,
                                    BaseType_t xReleaseAfterSend )
{
    BaseType_t xReturn;

    __CPROVER_assert( pxDescriptor != NULL, "The descriptor cannot be NULL" );
    __CPROVER_assert( pxDescriptor->pucEthernetBuffer != NULL, "The ethernet buffer cannot be NULL" );

    return xReturn;
}

uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    __CPROVER_assert( pucEthernetBuffer != NULL, "The ethernet buffer cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pucEthernetBuffer, uxBufferLength ), "pucEthernetBuffer should be readable." );

    uint16_t usReturn;
    return usReturn;
}

uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
    __CPROVER_assert( pucNextData != NULL, "The next data pointer cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pucNextData, uxByteCount ), "The pucNextData should be readable." );

    uint16_t usReturn;
    return usReturn;
}

void harness()
{
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
    NetworkBufferDescriptor_t * pxNetworkBuffer = ensure_FreeRTOS_NetworkBuffer_is_allocated();

    /* The code does not expect both of these to be equal to NULL at the same time. */
    __CPROVER_assume( pxSocket != NULL || pxNetworkBuffer != NULL );

    uint32_t ulLen;

    /* If network buffer is properly created. */
    if( ensure_memory_is_valid( pxNetworkBuffer, sizeof( *pxNetworkBuffer ) ) )
    {
        /* Assume that the length is proper. */
        __CPROVER_assume( ( ulLen >= sizeof( TCPPacket_t ) ) && ( ulLen < ipconfigNETWORK_MTU ) );
        pxNetworkBuffer->pucEthernetBuffer = safeMalloc( ulLen + ipSIZE_OF_ETH_HEADER );
        __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer );
    }
    /* If not. */
    else
    {
        /* Assume that the length is proper. The length should be between this range. It
         * is made so by the functions up the call tree. Essentially, this is equal to a
         * TCP packet header with and without TCP options. */
        __CPROVER_assume( ( ulLen >= ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER ) &&
                          ( ulLen <= ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER + 40 /* Maximum option bytes. */ ) );
    }

    BaseType_t xReleaseAfterSend;

    publicTCPReturnPacket( pxSocket, pxNetworkBuffer, ulLen, xReleaseAfterSend );
}
