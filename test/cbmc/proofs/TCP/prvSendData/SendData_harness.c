/*
 * FreeRTOS memory safety proofs with CBMC.
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* CBMC includes. */
#include "cbmc.h"

/****************************************************************
* Declare the IP Header Size external to the harness so it can be
* accessed by uxIPHeaderSizePacket.
****************************************************************/
size_t uxIPHeaderSizePacket_uxResult;

size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "pxNetworkBuffer should not be NULL" );
    __CPROVER_assert( pxNetworkBuffer->pucEthernetBuffer != NULL, "pucEthernetBuffer should not be NULL" );

    return uxIPHeaderSizePacket_uxResult;
}

void prvTCPReturnPacket( FreeRTOS_Socket_t * pxSocket,
                         NetworkBufferDescriptor_t * pxDescriptor,
                         uint32_t ulLen,
                         BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxSocket != NULL, "pxSocket should not be NULL" );
    __CPROVER_assert( pxDescriptor != NULL, "pxDescriptor should not be NULL" );
    __CPROVER_assert( pxDescriptor->pucEthernetBuffer != NULL, "pucEthernetBuffer should not be NULL" );
}

void prvTCPReturnPacket_IPV4( FreeRTOS_Socket_t * pxSocket,
                              NetworkBufferDescriptor_t * pxDescriptor,
                              uint32_t ulLen,
                              BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxSocket != NULL, "pxSocket should not be NULL" );
    __CPROVER_assert( pxDescriptor != NULL, "pxDescriptor should not be NULL" );
    __CPROVER_assert( pxDescriptor->pucEthernetBuffer != NULL, "pucEthernetBuffer should not be NULL" );
}

/* Memory assignment for FreeRTOS_Socket_t */
FreeRTOS_Socket_t * ensure_FreeRTOS_Socket_t_is_allocated()
{
    size_t buf_size; /* Give buffer_size an unconstrained value */
    FreeRTOS_Socket_t * pxSocket = safeMalloc( sizeof( FreeRTOS_Socket_t ) );

    __CPROVER_assume( pxSocket != NULL );
    pxSocket->u.xTCP.rxStream = safeMalloc( sizeof( StreamBuffer_t ) );
    pxSocket->u.xTCP.txStream = safeMalloc( sizeof( StreamBuffer_t ) );
    pxSocket->u.xTCP.pxPeerSocket = safeMalloc( sizeof( FreeRTOS_Socket_t ) );
    pxSocket->pxEndPoint = safeMalloc( sizeof( NetworkEndPoint_t ) );
    pxSocket->u.xTCP.pxAckMessage = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );

    if( pxSocket->u.xTCP.pxAckMessage != NULL )
    {
        __CPROVER_assume( ( buf_size > ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( TCPHeader_t ) ) ) && ( buf_size < ipconfigNETWORK_MTU ) );
        pxSocket->u.xTCP.pxAckMessage->pucEthernetBuffer = safeMalloc( buf_size );
        __CPROVER_assume( pxSocket->u.xTCP.pxAckMessage->pucEthernetBuffer != NULL );
    }

    return pxSocket;
}

/*
 * In this function, it only allocates network buffer by harness.
 */
void vReleaseNetworkBufferAndDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    __CPROVER_assert( pxNetworkBuffer != NULL,
                      "Precondition: pxNetworkBuffer != NULL" );

    if( pxNetworkBuffer->pucEthernetBuffer != NULL )
    {
        free( pxNetworkBuffer->pucEthernetBuffer );
    }

    free( pxNetworkBuffer );
}

void harness()
{
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    uint32_t ulReceiveLength;
    BaseType_t xByteCount;
    size_t buf_size; /* Give buffer_size an unconstrained value */

    /* The code does not expect pxSocket/pxNetworkBuffer to be equal to NULL. */
    pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
    __CPROVER_assume( pxSocket != NULL );
    __CPROVER_assume( pxNetworkBuffer != NULL );

    if( nondet_bool() )
    {
        uxIPHeaderSizePacket_uxResult = ipSIZE_OF_IPv6_HEADER;
    }
    else
    {
        uxIPHeaderSizePacket_uxResult = ipSIZE_OF_IPv4_HEADER;
    }

    __CPROVER_assume( ( buf_size > ( ipSIZE_OF_ETH_HEADER + uxIPHeaderSizePacket_uxResult + sizeof( TCPHeader_t ) ) ) && ( buf_size < ipconfigNETWORK_MTU ) );

    pxNetworkBuffer->pucEthernetBuffer = safeMalloc( buf_size );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    __CPROVER_havoc_object( pxNetworkBuffer->pucEthernetBuffer );

    prvSendData( pxSocket, &pxNetworkBuffer, ulReceiveLength, xByteCount );
}
