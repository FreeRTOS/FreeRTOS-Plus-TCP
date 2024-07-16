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
#include "FreeRTOS_Stream_Buffer.h"

/* CBMC includes. */
#include "cbmc.h"

/* This proof assumes that pxGetNetworkBufferWithDescriptor is implemented correctly. */
int32_t publicTCPPrepareSend( FreeRTOS_Socket_t * pxSocket,
                              NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                              UBaseType_t uxOptionsLength );

/* Memory assignment for FreeRTOS_Socket_t */
FreeRTOS_Socket_t * ensure_FreeRTOS_Socket_t_is_allocated()
{
    size_t buf_size; /* Give buffer_size an unconstrained value */
    FreeRTOS_Socket_t * pxSocket = safeMalloc( sizeof( FreeRTOS_Socket_t ) + sizeof( IPTCPSocket_t ) );

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

/* Get rid of configASSERT in FreeRTOS_TCP_IP.c */
BaseType_t xIsCallingFromIPTask( void )
{
    return pdTRUE;
}

/* Mock FreeRTOS_TCP_State_Handling.h APIs */
BaseType_t prvTCPSocketIsActive( eIPTCPState_t eStatus )
{
    return nondet_BaseType();
}

/* Mock FreeRTOS_TCP_WIN.h APIs */
BaseType_t xTCPWindowTxDone( const TCPWindow_t * pxWindow )
{
    __CPROVER_assert( pxWindow != NULL, "pxWindow cannot be NULL" );
    return nondet_uint32();
}

uint32_t ulTCPWindowTxGet( TCPWindow_t * pxWindow,
                           uint32_t ulWindowSize,
                           int32_t * plPosition )
{
    uint32_t ulReturn = nondet_uint32();

    __CPROVER_assert( pxWindow != NULL, "pxWindow cannot be NULL" );
    __CPROVER_assert( plPosition != NULL, "plPosition cannot be NULL" );

    /* This function returns the data length of next sending window, which is never larger than network MTU. */
    __CPROVER_assume( ulReturn < ipconfigNETWORK_MTU );
    return ulReturn;
}

/* Mock FreeRTOS_Stream_Buffers.h APIs */
size_t uxStreamBufferDistance( const StreamBuffer_t * const pxBuffer,
                               size_t uxLower,
                               size_t uxUpper )
{
    __CPROVER_assert( pxBuffer != NULL, "pxBuffer cannot be NULL" );
    return nondet_sizet();
}

size_t uxStreamBufferGet( StreamBuffer_t * const pxBuffer,
                          size_t uxOffset,
                          uint8_t * const pucData,
                          size_t uxMaxCount,
                          BaseType_t xPeek )
{
    __CPROVER_assert( pxBuffer != NULL, "pxBuffer cannot be NULL" );
    return nondet_sizet();
}

void * vSocketClose( FreeRTOS_Socket_t * pxSocket )
{
    __CPROVER_assert( pxSocket != NULL, "Closing socket cannot be NULL." );

    return NULL;
}

void vSocketWakeUpUser( FreeRTOS_Socket_t * pxSocket )
{
    __CPROVER_assert( pxSocket != NULL, "Closing socket cannot be NULL." );

    return NULL;
}

void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    FreeRTOS_Socket_t * pxSocket;
    size_t socketSize = sizeof( FreeRTOS_Socket_t );
    /* Allocates min. buffer size required for the proof */
    size_t bufferSize;

    pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
    __CPROVER_assume( pxSocket != NULL );

    if( pxSocket->u.xTCP.bits.bReuseSocket == pdFALSE )
    {
        /* Make sure we have parent socket if reuse is set to FALSE to avoid assertion in vTCPStateChange(). */
        __CPROVER_assume( pxSocket->u.xTCP.pxPeerSocket != NULL );
    }

    bufferSize = sizeof( TCPPacket_t ) + ipSIZE_OF_IPv6_HEADER;

    pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( bufferSize, 0 );
    __CPROVER_assume( pxNetworkBuffer != NULL );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Call to init the socket list. */
    vListInitialise( &xBoundTCPSocketsList );

    if( pxSocket )
    {
        publicTCPPrepareSend( pxSocket, &pxNetworkBuffer, 0 );
    }
}
