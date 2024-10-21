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

extern FreeRTOS_Socket_t * xSocketToListen;

/* Abstraction of xTaskGetCurrentTaskHandle */
TaskHandle_t xTaskGetCurrentTaskHandle( void )
{
    static int xIsInit = 0;
    static TaskHandle_t pxCurrentTCB;
    TaskHandle_t xRandomTaskHandle; /* not initialized on purpose */

    if( xIsInit == 0 )
    {
        pxCurrentTCB = xRandomTaskHandle;
        xIsInit = 1;
    }

    return pxCurrentTCB;
}

/* This proof assumes that prvTCPPrepareSend and prvTCPReturnPacket are correct.
 * These functions are proved to be correct separately. */

BaseType_t publicTCPHandleState( FreeRTOS_Socket_t * pxSocket,
                                 NetworkBufferDescriptor_t ** ppxNetworkBuffer );

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

/* lTCPAddRxdata is proven separately. */
int32_t lTCPAddRxdata( FreeRTOS_Socket_t * pxSocket,
                       size_t uxOffset,
                       const uint8_t * pcData,
                       uint32_t ulByteCount )
{
    return nondet_int32();
}

/* prvSendData is proven separately. */
BaseType_t prvSendData( FreeRTOS_Socket_t * pxSocket,
                        NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                        uint32_t ulReceiveLength,
                        BaseType_t xByteCount )
{
    __CPROVER_assert( pxSocket != NULL, "pxSocket cannot be NULL" );
    __CPROVER_assert( *ppxNetworkBuffer != NULL, "*ppxNetworkBuffer cannot be NULL" );

    return nondet_BaseType();
}

/* prvTCPPrepareSend is proven separately. */
int32_t prvTCPPrepareSend( FreeRTOS_Socket_t * pxSocket,
                           NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                           UBaseType_t uxOptionsLength )
{
    __CPROVER_assert( pxSocket != NULL, "pxSocket cannot be NULL" );
    __CPROVER_assert( *ppxNetworkBuffer != NULL, "*ppxNetworkBuffer cannot be NULL" );

    return nondet_int32();
}

/* Mock all window APIs */
int32_t lTCPWindowRxCheck( TCPWindow_t * pxWindow,
                           uint32_t ulSequenceNumber,
                           uint32_t ulLength,
                           uint32_t ulSpace,
                           uint32_t * pulSkipCount )
{
    __CPROVER_assert( pxWindow != NULL, "pxWindow cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pxWindow, sizeof( TCPWindow_t ) ), "pxWindow must be readable" );
    *pulSkipCount = nondet_uint32();

    return nondet_int32();
}

uint32_t ulTCPWindowTxAck( TCPWindow_t * pxWindow,
                           uint32_t ulSequenceNumber )
{
    __CPROVER_assert( pxWindow != NULL, "pxWindow cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pxWindow, sizeof( TCPWindow_t ) ), "pxWindow must be readable" );

    return nondet_uint32();
}

void vTCPWindowInit( TCPWindow_t * pxWindow,
                     uint32_t ulAckNumber,
                     uint32_t ulSequenceNumber,
                     uint32_t ulMSS )
{
    __CPROVER_assert( pxWindow != NULL, "pxWindow cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pxWindow, sizeof( TCPWindow_t ) ), "pxWindow must be readable" );
}

BaseType_t xTCPWindowRxEmpty( const TCPWindow_t * pxWindow )
{
    __CPROVER_assert( pxWindow != NULL, "pxWindow cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pxWindow, sizeof( TCPWindow_t ) ), "pxWindow must be readable" );

    return nondet_BaseType();
}

BaseType_t xTCPWindowTxDone( const TCPWindow_t * pxWindow )
{
    __CPROVER_assert( pxWindow != NULL, "pxWindow cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pxWindow, sizeof( TCPWindow_t ) ), "pxWindow must be readable" );

    return nondet_BaseType();
}

/* Mock all stream buffer APIs */
size_t uxStreamBufferGet( StreamBuffer_t * const pxBuffer,
                          size_t uxOffset,
                          uint8_t * const pucData,
                          size_t uxMaxCount,
                          BaseType_t xPeek )
{
    __CPROVER_assert( pxBuffer != NULL, "pxBuffer cannot be NULL" );

    return nondet_sizet();
}

size_t uxStreamBufferGetSpace( const StreamBuffer_t * const pxBuffer )
{
    __CPROVER_assert( pxBuffer != NULL, "pxBuffer cannot be NULL" );

    return nondet_sizet();
}

/* Mock all transmission APIs. */
UBaseType_t prvSetOptions( FreeRTOS_Socket_t * pxSocket,
                           const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    __CPROVER_assert( pxSocket != NULL, "pxSocket cannot be NULL" );
    __CPROVER_assert( pxNetworkBuffer != NULL, "pxNetworkBuffer cannot be NULL" );

    return nondet_ubasetype();
}

UBaseType_t prvSetSynAckOptions( FreeRTOS_Socket_t * pxSocket,
                                 TCPHeader_t * pxTCPHeader )
{
    __CPROVER_assert( pxSocket != NULL, "pxSocket cannot be NULL" );
    __CPROVER_assert( pxTCPHeader != NULL, "pxTCPHeader cannot be NULL" );

    return nondet_ubasetype();
}

void prvTCPAddTxData( FreeRTOS_Socket_t * pxSocket )
{
    __CPROVER_assert( pxSocket != NULL, "pxSocket cannot be NULL" );
}

BaseType_t prvTCPSendReset( NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "pxNetworkBuffer cannot be NULL" );

    return nondet_BaseType();
}

const char * FreeRTOS_inet_ntop( BaseType_t xAddressFamily,
                                 const void * pvSource,
                                 char * pcDestination,
                                 socklen_t uxSize )
{
    __CPROVER_assert( __CPROVER_r_ok( pcDestination, uxSize ), "input buffer must be available" );

    __CPROVER_assert( ( xAddressFamily == FREERTOS_AF_INET6 && __CPROVER_r_ok( pvSource, 16 ) ) ||
                      ( xAddressFamily == FREERTOS_AF_INET && __CPROVER_r_ok( pvSource, 4 ) ),
                      "input address must be available" );
}

void harness()
{
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();

    __CPROVER_assume( pxSocket != NULL );

    /* ucOptionLength is the number of valid bytes in ulOptionsData[].
     * ulOptionsData[] is initialized as uint32_t ulOptionsData[ipSIZE_TCP_OPTIONS/sizeof(uint32_t)].
     * This assumption is required for a memcpy function that copies uxOptionsLength
     * data from pxTCPHeader->ucOptdata to pxTCPWindow->ulOptionsData.*/
    __CPROVER_assume( pxSocket->u.xTCP.xTCPWindow.ucOptionLength == sizeof( uint32_t ) * ipSIZE_TCP_OPTIONS / sizeof( uint32_t ) );
    /* uxRxWinSize is initialized as size_t. This assumption is required to terminate `while(uxWinSize > 0xfffful)` loop.*/
    __CPROVER_assume( pxSocket->u.xTCP.uxRxWinSize >= 0 && pxSocket->u.xTCP.uxRxWinSize <= sizeof( size_t ) );
    /* uxRxWinSize is initialized as uint16_t. This assumption is required to terminate `while(uxWinSize > 0xfffful)` loop.*/
    __CPROVER_assume( pxSocket->u.xTCP.usMSS == sizeof( uint16_t ) );
    /* ucPeerWinScaleFactor is limited in range [0,14]. */
    __CPROVER_assume( pxSocket->u.xTCP.ucPeerWinScaleFactor <= tcpTCP_OPT_WSOPT_MAXIMUM_VALUE );

    if( xIsCallingFromIPTask() == pdFALSE )
    {
        __CPROVER_assume( pxSocket->u.xTCP.bits.bPassQueued == pdFALSE_UNSIGNED );
        __CPROVER_assume( pxSocket->u.xTCP.bits.bPassAccept == pdFALSE_UNSIGNED );
    }

    NetworkBufferDescriptor_t * pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
    __CPROVER_assume( pxNetworkBuffer != NULL );

    FreeRTOS_Socket_t xSck;
    xSocketToListen = &xSck;

    /* Call to init the socket list. */
    vListInitialise( &xBoundTCPSocketsList );

    /* Allocates min. buffer size required for the proof */
    pxNetworkBuffer->pucEthernetBuffer = safeMalloc( sizeof( TCPPacket_t ) + uxIPHeaderSizeSocket( pxSocket ) );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );
    pxNetworkBuffer->xDataLength = sizeof( TCPPacket_t ) + uxIPHeaderSizeSocket( pxSocket );

    if( pxSocket->u.xTCP.bits.bReuseSocket == pdFALSE )
    {
        /* Make sure we have parent socket if reuse is set to FALSE to avoid assertion in vTCPStateChange(). */
        __CPROVER_assume( pxSocket->u.xTCP.pxPeerSocket != NULL );
    }

    publicTCPHandleState( pxSocket, &pxNetworkBuffer );
}
