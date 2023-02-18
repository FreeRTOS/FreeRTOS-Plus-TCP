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

#ifndef FREERTOS_TCP_SOCKETS_H
#define FREERTOS_TCP_SOCKETS_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* Structure to pass for the 'FREERTOS_SO_SET_LOW_HIGH_WATER' option. */
typedef struct xLOW_HIGH_WATER
{
    size_t uxLittleSpace;     /**< Send a STOP when buffer space drops below X bytes */
    size_t uxEnoughSpace;     /**< Send a GO when buffer space grows above X bytes */
} LowHighWater_t;

/* Structure to hold the properties of Tx/Rx buffers and windows. */
typedef struct xWIN_PROPS
{
    /* Properties of the Tx buffer and Tx window. */
    int32_t lTxBufSize;     /**< Unit: bytes. */
    int32_t lTxWinSize;     /**< Unit: MSS. */

    /* Properties of the Rx buffer and Rx window. */
    int32_t lRxBufSize;     /**< Unit: bytes. */
    int32_t lRxWinSize;     /**< Unit: MSS. */
} WinProperties_t;

/* Release a TCP payload buffer that was obtained by
 * calling FreeRTOS_recv() with the FREERTOS_ZERO_COPY flag,
 * and a pointer to a void pointer. */
BaseType_t FreeRTOS_ReleaseTCPPayloadBuffer( Socket_t xSocket,
                                             void const * pvBuffer,
                                             BaseType_t xByteCount );

/* Connect a TCP socket to a remote socket. */
BaseType_t FreeRTOS_connect( Socket_t xClientSocket,
                             const struct freertos_sockaddr * pxAddress,
                             socklen_t xAddressLength );

/* Places a TCP socket into a state where it is listening for and can accept
 * incoming connection requests from remote sockets. */
BaseType_t FreeRTOS_listen( Socket_t xSocket,
                            BaseType_t xBacklog );

/* Accept a connection on a TCP socket. */
Socket_t FreeRTOS_accept( Socket_t xServerSocket,
                          struct freertos_sockaddr * pxAddress,
                          socklen_t * pxAddressLength );

/* Send data to a TCP socket. */
BaseType_t FreeRTOS_send( Socket_t xSocket,
                          const void * pvBuffer,
                          size_t uxDataLength,
                          BaseType_t xFlags );

/* Receive data from a TCP socket */
BaseType_t FreeRTOS_recv( Socket_t xSocket,
                          void * pvBuffer,
                          size_t uxBufferLength,
                          BaseType_t xFlags );

/* Disable reads and writes on a connected TCP socket. */
BaseType_t FreeRTOS_shutdown( Socket_t xSocket,
                              BaseType_t xHow );

/* Returns the number of bytes available in the Rx buffer. */
BaseType_t FreeRTOS_rx_size( ConstSocket_t xSocket );

#define FreeRTOS_recvcount( xSocket )    FreeRTOS_rx_size( xSocket )

/* Returns the free space in the Tx buffer. */
BaseType_t FreeRTOS_tx_space( ConstSocket_t xSocket );

#define FreeRTOS_outstanding( xSocket )    FreeRTOS_tx_size( xSocket )

/* Returns the number of bytes stored in the Tx buffer. */
BaseType_t FreeRTOS_tx_size( ConstSocket_t xSocket );

/* Returns pdTRUE if TCP socket is connected. */
BaseType_t FreeRTOS_issocketconnected( ConstSocket_t xSocket );

/* Return the remote address and IP port of a connected TCP Socket. */
BaseType_t FreeRTOS_GetRemoteAddress( ConstSocket_t xSocket,
                                      struct freertos_sockaddr * pxAddress );

/* Get the type of IP: either 'ipTYPE_IPv4' or 'ipTYPE_IPv6'. */
BaseType_t FreeRTOS_GetIPType( ConstSocket_t xSocket );

/* Returns the number of bytes that may be added to txStream. */
BaseType_t FreeRTOS_maywrite( ConstSocket_t xSocket );

/* Returns the actual size of MSS being used. */
BaseType_t FreeRTOS_mss( ConstSocket_t xSocket );

/* For internal use only: return the connection status. */
BaseType_t FreeRTOS_connstatus( ConstSocket_t xSocket );

/* For advanced applications only:
 * Get a direct pointer to the circular transmit buffer.
 * '*pxLength' will contain the number of bytes that may be written. */
uint8_t * FreeRTOS_get_tx_head( ConstSocket_t xSocket,
                                BaseType_t * pxLength );

/* For the web server: borrow the circular Rx buffer for inspection
 * HTML driver wants to see if a sequence of 13/10/13/10 is available. */
const struct xSTREAM_BUFFER * FreeRTOS_get_rx_buf( ConstSocket_t xSocket );

void FreeRTOS_netstat( void );

/* *INDENT-OFF* */
#ifdef __cplusplus
    } /* extern "C" */
#endif
/* *INDENT-ON* */

#endif /* FREERTOS_TCP_SOCKETS_H */
