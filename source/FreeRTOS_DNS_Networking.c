/*
 * FreeRTOS+TCP V3.1.0
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

/**
 * @file FreeRTOS_DNS_Networking.c
 * @brief Implements the Domain Name System Networking
 *        for the FreeRTOS+TCP network stack.
 */

#include "FreeRTOS.h"

#include "FreeRTOS_DNS_Networking.h"

#if ( ipconfigUSE_DNS != 0 )

/**
 * @brief Create a socket and bind it to the standard DNS port number.
 *
 * @return The created socket - or NULL if the socket could not be created or could not be bound.
 */
    Socket_t DNS_CreateSocket( TickType_t uxReadTimeOut_ticks )
    {
        Socket_t xSocket;
        struct freertos_sockaddr xAddress;
        TickType_t uxWriteTimeOut_ticks = ipconfigDNS_SEND_BLOCK_TIME_TICKS;
        BaseType_t xReturn;

        /* This must be the first time this function has been called.  Create
         * the socket. */
        xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

        if( xSocketValid( xSocket ) == pdFALSE )
        {
            /* There was an error, return NULL. */
            xSocket = NULL;
        }
        else
        {
            /* Auto bind the port. */
            xAddress.sin_port = 0U;
            xReturn = FreeRTOS_bind( xSocket, &xAddress, ( socklen_t ) sizeof( xAddress ) );

            /* Check the bind was successful, and clean up if not. */
            if( xReturn != 0 )
            {
                ( void ) FreeRTOS_closesocket( xSocket );
                xSocket = NULL;
            }
            else
            {
                /* Ideally we should check for the return value. But since we are passing
                 * correct parameters, and xSocket is != NULL, the return value is
                 * going to be '0' i.e. success. Thus, return value is discarded */
                ( void ) FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, &( uxWriteTimeOut_ticks ), sizeof( TickType_t ) );
                ( void ) FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &( uxReadTimeOut_ticks ), sizeof( TickType_t ) );
            }
        }

        return xSocket;
    }

/**
 * @brief perform a DNS network request
 * @param xDNSSocket Created socket
 * @param xAddress address structure (ip, port etc)
 * @param pxDNSBuf buffer to send
 * @return xReturn: true if the message could be sent
 *                  false otherwise
 *
 */
    BaseType_t DNS_SendRequest( Socket_t xDNSSocket,
                                const struct freertos_sockaddr * xAddress,
                                const struct xDNSBuffer * pxDNSBuf )
    {
        BaseType_t xReturn = pdFALSE;

        iptraceSENDING_DNS_REQUEST();

        /* Send the DNS message. */
        if( FreeRTOS_sendto( xDNSSocket,
                             pxDNSBuf->pucPayloadBuffer,
                             pxDNSBuf->uxPayloadLength,
                             FREERTOS_ZERO_COPY,
                             xAddress,
                             ( socklen_t ) sizeof( *xAddress ) ) != 0 )
        {
            xReturn = pdTRUE;
        }
        else
        {
            /* The message was not sent so the stack will not be
             * releasing the zero copy - it must be released here. */
            xReturn = pdFALSE;
        }

        return xReturn;
    }

/**
 * @brief perform a DNS network read
 * @param xDNSSocket socket
 * @param xAddress address to read from
 * @param pxReceiveBuffer buffer to fill with received data
 */
    void DNS_ReadReply( const ConstSocket_t xDNSSocket,
                        struct freertos_sockaddr * xAddress,
                        struct xDNSBuffer * pxReceiveBuffer )
    {
        uint32_t ulAddressLength = ( uint32_t ) sizeof( struct freertos_sockaddr );

        /* Wait for the reply. */
        pxReceiveBuffer->uxPayloadLength = ( size_t ) FreeRTOS_recvfrom( xDNSSocket,
                                                                         &pxReceiveBuffer->pucPayloadBuffer,
                                                                         0,
                                                                         FREERTOS_ZERO_COPY,
                                                                         xAddress,
                                                                         &ulAddressLength );
        pxReceiveBuffer->uxPayloadSize = pxReceiveBuffer->uxPayloadLength;
    }

/**
 * @brief perform a DNS network close
 * @param xDNSSocket
 */
    void DNS_CloseSocket( Socket_t xDNSSocket )
    {
        ( void ) FreeRTOS_closesocket( xDNSSocket );
    }
#endif /* if ( ipconfigUSE_DNS != 0 ) */
