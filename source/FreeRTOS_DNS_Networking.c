/*
 * FreeRTOS+TCP V2.3.4
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
 * https://github.com/FreeRTOS
 * https://www.FreeRTOS.org
 */

/**
 * @file FreeRTOS_DNS_Networking.c
 * @brief Implements the Domain Name System Networking
 *        for the FreeRTOS+TCP network stack.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

#include "FreeRTOS_DNS_Networking.h"

#if ( ipconfigUSE_DNS != 0 )

/**
 * @brief Bind the socket to a port number.
 * @param[in] xSocket: the socket that must be bound.
 * @param[in] usPort: the port number to bind to.
 * @return The created socket - or NULL if the socket could not be created or could not be bound.
 */
    BaseType_t DNS_BindSocket( Socket_t xSocket,
                               uint16_t usPort )
    {
        struct freertos_sockaddr xAddress;
        BaseType_t xReturn;

        /* Auto bind the port. */
        ( void ) memset( &( xAddress ), 0, sizeof( xAddress ) );
        xAddress.sin_family = FREERTOS_AF_INET;
        xAddress.sin_port = usPort;

        xReturn = FreeRTOS_bind( xSocket, &xAddress, sizeof( xAddress ) );

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Create a socket and bind it to the standard DNS port number.
 * @return The created socket - or NULL.
 */
    Socket_t DNS_CreateSocket( TickType_t uxReadTimeOut_ticks )
    {
        Socket_t xSocket;
        TickType_t uxWriteTimeOut_ticks = ipconfigDNS_SEND_BLOCK_TIME_TICKS;
        TickType_t uxReadTicks = uxReadTimeOut_ticks;

        if( uxReadTicks < 50U )
        {
            uxReadTicks = 50U;
        }

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
            /* Ideally we should check for the return value. But since we are passing
             * correct parameters, and xSocket is != NULL, the return value is
             * going to be '0' i.e. success. Thus, return value is discarded */
            ( void ) FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, &( uxWriteTimeOut_ticks ), sizeof( TickType_t ) );
            ( void ) FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &( uxReadTicks ), sizeof( TickType_t ) );
        }

        return xSocket;
    }
/*-----------------------------------------------------------*/

/**
 * @brief perform a DNS network request
 * @param xDNSSocket socket
 * @param xAddress address structure
 * @param pucBuffer buffer to send
 * @param uxBufferLength buffer length
 * @return xReturn: true if the message could be sent
 *                  false otherwise
 *
 */
    uint32_t DNS_SendRequest( Socket_t xDNSSocket,
                              struct freertos_sockaddr * xAddress,
                              uint8_t * pucBuffer,
                              size_t uxBufferLength )
    {
        BaseType_t xReturn = pdFALSE;

        iptraceSENDING_DNS_REQUEST();

        /* Send the DNS message. */
        if( FreeRTOS_sendto( xDNSSocket,
                             pucBuffer,
                             uxBufferLength,
                             FREERTOS_ZERO_COPY,
                             xAddress,
                             sizeof( *xAddress ) ) != 0 )
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
/*-----------------------------------------------------------*/

/**
 * @brief perform a DNS network read
 * @param xDNSSocket socket
 * @param xAddress address to read from
 * @param ppucReceiveBuffer buffer to fill with received data
 */
    int32_t DNS_ReadReply( Socket_t xDNSSocket,
                           struct freertos_sockaddr * xAddress,
                           uint8_t ** ppucReceiveBuffer )
    {
        socklen_t uxAddressLength = sizeof( struct freertos_sockaddr );

        /* Wait for the reply. */
        /* FREERTOS_ZERO_COPY: passing the address of a character pointer to avoid a copy. */
        return FreeRTOS_recvfrom( xDNSSocket,
                                  ppucReceiveBuffer,
                                  0,
                                  FREERTOS_ZERO_COPY,
                                  xAddress,
                                  ( uint32_t * ) &uxAddressLength );
    }
/*-----------------------------------------------------------*/

/**
 * @brief perform a DNS network close
 * @param xDNSSocket
 */
    void DNS_CloseSocket( Socket_t xDNSSocket )
    {
        ( void ) FreeRTOS_closesocket( xDNSSocket );
    }
#endif /* if ( ipconfigUSE_DNS != 0 ) */
/*-----------------------------------------------------------*/
