/*
 * FreeRTOS+TCP
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
 * @brief Bind the socket to a port number.
 * @param[in] xSocket the socket that must be bound.
 * @param[in] usPort the port number to bind to.
 * @return The created socket - or NULL if the socket could not be created or could not be bound.
 */
    BaseType_t DNS_BindSocket( Socket_t xSocket,
                               uint16_t usPort )
    {
        struct freertos_sockaddr xAddress;
        BaseType_t xReturn;

        ( void ) memset( &( xAddress ), 0, sizeof( xAddress ) );
        xAddress.sin_family = FREERTOS_AF_INET;
        xAddress.sin_port = usPort;

        xReturn = FreeRTOS_bind( xSocket, &xAddress, ( socklen_t ) sizeof( xAddress ) );

        return xReturn;
    }

/**
 * @brief Create a socket and bind it to the standard DNS port number.
 *
 * @return The created socket - or NULL if the socket could not be created or could not be bound.
 */
    Socket_t DNS_CreateSocket( TickType_t uxReadTimeOut_ticks )
    {
        Socket_t xSocket;
        TickType_t uxWriteTimeOut_ticks = ipconfigDNS_SEND_BLOCK_TIME_TICKS;

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
            ( void ) FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &( uxReadTimeOut_ticks ), sizeof( TickType_t ) );
        }

        return xSocket;
    }

/**
 * @brief perform a DNS network request
 * @param xDNSSocket Created socket
 * @param pxAddress to store data of the sender (ip, port etc)
 * @param pxDNSBuf buffer to send
 * @return xReturn: true if the message could be sent
 *                  false otherwise
 *
 */
    BaseType_t DNS_SendRequest( Socket_t xDNSSocket,
                                const struct freertos_sockaddr * pxAddress,
                                const struct xDNSBuffer * pxDNSBuf )
    {
        BaseType_t xReturn = pdFALSE;
        BaseType_t xSent;

        iptraceSENDING_DNS_REQUEST();

        /* Send the DNS message. */
        xSent = FreeRTOS_sendto( xDNSSocket,
                                 pxDNSBuf->pucPayloadBuffer,
                                 pxDNSBuf->uxPayloadLength,
                                 FREERTOS_ZERO_COPY,
                                 pxAddress,
                                 ( socklen_t ) sizeof( *pxAddress ) );

        if( xSent == ( BaseType_t ) pxDNSBuf->uxPayloadLength )
        {
            xReturn = pdPASS;

            /* Logging for debugging only */
            if( pxAddress->sin_family == FREERTOS_AF_INET4 )
            {
                FreeRTOS_debug_printf( ( "DNS_debug SendRequest to server %xip\n", ( unsigned ) FreeRTOS_ntohl( pxAddress->sin_address.ulIP_IPv4 ) ) );
            }
            else if( pxAddress->sin_family == FREERTOS_AF_INET6 )
            {
                FreeRTOS_debug_printf( ( "DNS_debug SendRequest to server %pip\n", pxAddress->sin_address.xIP_IPv6.ucBytes ) );
            }
            else
            {
                FreeRTOS_debug_printf( ( "DNS_debug SendRequest to family %u\n", ( unsigned ) pxAddress->sin_family ) );
            }
        }
        else
        {
            /* The message was not sent so the stack will not be
             * releasing the zero copy - it must be released here. */
            xReturn = pdFAIL;
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Read from the socket.
 * @param[in] xDNSSocket: the socket that must be bound.
 * @param[out] pxAddress: place to store the "from address".
 * @param[out] pxReceiveBuffer: Place to store the received reply.
 * @param[in] pxTargetAddress: The IP-address of the DNS used when sending.
 * @return The result: number of bytes, zero, or negative when error.
 */
    BaseType_t DNS_ReadReply( Socket_t xDNSSocket,
                              struct freertos_sockaddr * pxAddress,
                              struct xDNSBuffer * pxReceiveBuffer,
                              const IPv46_Address_t * pxTargetAddress )
    {
        BaseType_t xReturn;
        uint32_t ulAddressLength = ( uint32_t ) sizeof( struct freertos_sockaddr );
        struct freertos_sockaddr xFromAddress;

        TickType_t xTimeoutTime = xIsCallingFromIPTask() ? 0u : pdMS_TO_TICKS( 500u );

        FreeRTOS_setsockopt( xDNSSocket, 0, FREERTOS_SO_RCVTIMEO, &( xTimeoutTime ), sizeof xTimeoutTime );

        /* Wait for the reply. */
        xReturn = FreeRTOS_recvfrom( xDNSSocket,
                                     &pxReceiveBuffer->pucPayloadBuffer,
                                     0,
                                     FREERTOS_ZERO_COPY,
                                     &xFromAddress,
                                     &ulAddressLength );

        if( xReturn <= 0 )
        {
            /* 'pdFREERTOS_ERRNO_EWOULDBLOCK' is returned in case of a timeout. */
            FreeRTOS_printf( ( "DNS_ReadReply returns %d\n", ( int ) xReturn ) );
        }
        else
        {
            /* Accept the reply by default. When ipconfigDNS_CHECK_REPLY_SOURCE_IP
             * is enabled, the source-IP validation below may reject it. */
            BaseType_t xMatch = pdTRUE;

            #if ( ipconfigDNS_CHECK_REPLY_SOURCE_IP == 1 )
            {
                uint8_t sin_family = ( pxTargetAddress->xIs_IPv6 == pdTRUE ) ? FREERTOS_AF_INET6 : FREERTOS_AF_INET4;

                /* A reply of the wrong address family cannot have come from the
                 * queried server. */
                xMatch = pdFALSE;

                if( xFromAddress.sin_family == sin_family )
                {
                    size_t uxLen = ( pxTargetAddress->xIs_IPv6 == pdTRUE ) ? ipSIZE_OF_IPv6_ADDRESS : ipSIZE_OF_IPv4_ADDRESS;

                    /* Accept the reply only if it came from the server that was queried. */
                    xMatch = ( memcmp( pxTargetAddress->xIPAddress.xIP_IPv6.ucBytes, xFromAddress.sin_address.xIP_IPv6.ucBytes, uxLen ) == 0 ) ? pdTRUE : pdFALSE;

                    if( xMatch == pdFALSE )
                    {
                        /* The source IP did not match the queried server. Also accept the
                         * reply if the query was sent to the mDNS multicast address, since
                         * mDNS responses arrive from individual responders rather than the
                         * multicast address itself. */
                        if( pxTargetAddress->xIs_IPv6 == pdTRUE )
                        {
                            xMatch = ( memcmp( ipMDNS_IP_ADDR_IPv6.ucBytes, pxTargetAddress->xIPAddress.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) == 0 ) ? pdTRUE : pdFALSE;
                        }
                        else
                        {
                            xMatch = ( pxTargetAddress->xIPAddress.ulIP_IPv4 == ipMDNS_IP_ADDRESS ) ? pdTRUE : pdFALSE;
                        }
                    }
                }

                if( pxTargetAddress->xIs_IPv6 == pdTRUE )
                {
                    FreeRTOS_debug_printf( ( "DNS_debug Expected answer from %pip match %d\n", pxTargetAddress->xIPAddress.xIP_IPv6.ucBytes, ( int ) xMatch ) );
                }
                else
                {
                    FreeRTOS_debug_printf( ( "DNS_debug Expected answer from %xip match %d\n", ( unsigned ) FreeRTOS_ntohl( pxTargetAddress->xIPAddress.ulIP_IPv4 ), ( int ) xMatch ) );
                }

                if( xFromAddress.sin_family == FREERTOS_AF_INET4 )
                {
                    FreeRTOS_debug_printf( ( "DNS_debug ReadReply from server %xip\n", ( unsigned ) FreeRTOS_ntohl( xFromAddress.sin_address.ulIP_IPv4 ) ) );
                }
                else if( xFromAddress.sin_family == FREERTOS_AF_INET6 )
                {
                    FreeRTOS_debug_printf( ( "DNS_debug ReadReply from server %pip\n", xFromAddress.sin_address.xIP_IPv6.ucBytes ) );
                }
                else
                {
                    FreeRTOS_debug_printf( ( "DNS_debug ReadReply from family %u\n", ( unsigned ) xFromAddress.sin_family ) );
                }
            }
            #else /* if ( ipconfigDNS_CHECK_REPLY_SOURCE_IP == 1 ) */
            {
                /* Source-IP validation is opt-in; preserve legacy behaviour of
                 * accepting the reply regardless of its source address. */
                ( void ) pxTargetAddress;
            }
            #endif /* ipconfigDNS_CHECK_REPLY_SOURCE_IP */

            if( xMatch == pdFALSE )
            {
                FreeRTOS_debug_printf( ( "DNS_ReadReply: Source mismatch, discarding packet.\n" ) );

                /* Return an error so the caller knows this packet is invalid */
                xReturn = -pdFREERTOS_ERRNO_EINVAL;
            }
        }

        if( xReturn > 0 )
        {
            memcpy( pxAddress, &xFromAddress, sizeof *pxAddress );
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief perform a DNS network close
 * @param xDNSSocket the DNS socket to close
 */
    void DNS_CloseSocket( Socket_t xDNSSocket )
    {
        ( void ) FreeRTOS_closesocket( xDNSSocket );
    }
#endif /* if ( ipconfigUSE_DNS != 0 ) */
/*-----------------------------------------------------------*/
