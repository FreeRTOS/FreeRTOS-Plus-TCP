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

/**
 * @file FreeRTOS_Sockets.c
 * @brief Implements the Sockets API based on Berkeley sockets for the FreeRTOS+TCP network stack.
 *        Sockets are used by the application processes to interact with the IP-task which in turn
 *        interacts with the hardware.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_Sockets_Private.h"
#if ( ipconfigUSE_IPv4 != 0 )
    #include "FreeRTOS_IPv4_Sockets.h"
#endif
#if ( ipconfigUSE_IPv6 != 0 )
    #include "FreeRTOS_IPv6_Sockets.h"
#endif
#include "NetworkBufferManagement.h"

/*-----------------------------------------------------------*/

/**
 * @brief Check whether a given socket is valid or not. Validity is defined
 *        as the socket not being NULL and not being Invalid.
 * @param[in] xSocket: The socket to be checked.
 * @return pdTRUE if the socket is valid, else pdFALSE.
 *
 */
BaseType_t xSocketValid( const ConstSocket_t xSocket )
{
    BaseType_t xReturnValue = pdFALSE;

    /*
     * There are two values which can indicate an invalid socket:
     * FREERTOS_INVALID_SOCKET and NULL.  In order to compare against
     * both values, the code cannot be compliant with rule 11.4,
     * hence the Coverity suppression statement below.
     */

    /* MISRA Ref 11.4.1 [Socket error and integer to pointer conversion] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
    /* coverity[misra_c_2012_rule_11_4_violation] */
    if( ( xSocket != FREERTOS_INVALID_SOCKET ) && ( xSocket != NULL ) )
    {
        xReturnValue = pdTRUE;
    }

    return xReturnValue;
}
/*-----------------------------------------------------------*/

/**
 * @brief binds a socket to a local port number. If port 0 is provided,
 *        a system provided port number will be assigned. This function
 *        can be used for both UDP and TCP sockets. The actual binding
 *        will be performed by the IP-task to avoid mutual access to the
 *        bound-socket-lists (xBoundUDPSocketsList or xBoundTCPSocketsList).
 *
 * @param[in] xSocket: The socket being bound.
 * @param[in] pxAddress: The address struct carrying the port number to which
 *                       this socket is to be bound.
 * @param[in] xAddressLength: This parameter is not used internally. The
 *                       function signature is used to adhere to standard
 *                       Berkeley sockets API.
 *
 * @return The return value is 0 if the bind is successful.
 *         If some error occurred, then a negative value is returned.
 */
BaseType_t FreeRTOS_bind( Socket_t xSocket,
                          struct freertos_sockaddr const * pxAddress,
                          socklen_t xAddressLength )
{
    IPStackEvent_t xBindEvent;
    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
    BaseType_t xReturn = 0;

    ( void ) xAddressLength;

    configASSERT( xIsCallingFromIPTask() == pdFALSE );

    if( xSocketValid( pxSocket ) == pdFALSE )
    {
        xReturn = -pdFREERTOS_ERRNO_EINVAL;
    }

    /* Once a socket is bound to a port, it can not be bound to a different
     * port number */
    else if( socketSOCKET_IS_BOUND( pxSocket ) )
    {
        /* The socket is already bound. */
        FreeRTOS_debug_printf( ( "vSocketBind: Socket already bound to %d\n", pxSocket->usLocalPort ) );
        xReturn = -pdFREERTOS_ERRNO_EINVAL;
    }
    else
    {
        /* Prepare a messages to the IP-task in order to perform the binding.
         * The desired port number will be passed in usLocalPort. */
        xBindEvent.eEventType = eSocketBindEvent;
        xBindEvent.pvData = xSocket;

        if( pxAddress != NULL )
        {
            if( pxAddress->sin_family == ( uint8_t ) FREERTOS_AF_INET6 )
            {
                ( void ) memcpy( pxSocket->xLocalAddress.xIP_IPv6.ucBytes, pxAddress->sin_addr6.ucBytes, sizeof( pxSocket->xLocalAddress.xIP_IPv6.ucBytes ) );
                pxSocket->bits.bIsIPv6 = pdTRUE_UNSIGNED;
            }
            else
            {
                pxSocket->xLocalAddress.ulIP_IPv4 = FreeRTOS_ntohl( pxAddress->sin_addr );
                pxSocket->bits.bIsIPv6 = pdFALSE_UNSIGNED;
            }

            pxSocket->usLocalPort = FreeRTOS_ntohs( pxAddress->sin_port );
        }
        else
        {
            /* Caller wants to bind to a random port number. */
            pxSocket->usLocalPort = 0U;
            pxSocket->xLocalAddress.ulIP_IPv4 = 0U;
            ( void ) memset( pxSocket->xLocalAddress.xIP_IPv6.ucBytes, 0, sizeof( pxSocket->xLocalAddress.xIP_IPv6.ucBytes ) );
        }

        /* portMAX_DELAY is used as a the time-out parameter, as binding *must*
         * succeed before the socket can be used.  _RB_ The use of an infinite
         * block time needs be changed as it could result in the task hanging. */
        if( xSendEventStructToIPTask( &xBindEvent, ( TickType_t ) portMAX_DELAY ) == pdFAIL )
        {
            /* Failed to wake-up the IP-task, no use to wait for it */
            FreeRTOS_debug_printf( ( "FreeRTOS_bind: send event failed\n" ) );
            xReturn = -pdFREERTOS_ERRNO_ECANCELED;
        }
        else
        {
            /* The IP-task will set the 'eSOCKET_BOUND' bit when it has done its
             * job. */
            ( void ) xEventGroupWaitBits( pxSocket->xEventGroup, ( EventBits_t ) eSOCKET_BOUND, pdTRUE /*xClearOnExit*/, pdFALSE /*xWaitAllBits*/, portMAX_DELAY );

            if( !socketSOCKET_IS_BOUND( pxSocket ) )
            {
                xReturn = -pdFREERTOS_ERRNO_EINVAL;
            }
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Close a socket and free the allocated space. In case of a TCP socket:
 *        the connection will not be closed automatically. Subsequent messages
 *        for the closed socket will be responded to with a RST. The IP-task
 *        will actually close the socket, after receiving a 'eSocketCloseEvent'
 *        message.
 *
 * @param[in] xSocket: the socket being closed.
 *
 * @return There are three distinct values which can be returned:
 *         0: If the xSocket is NULL/invalid.
 *         1: If the socket was successfully closed (read the brief above).
 *        -1: If the socket was valid but could not be closed because the message
 *            could not be delivered to the IP-task. Try again later.
 */
BaseType_t FreeRTOS_closesocket( Socket_t xSocket )
{
    BaseType_t xResult;

    #if ( ipconfigUSE_CALLBACKS == 1 )
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
    #endif /* ipconfigUSE_CALLBACKS == 1 */
    IPStackEvent_t xCloseEvent;
    xCloseEvent.eEventType = eSocketCloseEvent;
    xCloseEvent.pvData = xSocket;

    if( xSocketValid( xSocket ) == pdFALSE )
    {
        xResult = 0;
    }
    else
    {
        #if ( ipconfigUSE_CALLBACKS == 1 )
            {
                #if ( ipconfigUSE_TCP == 1 )
                    if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP )
                    {
                        /* Make sure that IP-task won't call the user callback's anymore */
                        pxSocket->u.xTCP.pxHandleConnected = NULL;
                        pxSocket->u.xTCP.pxHandleReceive = NULL;
                        pxSocket->u.xTCP.pxHandleSent = NULL;
                    }
                    else
                #endif /* ipconfigUSE_TCP == 1 */

                if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_UDP )
                {
                    /* Clear the two UDP handlers. */
                    pxSocket->u.xUDP.pxHandleReceive = NULL;
                    pxSocket->u.xUDP.pxHandleSent = NULL;
                }
            }
        #endif /* ipconfigUSE_CALLBACKS == 1 */

        /* Let the IP task close the socket to keep it synchronised with the
         * packet handling. */

        /* The timeout value below is only used if this function is called from
         * a user task. If this function is called by the IP-task, it may fail
         * to close the socket when the event queue is full.
         * This should only happen in case of a user call-back. */
        if( xSendEventStructToIPTask( &xCloseEvent, ( TickType_t ) portMAX_DELAY ) == pdFAIL )
        {
            FreeRTOS_debug_printf( ( "FreeRTOS_closesocket: failed\n" ) );
            xResult = -1;
        }
        else
        {
            xResult = 1;
        }
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Convert the dotted decimal format of the IP-address to the 32-bit representation.
 *
 * @param[in] xAddressFamily: The Address family to which the IP-address belongs to. Only
 *                            FREERTOS_AF_INET (IPv4) is supported.
 * @param[in] pcSource: Pointer to the string holding the dotted decimal representation of
 *                      the IP-address.
 * @param[out] pvDestination: The pointer to the address struct/variable where the converted
 *                            IP-address will be stored. The buffer must be 4 bytes long
 *                            in case of a IPv4 address.
 *
 * @return If all checks pass, then pdPASS is returned or else pdFAIL is returned.
 */
BaseType_t FreeRTOS_inet_pton( BaseType_t xAddressFamily,
                               const char * pcSource,
                               void * pvDestination )
{
    BaseType_t xResult;

    /* Printable string to struct sockaddr. */
    switch( xAddressFamily )
    {
        case FREERTOS_AF_INET:
            xResult = FreeRTOS_inet_pton4( pcSource, pvDestination );
            break;

        case FREERTOS_AF_INET6:
            xResult = FreeRTOS_inet_pton6( pcSource, pvDestination );
            break;

        default:
            xResult = -pdFREERTOS_ERRNO_EAFNOSUPPORT;
            break;
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Convert the 32-bit representation of the IP-address to the dotted
 *        decimal format based on the Address Family. (Only FREERTOS_AF_INET
 *        is allowed).
 *
 * @param[in] xAddressFamily: The address family of the IP-address.
 * @param[in] pvSource: Pointer to the 32-bit representation of IP-address.
 * @param[out] pcDestination: The pointer to the character array where the dotted
 *                            decimal address will be stored if every check does pass.
 * @param[in] uxSize: Size of the character array. This value makes sure that the code
 *                    doesn't write beyond it's bounds.
 *
 * @return If every check does pass, then the pointer to the pcDestination is returned
 *         holding the dotted decimal format of IP-address. Else, a NULL is returned.
 */
const char * FreeRTOS_inet_ntop( BaseType_t xAddressFamily,
                                 const void * pvSource,
                                 char * pcDestination,
                                 socklen_t uxSize )
{
    const char * pcResult;

    /* Printable struct sockaddr to string. */
    switch( xAddressFamily )
    {
        case FREERTOS_AF_INET4:
            pcResult = FreeRTOS_inet_ntop4( pvSource, pcDestination, uxSize );
            break;

        case FREERTOS_AF_INET6:
            pcResult = FreeRTOS_inet_ntop6( pvSource, pcDestination, uxSize );
            break;

        default:
            /* errno should be set to pdFREERTOS_ERRNO_EAFNOSUPPORT. */
            pcResult = NULL;
            break;
    }

    return pcResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief This function converts a 48-bit MAC address to a human readable string.
 *
 * @param[in] pucSource: A pointer to an array of 6 bytes.
 * @param[out] pcTarget: A buffer that is 18 bytes long, it will contain the resulting string.
 * @param[in] cTen: Either an 'A' or an 'a'. It determines whether the hex numbers will use
 *                  capital or small letters.
 * @param[in] cSeparator: The separator that should appear between the bytes, either ':' or '-'.
 */
void FreeRTOS_EUI48_ntop( const uint8_t * pucSource,
                          char * pcTarget,
                          char cTen,
                          char cSeparator )
{
    size_t uxIndex;
    size_t uxNibble;
    size_t uxTarget = 0U;

    for( uxIndex = 0U; uxIndex < ipMAC_ADDRESS_LENGTH_BYTES; uxIndex++ )
    {
        uint8_t ucByte = pucSource[ uxIndex ];

        for( uxNibble = 0; uxNibble < 2U; uxNibble++ )
        {
            uint8_t ucNibble;
            char cResult;

            if( uxNibble == 0U )
            {
                ucNibble = ucByte >> 4;
            }
            else
            {
                ucNibble = ucByte & 0x0FU;
            }

            if( ucNibble <= 0x09U )
            {
                cResult = '0';
                cResult = cResult + ucNibble;
            }
            else
            {
                cResult = cTen; /* Either 'a' or 'A' */
                cResult = cResult + ( ucNibble - 10U );
            }

            pcTarget[ uxTarget ] = cResult;
            uxTarget++;
        }

        if( uxIndex == ( ipMAC_ADDRESS_LENGTH_BYTES - 1U ) )
        {
            pcTarget[ uxTarget ] = ( char ) 0;
            uxTarget++;
        }
        else
        {
            pcTarget[ uxTarget ] = cSeparator;
            uxTarget++;
        }
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief This function converts a human readable string, representing an 48-bit MAC address,
 *        into a 6-byte address. Valid inputs are e.g. "62:48:5:83:A0:b2" and "0-12-34-fe-dc-ba".
 *
 * @param[in] pcSource: The null terminated string to be parsed.
 * @param[out] pucTarget: A buffer that is 6 bytes long, it will contain the MAC address.
 *
 * @return pdTRUE in case the string got parsed correctly, otherwise pdFALSE.
 */
BaseType_t FreeRTOS_EUI48_pton( const char * pcSource,
                                uint8_t * pucTarget )
{
    BaseType_t xResult = pdFALSE;
    size_t uxByteNr = 0U;
    size_t uxSourceIndex;
    size_t uxNibbleCount = 0U;
    size_t uxLength = strlen( pcSource );
    uint32_t uxSum = 0U;
    uint8_t ucHex;
    char cChar;

    /* Ignore the following line from branch coverage since the exits from this loop are
     * covered by break statements. The loop is kept as is to future proof the code against
     * any changes. LCOV_EXCL_BR_START */
    for( uxSourceIndex = 0U; uxSourceIndex <= uxLength; uxSourceIndex++ )
    /* LCOV_EXCL_BR_STOP */
    {
        cChar = pcSource[ uxSourceIndex ];
        ucHex = ucASCIIToHex( cChar );

        if( ucHex != socketINVALID_HEX_CHAR )
        {
            /* A valid nibble was found. Shift it into the accumulator. */
            uxSum = uxSum << 4;

            if( uxSum > 0xffU )
            {
                /* A hex value was too big. */
                break;
            }

            uxSum |= ucHex;
            uxNibbleCount++;
        }
        else
        {
            if( uxNibbleCount != 2U )
            {
                /* Each number should have 2 nibbles. */
                break;
            }

            pucTarget[ uxByteNr ] = ( uint8_t ) uxSum;
            uxSum = 0U;
            uxNibbleCount = 0U;
            uxByteNr++;

            if( uxByteNr == ipMAC_ADDRESS_LENGTH_BYTES )
            {
                xResult = pdTRUE;
                break;
            }

            if( ( cChar != ':' ) && ( cChar != '-' ) )
            {
                /* Invalid character. */
                break;
            }
        }
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Function to get the local address and IP port of the given socket.
 *
 * @param[in] xSocket: Socket whose port is to be added to the pxAddress.
 * @param[out] pxAddress: Structure in which the IP address and the port number
 *                        is returned.
 *
 * @return Size of the freertos_sockaddr structure.
 */
size_t FreeRTOS_GetLocalAddress( ConstSocket_t xSocket,
                                 struct freertos_sockaddr * pxAddress )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;

    if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
    {
        pxAddress->sin_family = FREERTOS_AF_INET6;
        /* IP address of local machine. */
        ( void ) memcpy( pxAddress->sin_addr6.ucBytes, pxSocket->xLocalAddress.xIP_IPv6.ucBytes, sizeof( pxAddress->sin_addr6.ucBytes ) );
        /* Local port on this machine. */
        pxAddress->sin_port = FreeRTOS_htons( pxSocket->usLocalPort );
    }
    else
    {
        pxAddress->sin_family = FREERTOS_AF_INET;
        pxAddress->sin_len = ( uint8_t ) sizeof( *pxAddress );
        /* IP address of local machine. */
        pxAddress->sin_addr = FreeRTOS_htonl( pxSocket->xLocalAddress.ulIP_IPv4 );

        /* Local port on this machine. */
        pxAddress->sin_port = FreeRTOS_htons( pxSocket->usLocalPort );
    }

    return sizeof( *pxAddress );
}
/*-----------------------------------------------------------*/

/* FreeRTOS_setsockopt calls itself, but in a very limited way,
 * only when FREERTOS_SO_WIN_PROPERTIES is being set. */

/**
 * @brief Set the socket options for the given socket.
 *
 * @param[in] xSocket: The socket for which the options are to be set.
 * @param[in] lLevel: Not used. Parameter is used to maintain the Berkeley sockets
 *                    standard.
 * @param[in] lOptionName: The name of the option to be set.
 * @param[in] pvOptionValue: The value of the option to be set.
 * @param[in] uxOptionLength: Not used. Parameter is used to maintain the Berkeley
 *                            sockets standard.
 *
 * @return If the option can be set with the given value, then 0 is returned. Else,
 *         an error code is returned.
 */
BaseType_t FreeRTOS_setsockopt( Socket_t xSocket,
                                int32_t lLevel,
                                int32_t lOptionName,
                                const void * pvOptionValue,
                                size_t uxOptionLength )
{
/* The standard Berkeley function returns 0 for success. */
    BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;
    FreeRTOS_Socket_t * pxSocket;

    pxSocket = ( FreeRTOS_Socket_t * ) xSocket;

    /* The function prototype is designed to maintain the expected Berkeley
     * sockets standard, but this implementation does not use all the parameters. */
    ( void ) lLevel;
    ( void ) uxOptionLength;

    if( xSocketValid( pxSocket ) == pdTRUE )
    {
        switch( lOptionName )
        {
            case FREERTOS_SO_RCVTIMEO:
                /* Receive time out. */
                prvSetOptionTimeout( pxSocket, pvOptionValue, pdFALSE );
                xReturn = 0;
                break;

            case FREERTOS_SO_SNDTIMEO:
                prvSetOptionTimeout( pxSocket, pvOptionValue, pdTRUE );
                xReturn = 0;
                break;

                #if ( ipconfigUDP_MAX_RX_PACKETS > 0U )
                    case FREERTOS_SO_UDP_MAX_RX_PACKETS:

                        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_UDP )
                        {
                            break; /* will return -pdFREERTOS_ERRNO_EINVAL */
                        }

                        pxSocket->u.xUDP.uxMaxPackets = *( ( const UBaseType_t * ) pvOptionValue );
                        xReturn = 0;
                        break;
                #endif /* ipconfigUDP_MAX_RX_PACKETS */

            case FREERTOS_SO_UDPCKSUM_OUT:

                /* Turn calculating of the UDP checksum on/off for this socket. If pvOptionValue
                 * is anything else than NULL, the checksum generation will be turned on. */

                if( pvOptionValue == NULL )
                {
                    pxSocket->ucSocketOptions &= ~( ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT );
                }
                else
                {
                    pxSocket->ucSocketOptions |= ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT;
                }

                xReturn = 0;
                break;

                #if ( ipconfigUSE_CALLBACKS == 1 )
                    #if ( ipconfigUSE_TCP == 1 )
                        case FREERTOS_SO_TCP_CONN_HANDLER: /* Set a callback for (dis)connection events */
                        case FREERTOS_SO_TCP_RECV_HANDLER: /* Install a callback for receiving TCP data. Supply pointer to 'F_TCP_UDP_Handler_t' (see below) */
                        case FREERTOS_SO_TCP_SENT_HANDLER: /* Install a callback for sending TCP data. Supply pointer to 'F_TCP_UDP_Handler_t' (see below) */
                    #endif /* ipconfigUSE_TCP */
                    case FREERTOS_SO_UDP_RECV_HANDLER:     /* Install a callback for receiving UDP data. Supply pointer to 'F_TCP_UDP_Handler_t' (see below) */
                    case FREERTOS_SO_UDP_SENT_HANDLER:     /* Install a callback for sending UDP data. Supply pointer to 'F_TCP_UDP_Handler_t' (see below) */
                        xReturn = prvSetOptionCallback( pxSocket, lOptionName, pvOptionValue );
                        break;
                #endif /* ipconfigUSE_CALLBACKS */

                #if ( ipconfigSOCKET_HAS_USER_SEMAPHORE != 0 )
                    /* Each socket has a semaphore on which the using task normally
                     * sleeps. */
                    case FREERTOS_SO_SET_SEMAPHORE:
                        pxSocket->pxUserSemaphore = *( ( SemaphoreHandle_t * ) pvOptionValue );
                        xReturn = 0;
                        break;
                #endif /* ipconfigSOCKET_HAS_USER_SEMAPHORE */

                #if ( ipconfigSOCKET_HAS_USER_WAKE_CALLBACK != 0 )
                    case FREERTOS_SO_WAKEUP_CALLBACK:

                        /* Each socket can have a callback function that is executed
                         * when there is an event the socket's owner might want to
                         * process. */

                        /* The type cast of the pointer expression "A" to
                         * type "B" removes const qualifier from the pointed to type. */

                        /* MISRA Ref 11.8.1 [Function pointer and use of const pointer] */
                        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-118 */

                        /* MISRA Ref 11.1.1 [ Conversion between pointer to
                         * a function and another type ] */
                        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-111 */
                        /* coverity[misra_c_2012_rule_11_8_violation] */
                        /* coverity[misra_c_2012_rule_11_1_violation] */
                        pxSocket->pxUserWakeCallback = ( SocketWakeupCallback_t ) pvOptionValue;
                        xReturn = 0;
                        break;
                #endif /* ipconfigSOCKET_HAS_USER_WAKE_CALLBACK */

                #if ( ipconfigUSE_TCP != 0 )
                    case FREERTOS_SO_SET_LOW_HIGH_WATER:
                        xReturn = prvSetOptionLowHighWater( pxSocket, pvOptionValue );
                        break;

                    case FREERTOS_SO_SNDBUF: /* Set the size of the send buffer, in units of MSS (TCP only) */
                    case FREERTOS_SO_RCVBUF: /* Set the size of the receive buffer, in units of MSS (TCP only) */
                        xReturn = prvSockopt_so_buffer( pxSocket, lOptionName, pvOptionValue );
                        break;

                    case FREERTOS_SO_WIN_PROPERTIES: /* Set all buffer and window properties in one call, parameter is pointer to WinProperties_t */
                        xReturn = prvSetOptionTCPWindows( pxSocket, pvOptionValue );
                        break;

                    case FREERTOS_SO_REUSE_LISTEN_SOCKET: /* If true, the server-socket will turn into a connected socket */
                        xReturn = prvSetOptionReuseListenSocket( pxSocket, pvOptionValue );
                        break;

                    case FREERTOS_SO_CLOSE_AFTER_SEND: /* As soon as the last byte has been transmitted, finalise the connection */
                        xReturn = prvSetOptionCloseAfterSend( pxSocket, pvOptionValue );
                        break;

                    case FREERTOS_SO_SET_FULL_SIZE: /* Refuse to send packets smaller than MSS  */
                        xReturn = prvSetOptionSetFullSize( pxSocket, pvOptionValue );
                        break;

                    case FREERTOS_SO_STOP_RX: /* Refuse to receive more packets. */
                        xReturn = prvSetOptionStopRX( pxSocket, pvOptionValue );
                        break;
                #endif /* ipconfigUSE_TCP == 1 */

            default:
                /* No other options are handled. */
                xReturn = -pdFREERTOS_ERRNO_ENOPROTOOPT;
                break;
        }
    }
    else
    {
        xReturn = -pdFREERTOS_ERRNO_EINVAL;
    }

    return xReturn;
} /* Tested */

/**
 * @brief allocate and initialise a socket.
 *
 * @param[in] xDomain: The domain in which the socket should be created.
 * @param[in] xType: The type of the socket.
 * @param[in] xProtocol: The protocol of the socket.
 *
 * @return FREERTOS_INVALID_SOCKET if the allocation failed, or if there was
 *         a parameter error, otherwise a valid socket.
 */
Socket_t FreeRTOS_socket( BaseType_t xDomain,
                          BaseType_t xType,
                          BaseType_t xProtocol )
{
    FreeRTOS_Socket_t * pxSocket;

/* Note that this value will be over-written by the call to prvDetermineSocketSize. */
    size_t uxSocketSize = 1;
    EventGroupHandle_t xEventGroup;
    Socket_t xReturn;
    BaseType_t xProtocolCpy = xProtocol;

    /* Introduce a do-while loop to allow use of break statements. */
    do
    {
        /* The special protocol FREERTOS_SOCK_DEPENDENT_PROTO, which is equivalent
         * to passing 0 as defined by POSIX, indicates to the socket layer that it
         * should pick a sensible default protocol based off the given socket type.
         * If we can't, prvDetermineSocketSize will catch it as an invalid
         * type/protocol combo.
         */
        if( xProtocol == FREERTOS_SOCK_DEPENDENT_PROTO )
        {
            switch( xType )
            {
                case FREERTOS_SOCK_DGRAM:
                    xProtocolCpy = FREERTOS_IPPROTO_UDP;
                    break;

                case FREERTOS_SOCK_STREAM:
                    xProtocolCpy = FREERTOS_IPPROTO_TCP;
                    break;

                default:

                    /* incorrect xType. this will be caught by
                     * prvDetermineSocketSize.
                     */
                    break;
            }
        }

        if( prvDetermineSocketSize( xDomain, xType, xProtocolCpy, &uxSocketSize ) == pdFAIL )
        {
            /* MISRA Ref 11.4.1 [Socket error and integer to pointer conversion] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
            /* coverity[misra_c_2012_rule_11_4_violation] */
            xReturn = FREERTOS_INVALID_SOCKET;
            break;
        }

        /* Allocate the structure that will hold the socket information. The
        * size depends on the type of socket: UDP sockets need less space. A
        * define 'pvPortMallocSocket' will used to allocate the necessary space.
        * By default it points to the FreeRTOS function 'pvPortMalloc()'. */
        pxSocket = ( ( FreeRTOS_Socket_t * ) pvPortMallocSocket( uxSocketSize ) );

        if( pxSocket == NULL )
        {
            /* MISRA Ref 11.4.1 [Socket error and integer to pointer conversion] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
            /* coverity[misra_c_2012_rule_11_4_violation] */
            xReturn = FREERTOS_INVALID_SOCKET;
            iptraceFAILED_TO_CREATE_SOCKET();
            break;
        }

        xEventGroup = xEventGroupCreate();

        if( xEventGroup == NULL )
        {
            vPortFreeSocket( pxSocket );

            /* MISRA Ref 11.4.1 [Socket error and integer to pointer conversion] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
            /* coverity[misra_c_2012_rule_11_4_violation] */
            xReturn = FREERTOS_INVALID_SOCKET;
            iptraceFAILED_TO_CREATE_EVENT_GROUP();
        }
        else
        {
            /* Clear the entire space to avoid nulling individual entries. */
            ( void ) memset( pxSocket, 0, uxSocketSize );

            pxSocket->xEventGroup = xEventGroup;

            if( xDomain == ( uint8_t ) FREERTOS_AF_INET6 )
            {
                pxSocket->bits.bIsIPv6 = pdTRUE_UNSIGNED;
            }
            else
            {
                pxSocket->bits.bIsIPv6 = pdFALSE_UNSIGNED;
            }

            /* Initialise the socket's members.  The semaphore will be created
             * if the socket is bound to an address, for now the pointer to the
             * semaphore is just set to NULL to show it has not been created. */
            if( xProtocolCpy == FREERTOS_IPPROTO_UDP )
            {
                iptraceMEM_STATS_CREATE( tcpSOCKET_UDP, pxSocket, uxSocketSize + sizeof( StaticEventGroup_t ) );

                vListInitialise( &( pxSocket->u.xUDP.xWaitingPacketsList ) );

                #if ( ipconfigUDP_MAX_RX_PACKETS > 0U )
                    {
                        pxSocket->u.xUDP.uxMaxPackets = ( UBaseType_t ) ipconfigUDP_MAX_RX_PACKETS;
                    }
                #endif /* ipconfigUDP_MAX_RX_PACKETS > 0 */
            }

            #if ( ipconfigUSE_TCP == 1 )
                else if( xProtocolCpy == FREERTOS_IPPROTO_TCP )
                {
                    prvInitialiseTCPFields( pxSocket, uxSocketSize );
                }
                else
                {
                    /* MISRA wants to see an unconditional else clause. */
                }
            #endif /* ipconfigUSE_TCP == 1 */

            vListInitialiseItem( &( pxSocket->xBoundSocketListItem ) );
            listSET_LIST_ITEM_OWNER( &( pxSocket->xBoundSocketListItem ), ( void * ) pxSocket );

            pxSocket->xReceiveBlockTime = ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME;
            pxSocket->xSendBlockTime = ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME;
            pxSocket->ucSocketOptions = ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT;
            pxSocket->ucProtocol = ( uint8_t ) xProtocolCpy; /* protocol: UDP or TCP */

            xReturn = pxSocket;
        }
    } while( ipFALSE_BOOL );

    return xReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_SIGNALS != 0 )

/**
 * @brief Send a signal to the task which reads from this socket.
 *        The socket will receive an event of the type 'eSOCKET_INTR'.
 *        Any ongoing blocking API ( e.g. FreeRTOS_recv() ) will be terminated
 *        and return the value -pdFREERTOS_ERRNO_EINTR ( -4 ).
 *
 * @param[in] xSocket: The socket that will be signalled.
 */
    BaseType_t FreeRTOS_SignalSocket( Socket_t xSocket )
    {
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xReturn;

        if( pxSocket == NULL )
        {
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }
        else
        #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
            if( ( pxSocket->pxSocketSet != NULL ) && ( pxSocket->pxSocketSet->xSelectGroup != NULL ) )
            {
                ( void ) xEventGroupSetBits( pxSocket->pxSocketSet->xSelectGroup, ( EventBits_t ) eSELECT_INTR );
                xReturn = 0;
            }
            else
        #endif /* ipconfigSUPPORT_SELECT_FUNCTION */
        if( pxSocket->xEventGroup != NULL )
        {
            ( void ) xEventGroupSetBits( pxSocket->xEventGroup, ( EventBits_t ) eSOCKET_INTR );
            xReturn = 0;
        }
        else
        {
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief The same as 'FreeRTOS_SignalSocket()', except that this function should
 *        be called from an ISR context.
 *
 * @param[in] xSocket: The socket that will be signalled.
 * @param[in,out] pxHigherPriorityTaskWoken: will be set to non-zero in case a higher-
 *                priority task has become runnable.
 */
    BaseType_t FreeRTOS_SignalSocketFromISR( Socket_t xSocket,
                                             BaseType_t * pxHigherPriorityTaskWoken )
    {
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xReturn;
        IPStackEvent_t xEvent;

        configASSERT( pxSocket != NULL );
        configASSERT( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP );
        configASSERT( pxSocket->xEventGroup != NULL );

        xEvent.eEventType = eSocketSignalEvent;
        xEvent.pvData = pxSocket;

        /* The IP-task will call FreeRTOS_SignalSocket for this socket. */
        xReturn = xQueueSendToBackFromISR( xNetworkEventQueue, &xEvent, pxHigherPriorityTaskWoken );

        return xReturn;
    }
/*-----------------------------------------------------------*/
#endif /* ipconfigSUPPORT_SIGNALS */

#if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )

/**
 * @brief Create a socket set.
 *
 * @return The new socket set which was created, or NULL when allocation has failed.
 */
    SocketSet_t FreeRTOS_CreateSocketSet( void )
    {
        SocketSelect_t * pxSocketSet;

        pxSocketSet = ( ( SocketSelect_t * ) pvPortMalloc( sizeof( *pxSocketSet ) ) );

        if( pxSocketSet != NULL )
        {
            ( void ) memset( pxSocketSet, 0, sizeof( *pxSocketSet ) );
            pxSocketSet->xSelectGroup = xEventGroupCreate();

            if( pxSocketSet->xSelectGroup == NULL )
            {
                vPortFree( pxSocketSet );
                pxSocketSet = NULL;
            }
            else
            {
                /* Lint wants at least a comment, in case the macro is empty. */
                iptraceMEM_STATS_CREATE( tcpSOCKET_SET, pxSocketSet, sizeof( *pxSocketSet ) + sizeof( StaticEventGroup_t ) );
            }
        }

        return ( SocketSet_t ) pxSocketSet;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Delete a given socket set.
 *
 * @param[in] xSocketSet: The socket set being deleted.
 */
    void FreeRTOS_DeleteSocketSet( SocketSet_t xSocketSet )
    {
        IPStackEvent_t xCloseEvent;


        xCloseEvent.eEventType = eSocketSetDeleteEvent;
        xCloseEvent.pvData = ( void * ) xSocketSet;

        if( xSendEventStructToIPTask( &xCloseEvent, ( TickType_t ) portMAX_DELAY ) == pdFAIL )
        {
            FreeRTOS_printf( ( "FreeRTOS_DeleteSocketSet: xSendEventStructToIPTask failed\n" ) );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Clear select bits for a socket. If the mask becomes 0,
 *        remove the socket from the set.
 *
 * @param[in] xSocket: The socket whose select bits are being cleared.
 * @param[in] xSocketSet: The socket set of the socket.
 * @param[in] xBitsToClear: The bits to be cleared. Every '1' means that the
 *                corresponding bit will be cleared. See 'eSelectEvent_t' for
 *                the possible values.
 */
    void FreeRTOS_FD_CLR( Socket_t xSocket,
                          SocketSet_t xSocketSet,
                          EventBits_t xBitsToClear )
    {
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;

        configASSERT( pxSocket != NULL );
        configASSERT( xSocketSet != NULL );

        pxSocket->xSelectBits &= ~( xBitsToClear & ( ( EventBits_t ) eSELECT_ALL ) );

        if( ( pxSocket->xSelectBits & ( ( EventBits_t ) eSELECT_ALL ) ) != ( EventBits_t ) 0U )
        {
            pxSocket->pxSocketSet = ( SocketSelect_t * ) xSocketSet;
        }
        else
        {
            /* disconnect it from the socket set */
            pxSocket->pxSocketSet = NULL;
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Test if a socket belongs to a socket-set and if so, which event bit(s)
 *        are set.
 *
 * @param[in] xSocket: The socket of interest.
 * @param[in] xSocketSet: The socket set to which the socket belongs.
 *
 * @return If the socket belongs to the socket set: the event bits, otherwise zero.
 */
    EventBits_t FreeRTOS_FD_ISSET( const ConstSocket_t xSocket,
                                   const ConstSocketSet_t xSocketSet )
    {
        EventBits_t xReturn;
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;

        configASSERT( pxSocket != NULL );
        configASSERT( xSocketSet != NULL );

        if( xSocketSet == ( SocketSet_t ) pxSocket->pxSocketSet )
        {
            /* Make sure we're not adding bits which are reserved for internal
             * use. */
            xReturn = pxSocket->xSocketBits & ( ( EventBits_t ) eSELECT_ALL );
        }
        else
        {
            xReturn = 0;
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Add a socket to a set.
 *
 * @param[in] xSocket: The socket being added.
 * @param[in] xSocketSet: The socket set being added to.
 * @param[in] xBitsToSet: The event bits to set, a combination of the values defined
 *                        in 'eSelectEvent_t', for read, write, exception, etc.
 */
    void FreeRTOS_FD_SET( Socket_t xSocket,
                          SocketSet_t xSocketSet,
                          EventBits_t xBitsToSet )
    {
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
        SocketSelect_t * pxSocketSet = ( SocketSelect_t * ) xSocketSet;


        configASSERT( pxSocket != NULL );
        configASSERT( xSocketSet != NULL );

        /* Make sure we're not adding bits which are reserved for internal use,
         * such as eSELECT_CALL_IP */
        pxSocket->xSelectBits |= xBitsToSet & ( ( EventBits_t ) eSELECT_ALL );

        if( ( pxSocket->xSelectBits & ( ( EventBits_t ) eSELECT_ALL ) ) != ( EventBits_t ) 0U )
        {
            /* Adding a socket to a socket set. */
            pxSocket->pxSocketSet = ( SocketSelect_t * ) xSocketSet;

            /* Now have the IP-task call vSocketSelect() to see if the set contains
             * any sockets which are 'ready' and set the proper bits. */
            prvFindSelectedSocket( pxSocketSet );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief The select() statement: wait for an event to occur on any of the sockets
 *        included in a socket set.
 *
 * @param[in] xSocketSet: The socket set including the sockets on which we are
 *                        waiting for an event to occur.
 * @param[in] xBlockTimeTicks: Maximum time ticks to wait for an event to occur.
 *                   If the value is 'portMAX_DELAY' then the function will wait
 *                   indefinitely for an event to occur.
 *
 * @return The socket which might have triggered the event bit.
 */
    BaseType_t FreeRTOS_select( SocketSet_t xSocketSet,
                                TickType_t xBlockTimeTicks )
    {
        TimeOut_t xTimeOut;
        TickType_t xRemainingTime;
        SocketSelect_t * pxSocketSet = ( SocketSelect_t * ) xSocketSet;
        EventBits_t uxResult;

        configASSERT( xSocketSet != NULL );

        /* Only in the first round, check for non-blocking */
        xRemainingTime = xBlockTimeTicks;

        /* Fetch the current time */
        vTaskSetTimeOutState( &xTimeOut );

        for( ; ; )
        {
            /* Find a socket which might have triggered the bit
             * This function might return immediately or block for a limited time */
            uxResult = xEventGroupWaitBits( pxSocketSet->xSelectGroup, ( ( EventBits_t ) eSELECT_ALL ), pdFALSE, pdFALSE, xRemainingTime );

            #if ( ipconfigSUPPORT_SIGNALS != 0 )
                {
                    if( ( uxResult & ( ( EventBits_t ) eSELECT_INTR ) ) != 0U )
                    {
                        ( void ) xEventGroupClearBits( pxSocketSet->xSelectGroup, ( EventBits_t ) eSELECT_INTR );
                        FreeRTOS_debug_printf( ( "FreeRTOS_select: interrupted\n" ) );
                        break;
                    }
                }
            #endif /* ipconfigSUPPORT_SIGNALS */

            /* Have the IP-task find the socket which had an event */
            prvFindSelectedSocket( pxSocketSet );

            uxResult = xEventGroupGetBits( pxSocketSet->xSelectGroup );

            if( uxResult != 0U )
            {
                break;
            }

            /* Has the timeout been reached? */
            if( xTaskCheckForTimeOut( &xTimeOut, &xRemainingTime ) != pdFALSE )
            {
                break;
            }
        }

        return ( BaseType_t ) uxResult;
    }
/*-----------------------------------------------------------*/
#endif /* ipconfigSUPPORT_SELECT_FUNCTION */

#if 0
    #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
        struct pollfd
        {
            Socket_t fd;         /* file descriptor */
            EventBits_t events;  /* requested events */
            EventBits_t revents; /* returned events */
        };

        typedef BaseType_t nfds_t;

        BaseType_t poll( struct pollfd * fds,
                         nfds_t nfds,
                         BaseType_t timeout );
        BaseType_t poll( struct pollfd * fds,
                         nfds_t nfds,
                         BaseType_t timeout )
        {
            BaseType_t index;
            SocketSelect_t * pxSocketSet = NULL;
            BaseType_t xReturn = 0;

            /* See which socket-sets have been created and bound to the sockets involved. */
            for( index = 0; index < nfds; index++ )
            {
                FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) fds[ index ].fd;

                if( pxSocket->pxSocketSet != NULL )
                {
                    if( pxSocketSet == NULL )
                    {
                        /* Use this socket-set. */
                        pxSocketSet = pxSocket->pxSocketSet;
                        xReturn = 1;
                    }
                    else if( pxSocketSet == pxSocket->pxSocketSet )
                    {
                        /* Good: associated with the same socket-set. */
                    }
                    else
                    {
                        /* More than one socket-set is found: can not do a select on 2 sets. */
                        xReturn = -1;
                        break;
                    }
                }
            }

            if( xReturn == 0 )
            {
                /* Create a new socket-set, and attach all sockets to it. */
                pxSocketSet = FreeRTOS_CreateSocketSet();

                if( pxSocketSet != NULL )
                {
                    xReturn = 1;
                }
                else
                {
                    xReturn = -2;
                }

                /* Memory leak: when the last socket closes, there is no more reference to
                 * this socket-set.  It should be marked as an automatic or anonymous socket-set,
                 * so when closing the last member, its memory will be freed. */
            }

            if( xReturn > 0 )
            {
                /* Only one socket-set is found.  Connect all sockets to this socket-set. */
                for( index = 0; index < nfds; index++ )
                {
                    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) fds[ index ].fd;
                    EventBits_t xEventBits = fds[ index ].events;

                    FreeRTOS_FD_SET( pxSocket, pxSocketSet, xEventBits );
                    FreeRTOS_FD_CLR( pxSocket, pxSocketSet, ( EventBits_t ) ~xEventBits );
                }

                /* And sleep until an event happens or a time-out. */
                xReturn = FreeRTOS_select( pxSocketSet, timeout );

                /* Now set the return events, copying from the socked field 'xSocketBits'. */
                for( index = 0; index < nfds; index++ )
                {
                    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) fds[ index ].fd;

                    fds[ index ].revents = pxSocket->xSocketBits & ( ( EventBits_t ) eSELECT_ALL );
                }
            }
            else
            {
                /* -1: Sockets are connected to different socket sets. */
                /* -2: FreeRTOS_CreateSocketSet() failed. */
            }

            return xReturn;
        }

    #endif /* ipconfigSUPPORT_SELECT_FUNCTION */
#endif /* 0 */
