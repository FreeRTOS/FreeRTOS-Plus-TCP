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
#include "FreeRTOS_IPv6_Sockets.h"
#include "FreeRTOS_Routing.h"

/*-----------------------------------------------------------*/

/** @brief If FreeRTOS_sendto() is called on a socket that is not bound to a port
 *         number then, depending on the FreeRTOSIPConfig.h settings, it might be
 *         that a port number is automatically generated for the socket.
 *         Automatically generated port numbers will be between
 *         socketAUTO_PORT_ALLOCATION_START_NUMBER and 0xffff.
 *
 * @note Per https://tools.ietf.org/html/rfc6056, "the dynamic ports consist of
 *       the range 49152-65535. However, ephemeral port selection algorithms should
 *       use the whole range 1024-65535" excluding those already in use (inbound
 *       or outbound).
 */
#if !defined( socketAUTO_PORT_ALLOCATION_START_NUMBER )
    #define socketAUTO_PORT_ALLOCATION_START_NUMBER    ( ( uint16_t ) 0x0400 )
#endif

/** @brief Maximum value of port number which can be auto assigned. */
#define socketAUTO_PORT_ALLOCATION_MAX_NUMBER    ( ( uint16_t ) 0xffff )

/*-----------------------------------------------------------*/

/*
 * Allocate the next port number from the private allocation range.
 * TCP and UDP each have their own series of port numbers
 * ulProtocol is either ipPROTOCOL_UDP or ipPROTOCOL_TCP
 */
static uint16_t prvGetPrivatePortNumber( BaseType_t xProtocol );

static BaseType_t prvSocketBindAdd( FreeRTOS_Socket_t * pxSocket,
                                    const struct freertos_sockaddr * pxAddress,
                                    List_t * pxSocketList,
                                    BaseType_t xInternal );

#if ( ( ipconfigHAS_DEBUG_PRINTF != 0 ) || ( ipconfigHAS_PRINTF != 0 ) )
/* prepare a string which describes a socket, just for logging. */
    static const char * prvSocketProps( FreeRTOS_Socket_t * pxSocket );
#endif /* ipconfigHAS_DEBUG_PRINTF || ipconfigHAS_PRINTF */

/*-----------------------------------------------------------*/

/** @brief The list that contains mappings between sockets and port numbers.
 *         Accesses to this list must be protected by critical sections of
 *         some kind.
 */
List_t xBoundUDPSocketsList;

#if ( ipconfigUSE_TCP == 1 )

/** @brief The list that contains mappings between sockets and port numbers.
 *         Accesses to this list must be protected by critical sections of
 *         some kind.
 */
    List_t xBoundTCPSocketsList;

#endif /* ( ipconfigUSE_TCP == 1 ) */

/*-----------------------------------------------------------*/

/**
 * @brief Find an available port number per https://tools.ietf.org/html/rfc6056.
 *
 * @param[in] xProtocol: FREERTOS_IPPROTO_TCP/FREERTOS_IPPROTO_UDP.
 *
 * @return If an available protocol port is found then that port number is returned.
 *         Or else, 0 is returned.
 */
static uint16_t prvGetPrivatePortNumber( BaseType_t xProtocol )
{
    const uint16_t usEphemeralPortCount =
        socketAUTO_PORT_ALLOCATION_MAX_NUMBER - ( socketAUTO_PORT_ALLOCATION_START_NUMBER - 1U );
    uint16_t usIterations = usEphemeralPortCount;
    uint32_t ulRandomSeed = 0;
    uint16_t usResult = 0;
    const List_t * pxList;

    #if ( ipconfigUSE_TCP == 1 )
        if( xProtocol == ( BaseType_t ) FREERTOS_IPPROTO_TCP )
        {
            pxList = &xBoundTCPSocketsList;
        }
        else
    #endif
    {
        pxList = &xBoundUDPSocketsList;
    }

    /* Avoid compiler warnings if ipconfigUSE_TCP is not defined. */
    ( void ) xProtocol;

    /* Find the next available port using the random seed as a starting
     * point. */
    do
    {
        /* Only proceed if the random number generator succeeded. */
        if( xApplicationGetRandomNumber( &( ulRandomSeed ) ) == pdFALSE )
        {
            break;
        }

        /* Map the random to a candidate port. */
        usResult =
            socketAUTO_PORT_ALLOCATION_START_NUMBER +
            ( ( ( uint16_t ) ulRandomSeed ) % usEphemeralPortCount );

        /* Check if there's already an open socket with the same protocol
         * and port. */
        if( NULL == pxListFindListItemWithValue(
                pxList,
                ( TickType_t ) FreeRTOS_htons( usResult ) ) )
        {
            usResult = FreeRTOS_htons( usResult );
            break;
        }
        else
        {
            usResult = 0;
        }

        usIterations--;
    }
    while( usIterations > 0U );

    return usResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief : Bind a socket to a port number.
 * @param[in] pxSocket : The socket to be bound.
 * @param[in] pxAddress : The socket will be bound to this address.
 * @param[in] pxSocketList : will either point to xBoundUDPSocketsList or
 *                           xBoundTCPSocketsList.
 * @param[in] xInternal : pdTRUE if this function is called 'internally', i.e.
 *                        by the IP-task.
 */
static BaseType_t prvSocketBindAdd( FreeRTOS_Socket_t * pxSocket,
                                    const struct freertos_sockaddr * pxAddress,
                                    List_t * pxSocketList,
                                    BaseType_t xInternal )
{
    BaseType_t xReturn = 0;

    /* Check to ensure the port is not already in use.  If the bind is
     * called internally, a port MAY be used by more than one socket. */
    if( ( ( xInternal == pdFALSE ) || ( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP ) ) &&
        ( pxListFindListItemWithValue( pxSocketList, ( TickType_t ) pxAddress->sin_port ) != NULL ) )
    {
        FreeRTOS_debug_printf( ( "vSocketBind: %sP port %d in use\n",
                                 ( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP ) ? "TC" : "UD",
                                 FreeRTOS_ntohs( pxAddress->sin_port ) ) );
        xReturn = -pdFREERTOS_ERRNO_EADDRINUSE;
    }
    else
    {
        /* Allocate the port number to the socket.
         * This macro will set 'xBoundSocketListItem->xItemValue' */
        socketSET_SOCKET_PORT( pxSocket, pxAddress->sin_port );

        /* And also store it in a socket field 'usLocalPort' in host-byte-order,
         * mostly used for logging and debugging purposes */
        pxSocket->usLocalPort = FreeRTOS_ntohs( pxAddress->sin_port );

        if( pxAddress->sin_family == ( uint8_t ) FREERTOS_AF_INET6 )
        {
            pxSocket->xLocalAddress.ulIP_IPv4 = 0U;
            ( void ) memcpy( pxSocket->xLocalAddress.xIP_IPv6.ucBytes, pxAddress->sin_addr6.ucBytes, sizeof( pxSocket->xLocalAddress.xIP_IPv6.ucBytes ) );
        }
        else if( pxAddress->sin_addr != FREERTOS_INADDR_ANY )
        {
            pxSocket->pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( pxAddress->sin_addr, 7 );
        }
        else
        {
            /* Place holder, do nothing, MISRA compliance */
        }

        if( pxSocket->pxEndPoint != NULL )
        {
            pxSocket->xLocalAddress.ulIP_IPv4 = FreeRTOS_ntohl( pxSocket->pxEndPoint->ipv4_settings.ulIPAddress );
            /*TODO Check if needed for ipv6 setting */
        }
        else
        {
            pxSocket->xLocalAddress.ulIP_IPv4 = 0U;
            ( void ) memset( pxSocket->xLocalAddress.xIP_IPv6.ucBytes, 0, sizeof( pxSocket->xLocalAddress.xIP_IPv6.ucBytes ) );
        }

        /* Add the socket to the list of bound ports. */
        {
            /* If the network driver can iterate through 'xBoundUDPSocketsList',
             * by calling xPortHasUDPSocket() then the IP-task must temporarily
             * suspend the scheduler to keep the list in a consistent state. */
            #if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 1 )
                {
                    vTaskSuspendAll();
                }
            #endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */

            /* Add the socket to 'xBoundUDPSocketsList' or 'xBoundTCPSocketsList' */
            vListInsertEnd( pxSocketList, &( pxSocket->xBoundSocketListItem ) );

            #if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 1 )
                {
                    ( void ) xTaskResumeAll();
                }
            #endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

#if ( ( ipconfigHAS_DEBUG_PRINTF != 0 ) || ( ipconfigHAS_PRINTF != 0 ) )

    static const char * prvSocketProps( FreeRTOS_Socket_t * pxSocket )
    {
        static char pucReturn[ 92 ];

        /* For debugging purposes only: show some properties of a socket:
         * IP-addresses and port numbers. */
        #if ipconfigUSE_TCP == 1
            if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP )
            {
                if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
                {
                    /* The use of snprintf() is discouraged by the MISRA rules.
                     * This code however, is only active when logging is used. */

                    /* The format '%pip' takes an string of 16 bytes as
                     * a parameter, which is an IPv6 address.
                     * See printf-stdarg.c */
                    ( void ) snprintf( pucReturn, sizeof( pucReturn ), "%pip port %u to %pip port %u",
                                       pxSocket->xLocalAddress.xIP_IPv6.ucBytes,
                                       pxSocket->usLocalPort,
                                       pxSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes,
                                       pxSocket->u.xTCP.usRemotePort );
                }
                else
                {
                    ( void ) snprintf( pucReturn, sizeof( pucReturn ), "%xip port %u to %xip port %u",
                                       ( unsigned ) pxSocket->xLocalAddress.ulIP_IPv4,
                                       pxSocket->usLocalPort,
                                       ( unsigned ) pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4,
                                       pxSocket->u.xTCP.usRemotePort );
                }
            }
            else
        #endif /* if ipconfigUSE_TCP == 1 */

        if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_UDP )
        {
            if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
            {
                ( void ) snprintf( pucReturn, sizeof( pucReturn ),
                                   "%pip port %u",
                                   pxSocket->xLocalAddress.xIP_IPv6.ucBytes,
                                   pxSocket->usLocalPort );
            }
            else
            {
                ( void ) snprintf( pucReturn, sizeof( pucReturn ),
                                   "%xip port %u",
                                   ( unsigned ) pxSocket->xLocalAddress.ulIP_IPv4,
                                   pxSocket->usLocalPort );
            }
        }
        else
        {
            /* Protocol not handled. */
        }

        return pucReturn;
    }
#endif /* ( ( ipconfigHAS_DEBUG_PRINTF != 0 ) || ( ipconfigHAS_PRINTF != 0 ) ) */
/*-----------------------------------------------------------*/

/**
 * @brief Determine the socket size for the given protocol.
 *
 * @param[in] xDomain: The domain for which the size of socket is being determined.
 * @param[in] xType: Is this a datagram socket or a stream socket.
 * @param[in] xProtocol: The protocol being used.
 * @param[out] pxSocketSize: Pointer to a variable in which the size shall be returned
 *                           if all checks pass.
 *
 * @return pdPASS if socket size was determined and put in the parameter pxSocketSize
 *         correctly, else pdFAIL.
 */
BaseType_t prvDetermineSocketSize( BaseType_t xDomain,
                                          BaseType_t xType,
                                          BaseType_t xProtocol,
                                          size_t * pxSocketSize )
{
    BaseType_t xReturn = pdPASS;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    /* Asserts must not appear before it has been determined that the network
     * task is ready - otherwise the asserts will fail. */
    if( xIPIsNetworkTaskReady() == pdFALSE )
    {
        xReturn = pdFAIL;
    }
    else
    {
        /* Only Ethernet is currently supported. */
        #if ( ipconfigUSE_IPv6 == 0 )
            {
                configASSERT( xDomain == FREERTOS_AF_INET );
            }
        #else
            {
                configASSERT( ( xDomain == FREERTOS_AF_INET ) || ( xDomain == FREERTOS_AF_INET6 ) );
            }
        #endif

        /* Check if the UDP socket-list has been initialised. */
        configASSERT( listLIST_IS_INITIALISED( &xBoundUDPSocketsList ) );
        #if ( ipconfigUSE_TCP == 1 )
            {
                /* Check if the TCP socket-list has been initialised. */
                configASSERT( listLIST_IS_INITIALISED( &xBoundTCPSocketsList ) );
            }
        #endif /* ipconfigUSE_TCP == 1 */

        if( xProtocol == FREERTOS_IPPROTO_UDP )
        {
            if( xType != FREERTOS_SOCK_DGRAM )
            {
                xReturn = pdFAIL;
                configASSERT( xReturn == pdPASS ); /* LCOV_EXCL_BR_LINE Exclude this line from branch coverage as the not-taken condition will never happen. */
            }

            /* In case a UDP socket is created, do not allocate space for TCP data. */
            *pxSocketSize = ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xUDP );
        }

        #if ( ipconfigUSE_TCP == 1 )
            else if( xProtocol == FREERTOS_IPPROTO_TCP )
            {
                if( xType != FREERTOS_SOCK_STREAM )
                {
                    xReturn = pdFAIL;
                    configASSERT( xReturn == pdPASS ); /* LCOV_EXCL_BR_LINE Exclude this line from branch coverage as the not-taken condition will never happen. */
                }

                *pxSocketSize = ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP );
            }
        #endif /* ipconfigUSE_TCP == 1 */
        else
        {
            xReturn = pdFAIL;
            configASSERT( xReturn == pdPASS ); /* LCOV_EXCL_BR_LINE Exclude this line from branch coverage as the not-taken condition will never happen. */
        }
    }

    /* In case configASSERT() is not used */
    ( void ) xDomain;
    ( void ) pxSocket; /* Was only used for sizeof. */
    return xReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_CALLBACKS == 1 )

/**
 * @brief Set a callback function for either a TCP or a UDP socket.
 *        The callback function will be called on-connect, on-send
 *        or on-receive.
 *
 * @param[in] pxSocket: The socket whose options are being set.
 * @param[in] lOptionName: The option name like FREERTOS_SO_xxx_HANDLER.
 * @param[in] pvOptionValue: A pointer to a 'F_TCP_UDP_Handler_t',
 *                           which defines the handler.
 *
 * @return If there is no error, then 0 is returned. Or a negative errno
 *         value is returned.
 */
    BaseType_t prvSetOptionCallback( FreeRTOS_Socket_t * pxSocket,
                                            int32_t lOptionName,
                                            const void * pvOptionValue )
    {
        BaseType_t xReturn = 0;

        #if ( ipconfigUSE_TCP == 1 )
            {
                UBaseType_t uxProtocol;

                if( ( lOptionName == FREERTOS_SO_UDP_RECV_HANDLER ) ||
                    ( lOptionName == FREERTOS_SO_UDP_SENT_HANDLER ) )
                {
                    uxProtocol = ( UBaseType_t ) FREERTOS_IPPROTO_UDP;
                }
                else
                {
                    uxProtocol = ( UBaseType_t ) FREERTOS_IPPROTO_TCP;
                }

                if( pxSocket->ucProtocol != ( uint8_t ) uxProtocol )
                {
                    xReturn = -pdFREERTOS_ERRNO_EINVAL;
                }
            }
        #else /* if ( ipconfigUSE_TCP == 1 ) */
            {
                /* No need to check if the socket has the right
                 * protocol, because only UDP sockets can be created. */
            }
        #endif /* ipconfigUSE_TCP */

        if( xReturn == 0 )
        {
            switch( lOptionName )
            {
                #if ipconfigUSE_TCP == 1
                    case FREERTOS_SO_TCP_CONN_HANDLER:
                        pxSocket->u.xTCP.pxHandleConnected = ( ( const F_TCP_UDP_Handler_t * ) pvOptionValue )->pxOnTCPConnected;
                        break;

                    case FREERTOS_SO_TCP_RECV_HANDLER:
                        pxSocket->u.xTCP.pxHandleReceive = ( ( const F_TCP_UDP_Handler_t * ) pvOptionValue )->pxOnTCPReceive;
                        break;

                    case FREERTOS_SO_TCP_SENT_HANDLER:
                        pxSocket->u.xTCP.pxHandleSent = ( ( const F_TCP_UDP_Handler_t * ) pvOptionValue )->pxOnTCPSent;
                        break;
                #endif /* ipconfigUSE_TCP */
                case FREERTOS_SO_UDP_RECV_HANDLER:
                    pxSocket->u.xUDP.pxHandleReceive = ( ( const F_TCP_UDP_Handler_t * ) pvOptionValue )->pxOnUDPReceive;
                    break;

                case FREERTOS_SO_UDP_SENT_HANDLER:
                    pxSocket->u.xUDP.pxHandleSent = ( ( const F_TCP_UDP_Handler_t * ) pvOptionValue )->pxOnUDPSent;
                    break;

                default:
                    xReturn = -pdFREERTOS_ERRNO_EINVAL;
                    break;
            }
        }

        return xReturn;
    }
#endif /* ( ipconfigUSE_CALLBACKS == 1 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Handle the socket options FREERTOS_SO_RCVTIMEO and
 *        FREERTOS_SO_SNDTIMEO.
 *        Used in applications with streaming audio: tell the peer
 *        to stop or continue sending data.
 *
 * @param[in] pxSocket: The UDP socket used for the connection.
 * @param[in] pvOptionValue: The option name like FREERTOS_SO_xxx_HANDLER.
 * @param[in] xForSend: when true, handle 'FREERTOS_SO_SNDTIMEO',
 *            otherwise handle the option `FREERTOS_SO_RCVTIMEO`.
 */
void prvSetOptionTimeout( FreeRTOS_Socket_t * pxSocket,
                                 const void * pvOptionValue,
                                 BaseType_t xForSend )
{
    TickType_t xBlockTime = *( ( const TickType_t * ) pvOptionValue );

    if( xForSend == pdTRUE )
    {
        if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_UDP )
        {
            /* The send time out is capped for the reason stated in the
             * comments where ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS is defined
             * in FreeRTOSIPConfig.h (assuming an official configuration file
             * is being used. */
            if( xBlockTime > ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS )
            {
                xBlockTime = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS;
            }
        }
        else
        {
            /* For TCP socket, it isn't necessary to limit the blocking time
             * because  the FreeRTOS_send() function does not wait for a network
             * buffer to become available. */
        }

        pxSocket->xSendBlockTime = xBlockTime;
    }
    else
    {
        pxSocket->xReceiveBlockTime = xBlockTime;
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Find a list item associated with the wanted-item.
 *
 * @param[in] pxList: The list through which the search is to be conducted.
 * @param[in] xWantedItemValue: The wanted item whose association is to be found.
 *
 * @return The list item holding the value being searched for. If nothing is found,
 *         then a NULL is returned.
 */
const ListItem_t * pxListFindListItemWithValue( const List_t * pxList,
                                                TickType_t xWantedItemValue )
{
    const ListItem_t * pxResult = NULL;

    if( ( xIPIsNetworkTaskReady() != pdFALSE ) && ( pxList != NULL ) )
    {
        const ListItem_t * pxIterator;

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        const ListItem_t * pxEnd = ( ( const ListItem_t * ) &( pxList->xListEnd ) );

        for( pxIterator = listGET_NEXT( pxEnd );
             pxIterator != pxEnd;
             pxIterator = listGET_NEXT( pxIterator ) )
        {
            if( listGET_LIST_ITEM_VALUE( pxIterator ) == xWantedItemValue )
            {
                pxResult = pxIterator;
                break;
            }
        }
    }

    return pxResult;
} /* Tested */
/*-----------------------------------------------------------*/

/**
 * @brief Convert an ASCII character to its corresponding hexadecimal value.
 *        Accepted characters are 0-9, a-f, and A-F.
 *
 * @param[in] cChar: The character to be converted.
 *
 * @return The hexadecimal value, between 0 and 15.
 *         When the character is not valid, socketINVALID_HEX_CHAR will be returned.
 */

uint8_t ucASCIIToHex( char cChar )
{
    char cValue = cChar;
    uint8_t ucNew;

    if( ( cValue >= '0' ) && ( cValue <= '9' ) )
    {
        cValue -= ( char ) '0';
        /* The value will be between 0 and 9. */
        ucNew = ( uint8_t ) cValue;
    }
    else if( ( cValue >= 'a' ) && ( cValue <= 'f' ) )
    {
        cValue -= ( char ) 'a';
        ucNew = ( uint8_t ) cValue;
        /* The value will be between 10 and 15. */
        ucNew += ( uint8_t ) 10;
    }
    else if( ( cValue >= 'A' ) && ( cValue <= 'F' ) )
    {
        cValue -= ( char ) 'A';
        ucNew = ( uint8_t ) cValue;
        /* The value will be between 10 and 15. */
        ucNew += ( uint8_t ) 10;
    }
    else
    {
        /* The character does not represent a valid hex number, return 255. */
        ucNew = ( uint8_t ) socketINVALID_HEX_CHAR;
    }

    return ucNew;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the size of the IP-header, by checking if the socket bIsIPv6 set.
 * @param[in] pxSocket: The socket.
 * @return The size of the corresponding IP-header.
 */
size_t uxIPHeaderSizeSocket( const FreeRTOS_Socket_t * pxSocket )
{
    size_t uxResult;

    if( ( pxSocket != NULL ) && ( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED ) )
    {
        uxResult = ipSIZE_OF_IPv6_HEADER;
    }
    else
    {
        uxResult = ipSIZE_OF_IPv4_HEADER;
    }

    return uxResult;
}
/*-----------------------------------------------------------*/

#if ( ( ipconfigHAS_PRINTF != 0 ) )

/**
 * @brief Print a summary of all sockets and their connections.
 */
    void vNetStat( void )
    {
        /* Show a simple listing of all created sockets and their connections */
        const ListItem_t * pxIterator;
        BaseType_t count = 0;
        size_t uxMinimum = uxGetMinimumFreeNetworkBuffers();
        size_t uxCurrent = uxGetNumberOfFreeNetworkBuffers();

        FreeRTOS_printf( ( "Prot Port IP-Remote       : Port  R/T Status       Alive  tmout Child\n" ) );
        #if ( ipconfigUSE_TCP == 1 )
            count += vTCPNetStat();
        #endif
        count += vUDPNetStat();

        FreeRTOS_printf( ( "FreeRTOS_netstat: %d sockets %u < %u < %u buffers free\n",
                           ( int ) count,
                           ( unsigned ) uxMinimum,
                           ( unsigned ) uxCurrent,
                           ( unsigned ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ) );
    }
#endif /* ( ipconfigHAS_PRINTF != 0 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Initialise the bound TCP/UDP socket lists.
 */
void vNetworkSocketsInit( void )
{
    vListInitialise( &xBoundUDPSocketsList );

    #if ( ipconfigUSE_TCP == 1 )
        {
            vListInitialise( &xBoundTCPSocketsList );
        }
    #endif /* ipconfigUSE_TCP == 1 */
}
/*-----------------------------------------------------------*/

/**
 * @brief Internal version of bind() that should not be called directly.
 *        'xInternal' is used for TCP sockets only: it allows to have several
 *        (connected) child sockets bound to the same server port.
 *
 * @param[in] pxSocket: The socket is to be bound.
 * @param[in] pxBindAddress: The port to which this socket should be bound.
 * @param[in] uxAddressLength: The address length.
 * @param[in] xInternal: pdTRUE is calling internally, else pdFALSE.
 *
 * @return If the socket was bound to a port successfully, then a 0 is returned.
 *         Or else, an error code is returned.
 */
BaseType_t vSocketBind( FreeRTOS_Socket_t * pxSocket,
                        struct freertos_sockaddr * pxBindAddress,
                        size_t uxAddressLength,
                        BaseType_t xInternal )
{
    BaseType_t xReturn = 0; /* In Berkeley sockets, 0 means pass for bind(). */
    List_t * pxSocketList;
    struct freertos_sockaddr * pxAddress = pxBindAddress;

    #if ( ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND == 1 )
        struct freertos_sockaddr xAddress;
    #endif /* ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND */

    configASSERT( xSocketValid( pxSocket ) == pdTRUE );

    #if ( ipconfigUSE_TCP == 1 )
        if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP )
        {
            pxSocketList = &xBoundTCPSocketsList;
        }
        else
    #endif /* ipconfigUSE_TCP == 1 */
    {
        pxSocketList = &xBoundUDPSocketsList;
    }

    /* The function prototype is designed to maintain the expected Berkeley
     * sockets standard, but this implementation does not use all the parameters. */
    ( void ) uxAddressLength;

    #if ( ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND == 1 )
        {
            /* pxAddress will be NULL if sendto() was called on a socket without the
             * socket being bound to an address. In this case, automatically allocate
             * an address to the socket.  There is a small chance that the allocated
             * port will already be in use - if that is the case, then the check below
             * [pxListFindListItemWithValue()] will result in an error being returned. */
            if( pxAddress == NULL )
            {
                pxAddress = &xAddress;
                /* Put the port to zero to be assigned later. */
                pxAddress->sin_port = 0U;
            }
        }
    #endif /* ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND == 1 */

    /* Sockets must be bound before calling FreeRTOS_sendto() if
    * ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND is not set to 1. */
    configASSERT( pxAddress != NULL );

    #if ( ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND == 1 )
        /* pxAddress is not NULL, no testing needed. */
    #else
        if( pxAddress != NULL )
    #endif
    {
        /* Add a do-while loop to facilitate use of 'break' statements. */
        do
        {
            if( pxAddress->sin_port == 0U )
            {
                pxAddress->sin_port = prvGetPrivatePortNumber( ( BaseType_t ) pxSocket->ucProtocol );

                if( pxAddress->sin_port == ( uint16_t ) 0U )
                {
                    xReturn = -pdFREERTOS_ERRNO_EADDRNOTAVAIL;
                    break;
                }
            }

            /* If vSocketBind() is called from the API FreeRTOS_bind() it has been
             * confirmed that the socket was not yet bound to a port.  If it is called
             * from the IP-task, no such check is necessary. */

            xReturn = prvSocketBindAdd( pxSocket, pxAddress, pxSocketList, xInternal );
        } while( ipFALSE_BOOL );
    }

    #if ( ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND == 0 )
        else
        {
            xReturn = -pdFREERTOS_ERRNO_EADDRNOTAVAIL;
            FreeRTOS_debug_printf( ( "vSocketBind: Socket has no address.\n" ) );
        }
    #endif

    if( xReturn != 0 )
    {
        iptraceBIND_FAILED( xSocket, ( FreeRTOS_ntohs( pxAddress->sin_port ) ) );
    }

    return xReturn;
} /* Tested */
/*-----------------------------------------------------------*/

/**
 * @brief This is the internal version of FreeRTOS_closesocket(). It will
 *        be called by the IPtask only to avoid problems with synchronicity.
 *
 * @param[in] pxSocket: The socket descriptor of the socket being closed.
 *
 * @return Returns NULL, always.
 */
/* MISRA Ref 17.2.1 [Sockets and limited recursion] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-172 */
/* coverity[misra_c_2012_rule_17_2_violation] */
void * vSocketClose( FreeRTOS_Socket_t * pxSocket )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;

    #if ( ipconfigUSE_TCP == 1 )
        {
            /* For TCP: clean up a little more. */
            if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP )
            {
                #if ( ipconfigUSE_TCP_WIN == 1 )
                    {
                        if( pxSocket->u.xTCP.pxAckMessage != NULL )
                        {
                            vReleaseNetworkBufferAndDescriptor( pxSocket->u.xTCP.pxAckMessage );
                        }

                        /* Free the resources which were claimed by the tcpWin member */
                        vTCPWindowDestroy( &pxSocket->u.xTCP.xTCPWindow );
                    }
                #endif /* ipconfigUSE_TCP_WIN */

                /* Free the input and output streams */
                if( pxSocket->u.xTCP.rxStream != NULL )
                {
                    iptraceMEM_STATS_DELETE( pxSocket->u.xTCP.rxStream );
                    vPortFreeLarge( pxSocket->u.xTCP.rxStream );
                }

                if( pxSocket->u.xTCP.txStream != NULL )
                {
                    iptraceMEM_STATS_DELETE( pxSocket->u.xTCP.txStream );
                    vPortFreeLarge( pxSocket->u.xTCP.txStream );
                }

                /* In case this is a child socket, make sure the child-count of the
                 * parent socket is decreased. */
                prvTCPSetSocketCount( pxSocket );
            }
        }
    #endif /* ipconfigUSE_TCP == 1 */

    /* Socket must be unbound first, to ensure no more packets are queued on
     * it. */
    if( socketSOCKET_IS_BOUND( pxSocket ) )
    {
        /* If the network driver can iterate through 'xBoundUDPSocketsList',
         * by calling xPortHasUDPSocket(), then the IP-task must temporarily
         * suspend the scheduler to keep the list in a consistent state. */
        #if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 1 )
            {
                vTaskSuspendAll();
            }
        #endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */

        ( void ) uxListRemove( &( pxSocket->xBoundSocketListItem ) );

        #if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 1 )
            {
                ( void ) xTaskResumeAll();
            }
        #endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */
    }

    /* Now the socket is not bound the list of waiting packets can be
     * drained. */
    if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_UDP )
    {
        while( listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) ) > 0U )
        {
            pxNetworkBuffer = ( ( NetworkBufferDescriptor_t * ) listGET_OWNER_OF_HEAD_ENTRY( &( pxSocket->u.xUDP.xWaitingPacketsList ) ) );
            ( void ) uxListRemove( &( pxNetworkBuffer->xBufferListItem ) );
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
        }
    }

    if( pxSocket->xEventGroup != NULL )
    {
        vEventGroupDelete( pxSocket->xEventGroup );
    }

    #if ( ipconfigUSE_TCP == 1 ) && ( ipconfigHAS_DEBUG_PRINTF != 0 )
        {
            if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP )
            {
                FreeRTOS_debug_printf( ( "FreeRTOS_closesocket[%s]: buffers %lu socks %lu\n",
                                         prvSocketProps( pxSocket ),
                                         uxGetNumberOfFreeNetworkBuffers(),
                                         listCURRENT_LIST_LENGTH( &xBoundTCPSocketsList ) ) );
            }
        }
    #endif /* ( ipconfigUSE_TCP == 1 ) && ( ipconfigHAS_DEBUG_PRINTF != 0 ) */

    /* And finally, after all resources have been freed, free the socket space */
    iptraceMEM_STATS_DELETE( pxSocket );
    vPortFreeSocket( pxSocket );

    return NULL;
} /* Tested */
/*-----------------------------------------------------------*/

/**
 * @brief Check whether the socket is valid or not.
 *
 * @param[in] pxSocket: The socket being checked.
 * @param[in] xProtocol: The protocol for which the socket was created.
 * @param[in] xIsBound: pdTRUE when the socket should be bound, otherwise pdFALSE.
 *
 * @return If the socket is valid, then pdPASS is returned or else, pdFAIL
 *         is returned.
 */
BaseType_t vSocketValid( const FreeRTOS_Socket_t * pxSocket,
                         BaseType_t xProtocol,
                         BaseType_t xIsBound )
{
    BaseType_t xReturn;

    if( xSocketValid( pxSocket ) == pdFALSE )
    {
        xReturn = pdFALSE;
    }
    else if( ( xIsBound != pdFALSE ) && !socketSOCKET_IS_BOUND( pxSocket ) )
    {
        /* The caller expects the socket to be bound, but it isn't. */
        xReturn = pdFALSE;
    }
    else if( pxSocket->ucProtocol != ( uint8_t ) xProtocol )
    {
        /* Socket has a wrong type (UDP != TCP). */
        xReturn = pdFALSE;
    }
    else
    {
        xReturn = pdTRUE;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Wake up the user of the given socket through event-groups.
 *
 * @param[in] pxSocket: The socket whose user is to be woken up.
 */
void vSocketWakeUpUser( FreeRTOS_Socket_t * pxSocket )
{
/* _HT_ must work this out, now vSocketWakeUpUser will be called for any important
 * event or transition */
    #if ( ipconfigSOCKET_HAS_USER_SEMAPHORE == 1 )
        {
            if( pxSocket->pxUserSemaphore != NULL )
            {
                ( void ) xSemaphoreGive( pxSocket->pxUserSemaphore );
            }
        }
    #endif /* ipconfigSOCKET_HAS_USER_SEMAPHORE */

    #if ( ipconfigSOCKET_HAS_USER_WAKE_CALLBACK == 1 )
        {
            if( pxSocket->pxUserWakeCallback != NULL )
            {
                pxSocket->pxUserWakeCallback( pxSocket );
            }
        }
    #endif /* ipconfigSOCKET_HAS_USER_WAKE_CALLBACK */

    #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
        {
            if( pxSocket->pxSocketSet != NULL )
            {
                EventBits_t xSelectBits = ( pxSocket->xEventBits >> SOCKET_EVENT_BIT_COUNT ) & ( ( EventBits_t ) eSELECT_ALL );

                if( xSelectBits != 0U )
                {
                    pxSocket->xSocketBits |= xSelectBits;
                    ( void ) xEventGroupSetBits( pxSocket->pxSocketSet->xSelectGroup, xSelectBits );
                }
            }

            pxSocket->xEventBits &= ( EventBits_t ) eSOCKET_ALL;
        }
    #endif /* ipconfigSUPPORT_SELECT_FUNCTION */

    if( ( pxSocket->xEventGroup != NULL ) && ( pxSocket->xEventBits != 0U ) )
    {
        ( void ) xEventGroupSetBits( pxSocket->xEventGroup, pxSocket->xEventBits );
    }

    pxSocket->xEventBits = 0U;
}
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )

/**
 * @brief Send a message to the IP-task to have it check all sockets belonging to
 *        'pxSocketSet'
 *
 * @param[in] pxSocketSet: The socket set being asked to check.
 */
    static void prvFindSelectedSocket( SocketSelect_t * pxSocketSet )
    {
        IPStackEvent_t xSelectEvent;

        #if ( ipconfigSELECT_USES_NOTIFY != 0 )
            SocketSelectMessage_t xSelectMessage;
        #endif

        xSelectEvent.eEventType = eSocketSelectEvent;
        #if ( ipconfigSELECT_USES_NOTIFY != 0 )
            {
                xSelectMessage.pxSocketSet = pxSocketSet;
                xSelectMessage.xTaskhandle = xTaskGetCurrentTaskHandle();
                xSelectEvent.pvData = &( xSelectMessage );
            }
        #else
            {
                xSelectEvent.pvData = pxSocketSet;

                /* while the IP-task works on the request, the API will block on
                 * 'eSELECT_CALL_IP'.  So clear it first. */
                ( void ) xEventGroupClearBits( pxSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP );
            }
        #endif /* if ( ipconfigSELECT_USES_NOTIFY != 0 ) */

        /* Now send the socket select event */
        if( xSendEventStructToIPTask( &xSelectEvent, ( TickType_t ) portMAX_DELAY ) == pdFAIL )
        {
            /* Oops, we failed to wake-up the IP task. No use to wait for it. */
            FreeRTOS_debug_printf( ( "prvFindSelectedSocket: failed\n" ) );
        }
        else
        {
            /* As soon as the IP-task is ready, it will set 'eSELECT_CALL_IP' to
             * wakeup the calling API */
            #if ( ipconfigSELECT_USES_NOTIFY != 0 )
                {
                    ( void ) ulTaskNotifyTake( pdFALSE, portMAX_DELAY );
                }
            #else
                {
                    ( void ) xEventGroupWaitBits( pxSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdTRUE, pdFALSE, portMAX_DELAY );
                }
            #endif
        }
    }

/**
 * @brief This internal non-blocking function will check all sockets that belong
 *        to a select set.  The events bits of each socket will be updated, and it
 *        will check if an ongoing select() call must be interrupted because of an
 *        event has occurred.
 *
 * @param[in] pxSocketSet: The socket-set which is to be waited on for change.
 */
    void vSocketSelect( const SocketSelect_t * pxSocketSet )
    {
        BaseType_t xRound;
        EventBits_t xSocketBits, xBitsToClear;

        #if ipconfigUSE_TCP == 1
            BaseType_t xLastRound = 1;
        #else
            BaseType_t xLastRound = 0;
        #endif

        /* These flags will be switched on after checking the socket status. */
        EventBits_t xGroupBits = 0;

        for( xRound = 0; xRound <= xLastRound; xRound++ )
        {
            const ListItem_t * pxIterator;
            const ListItem_t * pxEnd;

            if( xRound == 0 )
            {
                /* MISRA Ref 11.3.1 [Misaligned access] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                /* coverity[misra_c_2012_rule_11_3_violation] */
                pxEnd = ( ( const ListItem_t * ) &( xBoundUDPSocketsList.xListEnd ) );
            }

            #if ipconfigUSE_TCP == 1
                else
                {
                    /* MISRA Ref 11.3.1 [Misaligned access] */
                    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                    /* coverity[misra_c_2012_rule_11_3_violation] */
                    pxEnd = ( ( const ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );
                }
            #endif /* ipconfigUSE_TCP == 1 */

            for( pxIterator = listGET_NEXT( pxEnd );
                 pxIterator != pxEnd;
                 pxIterator = listGET_NEXT( pxIterator ) )
            {
                FreeRTOS_Socket_t * pxSocket = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );

                if( pxSocket->pxSocketSet != pxSocketSet )
                {
                    /* Socket does not belong to this select group. */
                    continue;
                }

                xSocketBits = 0;

                #if ( ipconfigUSE_TCP == 1 )
                    if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP )
                    {
                        xSocketBits |= vSocketSelectTCP( pxSocket );
                    }
                    else
                #endif /* ipconfigUSE_TCP == 1 */
                {
                    /* Select events for UDP are simpler. */
                    if( ( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_READ ) != 0U ) &&
                        ( listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) ) > 0U ) )
                    {
                        xSocketBits |= ( EventBits_t ) eSELECT_READ;
                    }

                    /* The WRITE and EXCEPT bits are not used for UDP */
                } /* if( pxSocket->ucProtocol == FREERTOS_IPPROTO_TCP ) */

                /* Each socket keeps its own event flags, which are looked-up
                 * by FreeRTOS_FD_ISSSET() */
                pxSocket->xSocketBits = xSocketBits;

                /* The ORed value will be used to set the bits in the event
                 * group. */
                xGroupBits |= xSocketBits;
            } /* for( pxIterator ... ) */
        }     /* for( xRound = 0; xRound <= xLastRound; xRound++ ) */

        xBitsToClear = xEventGroupGetBits( pxSocketSet->xSelectGroup );

        /* Now set the necessary bits. */
        xBitsToClear = ( xBitsToClear & ~xGroupBits ) & ( ( EventBits_t ) eSELECT_ALL );

        #if ( ipconfigSUPPORT_SIGNALS != 0 )
            {
                /* Maybe the socketset was signalled, but don't
                 * clear the 'eSELECT_INTR' bit here, as it will be used
                 * and cleared in FreeRTOS_select(). */
                xBitsToClear &= ~( ( EventBits_t ) eSELECT_INTR );
            }
        #endif /* ipconfigSUPPORT_SIGNALS */

        if( xBitsToClear != 0U )
        {
            ( void ) xEventGroupClearBits( pxSocketSet->xSelectGroup, xBitsToClear );
        }

        /* Now include eSELECT_CALL_IP to wakeup the caller. */
        ( void ) xEventGroupSetBits( pxSocketSet->xSelectGroup, xGroupBits | ( EventBits_t ) eSELECT_CALL_IP );
    }

#endif /* ( ipconfigSUPPORT_SELECT_FUNCTION == 1 ) */
/*-----------------------------------------------------------*/
