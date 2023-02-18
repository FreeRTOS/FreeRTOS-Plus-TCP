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

#ifndef FREERTOS_SOCKETS_H
    #define FREERTOS_SOCKETS_H

    #ifdef __cplusplus
        extern "C" {
    #endif

/* Standard includes. */
    #include <string.h>

/* FreeRTOS includes. */
    #include "FreeRTOS.h"
    #include "event_groups.h"

/* Application level configuration options. */
    #include "FreeRTOSIPConfig.h"
    #include "FreeRTOSIPConfigDefaults.h"

    /*#include "FreeRTOS_UDP_Sockets.h"
    #if ( ipconfigUSE_TCP == 1 )
        #include "FreeRTOS_TCP_Sockets.h"
    #endif*/
    #include "FreeRTOS_IP_Common.h"

/* Assigned to an Socket_t variable when the socket is not valid, probably
 * because it could not be created. */
    #define FREERTOS_INVALID_SOCKET          ( ( Socket_t ) ~0U )

/* API function error values.  As errno is supported, the FreeRTOS sockets
 * functions return error codes rather than just a pass or fail indication.
 *
 * Like in errno.h, the error codes are defined as positive numbers.
 * However, in case of an error, API 's will still negative values, e.g.
 * return -pdFREERTOS_ERRNO_EWOULDBLOCK;
 * in case an operation would block.
 *
 * The following defines are obsolete, please use -pdFREERTOS_ERRNO_Exxx. */
    #define FREERTOS_SOCKET_ERROR            ( -1 )
    #define FREERTOS_EWOULDBLOCK             ( -pdFREERTOS_ERRNO_EWOULDBLOCK )
    #define FREERTOS_EINVAL                  ( -pdFREERTOS_ERRNO_EINVAL )
    #define FREERTOS_EADDRNOTAVAIL           ( -pdFREERTOS_ERRNO_EADDRNOTAVAIL )
    #define FREERTOS_EADDRINUSE              ( -pdFREERTOS_ERRNO_EADDRINUSE )
    #define FREERTOS_ENOBUFS                 ( -pdFREERTOS_ERRNO_ENOBUFS )
    #define FREERTOS_ENOPROTOOPT             ( -pdFREERTOS_ERRNO_ENOPROTOOPT )
    #define FREERTOS_ECLOSED                 ( -pdFREERTOS_ERRNO_ENOTCONN )

/* Values for the parameters to FreeRTOS_socket(), inline with the Berkeley
 * standard.  See the documentation of FreeRTOS_socket() for more information. */
    #define FREERTOS_AF_INET                 ( 2 )
    #define FREERTOS_AF_INET6                ( 10 )
    #define FREERTOS_SOCK_DGRAM              ( 2 )
    #define FREERTOS_IPPROTO_UDP             ( 17 )
    #define FREERTOS_SOCK_STREAM             ( 1 )
    #define FREERTOS_IPPROTO_TCP             ( 6 )
    #define FREERTOS_SOCK_DEPENDENT_PROTO    ( 0 )

    #define FREERTOS_AF_INET4                FREERTOS_AF_INET
/* Values for xFlags parameter of Receive/Send functions. */
    #define FREERTOS_ZERO_COPY               ( 1 )  /* Can be used with recvfrom(), sendto() and recv(),
                                                     * Indicates that the zero copy interface is being used.
                                                     * See the documentation for FreeRTOS_sockets() for more information. */
    #define FREERTOS_MSG_OOB                 ( 2 )  /* Not used. */
    #define FREERTOS_MSG_PEEK                ( 4 )  /* Can be used with recvfrom() and recv(). */
    #define FREERTOS_MSG_DONTROUTE           ( 8 )  /* Not used. */
    #define FREERTOS_MSG_DONTWAIT            ( 16 ) /* Can be used with recvfrom(), sendto(), recv() and send(). */

/* Values that can be passed in the option name parameter of calls to
 * FreeRTOS_setsockopt(). */
    #define FREERTOS_SO_RCVTIMEO             ( 0 ) /* Used to set the receive time out. */
    #define FREERTOS_SO_SNDTIMEO             ( 1 ) /* Used to set the send time out. */
    #define FREERTOS_SO_UDPCKSUM_OUT         ( 2 ) /* Used to turn the use of the UDP checksum
                                                    * by a socket on or off.  This also doubles
                                                    * as part of an 8-bit bitwise socket option. */
    #if ( ipconfigSOCKET_HAS_USER_SEMAPHORE == 1 )
        #define FREERTOS_SO_SET_SEMAPHORE    ( 3 ) /* Used to set a user's semaphore. */
    #endif

    #if ( ipconfigUSE_TCP == 1 )
        #define FREERTOS_SO_SNDBUF    ( 4 ) /* Set the size of the send buffer (TCP only). */
        #define FREERTOS_SO_RCVBUF    ( 5 ) /* Set the size of the receive buffer (TCP only). */
    #endif

    #if ( ipconfigUSE_CALLBACKS == 1 )

/* Supply pointer to 'F_TCP_UDP_Handler_t' for pvOptionValue parameter in
 * FreeRTOS_setsockopt() */
        #define FREERTOS_SO_TCP_CONN_HANDLER    ( 6 )  /* Install a callback for (dis) connection events. */
        #define FREERTOS_SO_TCP_RECV_HANDLER    ( 7 )  /* Install a callback for receiving TCP data. */
        #define FREERTOS_SO_TCP_SENT_HANDLER    ( 8 )  /* Install a callback for sending TCP data. */
        #define FREERTOS_SO_UDP_RECV_HANDLER    ( 9 )  /* Install a callback for receiving UDP data. */
        #define FREERTOS_SO_UDP_SENT_HANDLER    ( 10 ) /* Install a callback for sending UDP data. */
    #endif

    #if ( ipconfigUSE_TCP == 1 )
        #define FREERTOS_SO_REUSE_LISTEN_SOCKET    ( 11 ) /* When a listening socket gets connected, do not create a new one but re-use it. */
        #define FREERTOS_SO_CLOSE_AFTER_SEND       ( 12 ) /* As soon as the last byte has been transmitted, finalise the connection. */
        #define FREERTOS_SO_WIN_PROPERTIES         ( 13 ) /* Set all buffer and window properties in one call, parameter is pointer to WinProperties_t. */
        #define FREERTOS_SO_SET_FULL_SIZE          ( 14 ) /* Refuse to send packets smaller than MSS. */
        #define FREERTOS_SO_STOP_RX                ( 15 ) /* Temporarily hold up reception, used by streaming client. */
    #endif

    #if ( ipconfigUDP_MAX_RX_PACKETS > 0 )
        #define FREERTOS_SO_UDP_MAX_RX_PACKETS    ( 16 ) /* This option helps to limit the maximum number of packets a UDP socket will buffer. */
    #endif

    #if ( ipconfigSOCKET_HAS_USER_WAKE_CALLBACK == 1 )
        #define FREERTOS_SO_WAKEUP_CALLBACK    ( 17 )
    #endif

    #if ( ipconfigUSE_TCP == 1 )
        #define FREERTOS_SO_SET_LOW_HIGH_WATER            ( 18 )
    #endif
    #define FREERTOS_INADDR_ANY                           ( 0U ) /* The 0.0.0.0 IPv4 address. */

    #if ( 0 )                                                    /* Not Used */
        #define FREERTOS_NOT_LAST_IN_FRAGMENTED_PACKET    ( 0x80 )
        #define FREERTOS_FRAGMENTED_PACKET                ( 0x40 )
    #endif

    #if ( ipconfigUSE_TCP == 1 )
/* Values for 'xHow' flag of FreeRTOS_shutdown(), currently ignored. */
        #define FREERTOS_SHUT_RD      ( 0 )
        #define FREERTOS_SHUT_WR      ( 1 )
        #define FREERTOS_SHUT_RDWR    ( 2 )
    #endif

/* For compatibility with the expected Berkeley sockets naming. */
    #define socklen_t    uint32_t

/**
 * For this limited implementation, only two members are required in the
 * Berkeley style sockaddr structure.
 */
    struct freertos_sockaddr
    {
        uint8_t sin_len;          /**< length of this structure. */
        uint8_t sin_family;       /**< FREERTOS_AF_INET. */
        uint16_t sin_port;        /**< The port. */
        uint32_t sin_flowinfo;    /**< IPv6 flow information, not used in this library. */
        IP_Address_t sin_address; /**< The IPv4/IPv6 address. */
    };
    #define sin_addr              sin_address.ulIP_IPv4
    #define sin_addr4             sin_address.ulIP_IPv4
    #define sin_addr6             sin_address.xIP_IPv6
    #define sin_addrv4            sin_address.ulIP_IPv4
    #define sin_addrv6            sin_address.xIP_IPv6
    #define freertos_sockaddr6    freertos_sockaddr

/* Introduce a short name to make casting easier. */
    typedef struct freertos_sockaddr   xFreertosSocAddr;

/* The socket type itself. */
    struct xSOCKET;
    typedef struct xSOCKET             * Socket_t;
    typedef struct xSOCKET const       * ConstSocket_t;

/**
 * FULL, UP-TO-DATE AND MAINTAINED REFERENCE DOCUMENTATION FOR ALL THESE
 * FUNCTIONS IS AVAILABLE ON THE FOLLOWING URL:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/FreeRTOS_TCP_API_Functions.html
 */

    BaseType_t xSocketValid( const ConstSocket_t xSocket );

/* Binds a socket to a local port number. */
    BaseType_t FreeRTOS_bind( Socket_t xSocket,
                              struct freertos_sockaddr const * pxAddress,
                              socklen_t xAddressLength );

/* Close a socket. */
    BaseType_t FreeRTOS_closesocket( Socket_t xSocket );

/* Conversion Functions */

/** @brief This function converts a human readable string, representing an 48-bit MAC address,
 *  into a 6-byte address. Valid inputs are e.g. "62:48:5:83:A0:b2" and "0-12-34-fe-dc-ba". */
    BaseType_t FreeRTOS_EUI48_pton( const char * pcSource,
                                    uint8_t * pucTarget );

/** @brief This function converts a 48-bit MAC address to a human readable string. */
    void FreeRTOS_EUI48_ntop( const uint8_t * pucSource,
                              char * pcTarget,
                              char cTen,
                              char cSeparator );

    BaseType_t FreeRTOS_inet_pton( BaseType_t xAddressFamily,
                                   const char * pcSource,
                                   void * pvDestination );

    const char * FreeRTOS_inet_ntop( BaseType_t xAddressFamily,
                                     const void * pvSource,
                                     char * pcDestination,
                                     socklen_t uxSize );

/* End Conversion Functions */

/* Sets a socket option. */
    BaseType_t FreeRTOS_setsockopt( Socket_t xSocket,
                                    int32_t lLevel,
                                    int32_t lOptionName,
                                    const void * pvOptionValue,
                                    size_t uxOptionLength );

/* Create a TCP or UDP socket. */
    Socket_t FreeRTOS_socket( BaseType_t xDomain,
                              BaseType_t xType,
                              BaseType_t xProtocol );

    #if ( ipconfigUSE_CALLBACKS == 1 )

/*
 * Callback handlers for a socket
 * User-provided functions will be called for each sockopt callback defined
 * For example:
 * static void xOnTCPConnect( Socket_t xSocket, BaseType_t ulConnected ) {}
 * static BaseType_t xOnTCPReceive( Socket_t xSocket, void * pData, size_t uxLength )
 * {
 *     // handle the message
 *     return pdFALSE; // Not Used
 * }
 * static void xOnTCPSent( Socket_t xSocket, size_t xLength ) {}
 * static BaseType_t xOnUDPReceive( Socket_t xSocket, void * pData, size_t xLength, const struct freertos_sockaddr * pxFrom, const struct freertos_sockaddr * pxDest )
 * {
 *     // handle the message
 *     return pdTRUE; // message processing is finished, don't store
 * }
 * static void xOnUDPSent( Socket_t xSocket, size_t xLength ) {}
 * F_TCP_UDP_Handler_t xHand = { xOnTCPConnect, xOnTCPReceive, xOnTCPSent, xOnUDPReceive, xOnUDPSent };
 * FreeRTOS_setsockopt( sock, 0, FREERTOS_SO_TCP_CONN_HANDLER, ( void * ) &xHand, 0 );
 */

/* Connected callback handler for a TCP Socket. */
        typedef void (* FOnConnected_t )( Socket_t xSocket,
                                          BaseType_t ulConnected );

/* Received callback handler for a TCP Socket.
 * Return value is not currently used. */
        typedef BaseType_t (* FOnTCPReceive_t )( Socket_t xSocket,
                                                 void * pData,
                                                 size_t xLength );

/* Sent callback handler for a TCP Socket. */
        typedef void (* FOnTCPSent_t )( Socket_t xSocket,
                                        size_t xLength );

/* Received callback handler for a UDP Socket.
 * If a positive number is returned, the messages will not be stored in
 * xWaitingPacketsList for later processing by recvfrom(). */
        typedef BaseType_t (* FOnUDPReceive_t ) ( Socket_t xSocket,
                                                  void * pData,
                                                  size_t xLength,
                                                  const struct freertos_sockaddr * pxFrom,
                                                  const struct freertos_sockaddr * pxDest );

/* Sent callback handler for a UDP Socket */
        typedef void (* FOnUDPSent_t )( Socket_t xSocket,
                                        size_t xLength );

/* The following values are used in the lOptionName parameter of setsockopt()
 * to set the callback handlers options. */
        typedef struct xTCP_UDP_HANDLER
        {
            FOnConnected_t pxOnTCPConnected; /* FREERTOS_SO_TCP_CONN_HANDLER */
            FOnTCPReceive_t pxOnTCPReceive;  /* FREERTOS_SO_TCP_RECV_HANDLER */
            FOnTCPSent_t pxOnTCPSent;        /* FREERTOS_SO_TCP_SENT_HANDLER */
            FOnUDPReceive_t pxOnUDPReceive;  /* FREERTOS_SO_UDP_RECV_HANDLER */
            FOnUDPSent_t pxOnUDPSent;        /* FREERTOS_SO_UDP_SENT_HANDLER */
        } F_TCP_UDP_Handler_t;

    #endif /* ( ipconfigUSE_CALLBACKS == 1 ) */

    #if ( ipconfigSUPPORT_SIGNALS != 0 )
/* Send a signal to the task which is waiting for a given socket. */
        BaseType_t FreeRTOS_SignalSocket( Socket_t xSocket );

/* Send a signal to the task which reads from this socket (FromISR version). */
        BaseType_t FreeRTOS_SignalSocketFromISR( Socket_t xSocket,
                                                 BaseType_t * pxHigherPriorityTaskWoken );
    #endif

    #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )

/* The SocketSet_t type is the equivalent to the fd_set type used by the
 * Berkeley API. */
        struct xSOCKET_SET;
        typedef struct xSOCKET_SET         * SocketSet_t;
        typedef struct xSOCKET_SET const   * ConstSocketSet_t;

/* Create a socket set for use with the FreeRTOS_select() function */
        SocketSet_t FreeRTOS_CreateSocketSet( void );

        void FreeRTOS_DeleteSocketSet( SocketSet_t xSocketSet );

/* Block on a "socket set" until an event of interest occurs on a
 * socket within the set. */
        BaseType_t FreeRTOS_select( SocketSet_t xSocketSet,
                                    TickType_t xBlockTimeTicks );

/* For FD_SET and FD_CLR, a combination of the following bits can be used: */
        typedef enum eSELECT_EVENT
        {
            eSELECT_READ = 0x0001,
            eSELECT_WRITE = 0x0002,
            eSELECT_EXCEPT = 0x0004,
            eSELECT_INTR = 0x0008,
            eSELECT_ALL = 0x000F,
            /* Reserved for internal use: */
            eSELECT_CALL_IP = 0x0010,
            /* end */
        } eSelectEvent_t;

/* Clear a set event bit of interest for a socket of the socket set.
 * If all the event bits are clear then the socket will be removed
 * from the socket set. */
        void FreeRTOS_FD_CLR( Socket_t xSocket,
                              SocketSet_t xSocketSet,
                              EventBits_t xBitsToClear );

/* Check if a socket in a socket set has an event bit set. */
        EventBits_t FreeRTOS_FD_ISSET( const ConstSocket_t xSocket,
                                       const ConstSocketSet_t xSocketSet );

/* Add a socket to a socket set, and set the event bits of interest
 * for the added socket. */
        void FreeRTOS_FD_SET( Socket_t xSocket,
                              SocketSet_t xSocketSet,
                              EventBits_t xBitsToSet );

    #endif /* ( ipconfigSUPPORT_SELECT_FUNCTION == 1 ) */

	#include "FreeRTOS_UDP_Sockets.h"
	#include "FreeRTOS_TCP_Sockets.h"

    #ifdef __cplusplus
        } /* extern "C" */
    #endif

#endif /* FREERTOS_SOCKETS_H */
