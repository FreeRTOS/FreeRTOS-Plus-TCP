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

#ifndef FREERTOS_SOCKETS_PRIVATE_H
#define FREERTOS_SOCKETS_PRIVATE_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"
#include "event_groups.h"
#include "list.h"

/* Application level configuration options. */
#include "FreeRTOSIPConfig.h"
#include "FreeRTOSIPConfigDefaults.h"

#include "FreeRTOS_IP_Common.h"

/** @brief A block time of 0 simply means "don't block". */
#define socketDONT_BLOCK    ( ( TickType_t ) 0 )

/** @brief Test if a socket it bound which means it is either included in
 *         xBoundUDPSocketsList or xBoundTCPSocketsList */
#define socketSOCKET_IS_BOUND( pxSocket )    ( listLIST_ITEM_CONTAINER( &( pxSocket )->xBoundSocketListItem ) != NULL )

/* The ItemValue of the sockets xBoundSocketListItem member holds the socket's
 * port number. */
/** @brief Set the port number for the socket in the xBoundSocketListItem. */
#define socketSET_SOCKET_PORT( pxSocket, usPort )    listSET_LIST_ITEM_VALUE( ( &( ( pxSocket )->xBoundSocketListItem ) ), ( usPort ) )

/** @brief Get the port number for the socket in the xBoundSocketListItem. */
#define socketGET_SOCKET_PORT( pxSocket )            listGET_LIST_ITEM_VALUE( ( &( ( pxSocket )->xBoundSocketListItem ) ) )

typedef struct xSOCKET FreeRTOS_Socket_t;

/**
 * Structure to hold the information about a UDP socket.
 */
typedef struct UDPSOCKET
{
    List_t xWaitingPacketsList;   /**< Incoming packets */
    #if ( ipconfigUDP_MAX_RX_PACKETS > 0 )
        UBaseType_t uxMaxPackets; /**< Protection: limits the number of packets buffered per socket */
    #endif /* ipconfigUDP_MAX_RX_PACKETS */
    #if ( ipconfigUSE_CALLBACKS == 1 )
        FOnUDPReceive_t pxHandleReceive; /**<
                                          * In case of a UDP socket:
                                          * typedef void (* FOnUDPReceive_t) (Socket_t xSocket, void *pData, size_t xLength, struct freertos_sockaddr *pxAddr );
                                          */
        FOnUDPSent_t pxHandleSent;       /**< Function pointer to handle the events after a successful send. */
    #endif /* ipconfigUSE_CALLBACKS */
} IPUDPSocket_t;

/* Formally typedef'd as eSocketEvent_t. */
enum eSOCKET_EVENT
{
    eSOCKET_RECEIVE = 0x0001,
    eSOCKET_SEND = 0x0002,
    eSOCKET_ACCEPT = 0x0004,
    eSOCKET_CONNECT = 0x0008,
    eSOCKET_BOUND = 0x0010,
    eSOCKET_CLOSED = 0x0020,
    eSOCKET_INTR = 0x0040,
    eSOCKET_ALL = 0x007F,
};

/* For now, the lower 8 bits in 'xEventBits' will be reserved for the above
 * socket events. */
#define SOCKET_EVENT_BIT_COUNT    8

#if ( ipconfigSOCKET_HAS_USER_WAKE_CALLBACK == 1 )
    typedef void (* SocketWakeupCallback_t)( struct xSOCKET * pxSocket );
#endif

/*
 * Look up a local socket by finding a match with the local port.
 */
FreeRTOS_Socket_t * pxUDPSocketLookup( UBaseType_t uxLocalPort );

/*
 * Return the list item from within pxList that has an item value of
 * xWantedItemValue.  If there is no such list item return NULL.
 */
const ListItem_t * pxListFindListItemWithValue( const List_t * pxList,
												TickType_t xWantedItemValue );

/* Get the size of the IP-header.
 * The socket is checked for its type: IPv4 or IPv6.
 * Replaces xIPHeaderSize.
 */
size_t uxIPHeaderSizeSocket( const FreeRTOS_Socket_t * pxSocket );

/*
 * Initialize the socket list data structures for TCP and UDP.
 */
void vNetworkSocketsInit( void );

/*
 * The internal version of bind()
 * If 'ulInternal' is true, it is called by the driver
 * The TCP driver needs to bind a socket at the moment a listening socket
 * creates a new connected socket
 */
BaseType_t vSocketBind( FreeRTOS_Socket_t * pxSocket,
                        struct freertos_sockaddr * pxBindAddress,
                        size_t uxAddressLength,
                        BaseType_t xInternal );

/* Close a socket */
void * vSocketClose( FreeRTOS_Socket_t * pxSocket );

BaseType_t vSocketValid( const FreeRTOS_Socket_t * pxSocket,
                         BaseType_t xProtocol,
                         BaseType_t xIsBound );

/*
 * Currently called for any important event.
 */
void vSocketWakeUpUser( FreeRTOS_Socket_t * pxSocket );

/*
 * Actually a user thing, but because xBoundTCPSocketsList, let it do by the
 * IP-task
 */
#if ( ipconfigHAS_PRINTF != 0 )
    BaseType_t vNetStat( void );
    BaseType_t vUDPNetStat( void );
#endif

#if ( ipconfigUSE_TCP == 1 )

/**
 * Every TCP socket has a buffer space just big enough to store
 * the last TCP header received.
 * As a reference of this field may be passed to DMA, force the
 * alignment to 8 bytes.
 */
    typedef union
    {
        struct
        {
            uint64_t ullAlignmentWord; /**< Increase the alignment of this union by adding a 64-bit variable. */
        } a;                           /**< A struct to increase alignment. */
        struct
        {
            /* The next field only serves to give 'ucLastPacket' a correct
             * alignment of 8 + 2.  See comments in FreeRTOS_IP.h */
            uint8_t ucFillPacket[ ipconfigPACKET_FILLER_SIZE ];
            uint8_t ucLastPacket[ TCP_PACKET_SIZE ];
        } u; /**< The structure to give an alignment of 8 + 2 */
    } LastTCPPacket_t;

/**
 * Note that the values of all short and long integers in these structs
 * are being stored in the native-endian way
 * Translation should take place when accessing any structure which defines
 * network packets, such as IPHeader_t and TCPHeader_t
 */
    typedef struct TCPSOCKET
    {
        IP_Address_t xRemoteIP; /**< IP address of remote machine */
        uint16_t usRemotePort;  /**< Port on remote machine */
        struct
        {
            /* Most compilers do like bit-flags */
            uint32_t
                bMssChange : 1,        /**< This socket has seen a change in MSS */
                bPassAccept : 1,       /**< when true, this socket may be returned in a call to accept() */
                bPassQueued : 1,       /**< when true, this socket is an orphan until it gets connected
                                        * Why an orphan? Because it may not be returned in a accept() call until it
                                        * gets the state eESTABLISHED */
                bReuseSocket : 1,      /**< When a listening socket gets a connection, do not create a new instance but keep on using it */
                bCloseAfterSend : 1,   /**< As soon as the last byte has been transmitted, finalise the connection
                                        * Useful in e.g. FTP connections, where the last data bytes are sent along with the FIN flag */
                bUserShutdown : 1,     /**< User requesting a graceful shutdown */
                bCloseRequested : 1,   /**< Request to finalise the connection */
                bLowWater : 1,         /**< high-water level has been reached. Cleared as soon as 'rx-count < lo-water' */
                bWinChange : 1,        /**< The value of bLowWater has changed, must send a window update */
                bSendKeepAlive : 1,    /**< When this flag is true, a TCP keep-alive message must be send */
                bWaitKeepAlive : 1,    /**< When this flag is true, a TCP keep-alive reply is expected */
                bConnPrepared : 1,     /**< Connecting socket: Message has been prepared */
            #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
                bConnPassed : 1,       /**< Connecting socket: Socket has been passed in a successful select()  */
            #endif /* ipconfigSUPPORT_SELECT_FUNCTION */
            bFinAccepted : 1,          /**< This socket has received (or sent) a FIN and accepted it */
                bFinSent : 1,          /**< We've sent out a FIN */
                bFinRecv : 1,          /**< We've received a FIN from our peer */
                bFinAcked : 1,         /**< Our FIN packet has been acked */
                bFinLast : 1,          /**< The last ACK (after FIN and FIN+ACK) has been sent or will be sent by the peer */
                bRxStopped : 1,        /**< Application asked to temporarily stop reception */
                bMallocError : 1,      /**< There was an error allocating a stream */
                bWinScaling : 1;       /**< A TCP-Window Scaling option was offered and accepted in the SYN phase. */
        } bits;                        /**< The bits structure */
        uint32_t ulHighestRxAllowed;   /**< The highest sequence number that we can receive at any moment */
        uint16_t usTimeout;            /**< Time (in ticks) after which this socket needs attention */
        uint16_t usMSS;                /**< Current Maximum Segment Size */
        uint16_t usChildCount;         /**< In case of a listening socket: number of connections on this port number */
        uint16_t usBacklog;            /**< In case of a listening socket: maximum number of concurrent connections on this port number */
        uint8_t ucRepCount;            /**< Send repeat count, for retransmissions
                                        * This counter is separate from the xmitCount in the
                                        * TCP win segments */
        eIPTCPState_t eTCPState;       /**< TCP state: see eTCP_STATE */
        struct xSOCKET * pxPeerSocket; /**< for server socket: child, for child socket: parent */
        #if ( ipconfigTCP_KEEP_ALIVE == 1 )
            uint8_t ucKeepRepCount;
            TickType_t xLastAliveTime; /**< The last value of keepalive time.*/
        #endif /* ipconfigTCP_KEEP_ALIVE */
        #if ( ipconfigTCP_HANG_PROTECTION == 1 )
            TickType_t xLastActTime;                  /**< The last time when hang-protection was done.*/
        #endif /* ipconfigTCP_HANG_PROTECTION */
        size_t uxLittleSpace;                         /**< The value deemed as low amount of space. */
        size_t uxEnoughSpace;                         /**< The value deemed as enough space. */
        size_t uxRxStreamSize;                        /**< The Receive stream size */
        size_t uxTxStreamSize;                        /**< The transmit stream size */
        StreamBuffer_t * rxStream;                    /**< The pointer to the receive stream buffer. */
        StreamBuffer_t * txStream;                    /**< The pointer to the transmit stream buffer. */
        #if ( ipconfigUSE_TCP_WIN == 1 )
            NetworkBufferDescriptor_t * pxAckMessage; /**< The pointer to the ACK message */
        #endif /* ipconfigUSE_TCP_WIN */
        LastTCPPacket_t xPacket;                      /**< Buffer space to store the last TCP header received. */
        uint8_t tcpflags;                             /**< TCP flags */
        #if ( ipconfigUSE_TCP_WIN != 0 )
            uint8_t ucMyWinScaleFactor;               /**< Scaling factor of this device. */
            uint8_t ucPeerWinScaleFactor;             /**< Scaling factor of the peer. */
        #endif
        #if ( ipconfigUSE_CALLBACKS == 1 )
            FOnTCPReceive_t pxHandleReceive;  /**<
                                               * In case of a TCP socket:
                                               * typedef void (* FOnTCPReceive_t) (Socket_t xSocket, void *pData, size_t xLength );
                                               */
            FOnTCPSent_t pxHandleSent;        /**< Function pointer to handle a successful send event.  */
            FOnConnected_t pxHandleConnected; /**< Actually type: typedef void (* FOnConnected_t) (Socket_t xSocket, BaseType_t ulConnected ); */
        #endif /* ipconfigUSE_CALLBACKS */
        uint32_t ulWindowSize;                /**< Current Window size advertised by peer */
        size_t uxRxWinSize;                   /**< Fixed value: size of the TCP reception window */
        size_t uxTxWinSize;                   /**< Fixed value: size of the TCP transmit window */

        TCPWindow_t xTCPWindow;               /**< The TCP window struct*/
    } IPTCPSocket_t;

/*
 * Internal function to add streaming data to a TCP socket. If ulIn == true,
 * data will be added to the rxStream, otherwise to the tXStream.  Normally data
 * will be written with ulOffset == 0, meaning: at the end of the FIFO.  When
 * packet come in out-of-order, an offset will be used to put it in front and
 * the head will not change yet.
 */
    int32_t lTCPAddRxdata( FreeRTOS_Socket_t * pxSocket,
                           size_t uxOffset,
                           const uint8_t * pcData,
                           uint32_t ulByteCount );

    void prvInitialiseTCPFields( FreeRTOS_Socket_t * pxSocket,
                                 size_t uxSocketSize );

/** @brief Handle the socket options FREERTOS_SO_CLOSE_AFTER_SEND.
 */
    BaseType_t prvSetOptionCloseAfterSend( FreeRTOS_Socket_t * pxSocket,
                                           const void * pvOptionValue );

/**
 * @brief Handle the socket option FREERTOS_SO_SET_LOW_HIGH_WATER.
 */
    BaseType_t prvSetOptionLowHighWater( FreeRTOS_Socket_t * pxSocket,
                                         const void * pvOptionValue );

/**
 * @brief Handle the socket option FREERTOS_SO_SET_FULL_SIZE.
 */
    BaseType_t prvSetOptionSetFullSize( FreeRTOS_Socket_t * pxSocket,
                                        const void * pvOptionValue );

/**
 * @brief Handle the socket options FREERTOS_SO_REUSE_LISTEN_SOCKET.
 */
    BaseType_t prvSetOptionReuseListenSocket( FreeRTOS_Socket_t * pxSocket,
                                              const void * pvOptionValue );

/** @brief Handle the socket option FREERTOS_SO_STOP_RX. */
    BaseType_t prvSetOptionStopRX( FreeRTOS_Socket_t * pxSocket,
                                   const void * pvOptionValue );

/**
 * @brief Handle the socket option FREERTOS_SO_WIN_PROPERTIES.
 */
    BaseType_t prvSetOptionTCPWindows( FreeRTOS_Socket_t * pxSocket,
                                       const void * pvOptionValue );

/*
 * Internal function prvSockopt_so_buffer(): sets FREERTOS_SO_SNDBUF or
 * FREERTOS_SO_RCVBUF properties of a socket.
 */
    BaseType_t prvSockopt_so_buffer( FreeRTOS_Socket_t * pxSocket,
                                     int32_t lOptionName,
                                     const void * pvOptionValue );

/*
 * When a child socket gets closed, make sure to update the child-count of the parent
 */
    void prvTCPSetSocketCount( FreeRTOS_Socket_t const * pxSocketToDelete );

/*
 * Close the socket another time.
 */
    void vSocketCloseNextTime( FreeRTOS_Socket_t * pxSocket );

/*
 * Postpone a call to listen() by the IP-task.
 */
    void vSocketListenNextTime( FreeRTOS_Socket_t * pxSocket );

    #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
        EventBits_t vSocketSelectTCP( FreeRTOS_Socket_t * pxSocket );
    #endif /* ( ipconfigSUPPORT_SELECT_FUNCTION == 1 ) */

/*
 * Actually a user thing, but because xBoundTCPSocketsList, let it do by the
 * IP-task
 */
    #if ( ipconfigHAS_PRINTF != 0 )
        BaseType_t vTCPNetStat( void );
    #endif

/*
 * Internal: Sets a new state for a TCP socket and performs the necessary
 * actions like calling a OnConnected handler to notify the socket owner.
 */
    void vTCPStateChange( FreeRTOS_Socket_t * pxSocket,
                          enum eTCP_STATE eTCPState );

/*
 * Lookup a TCP socket, using a multiple matching: both port numbers and
 * return IP address.
 */
    FreeRTOS_Socket_t * pxTCPSocketLookup( uint32_t ulLocalIP,
                                           UBaseType_t uxLocalPort,
                                           IP_Address_t ulRemoteIP,
                                           UBaseType_t uxRemotePort );

    BaseType_t xTCPCheckNewClient( FreeRTOS_Socket_t * pxSocket );

/* At least one socket needs to check for timeouts */
    TickType_t xTCPTimerCheck( BaseType_t xWillSleep );

/*
 * Calculate when this socket needs to be checked to do (re-)transmissions.
 */
    TickType_t prvTCPNextTimeout( struct xSOCKET * pxSocket );

/*
 * For anti-hang protection and TCP keep-alive messages.  Called in two places:
 * after receiving a packet and after a state change.  The socket's alive timer
 * may be reset.
 */
    void prvTCPTouchSocket( struct xSOCKET * pxSocket );

#endif /* ( ipconfigUSE_TCP == 1 ) */

/**
 * Structure to hold information for a socket.
 */
struct xSOCKET
{
	EventBits_t xEventBits;         /**< The eventbits to keep track of events. */
	EventGroupHandle_t xEventGroup; /**< The event group for this socket. */

	/* Most compilers do like bit-flags */
	struct
	{
		uint32_t bIsIPv6 : 1; /**< Non-zero in case the connection is using IPv6. */
		uint32_t bSomeFlag : 1;
	}
	bits;

	ListItem_t xBoundSocketListItem;       /**< Used to reference the socket from a bound sockets list. */
	TickType_t xReceiveBlockTime;          /**< if recv[to] is called while no data is available, wait this amount of time. Unit in clock-ticks */
	TickType_t xSendBlockTime;             /**< if send[to] is called while there is not enough space to send, wait this amount of time. Unit in clock-ticks */

	IP_Address_t xLocalAddress;            /**< Local IP address */
	uint16_t usLocalPort;                  /**< Local port on this machine */
	uint8_t ucSocketOptions;               /**< Socket options */
	uint8_t ucProtocol;                    /**< choice of FREERTOS_IPPROTO_UDP/TCP */
	#if ( ipconfigSOCKET_HAS_USER_SEMAPHORE == 1 )
		SemaphoreHandle_t pxUserSemaphore; /**< The user semaphore */
	#endif /* ipconfigSOCKET_HAS_USER_SEMAPHORE */
	#if ( ipconfigSOCKET_HAS_USER_WAKE_CALLBACK == 1 )
		SocketWakeupCallback_t pxUserWakeCallback; /**< Pointer to the callback function. */
	#endif /* ipconfigSOCKET_HAS_USER_WAKE_CALLBACK */

	#if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
		struct xSOCKET_SET * pxSocketSet; /**< Pointer to the socket set structure */
		EventBits_t xSelectBits;          /**< User may indicate which bits are interesting for this socket. */

		EventBits_t xSocketBits;          /**< These bits indicate the events which have actually occurred.
										   * They are maintained by the IP-task */
	#endif /* ipconfigSUPPORT_SELECT_FUNCTION */
	struct xNetworkEndPoint * pxEndPoint; /**< The end-point to which the socket is bound. */
	/* TCP/UDP specific fields: */
	/* Before accessing any member of this structure, it should be confirmed */
	/* that the protocol corresponds with the type of structure */

	union
	{
		IPUDPSocket_t xUDP;           /**< Union member: UDP socket*/
		#if ( ipconfigUSE_TCP == 1 )
			IPTCPSocket_t xTCP;       /**< Union member: TCP socket */

			uint64_t ullTCPAlignment; /**< Make sure that xTCP is 8-bytes aligned by
									   * declaring a 64-bit variable in the same union */
		#endif /* ipconfigUSE_TCP */
	}
	u; /**< Union of TCP/UDP socket */
};


#if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )

/** @brief Structure for event groups of the Socket Select functions */
    typedef struct xSOCKET_SET
    {
        /** @brief Event group for the socket select function.
         */
        EventGroupHandle_t xSelectGroup;
    } SocketSelect_t;

/** @brief Define the data that must be passed for a 'eSocketSelectEvent'. */
    typedef struct xSocketSelectMessage
    {
        TaskHandle_t xTaskhandle;     /**< Task handle for use in the socket select functionality. */
        SocketSelect_t * pxSocketSet; /**< The event group for the socket select functionality. */
    } SocketSelectMessage_t;

    void vSocketSelect( const SocketSelect_t * pxSocketSet );

#endif /* ( ipconfigSUPPORT_SELECT_FUNCTION == 1 ) */

/* *INDENT-OFF* */
#ifdef __cplusplus
    } /* extern "C" */
#endif
/* *INDENT-ON* */

#endif /* FREERTOS_SOCKETS_PRIVATE_H */

