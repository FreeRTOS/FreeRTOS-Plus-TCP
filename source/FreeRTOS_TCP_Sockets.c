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
 * @file FreeRTOS_TCP_Sockets.c
 * @brief Implements the TCP Sockets API based on Berkeley sockets for the FreeRTOS+TCP network
 *        stack. Sockets are used by the application processes to interact with the IP-task
 *        which in turn interacts with the hardware.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "event_groups.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_TCP_Sockets.h"
#include "FreeRTOS_Sockets_Private.h"
#if ( ipconfigUSE_IPv4 != 0 )
    #include "FreeRTOS_IPv4_Sockets.h"
#endif
#if ( ipconfigUSE_IPv6 != 0 )
    #include "FreeRTOS_IPv6_Sockets.h"
#endif
#include "FreeRTOS_TCP_Transmission.h"
#include "FreeRTOS_TCP_State_Handling.h"

/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
#if ( ipconfigUSE_TCP == 1 )
/* *INDENT-ON* */

/** @brief
 * Define a maximum period of time (ms) to leave a TCP-socket unattended.
 * When a TCP timer expires, retries and keep-alive messages will be checked.
 */
#ifndef tcpMAXIMUM_TCP_WAKEUP_TIME_MS
    #define tcpMAXIMUM_TCP_WAKEUP_TIME_MS    20000U
#endif

/* Some helper macro's for defining the 20/80 % limits of uxLittleSpace / uxEnoughSpace. */
#define sock20_PERCENT     ( 20U )  /**< 20% of the defined limit. */
#define sock80_PERCENT     ( 80U )  /**< 80% of the defined limit. */
#define sock100_PERCENT    ( 100U ) /**< 100% of the defined limit. */

/*-----------------------------------------------------------*/

/*
 * Check if it makes any sense to wait for a connect event.
 * It may return: -EINPROGRESS, -EAGAIN, or 0 for OK.
 */
static BaseType_t bMayConnect( FreeRTOS_Socket_t const * pxSocket );

static FreeRTOS_Socket_t * prvAcceptWaitClient( FreeRTOS_Socket_t * pxParentSocket,
                                                struct freertos_sockaddr * pxAddress,
                                                socklen_t * pxAddressLength );

/** @brief Read the data from the stream buffer.
 */
static BaseType_t prvRecvData( FreeRTOS_Socket_t * pxSocket,
                               void * pvBuffer,
                               size_t uxBufferLength,
                               BaseType_t xFlags );

/** @brief This routine will wait for data to arrive in the stream buffer.
 */
static BaseType_t prvRecvWait( const FreeRTOS_Socket_t * pxSocket,
                               EventBits_t * pxEventBits,
                               BaseType_t xFlags );

/*
 * Called from FreeRTOS_connect(): make some checks and if allowed, send a
 * message to the IP-task to start connecting to a remote socket
 */
static BaseType_t prvTCPConnectStart( FreeRTOS_Socket_t * pxSocket,
                                      struct freertos_sockaddr const * pxAddress );

/*
 * Create a txStream or a rxStream, depending on the parameter 'xIsInputStream'
 */
static StreamBuffer_t * prvTCPCreateStream( FreeRTOS_Socket_t * pxSocket,
                                            BaseType_t xIsInputStream );

/*
 * Called from FreeRTOS_send(): some checks which will be done before
 * sending a TCP packed.
 */
static int32_t prvTCPSendCheck( FreeRTOS_Socket_t * pxSocket,
                                size_t uxDataLength );

/**
 * @brief This function tries to send TCP-data in a loop with a time-out.
 */
static BaseType_t prvTCPSendLoop( FreeRTOS_Socket_t * pxSocket,
                                  const void * pvBuffer,
                                  size_t uxDataLength,
                                  BaseType_t xFlags );

#if ( ipconfigUSE_CALLBACKS == 1 )

/** @brief The application can attach callback functions to a socket. In this function,
 *         called by lTCPAddRxdata(), the TCP reception handler will be called. */
    static void vTCPAddRxdata_Callback( FreeRTOS_Socket_t * pxSocket,
                                        const uint8_t * pcData,
                                        uint32_t ulByteCount );
#endif /* #if ( ipconfigUSE_CALLBACKS == 1 ) */

static void vTCPAddRxdata_Stored( FreeRTOS_Socket_t * pxSocket );

#if ( ipconfigHAS_PRINTF != 0 )
/** @brief A helper function of vTCPNetStat(), see below. */
    static void vTCPNetStat_TCPSocket( const FreeRTOS_Socket_t * pxSocket );
#endif

/* Check a single socket for retransmissions and timeouts */
static BaseType_t xTCPSocketCheck( FreeRTOS_Socket_t * pxSocket );

/*-----------------------------------------------------------*/

/** @brief When closing a socket an event is posted to the Network Event Queue.
 *         If the queue is full, then the event is not posted and the socket
 *         can be orphaned. To prevent this, the below variable is used to keep
 *         track of any socket which needs to be closed. This variable can be
 *         accessed by the IP task only. Thus, preventing any race condition.
 */
/* MISRA Ref 8.9.1 [File scoped variables] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-89 */
/* coverity[misra_c_2012_rule_8_9_violation] */
static FreeRTOS_Socket_t * xSocketToClose = NULL;

/** @brief When a connection is coming in on a reusable socket, and the
 *         SYN phase times out, the socket must be put back into eTCP_LISTEN
 *         mode, so it can accept a new connection again.
 *         This variable can be accessed by the IP task only. Thus, preventing any
 *         race condition.
 */
/* MISRA Ref 8.9.1 [File scoped variables] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-89 */
/* coverity[misra_c_2012_rule_8_9_violation] */
static FreeRTOS_Socket_t * xSocketToListen = NULL;

extern List_t xBoundTCPSocketsList;

/*-----------------------------------------------------------*/

/**
 * @brief Check if it makes any sense to wait for a connect event.
 *
 * @param[in] pxSocket: The socket trying to connect.
 *
 * @return It may return: -EINPROGRESS, -EAGAIN, or 0 for OK.
 */
static BaseType_t bMayConnect( FreeRTOS_Socket_t const * pxSocket )
{
    BaseType_t xResult;

    eIPTCPState_t eState = pxSocket->u.xTCP.eTCPState;

    switch( eState )
    {
        case eCLOSED:
        case eCLOSE_WAIT:
            xResult = 0;
            break;

        case eCONNECT_SYN:
            xResult = -pdFREERTOS_ERRNO_EINPROGRESS;
            break;

        case eTCP_LISTEN:
        case eSYN_FIRST:
        case eSYN_RECEIVED:
        case eESTABLISHED:
        case eFIN_WAIT_1:
        case eFIN_WAIT_2:
        case eCLOSING:
        case eLAST_ACK:
        case eTIME_WAIT:
        default:
            xResult = -pdFREERTOS_ERRNO_EAGAIN;
            break;
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Check if a new connection has come in for a socket in listen mode.
 *
 * @param[in] pxParentSocket : The parent socket, which is in listening mode.
 * @param[out] pxAddress : The address of the peer will be filled in 'pxAddress'.
 * @param[in] pxAddressLength : The actual size of the space pointed to by 'pxAddress'.
 * @return A new connected socket or NULL.
 */
static FreeRTOS_Socket_t * prvAcceptWaitClient( FreeRTOS_Socket_t * pxParentSocket,
                                                struct freertos_sockaddr * pxAddress,
                                                socklen_t * pxAddressLength )
{
    FreeRTOS_Socket_t * pxClientSocket = NULL;

    /* Is there a new client? */
    vTaskSuspendAll();
    {
        if( pxParentSocket->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED )
        {
            pxClientSocket = pxParentSocket->u.xTCP.pxPeerSocket;
        }
        else
        {
            pxClientSocket = pxParentSocket;
        }

        if( pxClientSocket != NULL )
        {
            pxParentSocket->u.xTCP.pxPeerSocket = NULL;

            /* Is it still not taken ? */
            if( pxClientSocket->u.xTCP.bits.bPassAccept != pdFALSE_UNSIGNED )
            {
                pxClientSocket->u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;
            }
            else
            {
                pxClientSocket = NULL;
            }
        }
    }
    ( void ) xTaskResumeAll();

    if( pxClientSocket != NULL )
    {
        if( pxAddressLength != NULL )
        {
            *pxAddressLength = sizeof( struct freertos_sockaddr );
        }

        if( pxClientSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
        {
            if( pxAddress != NULL )
            {
                pxAddress->sin_family = FREERTOS_AF_INET6;
                /* Copy IP-address and port number. */
                ( void ) memcpy( pxAddress->sin_addr6.ucBytes, pxClientSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                pxAddress->sin_port = FreeRTOS_ntohs( pxClientSocket->u.xTCP.usRemotePort );
            }
        }
        else
        {
            if( pxAddress != NULL )
            {
                pxAddress->sin_family = FREERTOS_AF_INET4;
                /* Copy IP-address and port number. */
                pxAddress->sin_addr = FreeRTOS_ntohl( pxClientSocket->u.xTCP.xRemoteIP.ulIP_IPv4 );
                pxAddress->sin_port = FreeRTOS_ntohs( pxClientSocket->u.xTCP.usRemotePort );
            }
        }
    }

    return pxClientSocket;
}
/*-----------------------------------------------------------*/

/**
 * @brief After all checks have been done in FreeRTOS_recv()
 *        read the data from the stream buffer.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[out] pvBuffer: The buffer to store the incoming data in.
 * @param[in] uxBufferLength: The length of the buffer so that the function
 *                            does not do out of bound access.
 * @param[in] xFlags: The flags for conveying preference. This routine
 *                    will check for 'FREERTOS_ZERO_COPY and/or'.
 *
 * @return The number of bytes actually received and stored in the pvBuffer.
 */
static BaseType_t prvRecvData( FreeRTOS_Socket_t * pxSocket,
                               void * pvBuffer,
                               size_t uxBufferLength,
                               BaseType_t xFlags )
{
    BaseType_t xByteCount;

    if( ( ( uint32_t ) xFlags & ( uint32_t ) FREERTOS_ZERO_COPY ) == 0U )
    {
        BaseType_t xIsPeek = ( ( ( uint32_t ) xFlags & ( uint32_t ) FREERTOS_MSG_PEEK ) != 0U ) ? 1L : 0L;

        xByteCount = ( BaseType_t )
                     uxStreamBufferGet( pxSocket->u.xTCP.rxStream,
                                        0U,
                                        ( uint8_t * ) pvBuffer,
                                        ( size_t ) uxBufferLength,
                                        xIsPeek );

        if( pxSocket->u.xTCP.bits.bLowWater != pdFALSE_UNSIGNED )
        {
            /* We had reached the low-water mark, now see if the flag
             * can be cleared */
            size_t uxFrontSpace = uxStreamBufferFrontSpace( pxSocket->u.xTCP.rxStream );

            if( uxFrontSpace >= pxSocket->u.xTCP.uxEnoughSpace )
            {
                pxSocket->u.xTCP.bits.bLowWater = pdFALSE_UNSIGNED;
                pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
                pxSocket->u.xTCP.usTimeout = 1U; /* because bLowWater is cleared. */
                ( void ) xSendEventToIPTask( eTCPTimerEvent );
            }
        }
    }
    else
    {
        /* Zero-copy reception of data: pvBuffer is a pointer to a pointer. */
        xByteCount = ( BaseType_t ) uxStreamBufferGetPtr( pxSocket->u.xTCP.rxStream, ( uint8_t ** ) pvBuffer );
    }

    return xByteCount;
}
/*-----------------------------------------------------------*/

/**
 * @brief After FreeRTOS_recv() has checked the validity of the parameters,
 *        this routine will wait for data to arrive in the stream buffer.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[out] pxEventBits: A bit-mask of socket events will be set:
 *             eSOCKET_RECEIVE, eSOCKET_CLOSED, and or eSOCKET_INTR.
 * @param[in] xFlags: flags passed by the user, only 'FREERTOS_MSG_DONTWAIT'
 *            is checked in this function.
 */
static BaseType_t prvRecvWait( const FreeRTOS_Socket_t * pxSocket,
                               EventBits_t * pxEventBits,
                               BaseType_t xFlags )
{
    BaseType_t xByteCount = 0;
    TickType_t xRemainingTime;
    BaseType_t xTimed = pdFALSE;
    TimeOut_t xTimeOut;
    EventBits_t xEventBits = ( EventBits_t ) 0U;

    if( pxSocket->u.xTCP.rxStream != NULL )
    {
        xByteCount = ( BaseType_t ) uxStreamBufferGetSize( pxSocket->u.xTCP.rxStream );
    }

    while( xByteCount == 0 )
    {
        eIPTCPState_t eType = ( eIPTCPState_t ) pxSocket->u.xTCP.eTCPState;

        if( ( eType == eCLOSED ) ||
            ( eType == eCLOSE_WAIT ) || /* (server + client) waiting for a connection termination request from the local user. */
            ( eType == eCLOSING ) )     /* (server + client) waiting for a connection termination request acknowledgement from the remote TCP. */
        {
            /* Return -ENOTCONN, unless there was a malloc failure. */
            xByteCount = -pdFREERTOS_ERRNO_ENOTCONN;

            if( pxSocket->u.xTCP.bits.bMallocError != pdFALSE_UNSIGNED )
            {
                /* The no-memory error has priority above the non-connected error.
                 * Both are fatal and will lead to closing the socket. */
                xByteCount = -pdFREERTOS_ERRNO_ENOMEM;
            }

            break;
        }

        if( xTimed == pdFALSE )
        {
            /* Only in the first round, check for non-blocking. */
            xRemainingTime = pxSocket->xReceiveBlockTime;

            if( xRemainingTime == ( TickType_t ) 0U )
            {
                #if ( ipconfigSUPPORT_SIGNALS != 0 )
                    {
                        /* Just check for the interrupt flag. */
                        xEventBits = xEventGroupWaitBits( pxSocket->xEventGroup, ( EventBits_t ) eSOCKET_INTR,
                                                          pdTRUE /*xClearOnExit*/, pdFALSE /*xWaitAllBits*/, socketDONT_BLOCK );
                    }
                #endif /* ipconfigSUPPORT_SIGNALS */
                break;
            }

            if( ( ( uint32_t ) xFlags & ( uint32_t ) FREERTOS_MSG_DONTWAIT ) != 0U )
            {
                break;
            }

            /* Don't get here a second time. */
            xTimed = pdTRUE;

            /* Fetch the current time. */
            vTaskSetTimeOutState( &xTimeOut );
        }

        /* Has the timeout been reached? */
        if( xTaskCheckForTimeOut( &xTimeOut, &xRemainingTime ) != pdFALSE )
        {
            break;
        }

        /* Block until there is a down-stream event. */
        xEventBits = xEventGroupWaitBits( pxSocket->xEventGroup,
                                          ( EventBits_t ) eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED | ( EventBits_t ) eSOCKET_INTR,
                                          pdTRUE /*xClearOnExit*/, pdFALSE /*xWaitAllBits*/, xRemainingTime );
        #if ( ipconfigSUPPORT_SIGNALS != 0 )
            {
                if( ( xEventBits & ( EventBits_t ) eSOCKET_INTR ) != 0U )
                {
                    break;
                }
            }
        #else
            {
                ( void ) xEventBits;
            }
        #endif /* ipconfigSUPPORT_SIGNALS */

        if( pxSocket->u.xTCP.rxStream != NULL )
        {
            xByteCount = ( BaseType_t ) uxStreamBufferGetSize( pxSocket->u.xTCP.rxStream );
        }
    } /* while( xByteCount == 0 ) */

    *( pxEventBits ) = xEventBits;

    return xByteCount;
}
/*-----------------------------------------------------------*/

/**
 * @brief Called from #FreeRTOS_connect(): make some checks and if allowed,
 *        send a message to the IP-task to start connecting to a remote socket.
 *
 * @param[in] pxSocket: The socket attempting to connect to a remote port.
 * @param[in] pxAddress: The address the socket is trying to connect to.
 *
 * @return 0 on successful checks or a negative error code.
 */
static BaseType_t prvTCPConnectStart( FreeRTOS_Socket_t * pxSocket,
                                      struct freertos_sockaddr const * pxAddress )
{
    BaseType_t xResult = 0;

    if( pxAddress == NULL )
    {
        /* NULL address passed to the function. Invalid value. */
        xResult = -pdFREERTOS_ERRNO_EINVAL;
    }
    else if( vSocketValid( pxSocket, FREERTOS_IPPROTO_TCP, pdFALSE ) == pdFALSE )
    {
        /* Not a valid socket or wrong type */
        xResult = -pdFREERTOS_ERRNO_EBADF;
    }
    else if( FreeRTOS_issocketconnected( pxSocket ) > 0 )
    {
        /* The socket is already connected. */
        xResult = -pdFREERTOS_ERRNO_EISCONN;
    }
    else if( !socketSOCKET_IS_BOUND( pxSocket ) )
    {
        /* Bind the socket to the port that the client task will send from.
         * Non-standard, so the error returned is that returned by bind(). */
        xResult = FreeRTOS_bind( pxSocket, NULL, 0U );
    }
    else
    {
        /* The socket is valid, not yet connected, and already bound to a port number. */
    }

    if( xResult == 0 )
    {
        /* Check if it makes any sense to wait for a connect event, this condition
         * might change while sleeping, so it must be checked within each loop */
        xResult = bMayConnect( pxSocket ); /* -EINPROGRESS, -EAGAIN, or 0 for OK */

        /* Start the connect procedure, kernel will start working on it */
        if( xResult == 0 )
        {
            pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;
            pxSocket->u.xTCP.ucRepCount = 0U;

            if( pxAddress->sin_family == ( uint8_t ) FREERTOS_AF_INET6 )
            {
                pxSocket->bits.bIsIPv6 = pdTRUE_UNSIGNED;
                FreeRTOS_printf( ( "FreeRTOS_connect: %u to %pip port %u\n",
                                   pxSocket->usLocalPort, pxAddress->sin_addr6.ucBytes, FreeRTOS_ntohs( pxAddress->sin_port ) ) );
                ( void ) memcpy( pxSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, pxAddress->sin_addr6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
            }
            else
            {
                pxSocket->bits.bIsIPv6 = pdFALSE_UNSIGNED;
                FreeRTOS_printf( ( "FreeRTOS_connect: %u to %lxip:%u\n",
                                   pxSocket->usLocalPort, FreeRTOS_ntohl( pxAddress->sin_addr ), FreeRTOS_ntohs( pxAddress->sin_port ) ) );
                pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4 = FreeRTOS_ntohl( pxAddress->sin_addr );
            }

            /* Port on remote machine. */
            pxSocket->u.xTCP.usRemotePort = FreeRTOS_ntohs( pxAddress->sin_port );

            /* (client) internal state: socket wants to send a connect. */
            vTCPStateChange( pxSocket, eCONNECT_SYN );

            /* To start an active connect. */
            pxSocket->u.xTCP.usTimeout = 1U;

            if( xSendEventToIPTask( eTCPTimerEvent ) != pdPASS )
            {
                xResult = -pdFREERTOS_ERRNO_ECANCELED;
            }
        }
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Create the stream buffer for the given socket.
 *
 * @param[in] pxSocket: the socket to create the stream for.
 * @param[in] xIsInputStream: Is this input stream? pdTRUE/pdFALSE?
 *
 * @return The stream buffer.
 */
static StreamBuffer_t * prvTCPCreateStream( FreeRTOS_Socket_t * pxSocket,
                                            BaseType_t xIsInputStream )
{
    StreamBuffer_t * pxBuffer;
    size_t uxLength;
    size_t uxSize;

    /* Now that a stream is created, the maximum size is fixed before
     * creation, it could still be changed with setsockopt(). */
    if( xIsInputStream != pdFALSE )
    {
        size_t uxLittlePerc = sock20_PERCENT;
        size_t uxEnoughPerc = sock80_PERCENT;
        size_t uxSegmentCount = pxSocket->u.xTCP.uxRxStreamSize / pxSocket->u.xTCP.usMSS;
        static const struct Percent
        {
            size_t uxPercLittle, uxPercEnough;
        }
        xPercTable[] =
        {
            { 0U,  100U }, /* 1 segment. */
            { 50U, 100U }, /* 2 segments. */
            { 34U, 100U }, /* 3 segments. */
            { 25U, 100U }, /* 4 segments. */
        };

        if( ( uxSegmentCount > 0U ) &&
            ( uxSegmentCount <= ARRAY_USIZE( xPercTable ) ) )
        {
            uxLittlePerc = xPercTable[ uxSegmentCount - 1U ].uxPercLittle;
            uxEnoughPerc = xPercTable[ uxSegmentCount - 1U ].uxPercEnough;
        }

        uxLength = pxSocket->u.xTCP.uxRxStreamSize;

        if( pxSocket->u.xTCP.uxLittleSpace == 0U )
        {
            pxSocket->u.xTCP.uxLittleSpace = ( uxLittlePerc * pxSocket->u.xTCP.uxRxStreamSize ) / sock100_PERCENT;
        }

        if( pxSocket->u.xTCP.uxEnoughSpace == 0U )
        {
            pxSocket->u.xTCP.uxEnoughSpace = ( uxEnoughPerc * pxSocket->u.xTCP.uxRxStreamSize ) / sock100_PERCENT;
        }
    }
    else
    {
        uxLength = pxSocket->u.xTCP.uxTxStreamSize;
    }

    /* Add an extra 4 (or 8) bytes. */
    uxLength += sizeof( size_t );

    /* And make the length a multiple of sizeof( size_t ). */
    uxLength &= ~( sizeof( size_t ) - 1U );

    uxSize = ( sizeof( *pxBuffer ) + uxLength ) - sizeof( pxBuffer->ucArray );

    pxBuffer = ( ( StreamBuffer_t * ) pvPortMallocLarge( uxSize ) );

    if( pxBuffer == NULL )
    {
        FreeRTOS_debug_printf( ( "prvTCPCreateStream: malloc failed\n" ) );
        pxSocket->u.xTCP.bits.bMallocError = pdTRUE;
        vTCPStateChange( pxSocket, eCLOSE_WAIT );
    }
    else
    {
        /* Clear the markers of the stream */
        ( void ) memset( pxBuffer, 0, sizeof( *pxBuffer ) - sizeof( pxBuffer->ucArray ) );
        pxBuffer->LENGTH = ( size_t ) uxLength;

        if( xTCPWindowLoggingLevel != 0 )
        {
            FreeRTOS_debug_printf( ( "prvTCPCreateStream: %cxStream created %u bytes (total %u)\n", ( xIsInputStream != 0 ) ? 'R' : 'T', ( unsigned ) uxLength, ( unsigned ) uxSize ) );
        }

        if( xIsInputStream != 0 )
        {
            iptraceMEM_STATS_CREATE( tcpRX_STREAM_BUFFER, pxBuffer, uxSize );
            pxSocket->u.xTCP.rxStream = pxBuffer;
        }
        else
        {
            iptraceMEM_STATS_CREATE( tcpTX_STREAM_BUFFER, pxBuffer, uxSize );
            pxSocket->u.xTCP.txStream = pxBuffer;
        }
    }

    return pxBuffer;
}
/*-----------------------------------------------------------*/

/**
 * @brief Called from FreeRTOS_send(): some checks which will be done before
 *        sending a TCP packed.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[in] uxDataLength: The length of the data to be sent.
 *
 * @return 0: representing OK, else a negative error code will be returned.
 */
static int32_t prvTCPSendCheck( FreeRTOS_Socket_t * pxSocket,
                                size_t uxDataLength )
{
    int32_t xResult = 1;

    /* Is this a socket of type TCP and is it already bound to a port number ? */
    if( vSocketValid( pxSocket, FREERTOS_IPPROTO_TCP, pdTRUE ) == pdFALSE )
    {
        xResult = -pdFREERTOS_ERRNO_EINVAL;
    }
    else if( pxSocket->u.xTCP.bits.bMallocError != pdFALSE_UNSIGNED )
    {
        xResult = -pdFREERTOS_ERRNO_ENOMEM;
    }
    else if( ( pxSocket->u.xTCP.eTCPState == eCLOSED ) ||
             ( pxSocket->u.xTCP.eTCPState == eCLOSE_WAIT ) ||
             ( pxSocket->u.xTCP.eTCPState == eCLOSING ) )
    {
        xResult = -pdFREERTOS_ERRNO_ENOTCONN;
    }
    else if( pxSocket->u.xTCP.bits.bFinSent != pdFALSE_UNSIGNED )
    {
        /* This TCP connection is closing already, the FIN flag has been sent.
         * Maybe it is still delivering or receiving data.
         * Return OK in order not to get closed/deleted too quickly */
        xResult = 0;
    }
    else if( uxDataLength == 0U )
    {
        /* send() is being called to send zero bytes */
        xResult = 0;
    }
    else if( pxSocket->u.xTCP.txStream == NULL )
    {
        /* Create the outgoing stream only when it is needed */
        ( void ) prvTCPCreateStream( pxSocket, pdFALSE );

        if( pxSocket->u.xTCP.txStream == NULL )
        {
            xResult = -pdFREERTOS_ERRNO_ENOMEM;
        }
    }
    else
    {
        /* Nothing. */
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief This internal function will try to send as many bytes as possible to a TCP-socket.
 *
 * @param[in] pxSocket : The socket owning the connection.
 * @param[in] pvBuffer : The buffer containing the data to be sent.
 * @param[in] uxDataLength : The number of bytes contained in the buffer.
 * @param[in] xFlags : Only the flag 'FREERTOS_MSG_DONTWAIT' will be tested.
 *
 * @result The number of bytes queued for transmission.
 */
static BaseType_t prvTCPSendLoop( FreeRTOS_Socket_t * pxSocket,
                                  const void * pvBuffer,
                                  size_t uxDataLength,
                                  BaseType_t xFlags )
{
    /* The number of bytes sent. */
    BaseType_t xBytesSent = 0;
    /* xBytesLeft is the number of bytes that still must be sent. */
    BaseType_t xBytesLeft = ( BaseType_t ) uxDataLength;
    /* xByteCount is number of bytes that can be sent now. */
    BaseType_t xByteCount = ( BaseType_t ) uxStreamBufferGetSpace( pxSocket->u.xTCP.txStream );
    TickType_t xRemainingTime;
    BaseType_t xTimed = pdFALSE;
    TimeOut_t xTimeOut;
    const uint8_t * pucSource = ( const uint8_t * ) pvBuffer;

    /* While there are still bytes to be sent. */
    while( xBytesLeft > 0 )
    {
        /* If txStream has space. */
        if( xByteCount > 0 )
        {
            BaseType_t xCloseAfterSend = pdFALSE;

            /* Don't send more than necessary. */
            if( xByteCount > xBytesLeft )
            {
                xByteCount = xBytesLeft;
            }

            if( ( pxSocket->u.xTCP.bits.bCloseAfterSend != pdFALSE_UNSIGNED ) &&
                ( xByteCount == xBytesLeft ) )
            {
                xCloseAfterSend = pdTRUE;

                /* Now suspend the scheduler: sending the last data and
                 * setting bCloseRequested must be done together */
                vTaskSuspendAll();
                pxSocket->u.xTCP.bits.bCloseRequested = pdTRUE_UNSIGNED;

                /* The flag 'bCloseAfterSend' can be set before sending data
                 * using setsockopt()
                 *
                 * When the last data packet is being sent out, a FIN flag will
                 * be included to let the peer know that no more data is to be
                 * expected.  The use of 'bCloseAfterSend' is not mandatory, it
                 * is just a faster way of transferring files (e.g. when using
                 * FTP). */
            }

            xByteCount = ( BaseType_t ) uxStreamBufferAdd( pxSocket->u.xTCP.txStream, 0U, pucSource, ( size_t ) xByteCount );

            if( xCloseAfterSend == pdTRUE )
            {
                /* Now when the IP-task transmits the data, it will also
                 * see that bCloseRequested is true and include the FIN
                 * flag to start closure of the connection. */
                ( void ) xTaskResumeAll();
            }

            /* Send a message to the IP-task so it can work on this
            * socket.  Data is sent, let the IP-task work on it. */
            pxSocket->u.xTCP.usTimeout = 1U;

            if( xIsCallingFromIPTask() == pdFALSE )
            {
                /* Only send a TCP timer event when not called from the
                 * IP-task. */
                ( void ) xSendEventToIPTask( eTCPTimerEvent );
            }

            xBytesLeft -= xByteCount;
            xBytesSent += xByteCount;

            if( ( xBytesLeft == 0 ) && ( pvBuffer == NULL ) )
            {
                /* pvBuffer can be NULL in case TCP zero-copy transmissions are used. */
                break;
            }

            /* As there are still bytes left to be sent, increase the
             * data pointer. */
            pucSource = &( pucSource[ xByteCount ] );
        } /* if( xByteCount > 0 ) */

        /* Not all bytes have been sent. In case the socket is marked as
         * blocking sleep for a while. */
        if( xTimed == pdFALSE )
        {
            /* Only in the first round, check for non-blocking. */
            xRemainingTime = pxSocket->xSendBlockTime;

            if( xIsCallingFromIPTask() != pdFALSE )
            {
                /* If this send function is called from within a
                 * call-back handler it may not block, otherwise
                 * chances would be big to get a deadlock: the IP-task
                 * waiting for itself. */
                xRemainingTime = ( TickType_t ) 0U;
            }

            if( xRemainingTime == ( TickType_t ) 0U )
            {
                break;
            }

            if( ( ( uint32_t ) xFlags & ( uint32_t ) FREERTOS_MSG_DONTWAIT ) != 0U )
            {
                break;
            }

            /* Don't get here a second time. */
            xTimed = pdTRUE;

            /* Fetch the current time. */
            vTaskSetTimeOutState( &xTimeOut );
        }
        else
        {
            /* Has the timeout been reached? */
            if( xTaskCheckForTimeOut( &xTimeOut, &xRemainingTime ) != pdFALSE )
            {
                break;
            }
        }

        /* Go sleeping until a SEND or a CLOSE event is received. */
        ( void ) xEventGroupWaitBits( pxSocket->xEventGroup, ( EventBits_t ) eSOCKET_SEND | ( EventBits_t ) eSOCKET_CLOSED,
                                      pdTRUE /*xClearOnExit*/, pdFALSE /*xWaitAllBits*/, xRemainingTime );
        /* See if in a meanwhile there is space in the TX-stream. */
        xByteCount = ( BaseType_t ) uxStreamBufferGetSpace( pxSocket->u.xTCP.txStream );
    } /* while( xBytesLeft > 0 ) */

    return xBytesSent;
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_CALLBACKS == 1 )

/**
 * @brief The application can attach callback functions to a socket. In this function,
 *        called by lTCPAddRxdata(), the TCP reception handler will be called.
 * @param[in] pxSocket: The socket which has received TCP data.
 * @param[in] pcData: The actual data received.
 * @param[in] ulByteCount: The number of bytes that were received.
 */
    static void vTCPAddRxdata_Callback( FreeRTOS_Socket_t * pxSocket,
                                        const uint8_t * pcData,
                                        uint32_t ulByteCount )
    {
        const uint8_t * pucBuffer = pcData;

        /* The socket owner has installed an OnReceive handler. Pass the
         * Rx data, without copying from the rxStream, to the user. */
        for( ; ; )
        {
            uint8_t * ucReadPtr = NULL;
            uint32_t ulCount;

            if( pucBuffer != NULL )
            {
                ucReadPtr = ( uint8_t * ) pucBuffer;
                ulCount = ulByteCount;
                pucBuffer = NULL;
            }
            else
            {
                ulCount = ( uint32_t ) uxStreamBufferGetPtr( pxSocket->u.xTCP.rxStream, &( ucReadPtr ) );
            }

            if( ulCount == 0U )
            {
                break;
            }

            /* For advanced users only: here a pointer to the RX-stream of a socket
             * is passed to an application hook. */
            ( void ) pxSocket->u.xTCP.pxHandleReceive( pxSocket, ucReadPtr, ( size_t ) ulCount );
            /* Forward the tail in the RX stream. */
            ( void ) uxStreamBufferGet( pxSocket->u.xTCP.rxStream, 0U, NULL, ( size_t ) ulCount, pdFALSE );
        }
    }
#endif /* #if ( ipconfigUSE_CALLBACKS == 1 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Called by lTCPAddRxdata(), the received data has just been added to the
 *        RX-stream. When the space is dropped below a threshold, it may set the
 *        bit field 'bLowWater'. Also the socket's events bits for READ will be set.
 * @param[in] pxSocket: the socket that has received new data.
 */
static void vTCPAddRxdata_Stored( FreeRTOS_Socket_t * pxSocket )
{
    /* See if running out of space. */
    if( pxSocket->u.xTCP.bits.bLowWater == pdFALSE_UNSIGNED )
    {
        size_t uxFrontSpace = uxStreamBufferFrontSpace( pxSocket->u.xTCP.rxStream );

        if( uxFrontSpace <= pxSocket->u.xTCP.uxLittleSpace )
        {
            pxSocket->u.xTCP.bits.bLowWater = pdTRUE_UNSIGNED;
            pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;

            /* bLowWater was reached, send the changed window size. */
            pxSocket->u.xTCP.usTimeout = 1U;
            ( void ) xSendEventToIPTask( eTCPTimerEvent );
        }
    }

    /* New incoming data is available, wake up the user.   User's
     * semaphores will be set just before the IP-task goes asleep. */
    pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_RECEIVE;

    #if ipconfigSUPPORT_SELECT_FUNCTION == 1
        {
            if( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_READ ) != 0U )
            {
                pxSocket->xEventBits |= ( ( ( EventBits_t ) eSELECT_READ ) << SOCKET_EVENT_BIT_COUNT );
            }
        }
    #endif
}
/*-----------------------------------------------------------*/

#if ( ipconfigHAS_PRINTF != 0 )

/**
 * @brief A helper function of vTCPNetStat(), see below.
 *
 * @param[in] pxSocket: The socket that needs logging.
 *
 * @return
 */
    static void vTCPNetStat_TCPSocket( const FreeRTOS_Socket_t * pxSocket )
    {
        char pcRemoteIp[ 40 ];
        int xIPWidth = 32;

        #if ( ipconfigTCP_KEEP_ALIVE == 1 )
            TickType_t age = xTaskGetTickCount() - pxSocket->u.xTCP.xLastAliveTime;
        #else
            TickType_t age = 0U;
        #endif

        char ucChildText[ 16 ] = "";

        if( pxSocket->u.xTCP.eTCPState == ( uint8_t ) eTCP_LISTEN )
        {
            /* Using function "snprintf". */
            const int32_t copied_len = snprintf( ucChildText, sizeof( ucChildText ), " %d/%d",
                                                 pxSocket->u.xTCP.usChildCount,
                                                 pxSocket->u.xTCP.usBacklog );
            ( void ) copied_len;
            /* These should never evaluate to false since the buffers are both shorter than 5-6 characters (<=65535) */
            configASSERT( copied_len >= 0 );                                /* LCOV_EXCL_BR_LINE the 'taken' branch will never execute. See the above comment. */
            configASSERT( copied_len < ( int32_t ) sizeof( ucChildText ) ); /* LCOV_EXCL_BR_LINE the 'taken' branch will never execute. See the above comment. */
        }

        if( age > 999999U )
        {
            age = 999999U;
        }

        if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
        {
            ( void ) snprintf( pcRemoteIp,
                               sizeof( pcRemoteIp ),
                               "%pip", pxSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes );
        }
        else
        {
            ( void ) snprintf( pcRemoteIp, sizeof( pcRemoteIp ), "%xip", ( unsigned ) pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4 );
        }

        FreeRTOS_printf( ( "TCP %5u %-*s:%-16xip:%5u %d/%d %-13.13s %6u %6u%s\n",
                           pxSocket->usLocalPort,         /* Local port on this machine */
                           xIPWidth,
                           pcRemoteIp,                    /* IP address of remote machine */
                           pxSocket->u.xTCP.usRemotePort, /* Port on remote machine */
                           ( pxSocket->u.xTCP.rxStream != NULL ) ? 1 : 0,
                           ( pxSocket->u.xTCP.txStream != NULL ) ? 1 : 0,
                           FreeRTOS_GetTCPStateName( pxSocket->u.xTCP.eTCPState ),
                           ( unsigned ) ( ( age > 999999U ) ? 999999U : age ), /* Format 'age' for printing */
                           pxSocket->u.xTCP.usTimeout,
                           ucChildText ) );
    }

#endif /* ( ipconfigHAS_PRINTF != 0 ) */
/*-----------------------------------------------------------*/

/**
 * @brief As soon as a TCP socket timer expires, this function will be called
 *       (from xTCPTimerCheck). It can send a delayed ACK or new data.
 *
 * @param[in] pxSocket: socket to be checked.
 *
 * @return 0 on success, a negative error code on failure. A negative value will be
 *         returned in case the hang-protection has put the socket in a wait-close state.
 *
 * @note Sequence of calling (normally) :
 *   IP-Task:
 *      xTCPTimerCheck()                // Check all sockets ( declared in FreeRTOS_Sockets.c )
 *      xTCPSocketCheck()               // Either send a delayed ACK or call prvTCPSendPacket()
 *      prvTCPSendPacket()              // Either send a SYN or call prvTCPSendRepeated ( regular messages )
 *      prvTCPSendRepeated()            // Send at most 8 messages on a row
 *          prvTCPReturnPacket()        // Prepare for returning
 *          xNetworkInterfaceOutput()   // Sends data to the NIC ( declared in portable/NetworkInterface/xxx )
 */
static BaseType_t xTCPSocketCheck( FreeRTOS_Socket_t * pxSocket )
{
    BaseType_t xResult = 0;
    BaseType_t xReady = pdFALSE;

    if( ( pxSocket->u.xTCP.eTCPState >= eESTABLISHED ) && ( pxSocket->u.xTCP.txStream != NULL ) )
    {
        /* The API FreeRTOS_send() might have added data to the TX stream.  Add
         * this data to the windowing system so it can be transmitted. */
        prvTCPAddTxData( pxSocket );
    }

    #if ( ipconfigUSE_TCP_WIN == 1 )
        {
            if( pxSocket->u.xTCP.pxAckMessage != NULL )
            {
                /* The first task of this regular socket check is to send-out delayed
                 * ACK's. */
                if( pxSocket->u.xTCP.bits.bUserShutdown == pdFALSE_UNSIGNED )
                {
                    /* Earlier data was received but not yet acknowledged.  This
                     * function is called when the TCP timer for the socket expires, the
                     * ACK may be sent now. */
                    if( pxSocket->u.xTCP.eTCPState != eCLOSED )
                    {
                        if( ( xTCPWindowLoggingLevel > 1 ) && ipconfigTCP_MAY_LOG_PORT( pxSocket->usLocalPort ) )
                        {
                            FreeRTOS_debug_printf( ( "Send[%u->%u] del ACK %u SEQ %u (len %u)\n",
                                                     pxSocket->usLocalPort,
                                                     pxSocket->u.xTCP.usRemotePort,
                                                     ( unsigned ) ( pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber - pxSocket->u.xTCP.xTCPWindow.rx.ulFirstSequenceNumber ),
                                                     ( unsigned ) ( pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber - pxSocket->u.xTCP.xTCPWindow.tx.ulFirstSequenceNumber ),
                                                     ( unsigned ) ( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER ) ) );
                        }

                        prvTCPReturnPacket( pxSocket, pxSocket->u.xTCP.pxAckMessage, uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER, ipconfigZERO_COPY_TX_DRIVER );

                        #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
                            {
                                /* The ownership has been passed to the SEND routine,
                                 * clear the pointer to it. */
                                pxSocket->u.xTCP.pxAckMessage = NULL;
                            }
                        #endif /* ipconfigZERO_COPY_TX_DRIVER */
                    }

                    if( prvTCPNextTimeout( pxSocket ) > 1U )
                    {
                        /* Tell the code below that this function is ready. */
                        xReady = pdTRUE;
                    }
                }
                else
                {
                    /* The user wants to perform an active shutdown(), skip sending
                     * the delayed ACK.  The function prvTCPSendPacket() will send the
                     * FIN along with the ACK's. */
                }

                if( pxSocket->u.xTCP.pxAckMessage != NULL )
                {
                    vReleaseNetworkBufferAndDescriptor( pxSocket->u.xTCP.pxAckMessage );
                    pxSocket->u.xTCP.pxAckMessage = NULL;
                }
            }
        }
    #endif /* ipconfigUSE_TCP_WIN */

    if( xReady == pdFALSE )
    {
        /* The second task of this regular socket check is sending out data. */
        if( ( pxSocket->u.xTCP.eTCPState >= eESTABLISHED ) ||
            ( pxSocket->u.xTCP.eTCPState == eCONNECT_SYN ) )
        {
            ( void ) prvTCPSendPacket( pxSocket );
        }

        /* Set the time-out for the next wakeup for this socket. */
        ( void ) prvTCPNextTimeout( pxSocket );

        #if ( ipconfigTCP_HANG_PROTECTION == 1 )
            {
                /* In all (non-connected) states in which keep-alive messages can not be sent
                 * the anti-hang protocol will close sockets that are 'hanging'. */
                xResult = prvTCPStatusAgeCheck( pxSocket );
            }
        #endif
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Called by FreeRTOS_socket(), it will initialise some essential TCP
 *        fields in the socket.
 * @param[in] pxSocket: the TCP socket to be initialised.
 * @param[in] uxSocketSize: The calculated size of the socket, only used to
 *                          gather memory usage statistics.
 */
void prvInitialiseTCPFields( FreeRTOS_Socket_t * pxSocket,
                             size_t uxSocketSize )
{
    ( void ) uxSocketSize;
    /* Lint wants at least a comment, in case the macro is empty. */
    iptraceMEM_STATS_CREATE( tcpSOCKET_TCP, pxSocket, uxSocketSize + sizeof( StaticEventGroup_t ) );
    /* StreamSize is expressed in number of bytes */
    /* Round up buffer sizes to nearest multiple of MSS */
    pxSocket->u.xTCP.usMSS = ( uint16_t ) ipconfigTCP_MSS;

    if( pxSocket->bits.bIsIPv6 != 0U )
    {
        uint16_t usDifference = ipSIZE_OF_IPv6_HEADER - ipSIZE_OF_IPv4_HEADER;

        if( pxSocket->u.xTCP.usMSS > usDifference )
        {
            pxSocket->u.xTCP.usMSS -= ( uint16_t ) usDifference;
        }
    }

    pxSocket->u.xTCP.uxRxStreamSize = ( size_t ) ipconfigTCP_RX_BUFFER_LENGTH;
    pxSocket->u.xTCP.uxTxStreamSize = ( size_t ) FreeRTOS_round_up( ipconfigTCP_TX_BUFFER_LENGTH, ipconfigTCP_MSS );
    /* Use half of the buffer size of the TCP windows */
    #if ( ipconfigUSE_TCP_WIN == 1 )
        {
            pxSocket->u.xTCP.uxRxWinSize = FreeRTOS_max_size_t( 1U, ( pxSocket->u.xTCP.uxRxStreamSize / 2U ) / ipconfigTCP_MSS );
            pxSocket->u.xTCP.uxTxWinSize = FreeRTOS_max_size_t( 1U, ( pxSocket->u.xTCP.uxTxStreamSize / 2U ) / ipconfigTCP_MSS );
        }
    #else
        {
            pxSocket->u.xTCP.uxRxWinSize = 1U;
            pxSocket->u.xTCP.uxTxWinSize = 1U;
        }
    #endif

    /* The above values are just defaults, and can be overridden by
     * calling FreeRTOS_setsockopt().  No buffers will be allocated until a
     * socket is connected and data is exchanged. */
}
/*-----------------------------------------------------------*/

/**
 * @brief Calculate after how much time this socket needs to be checked again.
 *
 * @param[in] pxSocket: The socket to be checked.
 *
 * @return The number of clock ticks before the timer expires.
 */
TickType_t prvTCPNextTimeout( struct xSOCKET * pxSocket )
{
    TickType_t ulDelayMs = ( TickType_t ) tcpMAXIMUM_TCP_WAKEUP_TIME_MS;

    if( pxSocket->u.xTCP.eTCPState == eCONNECT_SYN )
    {
        /* The socket is actively connecting to a peer. */
        if( pxSocket->u.xTCP.bits.bConnPrepared != pdFALSE_UNSIGNED )
        {
            /* Ethernet address has been found, use progressive timeout for
             * active connect(). */
            if( pxSocket->u.xTCP.ucRepCount < 3U )
            {
                ulDelayMs = ( ( ( uint32_t ) 3000U ) << ( pxSocket->u.xTCP.ucRepCount - 1U ) );
            }
            else
            {
                ulDelayMs = 11000U;
            }
        }
        else
        {
            /* Still in the ARP phase: check every half second. */
            ulDelayMs = 500U;
        }

        FreeRTOS_debug_printf( ( "Connect[%xip:%u]: next timeout %u: %u ms\n",
                                 ( unsigned ) pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4, pxSocket->u.xTCP.usRemotePort,
                                 pxSocket->u.xTCP.ucRepCount, ( unsigned ) ulDelayMs ) );
        pxSocket->u.xTCP.usTimeout = ( uint16_t ) ipMS_TO_MIN_TICKS( ulDelayMs );
    }
    else if( pxSocket->u.xTCP.usTimeout == 0U )
    {
        /* Let the sliding window mechanism decide what time-out is appropriate. */
        BaseType_t xResult = xTCPWindowTxHasData( &pxSocket->u.xTCP.xTCPWindow, pxSocket->u.xTCP.ulWindowSize, &ulDelayMs );

        if( ulDelayMs == 0U )
        {
            if( xResult != ( BaseType_t ) 0 )
            {
                ulDelayMs = 1U;
            }
            else
            {
                ulDelayMs = tcpMAXIMUM_TCP_WAKEUP_TIME_MS;
            }
        }
        else
        {
            /* ulDelayMs contains the time to wait before a re-transmission. */
        }

        pxSocket->u.xTCP.usTimeout = ( uint16_t ) ipMS_TO_MIN_TICKS( ulDelayMs ); /* LCOV_EXCL_BR_LINE ulDelayMs will not be smaller than 1 */
    }
    else
    {
        /* field '.usTimeout' has already been set (by the
         * keep-alive/delayed-ACK mechanism). */
    }

    /* Return the number of clock ticks before the timer expires. */
    return ( TickType_t ) pxSocket->u.xTCP.usTimeout;
}
/*-----------------------------------------------------------*/

/**
 * @brief Handle the socket option FREERTOS_SO_WIN_PROPERTIES, which sets
 *        the sizes of the TCP windows and the sizes of the stream buffers.
 *
 * @param[in] pxSocket: The socket whose options are being set.
 * @param[in] pvOptionValue: The pointer that is passed by the application.
 */
BaseType_t prvSetOptionTCPWindows( FreeRTOS_Socket_t * pxSocket,
                                   const void * pvOptionValue )
{
    BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;
    const WinProperties_t * pxProps;

    do
    {
        IPTCPSocket_t * pxTCP = &( pxSocket->u.xTCP );

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
        {
            FreeRTOS_debug_printf( ( "Set SO_WIN_PROP: wrong socket type\n" ) );
            break; /* will return -pdFREERTOS_ERRNO_EINVAL */
        }

        if( ( pxTCP->txStream != NULL ) || ( pxTCP->rxStream != NULL ) )
        {
            FreeRTOS_debug_printf( ( "Set SO_WIN_PROP: buffer already created\n" ) );
            break; /* will return -pdFREERTOS_ERRNO_EINVAL */
        }

        pxProps = ( const WinProperties_t * ) pvOptionValue;

        /* Validity of txStream will be checked by the function below. */
        xReturn = prvSockopt_so_buffer( pxSocket, FREERTOS_SO_SNDBUF, &( pxProps->lTxBufSize ) );

        if( xReturn != 0 )
        {
            break; /* will return an error. */
        }

        xReturn = prvSockopt_so_buffer( pxSocket, FREERTOS_SO_RCVBUF, &( pxProps->lRxBufSize ) );

        if( xReturn != 0 )
        {
            break; /* will return an error. */
        }

        #if ( ipconfigUSE_TCP_WIN == 1 )
            {
                pxTCP->uxRxWinSize = ( uint32_t ) pxProps->lRxWinSize; /* Fixed value: size of the TCP reception window */
                pxTCP->uxTxWinSize = ( uint32_t ) pxProps->lTxWinSize; /* Fixed value: size of the TCP transmit window */
            }
        #else
            {
                pxTCP->uxRxWinSize = 1U;
                pxTCP->uxTxWinSize = 1U;
            }
        #endif

        /* In case the socket has already initialised its tcpWin,
         * adapt the window size parameters */
        if( pxTCP->xTCPWindow.u.bits.bHasInit != pdFALSE_UNSIGNED )
        {
            pxTCP->xTCPWindow.xSize.ulRxWindowLength = ( uint32_t ) ( pxTCP->uxRxWinSize * pxTCP->usMSS );
            pxTCP->xTCPWindow.xSize.ulTxWindowLength = ( uint32_t ) ( pxTCP->uxTxWinSize * pxTCP->usMSS );
        }
    }
    while( ipFALSE_BOOL );

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Handle the socket option FREERTOS_SO_SET_LOW_HIGH_WATER, which sets
 *        the low- and the high-water values for TCP reception. Useful when
 *        streaming music.
 *
 * @param[in] pxSocket: The socket whose options are being set.
 * @param[in] pvOptionValue: The pointer that is passed by the application.
 */
BaseType_t prvSetOptionLowHighWater( FreeRTOS_Socket_t * pxSocket,
                                     const void * pvOptionValue )
{
    BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;
    const LowHighWater_t * pxLowHighWater = ( const LowHighWater_t * ) pvOptionValue;

    if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        /* It is not allowed to access 'pxSocket->u.xTCP'. */
        FreeRTOS_debug_printf( ( "FREERTOS_SO_SET_LOW_HIGH_WATER: wrong socket type\n" ) );
    }
    else if( ( pxLowHighWater->uxLittleSpace >= pxLowHighWater->uxEnoughSpace ) ||
             ( pxLowHighWater->uxEnoughSpace > pxSocket->u.xTCP.uxRxStreamSize ) )
    {
        /* Impossible values. */
        FreeRTOS_debug_printf( ( "FREERTOS_SO_SET_LOW_HIGH_WATER: bad values\n" ) );
    }
    else
    {
        /* Send a STOP when buffer space drops below 'uxLittleSpace' bytes. */
        pxSocket->u.xTCP.uxLittleSpace = pxLowHighWater->uxLittleSpace;
        /* Send a GO when buffer space grows above 'uxEnoughSpace' bytes. */
        pxSocket->u.xTCP.uxEnoughSpace = pxLowHighWater->uxEnoughSpace;
        xReturn = 0;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Handle the socket option FREERTOS_SO_SET_FULL_SIZE.
 *        When enabled, the IP-stack will only send packets when
 *        there are at least MSS bytes to send.
 *
 * @param[in] pxSocket: The socket whose options are being set.
 * @param[in] pvOptionValue: The option name like FREERTOS_SO_xxx_HANDLER.
 */
BaseType_t prvSetOptionSetFullSize( FreeRTOS_Socket_t * pxSocket,
                                    const void * pvOptionValue )
{
    BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;

    if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        if( *( ( const BaseType_t * ) pvOptionValue ) != 0 )
        {
            pxSocket->u.xTCP.xTCPWindow.u.bits.bSendFullSize = pdTRUE_UNSIGNED;
        }
        else
        {
            pxSocket->u.xTCP.xTCPWindow.u.bits.bSendFullSize = pdFALSE_UNSIGNED;
        }

        if( ( pxSocket->u.xTCP.eTCPState >= eESTABLISHED ) &&
            ( FreeRTOS_outstanding( pxSocket ) != 0 ) )
        {
            /* There might be some data in the TX-stream, less than full-size,
             * which equals a MSS.  Wake-up the IP-task to check this. */
            pxSocket->u.xTCP.usTimeout = 1U;
            ( void ) xSendEventToIPTask( eTCPTimerEvent );
        }

        xReturn = 0;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Handle the socket option FREERTOS_SO_STOP_RX.
 *        Used in applications with streaming audio: tell the peer
 *        to stop or continue sending data.
 *
 * @param[in] pxSocket: The TCP socket used for the connection.
 * @param[in] pvOptionValue: The option name like FREERTOS_SO_xxx_HANDLER.
 */
BaseType_t prvSetOptionStopRX( FreeRTOS_Socket_t * pxSocket,
                               const void * pvOptionValue )
{
    BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;

    if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        if( *( ( const BaseType_t * ) pvOptionValue ) != 0 )
        {
            pxSocket->u.xTCP.bits.bRxStopped = pdTRUE_UNSIGNED;
        }
        else
        {
            pxSocket->u.xTCP.bits.bRxStopped = pdFALSE_UNSIGNED;
        }

        pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
        pxSocket->u.xTCP.usTimeout = 1U; /* to set/clear bRxStopped */
        ( void ) xSendEventToIPTask( eTCPTimerEvent );
        xReturn = 0;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Handle the socket options FREERTOS_SO_REUSE_LISTEN_SOCKET.
 *        When set, a listening socket will turn itself into a child
 *        socket when it receives a connection.
 *
 * @param[in] pxSocket: The TCP socket used for the connection.
 * @param[in] pvOptionValue: The option name like FREERTOS_SO_xxx_HANDLER.
 */
BaseType_t prvSetOptionReuseListenSocket( FreeRTOS_Socket_t * pxSocket,
                                          const void * pvOptionValue )
{
    BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;

    if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        if( *( ( const BaseType_t * ) pvOptionValue ) != 0 )
        {
            pxSocket->u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
        }
        else
        {
            pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE_UNSIGNED;
        }

        xReturn = 0;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Handle the socket options FREERTOS_SO_CLOSE_AFTER_SEND.
 *        As soon as the last byte has been transmitted, initiate
 *        a graceful closure of the TCP connection.
 *
 * @param[in] pxSocket: The TCP socket used for the connection.
 * @param[in] pvOptionValue: A pointer to a binary value of size
 *            BaseType_t.
 */
BaseType_t prvSetOptionCloseAfterSend( FreeRTOS_Socket_t * pxSocket,
                                       const void * pvOptionValue )
{
    BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;

    if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        if( *( ( const BaseType_t * ) pvOptionValue ) != 0 )
        {
            pxSocket->u.xTCP.bits.bCloseAfterSend = pdTRUE_UNSIGNED;
        }
        else
        {
            pxSocket->u.xTCP.bits.bCloseAfterSend = pdFALSE_UNSIGNED;
        }

        xReturn = 0;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief When a child socket gets closed, make sure to update the child-count of the
 *        parent. When a listening parent socket is closed, make sure to close also
 *        all orphaned child-sockets.
 *
 * @param[in] pxSocketToDelete: The socket being closed.
 */
/* MISRA Ref 17.2.1 [Sockets and limited recursion] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-172 */
/* coverity[misra_c_2012_rule_17_2_violation] */
/* coverity[recursive_step] */
void prvTCPSetSocketCount( FreeRTOS_Socket_t const * pxSocketToDelete )
{
    const ListItem_t * pxIterator;

    /* MISRA Ref 11.3.1 [Misaligned access] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
    /* coverity[misra_c_2012_rule_11_3_violation] */
    const ListItem_t * pxEnd = ( ( const ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );
    FreeRTOS_Socket_t * pxOtherSocket;
    uint16_t usLocalPort = pxSocketToDelete->usLocalPort;

    if( pxSocketToDelete->u.xTCP.eTCPState == eTCP_LISTEN )
    {
        pxIterator = listGET_NEXT( pxEnd );

        while( pxIterator != pxEnd )
        {
            pxOtherSocket = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );

            /* This needs to be done here, before calling vSocketClose. */
            pxIterator = listGET_NEXT( pxIterator );

            if( ( pxOtherSocket->u.xTCP.eTCPState != eTCP_LISTEN ) &&
                ( pxOtherSocket->usLocalPort == usLocalPort ) &&
                ( ( pxOtherSocket->u.xTCP.bits.bPassQueued != pdFALSE_UNSIGNED ) ||
                  ( pxOtherSocket->u.xTCP.bits.bPassAccept != pdFALSE_UNSIGNED ) ) )
            {
                /* MISRA Ref 17.2.1 [Sockets and limited recursion] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-172 */
                /* coverity[misra_c_2012_rule_17_2_violation] */
                /* coverity[recursive_step] */
                ( void ) vSocketClose( pxOtherSocket );
            }
        }
    }
    else
    {
        for( pxIterator = listGET_NEXT( pxEnd );
             pxIterator != pxEnd;
             pxIterator = listGET_NEXT( pxIterator ) )
        {
            pxOtherSocket = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );

            if( ( pxOtherSocket->u.xTCP.eTCPState == eTCP_LISTEN ) &&
                ( pxOtherSocket->usLocalPort == usLocalPort ) &&
                ( pxOtherSocket->u.xTCP.usChildCount != 0U ) )
            {
                pxOtherSocket->u.xTCP.usChildCount--;
                FreeRTOS_debug_printf( ( "Lost: Socket %u now has %u / %u child%s\n",
                                         pxOtherSocket->usLocalPort,
                                         pxOtherSocket->u.xTCP.usChildCount,
                                         pxOtherSocket->u.xTCP.usBacklog,
                                         ( pxOtherSocket->u.xTCP.usChildCount == 1U ) ? "" : "ren" ) );
                break;
            }
        }
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Set the value of receive/send buffer after some preliminary checks.
 *
 * @param[in] pxSocket: The socket whose options are being set.
 * @param[in] lOptionName: The option name: either FREERTOS_SO_SNDBUF or
 *                         FREERTOS_SO_SNDBUF.
 * @param[in] pvOptionValue: The value of the option being set.
 *
 * @return If there is no error, then 0 is returned. Or a negative errno
 *         value is returned.
 */
BaseType_t prvSockopt_so_buffer( FreeRTOS_Socket_t * pxSocket,
                                 int32_t lOptionName,
                                 const void * pvOptionValue )
{
    uint32_t ulNewValue;
    BaseType_t xReturn;

    if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        FreeRTOS_debug_printf( ( "Set SO_%sBUF: wrong socket type\n",
                                 ( lOptionName == FREERTOS_SO_SNDBUF ) ? "SND" : "RCV" ) );
        xReturn = -pdFREERTOS_ERRNO_EINVAL;
    }
    else if( ( ( lOptionName == FREERTOS_SO_SNDBUF ) && ( pxSocket->u.xTCP.txStream != NULL ) ) ||
             ( ( lOptionName == FREERTOS_SO_RCVBUF ) && ( pxSocket->u.xTCP.rxStream != NULL ) ) )
    {
        FreeRTOS_debug_printf( ( "Set SO_%sBUF: buffer already created\n",
                                 ( lOptionName == FREERTOS_SO_SNDBUF ) ? "SND" : "RCV" ) );
        xReturn = -pdFREERTOS_ERRNO_EINVAL;
    }
    else
    {
        ulNewValue = *( ( const uint32_t * ) pvOptionValue );

        if( lOptionName == FREERTOS_SO_SNDBUF )
        {
            /* Round up to nearest MSS size */
            ulNewValue = FreeRTOS_round_up( ulNewValue, ( uint32_t ) pxSocket->u.xTCP.usMSS );
            pxSocket->u.xTCP.uxTxStreamSize = ulNewValue;
        }
        else
        {
            pxSocket->u.xTCP.uxRxStreamSize = ulNewValue;
        }

        xReturn = 0;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief 'Touch' the socket to keep it alive/updated.
 *
 * @param[in] pxSocket: The socket to be updated.
 *
 * @note This is used for anti-hanging protection and TCP keep-alive messages.
 *       Called in two places: after receiving a packet and after a state change.
 *       The socket's alive timer may be reset.
 */
void prvTCPTouchSocket( struct xSOCKET * pxSocket )
{
    #if ( ipconfigTCP_HANG_PROTECTION == 1 )
        {
            pxSocket->u.xTCP.xLastActTime = xTaskGetTickCount();
        }
    #endif

    #if ( ipconfigTCP_KEEP_ALIVE == 1 )
        {
            pxSocket->u.xTCP.bits.bWaitKeepAlive = pdFALSE_UNSIGNED;
            pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;
            pxSocket->u.xTCP.ucKeepRepCount = 0U;
            pxSocket->u.xTCP.xLastAliveTime = xTaskGetTickCount();
        }
    #endif

    ( void ) pxSocket;
}
/*-----------------------------------------------------------*/

/** @brief Close the socket another time.
 *
 * @param[in] pxSocket: The socket to be checked.
 */
/* coverity[single_use] */
void vSocketCloseNextTime( FreeRTOS_Socket_t * pxSocket )
{
    if( ( xSocketToClose != NULL ) && ( xSocketToClose != pxSocket ) )
    {
        ( void ) vSocketClose( xSocketToClose );
    }

    xSocketToClose = pxSocket;
}
/*-----------------------------------------------------------*/

/** @brief Postpone a call to FreeRTOS_listen() to avoid recursive calls.
 *
 * @param[in] pxSocket: The socket to be checked.
 */
/* coverity[single_use] */
void vSocketListenNextTime( FreeRTOS_Socket_t * pxSocket )
{
    if( ( xSocketToListen != NULL ) && ( xSocketToListen != pxSocket ) )
    {
        ( void ) FreeRTOS_listen( ( Socket_t ) xSocketToListen, ( BaseType_t ) ( xSocketToListen->u.xTCP.usBacklog ) );
    }

    xSocketToListen = pxSocket;
}
/*-----------------------------------------------------------*/

/**
 * @brief Changing to a new state. Centralised here to do specific actions such as
 *        resetting the alive timer, calling the user's OnConnect handler to notify
 *        that a socket has got (dis)connected, and setting bit to unblock a call to
 *        FreeRTOS_select().
 *
 * @param[in] pxSocket: The socket whose state we are trying to change.
 * @param[in] eTCPState: The state to which we want to change to.
 */
void vTCPStateChange( FreeRTOS_Socket_t * pxSocket,
                      enum eTCP_STATE eTCPState )
{
    FreeRTOS_Socket_t * xParent = pxSocket;
    BaseType_t bBefore = tcpNOW_CONNECTED( ( BaseType_t ) pxSocket->u.xTCP.eTCPState ); /* Was it connected ? */
    BaseType_t bAfter = tcpNOW_CONNECTED( ( BaseType_t ) eTCPState );                   /* Is it connected now ? */

    eIPTCPState_t xPreviousState = pxSocket->u.xTCP.eTCPState;

    #if ( ipconfigUSE_CALLBACKS == 1 )
        FreeRTOS_Socket_t * xConnected = NULL;
    #endif

    if( ( ( xPreviousState == eCONNECT_SYN ) ||
          ( xPreviousState == eSYN_FIRST ) ||
          ( xPreviousState == eSYN_RECEIVED ) ) &&
        ( eTCPState == eCLOSE_WAIT ) )
    {
        /* A socket was in the connecting phase but something
         * went wrong and it should be closed. */
        FreeRTOS_debug_printf( ( "Move from %s to %s\n",
                                 FreeRTOS_GetTCPStateName( xPreviousState ),
                                 FreeRTOS_GetTCPStateName( eTCPState ) ) );

        /* Set the flag to show that it was connected before and that the
         * status has changed now. This will cause the control flow to go
         * in the below if condition.*/
        bBefore = pdTRUE;
    }

    /* Has the connected status changed? */
    if( bBefore != bAfter )
    {
        /* if bPassQueued is true, this socket is an orphan until it gets connected. */
        if( pxSocket->u.xTCP.bits.bPassQueued != pdFALSE_UNSIGNED )
        {
            /* Find it's parent if the reuse bit is not set. */
            if( pxSocket->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED )
            {
                xParent = pxSocket->u.xTCP.pxPeerSocket;
                configASSERT( xParent != NULL );
            }
        }

        /* Is the socket connected now ? */
        if( bAfter != pdFALSE )
        {
            /* if bPassQueued is true, this socket is an orphan until it gets connected. */
            if( pxSocket->u.xTCP.bits.bPassQueued != pdFALSE_UNSIGNED )
            {
                if( xParent != NULL )
                {
                    /* The child socket has got connected.  See if the parent
                     * ( the listening socket ) should be signalled, or if a
                     * call-back must be made, in which case 'xConnected' will
                     * be set to the parent socket. */

                    if( xParent->u.xTCP.pxPeerSocket == NULL )
                    {
                        xParent->u.xTCP.pxPeerSocket = pxSocket;
                    }

                    xParent->xEventBits |= ( EventBits_t ) eSOCKET_ACCEPT;

                    #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
                        {
                            /* Library support FreeRTOS_select().  Receiving a new
                             * connection is being translated as a READ event. */
                            if( ( xParent->xSelectBits & ( ( EventBits_t ) eSELECT_READ ) ) != 0U )
                            {
                                xParent->xEventBits |= ( ( EventBits_t ) eSELECT_READ ) << SOCKET_EVENT_BIT_COUNT;
                            }
                        }
                    #endif

                    #if ( ipconfigUSE_CALLBACKS == 1 )
                        {
                            if( ( ipconfigIS_VALID_PROG_ADDRESS( xParent->u.xTCP.pxHandleConnected ) ) &&
                                ( xParent->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED ) )
                            {
                                /* The listening socket does not become connected itself, in stead
                                 * a child socket is created.
                                 * Postpone a call the OnConnect event until the end of this function. */
                                xConnected = xParent;
                            }
                        }
                    #endif
                }

                /* Don't need to access the parent socket anymore, so the
                 * reference 'pxPeerSocket' may be cleared. */
                pxSocket->u.xTCP.pxPeerSocket = NULL;
                pxSocket->u.xTCP.bits.bPassQueued = pdFALSE_UNSIGNED;

                /* When true, this socket may be returned in a call to accept(). */
                pxSocket->u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
            }
            else
            {
                /* An active connect() has succeeded. In this case there is no
                 * ( listening ) parent socket. Signal the now connected socket. */

                pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_CONNECT;

                #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
                    {
                        if( ( pxSocket->xSelectBits & ( ( EventBits_t ) eSELECT_WRITE ) ) != 0U )
                        {
                            pxSocket->xEventBits |= ( ( EventBits_t ) eSELECT_WRITE ) << SOCKET_EVENT_BIT_COUNT;
                        }
                    }
                #endif
            }
        }
        else /* bAfter == pdFALSE, connection is closed. */
        {
            /* Notify/wake-up the socket-owner by setting the event bits. */
            xParent->xEventBits |= ( EventBits_t ) eSOCKET_CLOSED;

            #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
                {
                    if( ( xParent->xSelectBits & ( EventBits_t ) eSELECT_EXCEPT ) != 0U )
                    {
                        xParent->xEventBits |= ( ( EventBits_t ) eSELECT_EXCEPT ) << SOCKET_EVENT_BIT_COUNT;
                    }
                }
            #endif
        }

        #if ( ipconfigUSE_CALLBACKS == 1 )
            {
                if( ( ipconfigIS_VALID_PROG_ADDRESS( pxSocket->u.xTCP.pxHandleConnected ) ) && ( xConnected == NULL ) )
                {
                    /* The 'connected' state has changed, call the user handler. */
                    xConnected = pxSocket;
                }
            }
        #endif /* ipconfigUSE_CALLBACKS */

        if( prvTCPSocketIsActive( pxSocket->u.xTCP.eTCPState ) == 0 )
        {
            /* Now the socket isn't in an active state anymore so it
             * won't need further attention of the IP-task.
             * Setting time-out to zero means that the socket won't get checked during
             * timer events. */
            pxSocket->u.xTCP.usTimeout = 0U;
        }
    }

    /* Fill in the new state. */
    pxSocket->u.xTCP.eTCPState = eTCPState;

    if( ( eTCPState == eCLOSED ) ||
        ( eTCPState == eCLOSE_WAIT ) )
    {
        /* Socket goes to status eCLOSED because of a RST.
         * When nobody owns the socket yet, delete it. */
        vTaskSuspendAll();
        {
            if( ( pxSocket->u.xTCP.bits.bPassQueued != pdFALSE_UNSIGNED ) ||
                ( pxSocket->u.xTCP.bits.bPassAccept != pdFALSE_UNSIGNED ) )
            {
                if( pxSocket->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED )
                {
                    pxSocket->u.xTCP.bits.bPassQueued = pdFALSE_UNSIGNED;
                    pxSocket->u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;
                }

                xTaskResumeAll();

                FreeRTOS_printf( ( "vTCPStateChange: Closing socket\n" ) );

                if( pxSocket->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED )
                {
                    configASSERT( xIsCallingFromIPTask() != pdFALSE );
                    vSocketCloseNextTime( pxSocket );
                }
            }
            else
            {
                xTaskResumeAll();
            }
        }
    }

    if( ( eTCPState == eCLOSE_WAIT ) && ( pxSocket->u.xTCP.bits.bReuseSocket == pdTRUE_UNSIGNED ) )
    {
        switch( xPreviousState )
        {
            case eSYN_FIRST:    /* 3 (server) Just created, must ACK the SYN request */
            case eSYN_RECEIVED: /* 4 (server) waiting for a confirming connection request */
                FreeRTOS_debug_printf( ( "Restoring a reuse socket port %u\n", pxSocket->usLocalPort ) );

                /* Go back into listening mode. Set the TCP status to 'eCLOSED',
                 * otherwise FreeRTOS_listen() will refuse the action. */
                pxSocket->u.xTCP.eTCPState = eCLOSED;

                /* vSocketListenNextTime() makes sure that FreeRTOS_listen() will be called
                 * before the IP-task handles any new message. */
                vSocketListenNextTime( pxSocket );
                break;

            default:
                /* Nothing to do. */
                break;
        }
    }

    /* Touch the alive timers because moving to another state. */
    prvTCPTouchSocket( pxSocket );

    #if ( ipconfigHAS_DEBUG_PRINTF == 1 )
        {
            if( ( xTCPWindowLoggingLevel >= 0 ) && ( ipconfigTCP_MAY_LOG_PORT( pxSocket->usLocalPort ) ) )
            {
                FreeRTOS_debug_printf( ( "Socket %u -> %xip:%u State %s->%s\n",
                                         pxSocket->usLocalPort,
                                         ( unsigned ) pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4,
                                         pxSocket->u.xTCP.usRemotePort,
                                         FreeRTOS_GetTCPStateName( ( UBaseType_t ) xPreviousState ),
                                         FreeRTOS_GetTCPStateName( ( UBaseType_t ) eTCPState ) ) );
            }
        }
    #endif /* ipconfigHAS_DEBUG_PRINTF */

    #if ( ipconfigUSE_CALLBACKS == 1 )
        {
            if( xConnected != NULL )
            {
                /* The 'connected' state has changed, call the OnConnect handler of the parent. */
                xConnected->u.xTCP.pxHandleConnected( ( Socket_t ) xConnected, bAfter );
            }
        }
    #endif

    if( xParent != NULL )
    {
        vSocketWakeUpUser( xParent );
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief In the API accept(), the user asks is there is a new client? As API's can
 *        not walk through the xBoundTCPSocketsList the IP-task will do this.
 *
 * @param[in] pxSocket: The socket for which the bound socket list will be iterated.
 *
 * @return if there is a new client, then pdTRUE is returned or else, pdFALSE.
 */
BaseType_t xTCPCheckNewClient( FreeRTOS_Socket_t * pxSocket )
{
    TickType_t uxLocalPort = ( TickType_t ) FreeRTOS_htons( pxSocket->usLocalPort );
    const ListItem_t * pxIterator;
    FreeRTOS_Socket_t * pxFound;
    BaseType_t xResult = pdFALSE;

    /* MISRA Ref 11.3.1 [Misaligned access] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
    /* coverity[misra_c_2012_rule_11_3_violation] */
    const ListItem_t * pxEndTCP = ( ( const ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    /* Here xBoundTCPSocketsList can be accessed safely IP-task is the only one
     * who has access. */
    for( pxIterator = ( const ListItem_t * ) listGET_HEAD_ENTRY( &xBoundTCPSocketsList );
         pxIterator != pxEndTCP;
         pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator ) )
    {
        if( listGET_LIST_ITEM_VALUE( pxIterator ) == ( configLIST_VOLATILE TickType_t ) uxLocalPort )
        {
            pxFound = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );

            if( ( pxFound->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP ) && ( pxFound->u.xTCP.bits.bPassAccept != pdFALSE_UNSIGNED ) )
            {
                pxSocket->u.xTCP.pxPeerSocket = pxFound;
                FreeRTOS_debug_printf( ( "xTCPCheckNewClient[0]: client on port %u\n", pxSocket->usLocalPort ) );
                xResult = pdTRUE;
                break;
            }
        }
    }

    return xResult;
}
/*-----------------------------------------------------------*/

#if ( ( ipconfigHAS_PRINTF != 0 ) )

/**
 * @brief Print a summary of all sockets and their connections.
 */
    BaseType_t vTCPNetStat( void )
    {
        /* Show a simple listing of all created sockets and their connections */
        const ListItem_t * pxIterator;
        BaseType_t count = 0;

        if( !listLIST_IS_INITIALISED( &xBoundTCPSocketsList ) )
        {
            FreeRTOS_printf( ( "PLUS-TCP TCP not initialized\n" ) );
        }
        else
        {
            /* Casting a "MiniListItem_t" to a "ListItem_t".
             * This is safe because only its address is being accessed, not its fields. */
            const ListItem_t * pxEndTCP = listGET_END_MARKER( &xBoundTCPSocketsList );

            for( pxIterator = listGET_HEAD_ENTRY( &xBoundTCPSocketsList );
                 pxIterator != pxEndTCP;
                 pxIterator = listGET_NEXT( pxIterator ) )
            {
                const FreeRTOS_Socket_t * pxSocket = ( ( const FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );
                vTCPNetStat_TCPSocket( pxSocket );
                count++;
            }
        }

        return count;
    }
#endif /* ( ipconfigHAS_PRINTF != 0 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Add data to the RxStream. When uxOffset > 0, data has come in out-of-order
 *        and will be put in front of the head so it can not be popped by the user.
 *
 * @param[in] pxSocket: The socket to whose RxStream data is to be added.
 * @param[in] uxOffset: Offset of the packet.
 * @param[in] pcData: The data to be added to the RxStream.
 * @param[in] ulByteCount: Number of bytes in the data.
 *
 * @return The number of bytes actually added to the RxStream. Or else, a negative
 *         error code is returned.
 */
int32_t lTCPAddRxdata( FreeRTOS_Socket_t * pxSocket,
                       size_t uxOffset,
                       const uint8_t * pcData,
                       uint32_t ulByteCount )
{
    StreamBuffer_t * pxStream = pxSocket->u.xTCP.rxStream;
    int32_t xResult = 0;

    #if ( ipconfigUSE_CALLBACKS == 1 )
        BaseType_t bHasHandler = ipconfigIS_VALID_PROG_ADDRESS( pxSocket->u.xTCP.pxHandleReceive ) ? pdTRUE : pdFALSE;
        const uint8_t * pucBuffer = NULL;
    #endif /* ipconfigUSE_CALLBACKS */

    /* int32_t uxStreamBufferAdd( pxBuffer, uxOffset, pucData, aCount )
     * if( pucData != NULL ) copy data the the buffer
     * if( pucData == NULL ) no copying, just advance rxHead
     * if( uxOffset != 0 ) Just store data which has come out-of-order
     * if( uxOffset == 0 ) Also advance rxHead */
    if( pxStream == NULL )
    {
        pxStream = prvTCPCreateStream( pxSocket, pdTRUE );

        if( pxStream == NULL )
        {
            xResult = -1;
        }
    }

    if( xResult >= 0 )
    {
        #if ( ipconfigUSE_CALLBACKS == 1 )
            {
                if( ( bHasHandler != pdFALSE ) && ( uxStreamBufferGetSize( pxStream ) == 0U ) && ( uxOffset == 0U ) && ( pcData != NULL ) )
                {
                    /* Data can be passed directly to the user because there is
                     * no data in the RX-stream, it the new data must be stored
                     * at offset zero, and a buffer 'pcData' is provided.
                     */
                    pucBuffer = pcData;

                    /* Zero-copy for call-back: no need to add the bytes to the
                     * stream, only the pointer will be advanced by uxStreamBufferAdd(). */
                    pcData = NULL;
                }
            }
        #endif /* ipconfigUSE_CALLBACKS */

        xResult = ( int32_t ) uxStreamBufferAdd( pxStream, uxOffset, pcData, ( size_t ) ulByteCount );

        #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
            {
                if( xResult != ( int32_t ) ulByteCount )
                {
                    FreeRTOS_debug_printf( ( "lTCPAddRxdata: at %u: %d/%u bytes (tail %u head %u space %u front %u)\n",
                                             ( unsigned int ) uxOffset,
                                             ( int ) xResult,
                                             ( unsigned int ) ulByteCount,
                                             ( unsigned int ) pxStream->uxTail,
                                             ( unsigned int ) pxStream->uxHead,
                                             ( unsigned int ) uxStreamBufferFrontSpace( pxStream ),
                                             ( unsigned int ) pxStream->uxFront ) );
                }
            }
        #endif /* ipconfigHAS_DEBUG_PRINTF */

        if( uxOffset == 0U )
        {
            /* Data is being added to rxStream at the head (offs = 0) */
            #if ( ipconfigUSE_CALLBACKS == 1 )
                if( bHasHandler != pdFALSE )
                {
                    vTCPAddRxdata_Callback( pxSocket, pucBuffer, ulByteCount );
                }
                else
            #endif /* ipconfigUSE_CALLBACKS */
            {
                vTCPAddRxdata_Stored( pxSocket );
            }
        }
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief As multiple sockets may be bound to the same local port number
 *        looking up a socket is a little more complex: Both a local port,
 *        and a remote port and IP address are being used to find a match.
 *        For a socket in listening mode, the remote port and IP address
 *        are both 0.
 *
 * @param[in] ulLocalIP: Local IP address. Ignored for now.
 * @param[in] uxLocalPort: Local port number.
 * @param[in] ulRemoteIP: Remote (peer) IP address.
 * @param[in] uxRemotePort: Remote (peer) port.
 *
 * @return The socket which was found.
 */
FreeRTOS_Socket_t * pxTCPSocketLookup( uint32_t ulLocalIP,
                                       UBaseType_t uxLocalPort,
                                       IP_Address_t ulRemoteIP,
                                       UBaseType_t uxRemotePort )
{
    const ListItem_t * pxIterator;
    FreeRTOS_Socket_t * pxResult = NULL, * pxListenSocket = NULL;

    /* MISRA Ref 11.3.1 [Misaligned access] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
    /* coverity[misra_c_2012_rule_11_3_violation] */
    const ListItem_t * pxEnd = ( ( const ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    /* __XX__ TODO ulLocalIP is not used, for misra compliance*/
    ( void ) ulLocalIP;

    for( pxIterator = listGET_NEXT( pxEnd );
         pxIterator != pxEnd;
         pxIterator = listGET_NEXT( pxIterator ) )
    {
        FreeRTOS_Socket_t * pxSocket = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );

        if( pxSocket->usLocalPort == ( uint16_t ) uxLocalPort )
        {
            if( pxSocket->u.xTCP.eTCPState == eTCP_LISTEN )
            {
                /* If this is a socket listening to uxLocalPort, remember it
                 * in case there is no perfect match. */
                pxListenSocket = pxSocket;
            }
            else if( pxSocket->u.xTCP.usRemotePort == ( uint16_t ) uxRemotePort )
            {
                if( ulRemoteIP.ulIP_IPv4 == 0 )
                {
                    #if ( ipconfigUSE_IPv6 != 0 )
                        pxResult = pxTCPSocketLookup_IPv6( pxSocket, &ulRemoteIP.xIP_IPv6, ulRemoteIP.ulIP_IPv4 );
                    #endif
                }
                else
                {
                    if( pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4 == ulRemoteIP.ulIP_IPv4 )
                    {
                        /* For sockets not in listening mode, find a match with
                         * xLocalPort, ulRemoteIP AND xRemotePort. */
                        pxResult = pxSocket;
                    }
                }

                if( pxResult != NULL )
                {
                    break;
                }
            }
            else
            {
                /* This 'pxSocket' doesn't match. */
            }
        }
    }

    if( pxResult == NULL )
    {
        /* An exact match was not found, maybe a listening socket was
         * found. */
        pxResult = pxListenSocket;
    }

    return pxResult;
}
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )

/**
 * @brief This internal function will check if a given TCP
 *        socket has had any select event, either READ, WRITE,
 *        or EXCEPT.
 *
 * @param[in] pxSocket: The socket which needs to be checked.
 * @return An event mask of events that are active for this socket.
 */
    static EventBits_t vSocketSelectTCP( FreeRTOS_Socket_t * pxSocket )
    {
        /* Check if the TCP socket has already been accepted by
         * the owner.  If not, it is useless to return it from a
         * select(). */
        BaseType_t bAccepted = pdFALSE;
        EventBits_t xSocketBits = 0U;

        if( pxSocket->u.xTCP.bits.bPassQueued == pdFALSE_UNSIGNED )
        {
            if( pxSocket->u.xTCP.bits.bPassAccept == pdFALSE_UNSIGNED )
            {
                bAccepted = pdTRUE;
            }
        }

        /* Is the set owner interested in READ events? */
        if( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_READ ) != ( EventBits_t ) 0U )
        {
            if( pxSocket->u.xTCP.eTCPState == eTCP_LISTEN )
            {
                if( ( pxSocket->u.xTCP.pxPeerSocket != NULL ) && ( pxSocket->u.xTCP.pxPeerSocket->u.xTCP.bits.bPassAccept != pdFALSE_UNSIGNED ) )
                {
                    xSocketBits |= ( EventBits_t ) eSELECT_READ;
                }
            }
            else if( ( pxSocket->u.xTCP.bits.bReuseSocket != pdFALSE_UNSIGNED ) && ( pxSocket->u.xTCP.bits.bPassAccept != pdFALSE_UNSIGNED ) )
            {
                /* This socket has the re-use flag. After connecting it turns into
                 * a connected socket. Set the READ event, so that accept() will be called. */
                xSocketBits |= ( EventBits_t ) eSELECT_READ;
            }
            else if( ( bAccepted != 0 ) && ( FreeRTOS_recvcount( pxSocket ) > 0 ) )
            {
                xSocketBits |= ( EventBits_t ) eSELECT_READ;
            }
            else
            {
                /* Nothing. */
            }
        }

        /* Is the set owner interested in EXCEPTION events? */
        if( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_EXCEPT ) != 0U )
        {
            if( ( pxSocket->u.xTCP.eTCPState == eCLOSE_WAIT ) || ( pxSocket->u.xTCP.eTCPState == eCLOSED ) )
            {
                xSocketBits |= ( EventBits_t ) eSELECT_EXCEPT;
            }
        }

        /* Is the set owner interested in WRITE events? */
        if( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_WRITE ) != 0U )
        {
            BaseType_t bMatch = pdFALSE;

            if( bAccepted != 0 )
            {
                if( FreeRTOS_tx_space( pxSocket ) > 0 )
                {
                    bMatch = pdTRUE;
                }
            }

            if( bMatch == pdFALSE )
            {
                if( ( pxSocket->u.xTCP.bits.bConnPrepared != pdFALSE_UNSIGNED ) &&
                    ( pxSocket->u.xTCP.eTCPState >= eESTABLISHED ) &&
                    ( pxSocket->u.xTCP.bits.bConnPassed == pdFALSE_UNSIGNED ) )
                {
                    pxSocket->u.xTCP.bits.bConnPassed = pdTRUE_UNSIGNED;
                    bMatch = pdTRUE;
                }
            }

            if( bMatch != pdFALSE )
            {
                xSocketBits |= ( EventBits_t ) eSELECT_WRITE;
            }
        }

        return xSocketBits;
    }
#endif /* ipconfigSUPPORT_SELECT_FUNCTION == 1 */
/*-----------------------------------------------------------*/

/**
 * @brief A TCP timer has expired, now check all TCP sockets for:
 *        - Active connect
 *        - Send a delayed ACK
 *        - Send new data
 *        - Send a keep-alive packet
 *        - Check for timeout (in non-connected states only)
 *
 * @param[in] xWillSleep: Whether the calling task is going to sleep.
 *
 * @return Minimum amount of time before the timer shall expire.
 */
TickType_t xTCPTimerCheck( BaseType_t xWillSleep )
{
    FreeRTOS_Socket_t * pxSocket;
    TickType_t xShortest = pdMS_TO_TICKS( ( TickType_t ) ipTCP_TIMER_PERIOD_MS );
    TickType_t xNow = xTaskGetTickCount();
    static TickType_t xLastTime = 0U;
    TickType_t xDelta = xNow - xLastTime;

    /* MISRA Ref 11.3.1 [Misaligned access] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
    /* coverity[misra_c_2012_rule_11_3_violation] */
    const ListItem_t * pxEnd = ( ( const ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    /* MISRA Ref 11.3.1 [Misaligned access] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
    /* coverity[misra_c_2012_rule_11_3_violation] */
    const ListItem_t * pxIterator = ( const ListItem_t * ) listGET_HEAD_ENTRY( &xBoundTCPSocketsList );

    xLastTime = xNow;

    if( xDelta == 0U )
    {
        xDelta = 1U;
    }

    while( pxIterator != pxEnd )
    {
        pxSocket = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );
        pxIterator = ( ListItem_t * ) listGET_NEXT( pxIterator );

        /* Sockets with 'timeout == 0' do not need any regular attention. */
        if( pxSocket->u.xTCP.usTimeout == 0U )
        {
            continue;
        }

        if( xDelta < ( TickType_t ) pxSocket->u.xTCP.usTimeout )
        {
            pxSocket->u.xTCP.usTimeout = ( uint16_t ) ( ( ( TickType_t ) pxSocket->u.xTCP.usTimeout ) - xDelta );
        }
        else
        {
            BaseType_t xRc;

            pxSocket->u.xTCP.usTimeout = 0U;
            xRc = xTCPSocketCheck( pxSocket );

            /* Within this function, the socket might want to send a delayed
             * ack or send out data or whatever it needs to do. */
            if( xRc < 0 )
            {
                /* Continue because the socket was deleted. */
                continue;
            }
        }

        /* In xEventBits the driver may indicate that the socket has
         * important events for the user.  These are only done just before the
         * IP-task goes to sleep. */
        if( pxSocket->xEventBits != 0U )
        {
            if( xWillSleep != pdFALSE )
            {
                /* The IP-task is about to go to sleep, so messages can be
                 * sent to the socket owners. */
                vSocketWakeUpUser( pxSocket );
            }
            else
            {
                /* Or else make sure this will be called again to wake-up
                 * the sockets' owner. */
                xShortest = ( TickType_t ) 0;
            }
        }

        if( ( pxSocket->u.xTCP.usTimeout != 0U ) && ( xShortest > ( TickType_t ) pxSocket->u.xTCP.usTimeout ) )
        {
            xShortest = ( TickType_t ) pxSocket->u.xTCP.usTimeout;
        }
    }

    return xShortest;
}
/*-----------------------------------------------------------*/

/**
 * @brief Connect to a remote port.
 *
 * @param[in] xClientSocket: The socket initiating the connection.
 * @param[in] pxAddress: The address of the remote socket.
 * @param[in] xAddressLength: This parameter is not used. It is kept in
 *                   the function signature to adhere to the Berkeley
 *                   sockets standard.
 *
 * @return 0 is returned on a successful connection, else a negative
 *         error code is returned.
 */
BaseType_t FreeRTOS_connect( Socket_t xClientSocket,
                             const struct freertos_sockaddr * pxAddress,
                             socklen_t xAddressLength )
{
    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xClientSocket;
    TickType_t xRemainingTime;
    BaseType_t xTimed = pdFALSE;
    BaseType_t xResult = -pdFREERTOS_ERRNO_EINVAL;
    TimeOut_t xTimeOut;

    ( void ) xAddressLength;

    xResult = prvTCPConnectStart( pxSocket, pxAddress );

    if( xResult == 0 )
    {
        /* And wait for the result */
        for( ; ; )
        {
            EventBits_t uxEvents;

            if( xTimed == pdFALSE )
            {
                /* Only in the first round, check for non-blocking */
                xRemainingTime = pxSocket->xReceiveBlockTime;

                if( xRemainingTime == ( TickType_t ) 0 )
                {
                    /* Not yet connected, correct state, non-blocking. */
                    xResult = -pdFREERTOS_ERRNO_EWOULDBLOCK;
                    break;
                }

                /* Don't get here a second time. */
                xTimed = pdTRUE;

                /* Fetch the current time */
                vTaskSetTimeOutState( &xTimeOut );
            }

            /* Did it get connected while sleeping ? */
            xResult = FreeRTOS_issocketconnected( pxSocket );

            /* Returns positive when connected, negative means an error */
            if( xResult < 0 )
            {
                /* Return the error */
                break;
            }

            if( xResult > 0 )
            {
                /* Socket now connected, return a zero */
                xResult = 0;
                break;
            }

            /* Is it allowed to sleep more? */
            if( xTaskCheckForTimeOut( &xTimeOut, &xRemainingTime ) != pdFALSE )
            {
                xResult = -pdFREERTOS_ERRNO_ETIMEDOUT;
                break;
            }

            /* Go sleeping until we get any down-stream event */
            uxEvents = xEventGroupWaitBits( pxSocket->xEventGroup,
                                            ( EventBits_t ) eSOCKET_CONNECT | ( EventBits_t ) eSOCKET_CLOSED,
                                            pdTRUE /*xClearOnExit*/,
                                            pdFALSE /*xWaitAllBits*/,
                                            xRemainingTime );

            if( ( uxEvents & ( EventBits_t ) eSOCKET_CLOSED ) != 0U )
            {
                xResult = -pdFREERTOS_ERRNO_ENOTCONN;
                FreeRTOS_debug_printf( ( "FreeRTOS_connect() stopped due to an error\n" ) );
                break;
            }
        }
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Request to put a socket in listen mode.
 *
 * @param[in] xSocket: the socket to be put in listening mode.
 * @param[in] xBacklog: Maximum number of child sockets.
 *
 * @return 0 in case of success, or else a negative error code is
 *         returned.
 */
BaseType_t FreeRTOS_listen( Socket_t xSocket,
                            BaseType_t xBacklog )
{
    FreeRTOS_Socket_t * pxSocket;
    BaseType_t xResult = 0;

    pxSocket = ( FreeRTOS_Socket_t * ) xSocket;

    /* listen() is allowed for a valid TCP socket in Closed state and already
     * bound. */
    if( vSocketValid( pxSocket, FREERTOS_IPPROTO_TCP, pdTRUE ) == pdFALSE )
    {
        xResult = -pdFREERTOS_ERRNO_EOPNOTSUPP;
    }
    else if( ( pxSocket->u.xTCP.eTCPState != eCLOSED ) && ( pxSocket->u.xTCP.eTCPState != eCLOSE_WAIT ) )
    {
        /* Socket is in a wrong state. */
        xResult = -pdFREERTOS_ERRNO_EOPNOTSUPP;
    }
    else
    {
        /* Backlog is interpreted here as "the maximum number of child
         * sockets. */
        pxSocket->u.xTCP.usBacklog = ( uint16_t ) FreeRTOS_min_int32( ( int32_t ) 0xffff, ( int32_t ) xBacklog );

        /* This cleaning is necessary only if a listening socket is being
         * reused as it might have had a previous connection. */
        if( pxSocket->u.xTCP.bits.bReuseSocket != pdFALSE_UNSIGNED )
        {
            if( pxSocket->u.xTCP.rxStream != NULL )
            {
                vStreamBufferClear( pxSocket->u.xTCP.rxStream );
            }

            if( pxSocket->u.xTCP.txStream != NULL )
            {
                vStreamBufferClear( pxSocket->u.xTCP.txStream );
            }

            ( void ) memset( pxSocket->u.xTCP.xPacket.u.ucLastPacket, 0, sizeof( pxSocket->u.xTCP.xPacket.u.ucLastPacket ) );
            ( void ) memset( &pxSocket->u.xTCP.xTCPWindow, 0, sizeof( pxSocket->u.xTCP.xTCPWindow ) );
            ( void ) memset( &pxSocket->u.xTCP.bits, 0, sizeof( pxSocket->u.xTCP.bits ) );

            /* Now set the bReuseSocket flag again, because the bits have
             * just been cleared. */
            pxSocket->u.xTCP.bits.bReuseSocket = pdTRUE;
        }

        vTCPStateChange( pxSocket, eTCP_LISTEN );
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Accept a connection on an listening socket.
 *
 * @param[in] xServerSocket: The socket in listening mode.
 * @param[out] pxAddress: The address of the machine trying to connect to this node
 *                        is returned in this pointer.
 * @param[out] pxAddressLength: The length of the address of the remote machine.
 *
 * @return FreeRTOS_accept: can return a new connected socket if the server socket
 *         is in listen mode and receives a connection request. The new socket will
 *         be bound already to the same port number as the listening socket.
 */
Socket_t FreeRTOS_accept( Socket_t xServerSocket,
                          struct freertos_sockaddr * pxAddress,
                          socklen_t * pxAddressLength )
{
    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xServerSocket;
    FreeRTOS_Socket_t * pxClientSocket = NULL;
    TickType_t xRemainingTime;
    BaseType_t xTimed = pdFALSE;
    TimeOut_t xTimeOut;
    IPStackEvent_t xAskEvent;

    if( vSocketValid( pxSocket, FREERTOS_IPPROTO_TCP, pdTRUE ) == pdFALSE )
    {
        /* Not a valid socket or wrong type */

        /* MISRA Ref 11.4.1 [Socket error and integer to pointer conversion] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
        /* coverity[misra_c_2012_rule_11_4_violation] */
        pxClientSocket = FREERTOS_INVALID_SOCKET;
    }
    else if( ( pxSocket->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED ) &&
             ( pxSocket->u.xTCP.eTCPState != eTCP_LISTEN ) )
    {
        /* Parent socket is not in listening mode */

        /* MISRA Ref 11.4.1 [Socket error and integer to pointer conversion] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
        /* coverity[misra_c_2012_rule_11_4_violation] */
        pxClientSocket = FREERTOS_INVALID_SOCKET;
    }
    else
    {
        /* Loop will stop with breaks. */
        for( ; ; )
        {
            pxClientSocket = prvAcceptWaitClient( pxSocket, pxAddress, pxAddressLength );

            if( pxClientSocket != NULL )
            {
                if( pxSocket->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED )
                {
                    /* Ask to set an event in 'xEventGroup' as soon as a new
                     * client gets connected for this listening socket. */
                    xAskEvent.eEventType = eTCPAcceptEvent;
                    xAskEvent.pvData = pxSocket;
                    ( void ) xSendEventStructToIPTask( &xAskEvent, portMAX_DELAY );
                }

                break;
            }

            if( xTimed == pdFALSE )
            {
                /* Only in the first round, check for non-blocking */
                xRemainingTime = pxSocket->xReceiveBlockTime;

                if( xRemainingTime == ( TickType_t ) 0 )
                {
                    break;
                }

                /* Don't get here a second time */
                xTimed = pdTRUE;

                /* Fetch the current time */
                vTaskSetTimeOutState( &xTimeOut );
            }

            /* Has the timeout been reached? */
            if( xTaskCheckForTimeOut( &xTimeOut, &xRemainingTime ) != pdFALSE )
            {
                break;
            }

            /* Put the calling task to 'sleep' until a down-stream event is received. */
            ( void ) xEventGroupWaitBits( pxSocket->xEventGroup,
                                          ( EventBits_t ) eSOCKET_ACCEPT,
                                          pdTRUE /*xClearOnExit*/,
                                          pdFALSE /*xWaitAllBits*/,
                                          xRemainingTime );
        }
    }

    return pxClientSocket;
}
/*-----------------------------------------------------------*/

/**
 * @brief Send data using a TCP socket. It is not necessary to have the socket
 *        connected already. Outgoing data will be stored and delivered as soon as
 *        the socket gets connected.
 *
 * @param[in] xSocket: The socket owning the connection.
 * @param[in] pvBuffer: The buffer containing the data. The value of this pointer
 *                      may be NULL in case zero-copy transmissions are used.
 *                      It is used in combination with 'FreeRTOS_get_tx_head()'.
 * @param[in] uxDataLength: The length of the data to be added.
 * @param[in] xFlags: This parameter is not used. (zero or FREERTOS_MSG_DONTWAIT).
 *
 * @return The number of bytes actually sent. Zero when nothing could be sent
 *         or a negative error code in case an error occurred.
 */
BaseType_t FreeRTOS_send( Socket_t xSocket,
                          const void * pvBuffer,
                          size_t uxDataLength,
                          BaseType_t xFlags )
{
    BaseType_t xByteCount = -pdFREERTOS_ERRNO_EINVAL;
    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;

    if( pvBuffer != NULL )
    {
        /* Check if this is a valid TCP socket, affirm that it is not closed or closing,
         * affirm that there was not malloc-problem, test if uxDataLength is non-zero,
         * and if the connection is not in a confirmed FIN state. */
        xByteCount = ( BaseType_t ) prvTCPSendCheck( pxSocket, uxDataLength );
    }

    if( xByteCount > 0 )
    {
        /* prvTCPSendLoop() will try to send as many bytes as possible,
         * returning number of bytes that have been queued for transmission.. */
        xByteCount = prvTCPSendLoop( pxSocket, pvBuffer, uxDataLength, xFlags );

        if( xByteCount == 0 )
        {
            if( pxSocket->u.xTCP.eTCPState > eESTABLISHED )
            {
                xByteCount = ( BaseType_t ) -pdFREERTOS_ERRNO_ENOTCONN;
            }
            else
            {
                if( ipconfigTCP_MAY_LOG_PORT( pxSocket->usLocalPort ) )
                {
                    FreeRTOS_debug_printf( ( "FreeRTOS_send: %u -> %xip:%d: no space\n",
                                             pxSocket->usLocalPort,
                                             ( unsigned ) pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4,
                                             pxSocket->u.xTCP.usRemotePort ) );
                }

                xByteCount = ( BaseType_t ) -pdFREERTOS_ERRNO_ENOSPC;
            }
        }
    }

    return xByteCount;
}
/*-----------------------------------------------------------*/

/**
 * @brief Read incoming data from a TCP socket. Only after the last
 *        byte has been read, a close error might be returned.
 *
 * @param[in] xSocket: The socket owning the connection.
 * @param[out] pvBuffer: The buffer to store the incoming data in.
 * @param[in] uxBufferLength: The length of the buffer so that the function
 *                            does not do out of bound access.
 * @param[in] xFlags: The flags for conveying preference. The values
 *                    FREERTOS_MSG_DONTWAIT, FREERTOS_ZERO_COPY and/or
 *                    FREERTOS_MSG_PEEK can be used.
 *
 * @return The number of bytes actually received and stored in the pvBuffer.
 */
BaseType_t FreeRTOS_recv( Socket_t xSocket,
                          void * pvBuffer,
                          size_t uxBufferLength,
                          BaseType_t xFlags )
{
    BaseType_t xByteCount = 0;
    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
    EventBits_t xEventBits = ( EventBits_t ) 0U;

    /* Check if the socket is valid, has type TCP and if it is bound to a
     * port. */
    if( vSocketValid( pxSocket, FREERTOS_IPPROTO_TCP, pdTRUE ) == pdFALSE )
    {
        xByteCount = -pdFREERTOS_ERRNO_EINVAL;
    }
    else if( ( ( ( uint32_t ) xFlags & ( uint32_t ) FREERTOS_ZERO_COPY ) != 0U ) &&
             ( pvBuffer == NULL ) )
    {
        /* In zero-copy mode, pvBuffer is a pointer to a pointer ( not NULL ). */
        xByteCount = -pdFREERTOS_ERRNO_EINVAL;
    }
    else
    {
        /* The function parameters have been checked, now wait for incoming data. */
        xByteCount = prvRecvWait( pxSocket, &( xEventBits ), xFlags );

        #if ( ipconfigSUPPORT_SIGNALS != 0 )
            if( ( xEventBits & ( EventBits_t ) eSOCKET_INTR ) != 0U )
            {
                if( ( xEventBits & ( ( EventBits_t ) eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED ) ) != 0U )
                {
                    /* Shouldn't have cleared other flags. */
                    xEventBits &= ~( ( EventBits_t ) eSOCKET_INTR );
                    ( void ) xEventGroupSetBits( pxSocket->xEventGroup, xEventBits );
                }

                xByteCount = -pdFREERTOS_ERRNO_EINTR;
            }
            else
        #endif /* ipconfigSUPPORT_SIGNALS */

        if( xByteCount > 0 )
        {
            /* Get the actual data from the buffer, or in case of zero-copy,
             * let *pvBuffer point to the RX-stream of the socket. */
            xByteCount = prvRecvData( pxSocket, pvBuffer, uxBufferLength, xFlags );
        }
    } /* vSocketValid() */

    return xByteCount;
}
/*-----------------------------------------------------------*/

/**
 * @brief Shutdown - This function will shut down the connection in both
 *        directions. However, it will first deliver all data queued for
 *        transmission, and also it will first wait to receive any missing
 *        packets from the peer.
 *
 * @param[in] xSocket: The socket owning the connection.
 * @param[in] xHow: Not used. Just present to stick to Berkeley standard.
 *
 * @return 0 on successful shutdown or else a negative error code.
 */
BaseType_t FreeRTOS_shutdown( Socket_t xSocket,
                              BaseType_t xHow )
{
    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
    BaseType_t xResult;

    if( vSocketValid( pxSocket, FREERTOS_IPPROTO_TCP, pdTRUE ) == pdFALSE )
    {
        /*_RB_ Is this comment correct?  The socket is not of a type that
         * supports the listen() operation. */
        xResult = -pdFREERTOS_ERRNO_EOPNOTSUPP;
    }
    else if( pxSocket->u.xTCP.eTCPState != eESTABLISHED )
    {
        /* The socket is not connected. */
        xResult = -pdFREERTOS_ERRNO_ENOTCONN;
    }
    else
    {
        pxSocket->u.xTCP.bits.bUserShutdown = pdTRUE_UNSIGNED;

        /* Let the IP-task perform the shutdown of the connection. */
        pxSocket->u.xTCP.usTimeout = 1U;
        ( void ) xSendEventToIPTask( eTCPTimerEvent );
        xResult = 0;
    }

    ( void ) xHow;

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Returns the number of bytes which can be read from the RX stream buffer.
 *
 * @param[in] xSocket: the socket to get the number of bytes from.
 *
 * @return Returns the number of bytes which can be read. Or an error
 *         code is returned.
 */
BaseType_t FreeRTOS_rx_size( ConstSocket_t xSocket )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
    BaseType_t xReturn;

    if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        xReturn = -pdFREERTOS_ERRNO_EINVAL;
    }
    else if( pxSocket->u.xTCP.rxStream != NULL )
    {
        xReturn = ( BaseType_t ) uxStreamBufferGetSize( pxSocket->u.xTCP.rxStream );
    }
    else
    {
        xReturn = 0;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the number of bytes that can be written in the Tx buffer
 *        of the given socket.
 *
 * @param[in] xSocket: the socket to be checked.
 *
 * @return The bytes that can be written. Or else an error code.
 */
BaseType_t FreeRTOS_tx_space( ConstSocket_t xSocket )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
    BaseType_t xReturn;

    if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        xReturn = -pdFREERTOS_ERRNO_EINVAL;
    }
    else
    {
        if( pxSocket->u.xTCP.txStream != NULL )
        {
            xReturn = ( BaseType_t ) uxStreamBufferGetSpace( pxSocket->u.xTCP.txStream );
        }
        else
        {
            xReturn = ( BaseType_t ) pxSocket->u.xTCP.uxTxStreamSize;
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Returns the number of bytes stored in the Tx buffer.
 *
 * @param[in] xSocket: The socket to be checked.
 *
 * @return The number of bytes stored in the Tx buffer of the socket.
 *         Or an error code.
 */
BaseType_t FreeRTOS_tx_size( ConstSocket_t xSocket )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
    BaseType_t xReturn;

    if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        xReturn = -pdFREERTOS_ERRNO_EINVAL;
    }
    else
    {
        if( pxSocket->u.xTCP.txStream != NULL )
        {
            xReturn = ( BaseType_t ) uxStreamBufferGetSize( pxSocket->u.xTCP.txStream );
        }
        else
        {
            xReturn = 0;
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Is the socket connected.
 *
 * @param[in] xSocket: The socket being checked.
 *
 * @return pdTRUE if TCP socket is connected.
 */
BaseType_t FreeRTOS_issocketconnected( ConstSocket_t xSocket )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
    BaseType_t xReturn = pdFALSE;

    if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        xReturn = -pdFREERTOS_ERRNO_EINVAL;
    }
    else
    {
        if( pxSocket->u.xTCP.eTCPState >= eESTABLISHED )
        {
            if( pxSocket->u.xTCP.eTCPState < eCLOSE_WAIT )
            {
                xReturn = pdTRUE;
            }
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Function to get the remote IP-address and port number.
 *
 * @param[in] xSocket: Socket owning the connection.
 * @param[out] pxAddress: The address pointer to which the address
 *                        is to be added.
 *
 * @return The size of the address being returned. Or else a negative
 *         error code will be returned.
 */

/* Function to get the remote address and IP port */
BaseType_t FreeRTOS_GetRemoteAddress( ConstSocket_t xSocket,
                                      struct freertos_sockaddr * pxAddress )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
    BaseType_t xResult;

    if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        xResult = -pdFREERTOS_ERRNO_EINVAL;
    }
    else
    {
        /* BSD style sockets communicate IP and port addresses in network
         * byte order.
         * IP address of remote machine. */
        if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
        {
            pxAddress->sin_family = FREERTOS_AF_INET6;

            /* IP address of remote machine. */
            ( void ) memcpy( pxAddress->sin_addr6.ucBytes, pxSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, sizeof( pxAddress->sin_addr6.ucBytes ) );

            /* Port of remote machine. */
            pxAddress->sin_port = FreeRTOS_htons( pxSocket->u.xTCP.usRemotePort );
        }
        else
        {
            pxAddress->sin_len = ( uint8_t ) sizeof( *pxAddress );
            pxAddress->sin_family = FREERTOS_AF_INET;

            /* IP address of remote machine. */
            pxAddress->sin_addr = FreeRTOS_htonl( pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4 );

            /* Port on remote machine. */
            pxAddress->sin_port = FreeRTOS_htons( pxSocket->u.xTCP.usRemotePort );
        }

        xResult = ( BaseType_t ) sizeof( *pxAddress );
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the version of IP: either 'ipTYPE_IPv4' or 'ipTYPE_IPv6'.
 *
 * @param[in] xSocket : The socket to be checked.
 *
 * @return Either ipTYPE_IPv4 or ipTYPE_IPv6.
 */
BaseType_t FreeRTOS_GetIPType( ConstSocket_t xSocket )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
    BaseType_t xResult;

    if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
    {
        xResult = ( BaseType_t ) ipTYPE_IPv6;
    }
    else
    {
        xResult = ( BaseType_t ) ipTYPE_IPv4;
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Check the number of bytes that may be added to txStream.
 *
 * @param[in] xSocket: The socket to be checked.
 *
 * @return the number of bytes that may be added to txStream or
 *         else a negative error code.
 */
BaseType_t FreeRTOS_maywrite( ConstSocket_t xSocket )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
    BaseType_t xResult = 0;

    if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        xResult = -pdFREERTOS_ERRNO_EINVAL;
    }
    else if( pxSocket->u.xTCP.eTCPState != eESTABLISHED )
    {
        if( ( pxSocket->u.xTCP.eTCPState < eCONNECT_SYN ) || ( pxSocket->u.xTCP.eTCPState > eESTABLISHED ) )
        {
            xResult = -1;
        }
    }
    else if( pxSocket->u.xTCP.txStream == NULL )
    {
        xResult = ( BaseType_t ) pxSocket->u.xTCP.uxTxStreamSize;
    }
    else
    {
        xResult = ( BaseType_t ) uxStreamBufferGetSpace( pxSocket->u.xTCP.txStream );
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the actual value of Maximum Segment Size ( MSS ) being used.
 *
 * @param[in] xSocket: The socket whose MSS is to be returned.
 *
 * @return the actual size of MSS being used or an error code.
 */
BaseType_t FreeRTOS_mss( ConstSocket_t xSocket )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
    BaseType_t xReturn;

    if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        xReturn = -pdFREERTOS_ERRNO_EINVAL;
    }
    else
    {
        /* usMSS is declared as uint16_t to save space.  FreeRTOS_mss()
         * will often be used in signed native-size expressions cast it to
         * BaseType_t. */
        xReturn = ( BaseType_t ) ( pxSocket->u.xTCP.usMSS );
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the connection status. The values correspond to the members
 *        of the enum 'eIPTCPState_t'.
 *
 * @param[in] xSocket: Socket to get the connection status from.
 *
 * @return The connection status or an error code.
 *
 * @note For internal use only.
 */
BaseType_t FreeRTOS_connstatus( ConstSocket_t xSocket )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
    BaseType_t xReturn;

    if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
    {
        xReturn = -pdFREERTOS_ERRNO_EINVAL;
    }
    else
    {
        /* Cast it to BaseType_t. */
        xReturn = ( BaseType_t ) ( pxSocket->u.xTCP.eTCPState );
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get a direct pointer to the circular transmit buffer.
 *
 * @param[in] xSocket: The socket owning the buffer.
 * @param[in] pxLength: This will contain the number of bytes that may be written.
 *
 * @return Head of the circular transmit buffer if all checks pass. Or else, NULL
 *         is returned.
 */
uint8_t * FreeRTOS_get_tx_head( ConstSocket_t xSocket,
                                BaseType_t * pxLength )
{
    uint8_t * pucReturn = NULL;
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
    StreamBuffer_t * pxBuffer = NULL;

    *pxLength = 0;

    /* Confirm that this is a TCP socket before dereferencing structure
     * member pointers. */
    if( vSocketValid( pxSocket, FREERTOS_IPPROTO_TCP, pdFALSE ) == pdTRUE )
    {
        pxBuffer = pxSocket->u.xTCP.txStream;

        if( pxBuffer != NULL )
        {
            size_t uxSpace = uxStreamBufferGetSpace( pxBuffer );
            size_t uxRemain = pxBuffer->LENGTH - pxBuffer->uxHead;

            if( uxRemain <= uxSpace )
            {
                *pxLength = ( BaseType_t ) uxRemain;
            }
            else
            {
                *pxLength = ( BaseType_t ) uxSpace;
            }

            pucReturn = &( pxBuffer->ucArray[ pxBuffer->uxHead ] );
        }
    }

    return pucReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief For the web server: borrow the circular Rx buffer for inspection.
 *        HTML driver wants to see if a sequence of 13/10/13/10 is available.
 *
 * @param[in] xSocket: The socket whose Rx stream is to be returned.
 *
 * @return The Rx stream of the socket if all checks pass, else NULL.
 */
const struct xSTREAM_BUFFER * FreeRTOS_get_rx_buf( ConstSocket_t xSocket )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
    const struct xSTREAM_BUFFER * pxReturn = NULL;


    /* Confirm that this is a TCP socket before dereferencing structure
     * member pointers. */
    if( vSocketValid( pxSocket, FREERTOS_IPPROTO_TCP, pdFALSE ) == pdTRUE )
    {
        pxReturn = pxSocket->u.xTCP.rxStream;
    }

    return pxReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the net status. The IP-task will print a summary of all sockets and
 *        their connections.
 */
void FreeRTOS_netstat( void )
{
    IPStackEvent_t xAskEvent;

    /* Ask the IP-task to call vTCPNetStat()
     * to avoid accessing xBoundTCPSocketsList
     */
    xAskEvent.eEventType = eTCPNetStat;
    xAskEvent.pvData = ( void * ) NULL;
    ( void ) xSendEventStructToIPTask( &xAskEvent, pdMS_TO_TICKS( 1000U ) );
}
/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
#endif /* ipconfigUSE_TCP == 1 */
/* *INDENT-ON* */
