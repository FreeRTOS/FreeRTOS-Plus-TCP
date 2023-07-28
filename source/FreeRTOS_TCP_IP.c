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
 * @file FreeRTOS_TCP_IP.c
 * @brief Module which handles the TCP connections for FreeRTOS+TCP.
 * It depends on  FreeRTOS_TCP_WIN.c, which handles the TCP windowing
 * schemes.
 *
 * Endianness: in this module all ports and IP addresses are stored in
 * host byte-order, except fields in the IP-packets
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
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"

#include "FreeRTOS_TCP_Reception.h"
#include "FreeRTOS_TCP_Transmission.h"
#include "FreeRTOS_TCP_State_Handling.h"
#include "FreeRTOS_TCP_Utils.h"

/* Just make sure the contents doesn't get compiled if TCP is not enabled. */
#if ipconfigUSE_TCP == 1



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
    _static FreeRTOS_Socket_t * xSocketToListen = NULL;

    #if ( ipconfigHAS_DEBUG_PRINTF != 0 )

/*
 * For logging and debugging: make a string showing the TCP flags.
 */
        const char * prvTCPFlagMeaning( UBaseType_t xFlags );
    #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */


/*-----------------------------------------------------------*/


/** @brief Close the socket another time.
 *
 * @param[in] pxSocket The socket to be checked.
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
 * @param[in] pxSocket The socket to be checked.
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
 * @brief As soon as a TCP socket timer expires, this function will be called
 *       (from xTCPTimerCheck). It can send a delayed ACK or new data.
 *
 * @param[in] pxSocket socket to be checked.
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
    BaseType_t xTCPSocketCheck( FreeRTOS_Socket_t * pxSocket )
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

                            prvTCPReturnPacket( pxSocket, pxSocket->u.xTCP.pxAckMessage, ( uint32_t ) ( uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER ), ipconfigZERO_COPY_TX_DRIVER );

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
 * @brief 'Touch' the socket to keep it alive/updated.
 *
 * @param[in] pxSocket The socket to be updated.
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

/**
 * @brief Changing to a new state. Centralised here to do specific actions such as
 *        resetting the alive timer, calling the user's OnConnect handler to notify
 *        that a socket has got (dis)connected, and setting bit to unblock a call to
 *        FreeRTOS_select().
 *
 * @param[in] pxSocket The socket whose state we are trying to change.
 * @param[in] eTCPState The state to which we want to change to.
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
                                     FreeRTOS_GetTCPStateName( ( UBaseType_t ) xPreviousState ),
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

                    ( void ) xTaskResumeAll();

                    FreeRTOS_printf( ( "vTCPStateChange: Closing socket\n" ) );

                    if( pxSocket->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED )
                    {
                        configASSERT( xIsCallingFromIPTask() != pdFALSE );
                        vSocketCloseNextTime( pxSocket );
                    }
                }
                else
                {
                    ( void ) xTaskResumeAll();
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
                    char pcBuffer[ 40 ];

                    switch( pxSocket->bits.bIsIPv6 ) /* LCOV_EXCL_BR_LINE */
                    {
                        #if ( ipconfigUSE_IPv4 != 0 )
                            case pdFALSE_UNSIGNED:
                               {
                                   uint32_t ulIPAddress = FreeRTOS_ntohl( pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4 );
                                   FreeRTOS_inet_ntop( FREERTOS_AF_INET4,
                                                       ( const uint8_t * ) &ulIPAddress,
                                                       pcBuffer,
                                                       sizeof( pcBuffer ) );
                               }
                               break;
                        #endif /* ( ipconfigUSE_IPv4 != 0 ) */

                        #if ( ipconfigUSE_IPv6 != 0 )
                            case pdTRUE_UNSIGNED:
                                FreeRTOS_inet_ntop( FREERTOS_AF_INET6,
                                                    pxSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes,
                                                    pcBuffer,
                                                    sizeof( pcBuffer ) );
                                break;
                        #endif /* ( ipconfigUSE_IPv6 != 0 ) */

                        default:   /* LCOV_EXCL_LINE */
                            /* MISRA 16.4 Compliance */
                            break; /* LCOV_EXCL_LINE */
                    }

                    FreeRTOS_debug_printf( ( "Socket %u -> [%s]:%u State %s->%s\n",
                                             pxSocket->usLocalPort,
                                             pcBuffer,
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
 * @brief Calculate after how much time this socket needs to be checked again.
 *
 * @param[in] pxSocket The socket to be checked.
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
 * @brief Process the received TCP packet.
 *
 * @param[in] pxDescriptor The descriptor in which the TCP packet is held.
 *
 * @return If the processing of the packet was successful, then pdPASS is returned
 *         or else pdFAIL.
 *
 * @note FreeRTOS_TCP_IP has only 2 public functions, this is the second one:
 *  xProcessReceivedTCPPacket()
 *      prvTCPHandleState()
 *          prvTCPPrepareSend()
 *              prvTCPReturnPacket()
 *              xNetworkInterfaceOutput()  // Sends data to the NIC
 *      prvTCPSendRepeated()
 *          prvTCPReturnPacket()        // Prepare for returning
 *          xNetworkInterfaceOutput()   // Sends data to the NIC
 */
    BaseType_t xProcessReceivedTCPPacket( NetworkBufferDescriptor_t * pxDescriptor )
    {
        /* Function might modify the parameter. */
        const NetworkBufferDescriptor_t * pxNetworkBuffer = pxDescriptor;

        configASSERT( pxNetworkBuffer != NULL );
        configASSERT( pxNetworkBuffer->pucEthernetBuffer != NULL );

        BaseType_t xResult;

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        switch( ( ( const EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer )->usFrameType )
        {
            #if ( ipconfigUSE_IPv4 != 0 )
                case ipIPv4_FRAME_TYPE:
                    xResult = xProcessReceivedTCPPacket_IPV4( pxDescriptor );
                    break;
            #endif /* ( ipconfigUSE_IPv4 != 0 ) */

            #if ( ipconfigUSE_IPv6 != 0 )
                case ipIPv6_FRAME_TYPE:
                    xResult = xProcessReceivedTCPPacket_IPV6( pxDescriptor );
                    break;
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */

            default:
                /* Shouldn't reach here */
                xResult = pdFAIL;
                break;
        }

        return xResult;
    }
    /*-----------------------------------------------------------*/


/**
 * @brief In the API accept(), the user asks is there is a new client? As API's can
 *        not walk through the xBoundTCPSocketsList the IP-task will do this.
 *
 * @param[in] pxSocket The socket for which the bound socket list will be iterated.
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


#endif /* ipconfigUSE_TCP == 1 */

/* Provide access to private members for testing. */
#ifdef FREERTOS_ENABLE_UNIT_TESTS
    #include "freertos_tcp_test_access_tcp_define.h"
#endif

/* Provide access to private members for verification. */
#ifdef FREERTOS_TCP_ENABLE_VERIFICATION
    #include "aws_freertos_tcp_verification_access_tcp_define.h"
#endif
