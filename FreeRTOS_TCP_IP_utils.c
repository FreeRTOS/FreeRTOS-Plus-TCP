/*
 * FreeRTOS+TCP V2.3.3
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file FreeRTOS_TCP_IP_utils.c
 *
 * This module contains a set of relatively unrelated functions
 * that are called from other FreeRTOS_TCP_IP modules.
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
#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_TCP_IP_utils.h"


/* Just make sure the contents doesn't get compiled if TCP is not enabled. */
#if ipconfigUSE_TCP == 1

/**
 * @brief Set the MSS (Maximum segment size) associated with the given socket.
 *
 * @param[in] pxSocket: The socket whose MSS is to be set.
 */
    void prvSocketSetMSS( FreeRTOS_Socket_t * pxSocket )
    {
        uint32_t ulMSS = ipconfigTCP_MSS;

        if( ( ( FreeRTOS_ntohl( pxSocket->u.xTCP.ulRemoteIP ) ^ *ipLOCAL_IP_ADDRESS_POINTER ) & xNetworkAddressing.ulNetMask ) != 0UL )
        {
            /* Data for this peer will pass through a router, and maybe through
             * the internet.  Limit the MSS to 1400 bytes or less. */
            ulMSS = FreeRTOS_min_uint32( ( uint32_t ) tcpREDUCED_MSS_THROUGH_INTERNET, ulMSS );
        }

        FreeRTOS_debug_printf( ( "prvSocketSetMSS: %lu bytes for %lxip:%u\n", ulMSS, pxSocket->u.xTCP.ulRemoteIP, pxSocket->u.xTCP.usRemotePort ) );

        pxSocket->u.xTCP.usInitMSS = ( uint16_t ) ulMSS;
        pxSocket->u.xTCP.usCurMSS = ( uint16_t ) ulMSS;
    }
    /*-----------------------------------------------------------*/


/**
 * @brief Create the TCP window for the given socket.
 *
 * @param[in] pxSocket: The socket for which the window is being created.
 *
 * @note The SYN event is very important: the sequence numbers, which have a kind of
 *       random starting value, are being synchronized. The sliding window manager
 *       (in FreeRTOS_TCP_WIN.c) needs to know them, along with the Maximum Segment
 *       Size (MSS).
 */
    void prvTCPCreateWindow( FreeRTOS_Socket_t * pxSocket )
    {
        if( xTCPWindowLoggingLevel != 0 )
        {
            FreeRTOS_debug_printf( ( "Limits (using): TCP Win size %u Water %u <= %u <= %u\n",
                                     ( unsigned ) pxSocket->u.xTCP.uxRxWinSize * ipconfigTCP_MSS,
                                     ( unsigned ) pxSocket->u.xTCP.uxLittleSpace,
                                     ( unsigned ) pxSocket->u.xTCP.uxEnoughSpace,
                                     ( unsigned ) pxSocket->u.xTCP.uxRxStreamSize ) );
        }

        vTCPWindowCreate(
            &pxSocket->u.xTCP.xTCPWindow,
            ipconfigTCP_MSS * pxSocket->u.xTCP.uxRxWinSize,
            ipconfigTCP_MSS * pxSocket->u.xTCP.uxTxWinSize,
            pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber,
            pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber,
            ( uint32_t ) pxSocket->u.xTCP.usInitMSS );
    }
    /*-----------------------------------------------------------*/


/**
 * @brief The API FreeRTOS_send() adds data to the TX stream. Add
 *        this data to the windowing system to it can be transmitted.
 *
 * @param[in] pxSocket: The socket owning the connection.
 */
    void prvTCPAddTxData( FreeRTOS_Socket_t * pxSocket )
    {
        int32_t lCount, lLength;

        /* A txStream has been created already, see if the socket has new data for
         * the sliding window.
         *
         * uxStreamBufferMidSpace() returns the distance between rxHead and rxMid.  It
         * contains new Tx data which has not been passed to the sliding window yet.
         * The oldest data not-yet-confirmed can be found at rxTail. */
        lLength = ( int32_t ) uxStreamBufferMidSpace( pxSocket->u.xTCP.txStream );

        if( lLength > 0 )
        {
            /* All data between txMid and rxHead will now be passed to the sliding
             * window manager, so it can start transmitting them.
             *
             * Hand over the new data to the sliding window handler.  It will be
             * split-up in chunks of 1460 bytes each (or less, depending on
             * ipconfigTCP_MSS). */
            lCount = lTCPWindowTxAdd( &pxSocket->u.xTCP.xTCPWindow,
                                      ( uint32_t ) lLength,
                                      ( int32_t ) pxSocket->u.xTCP.txStream->uxMid,
                                      ( int32_t ) pxSocket->u.xTCP.txStream->LENGTH );

            /* Move the rxMid pointer forward up to rxHead. */
            if( lCount > 0 )
            {
                vStreamBufferMoveMid( pxSocket->u.xTCP.txStream, ( size_t ) lCount );
            }
        }
    }
    /*-----------------------------------------------------------*/


/**
 * @brief Check if the size of a network buffer is big enough to hold the outgoing message.
 *        Allocate a new bigger network buffer when necessary.
 *
 * @param[in] pxSocket: Socket whose buffer is being resized.
 * @param[in] pxNetworkBuffer: The network buffer whose size is being increased.
 * @param[in] lDataLen: Length of the data to be put in the buffer.
 * @param[in] uxOptionsLength: Length of options.
 *
 * @return If the resizing is successful: The new buffer with the size being asked for
 *                with old data copied in it.
 *         Else, NULL.
 *
 * @note The old network buffer will be released if the resizing is successful and
 *       cannot be used any longer.
 */
    NetworkBufferDescriptor_t * prvTCPBufferResize( const FreeRTOS_Socket_t * pxSocket,
                                                    NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                    int32_t lDataLen,
                                                    UBaseType_t uxOptionsLength )
    {
        NetworkBufferDescriptor_t * pxReturn;
        size_t uxNeeded;
        BaseType_t xResize;

        if( xBufferAllocFixedSize != pdFALSE )
        {
            /* Network buffers are created with a fixed size and can hold the largest
             * MTU. */
            uxNeeded = ( size_t ) ipTOTAL_ETHERNET_FRAME_SIZE;

            /* and therefore, the buffer won't be too small.
             * Only ask for a new network buffer in case none was supplied. */
            if( pxNetworkBuffer == NULL )
            {
                xResize = pdTRUE;
            }
            else
            {
                xResize = pdFALSE;
            }
        }
        else
        {
            /* Network buffers are created with a variable size. See if it must
             * grow. */
            uxNeeded = ipNUMERIC_CAST( size_t, ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength ) + lDataLen;

            if( uxNeeded < sizeof( pxSocket->u.xTCP.xPacket.u.ucLastPacket ) )
            {
                uxNeeded = sizeof( pxSocket->u.xTCP.xPacket.u.ucLastPacket );
            }

            /* In case we were called from a TCP timer event, a buffer must be
             *  created.  Otherwise, test 'xDataLength' of the provided buffer. */
            if( ( pxNetworkBuffer == NULL ) || ( pxNetworkBuffer->xDataLength < uxNeeded ) )
            {
                xResize = pdTRUE;
            }
            else
            {
                xResize = pdFALSE;
            }
        }

        if( xResize != pdFALSE )
        {
            /* The caller didn't provide a network buffer or the provided buffer is
             * too small.  As we must send-out a data packet, a buffer will be created
             * here. */
            pxReturn = pxGetNetworkBufferWithDescriptor( uxNeeded, 0U );

            if( pxReturn != NULL )
            {
                /* Set the actual packet size, in case the returned buffer is larger. */
                pxReturn->xDataLength = uxNeeded;

                /* Copy the existing data to the new created buffer. */
                if( pxNetworkBuffer != NULL )
                {
                    /* Either from the previous buffer... */
                    ( void ) memcpy( pxReturn->pucEthernetBuffer, pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength );

                    /* ...and release it. */
                    vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
                }
                else
                {
                    /* Or from the socket field 'xTCP.xPacket'. */
                    ( void ) memcpy( pxReturn->pucEthernetBuffer, pxSocket->u.xTCP.xPacket.u.ucLastPacket, sizeof( pxSocket->u.xTCP.xPacket.u.ucLastPacket ) );
                }
            }
        }
        else
        {
            /* xResize is false, the network buffer provided was big enough. */
            configASSERT( pxNetworkBuffer != NULL ); /* to tell lint: when xResize is false, pxNetworkBuffer is not NULL. */
            pxReturn = pxNetworkBuffer;

            pxNetworkBuffer->xDataLength = ( size_t ) ( ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength ) + ( size_t ) lDataLen;
        }

        return pxReturn;
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
        FreeRTOS_Socket_t * xParent = NULL;
        BaseType_t bBefore = ipNUMERIC_CAST( BaseType_t, tcpNOW_CONNECTED( ( BaseType_t ) pxSocket->u.xTCP.ucTCPState ) ); /* Was it connected ? */
        BaseType_t bAfter = ipNUMERIC_CAST( BaseType_t, tcpNOW_CONNECTED( ( BaseType_t ) eTCPState ) );                    /* Is it connected now ? */

        #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
            BaseType_t xPreviousState = ( BaseType_t ) pxSocket->u.xTCP.ucTCPState;
        #endif
        #if ( ipconfigUSE_CALLBACKS == 1 )
            FreeRTOS_Socket_t * xConnected = NULL;
        #endif

        /* Has the connected status changed? */
        if( bBefore != bAfter )
        {
            /* Is the socket connected now ? */
            if( bAfter != pdFALSE )
            {
                /* if bPassQueued is true, this socket is an orphan until it gets connected. */
                if( pxSocket->u.xTCP.bits.bPassQueued != pdFALSE_UNSIGNED )
                {
                    /* Now that it is connected, find it's parent. */
                    if( pxSocket->u.xTCP.bits.bReuseSocket != pdFALSE_UNSIGNED )
                    {
                        xParent = pxSocket;
                    }
                    else
                    {
                        xParent = pxSocket->u.xTCP.pxPeerSocket;
                        configASSERT( xParent != NULL );
                    }

                    if( xParent != NULL )
                    {
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
                /* Notify/wake-up the socket-owner by setting a semaphore. */
                pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_CLOSED;

                #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
                    {
                        if( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_EXCEPT ) != 0U )
                        {
                            pxSocket->xEventBits |= ( ( EventBits_t ) eSELECT_EXCEPT ) << SOCKET_EVENT_BIT_COUNT;
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

            if( prvTCPSocketIsActive( ipNUMERIC_CAST( eIPTCPState_t, pxSocket->u.xTCP.ucTCPState ) ) == 0 )
            {
                /* Now the socket isn't in an active state anymore so it
                 * won't need further attention of the IP-task.
                 * Setting time-out to zero means that the socket won't get checked during
                 * timer events. */
                pxSocket->u.xTCP.usTimeout = 0U;
            }
        }
        else
        {
            if( ( eTCPState == eCLOSED ) ||
                ( eTCPState == eCLOSE_WAIT ) )
            {
                /* Socket goes to status eCLOSED because of a RST.
                 * When nobody owns the socket yet, delete it. */
                if( ( pxSocket->u.xTCP.bits.bPassQueued != pdFALSE_UNSIGNED ) ||
                    ( pxSocket->u.xTCP.bits.bPassAccept != pdFALSE_UNSIGNED ) )
                {
                    FreeRTOS_debug_printf( ( "vTCPStateChange: Closing socket\n" ) );

                    if( pxSocket->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED )
                    {
                        configASSERT( xIsCallingFromIPTask() != pdFALSE );
                        vSocketCloseNextTime( pxSocket );
                    }
                }
            }
        }

        /* Fill in the new state. */
        pxSocket->u.xTCP.ucTCPState = ( uint8_t ) eTCPState;

        /* Touch the alive timers because moving to another state. */
        prvTCPTouchSocket( pxSocket );

        #if ( ipconfigHAS_DEBUG_PRINTF == 1 )
            {
                if( ( xTCPWindowLoggingLevel >= 0 ) && ( ipconfigTCP_MAY_LOG_PORT( pxSocket->usLocalPort ) ) )
                {
                    FreeRTOS_debug_printf( ( "Socket %d -> %lxip:%u State %s->%s\n",
                                             pxSocket->usLocalPort,
                                             pxSocket->u.xTCP.ulRemoteIP,
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
 * @brief Check whether the socket is active or not.
 *
 * @param[in] xStatus: The status of the socket.
 *
 * @return pdTRUE if the socket must be checked. Non-active sockets
 *         are waiting for user action, either connect() or close().
 */
    BaseType_t prvTCPSocketIsActive( eIPTCPState_t xStatus )
    {
        BaseType_t xResult;

        switch( xStatus )
        {
            case eCLOSED:
            case eCLOSE_WAIT:
            case eFIN_WAIT_2:
            case eCLOSING:
            case eTIME_WAIT:
                xResult = pdFALSE;
                break;

            case eTCP_LISTEN:
            case eCONNECT_SYN:
            case eSYN_FIRST:
            case eSYN_RECEIVED:
            case eESTABLISHED:
            case eFIN_WAIT_1:
            case eLAST_ACK:
            default:
                xResult = pdTRUE;
                break;
        }

        return xResult;
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
    void prvTCPTouchSocket( FreeRTOS_Socket_t * pxSocket )
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

    #if ( ipconfigUSE_TCP_WIN != 0 )

/**
 * @brief Get the window scaling factor for the TCP connection.
 *
 * @param[in] pxSocket: The socket owning the TCP connection.
 *
 * @return The scaling factor.
 */
        uint8_t prvWinScaleFactor( const FreeRTOS_Socket_t * pxSocket )
        {
            size_t uxWinSize;
            uint8_t ucFactor;


            /* 'xTCP.uxRxWinSize' is the size of the reception window in units of MSS. */
            uxWinSize = pxSocket->u.xTCP.uxRxWinSize * ( size_t ) pxSocket->u.xTCP.usInitMSS;
            ucFactor = 0U;

            while( uxWinSize > 0xffffUL )
            {
                /* Divide by two and increase the binary factor by 1. */
                uxWinSize >>= 1;
                ucFactor++;
            }

            FreeRTOS_debug_printf( ( "prvWinScaleFactor: uxRxWinSize %u MSS %u Factor %u\n",
                                     ( unsigned ) pxSocket->u.xTCP.uxRxWinSize,
                                     ( unsigned ) pxSocket->u.xTCP.usInitMSS,
                                     ucFactor ) );

            return ucFactor;
        }

    #endif /* if ( ipconfigUSE_TCP_WIN != 0 ) */
    /*-----------------------------------------------------------*/

/**
 * @brief Common code for sending a TCP protocol control packet (i.e. no options, no
 *        payload, just flags).
 *
 * @param[in] pxNetworkBuffer: The network buffer received from the peer.
 * @param[in] ucTCPFlags: The flags to determine what kind of packet this is.
 *
 * @return pdFAIL always indicating that the packet was not consumed.
 */
    BaseType_t prvTCPSendSpecialPacketHelper( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                              uint8_t ucTCPFlags )
    {
        #if ( ipconfigIGNORE_UNKNOWN_PACKETS == 1 )
            /* Configured to ignore unknown packets just suppress a compiler warning. */
            ( void ) pxNetworkBuffer;
            ( void ) ucTCPFlags;
        #else
            {
                /* Map the ethernet buffer onto the TCPPacket_t struct for easy access to the fields. */
                TCPPacket_t * pxTCPPacket = ipCAST_PTR_TO_TYPE_PTR( TCPPacket_t, pxNetworkBuffer->pucEthernetBuffer );
                const uint32_t ulSendLength =
                    ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER ); /* Plus 0 options. */

                pxTCPPacket->xTCPHeader.ucTCPFlags = ucTCPFlags;
                pxTCPPacket->xTCPHeader.ucTCPOffset = ( ipSIZE_OF_TCP_HEADER ) << 2;

                prvTCPReturnPacket( NULL, pxNetworkBuffer, ulSendLength, pdFALSE );
            }
        #endif /* !ipconfigIGNORE_UNKNOWN_PACKETS */

        /* The packet was not consumed. */
        return pdFAIL;
    }
    /*-----------------------------------------------------------*/


/**
 * @brief  Return (or send) a packet to the peer. The data is stored in pxBuffer,
 *         which may either point to a real network buffer or to a TCP socket field
 *         called 'xTCP.xPacket'. A temporary xNetworkBuffer will be used to pass
 *         the data to the NIC.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[in] pxDescriptor: The network buffer descriptor carrying the packet.
 * @param[in] ulLen: Length of the packet being sent.
 * @param[in] xReleaseAfterSend: pdTRUE if the ownership of the descriptor is
 *                               transferred to the network interface.
 */
    void prvTCPReturnPacket( FreeRTOS_Socket_t * pxSocket,
                             NetworkBufferDescriptor_t * pxDescriptor,
                             uint32_t ulLen,
                             BaseType_t xReleaseAfterSend )
    {
        TCPPacket_t * pxTCPPacket;
        IPHeader_t * pxIPHeader;
        BaseType_t xDoRelease = xReleaseAfterSend;
        EthernetHeader_t * pxEthernetHeader;
        uint32_t ulFrontSpace, ulSpace, ulSourceAddress, ulWinSize;
        const TCPWindow_t * pxTCPWindow;
        NetworkBufferDescriptor_t * pxNetworkBuffer = pxDescriptor;
        NetworkBufferDescriptor_t xTempBuffer;
        /* memcpy() helper variables for MISRA Rule 21.15 compliance*/
        const void * pvCopySource;
        void * pvCopyDest;


        /* For sending, a pseudo network buffer will be used, as explained above. */

        if( pxNetworkBuffer == NULL )
        {
            pxNetworkBuffer = &xTempBuffer;

            #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
                {
                    pxNetworkBuffer->pxNextBuffer = NULL;
                }
            #endif
            pxNetworkBuffer->pucEthernetBuffer = pxSocket->u.xTCP.xPacket.u.ucLastPacket;
            pxNetworkBuffer->xDataLength = sizeof( pxSocket->u.xTCP.xPacket.u.ucLastPacket );
            xDoRelease = pdFALSE;
        }

        #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
            {
                if( xDoRelease == pdFALSE )
                {
                    pxNetworkBuffer = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, ( size_t ) pxNetworkBuffer->xDataLength );

                    if( pxNetworkBuffer != NULL )
                    {
                        xDoRelease = pdTRUE;
                    }
                    else
                    {
                        FreeRTOS_debug_printf( ( "prvTCPReturnPacket: duplicate failed\n" ) );
                    }
                }
            }
        #endif /* ipconfigZERO_COPY_TX_DRIVER */

        #ifndef __COVERITY__
            if( pxNetworkBuffer != NULL )
        #endif
        {
            /* Map the ethernet buffer onto a TCPPacket_t struct for easy access to the fields. */
            pxTCPPacket = ipCAST_PTR_TO_TYPE_PTR( TCPPacket_t, pxNetworkBuffer->pucEthernetBuffer );
            pxIPHeader = &pxTCPPacket->xIPHeader;
            pxEthernetHeader = &pxTCPPacket->xEthernetHeader;

            /* Fill the packet, using hton translations. */
            if( pxSocket != NULL )
            {
                /* Calculate the space in the RX buffer in order to advertise the
                 * size of this socket's reception window. */
                pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );

                if( pxSocket->u.xTCP.rxStream != NULL )
                {
                    /* An RX stream was created already, see how much space is
                     * available. */
                    ulFrontSpace = ( uint32_t ) uxStreamBufferFrontSpace( pxSocket->u.xTCP.rxStream );
                }
                else
                {
                    /* No RX stream has been created, the full stream size is
                     * available. */
                    ulFrontSpace = ( uint32_t ) pxSocket->u.xTCP.uxRxStreamSize;
                }

                /* Take the minimum of the RX buffer space and the RX window size. */
                ulSpace = FreeRTOS_min_uint32( pxTCPWindow->xSize.ulRxWindowLength, ulFrontSpace );

                if( ( pxSocket->u.xTCP.bits.bLowWater != pdFALSE_UNSIGNED ) || ( pxSocket->u.xTCP.bits.bRxStopped != pdFALSE_UNSIGNED ) )
                {
                    /* The low-water mark was reached, meaning there was little
                     * space left.  The socket will wait until the application has read
                     * or flushed the incoming data, and 'zero-window' will be
                     * advertised. */
                    ulSpace = 0U;
                }

                /* If possible, advertise an RX window size of at least 1 MSS, otherwise
                 * the peer might start 'zero window probing', i.e. sending small packets
                 * (1, 2, 4, 8... bytes). */
                if( ( ulSpace < pxSocket->u.xTCP.usCurMSS ) && ( ulFrontSpace >= pxSocket->u.xTCP.usCurMSS ) )
                {
                    ulSpace = pxSocket->u.xTCP.usCurMSS;
                }

                /* Avoid overflow of the 16-bit win field. */
                #if ( ipconfigUSE_TCP_WIN != 0 )
                    {
                        ulWinSize = ( ulSpace >> pxSocket->u.xTCP.ucMyWinScaleFactor );
                    }
                #else
                    {
                        ulWinSize = ulSpace;
                    }
                #endif

                if( ulWinSize > 0xfffcUL )
                {
                    ulWinSize = 0xfffcUL;
                }

                pxTCPPacket->xTCPHeader.usWindow = FreeRTOS_htons( ( uint16_t ) ulWinSize );

                /* The new window size has been advertised, switch off the flag. */
                pxSocket->u.xTCP.bits.bWinChange = pdFALSE_UNSIGNED;

                /* Later on, when deciding to delay an ACK, a precise estimate is needed
                 * of the free RX space.  At this moment, 'ulHighestRxAllowed' would be the
                 * highest sequence number minus 1 that the socket will accept. */
                pxSocket->u.xTCP.ulHighestRxAllowed = pxTCPWindow->rx.ulCurrentSequenceNumber + ulSpace;

                #if ( ipconfigTCP_KEEP_ALIVE == 1 )
                    if( pxSocket->u.xTCP.bits.bSendKeepAlive != pdFALSE_UNSIGNED )
                    {
                        /* Sending a keep-alive packet, send the current sequence number
                         * minus 1, which will be recognised as a keep-alive packet and
                         * responded to by acknowledging the last byte. */
                        pxSocket->u.xTCP.bits.bSendKeepAlive = pdFALSE_UNSIGNED;
                        pxSocket->u.xTCP.bits.bWaitKeepAlive = pdTRUE_UNSIGNED;

                        pxTCPPacket->xTCPHeader.ulSequenceNumber = pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber - 1UL;
                        pxTCPPacket->xTCPHeader.ulSequenceNumber = FreeRTOS_htonl( pxTCPPacket->xTCPHeader.ulSequenceNumber );
                    }
                    else
                #endif /* if ( ipconfigTCP_KEEP_ALIVE == 1 ) */
                {
                    pxTCPPacket->xTCPHeader.ulSequenceNumber = FreeRTOS_htonl( pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber );

                    if( ( pxTCPPacket->xTCPHeader.ucTCPFlags & ( uint8_t ) tcpTCP_FLAG_FIN ) != 0U )
                    {
                        /* Suppress FIN in case this packet carries earlier data to be
                         * retransmitted. */
                        uint32_t ulDataLen = ( uint32_t ) ( ulLen - ( ipSIZE_OF_TCP_HEADER + ipSIZE_OF_IPv4_HEADER ) );

                        if( ( pxTCPWindow->ulOurSequenceNumber + ulDataLen ) != pxTCPWindow->tx.ulFINSequenceNumber )
                        {
                            pxTCPPacket->xTCPHeader.ucTCPFlags &= ( ( uint8_t ) ~tcpTCP_FLAG_FIN );
                            FreeRTOS_debug_printf( ( "Suppress FIN for %lu + %lu < %lu\n",
                                                     pxTCPWindow->ulOurSequenceNumber - pxTCPWindow->tx.ulFirstSequenceNumber,
                                                     ulDataLen,
                                                     pxTCPWindow->tx.ulFINSequenceNumber - pxTCPWindow->tx.ulFirstSequenceNumber ) );
                        }
                    }
                }

                /* Tell which sequence number is expected next time */
                pxTCPPacket->xTCPHeader.ulAckNr = FreeRTOS_htonl( pxTCPWindow->rx.ulCurrentSequenceNumber );
            }
            else
            {
                /* Sending data without a socket, probably replying with a RST flag
                 * Just swap the two sequence numbers. */
                vFlip_32( pxTCPPacket->xTCPHeader.ulSequenceNumber, pxTCPPacket->xTCPHeader.ulAckNr );
            }

            pxIPHeader->ucTimeToLive = ( uint8_t ) ipconfigTCP_TIME_TO_LIVE;
            pxIPHeader->usLength = FreeRTOS_htons( ulLen );

            if( ( pxSocket == NULL ) || ( *ipLOCAL_IP_ADDRESS_POINTER == 0UL ) )
            {
                /* When pxSocket is NULL, this function is called by prvTCPSendReset()
                * and the IP-addresses must be swapped.
                * Also swap the IP-addresses in case the IP-tack doesn't have an
                * IP-address yet, i.e. when ( *ipLOCAL_IP_ADDRESS_POINTER == 0UL ). */
                ulSourceAddress = pxIPHeader->ulDestinationIPAddress;
            }
            else
            {
                ulSourceAddress = *ipLOCAL_IP_ADDRESS_POINTER;
            }

            pxIPHeader->ulDestinationIPAddress = pxIPHeader->ulSourceIPAddress;
            pxIPHeader->ulSourceIPAddress = ulSourceAddress;
            vFlip_16( pxTCPPacket->xTCPHeader.usSourcePort, pxTCPPacket->xTCPHeader.usDestinationPort );

            /* Just an increasing number. */
            pxIPHeader->usIdentification = FreeRTOS_htons( usPacketIdentifier );
            usPacketIdentifier++;

            /* The stack doesn't support fragments, so the fragment offset field must always be zero.
             * The header was never memset to zero, so set both the fragment offset and fragmentation flags in one go.
             */
            #if ( ipconfigFORCE_IP_DONT_FRAGMENT != 0 )
                pxIPHeader->usFragmentOffset = ipFRAGMENT_FLAGS_DONT_FRAGMENT;
            #else
                pxIPHeader->usFragmentOffset = 0U;
            #endif

            /* Important: tell NIC driver how many bytes must be sent. */
            pxNetworkBuffer->xDataLength = ulLen + ipSIZE_OF_ETH_HEADER;

            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
                {
                    /* calculate the IP header checksum, in case the driver won't do that. */
                    pxIPHeader->usHeaderChecksum = 0x00U;
                    pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
                    pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );

                    /* calculate the TCP checksum for an outgoing packet. */
                    ( void ) usGenerateProtocolChecksum( ( uint8_t * ) pxTCPPacket, pxNetworkBuffer->xDataLength, pdTRUE );

                    /* A calculated checksum of 0 must be inverted as 0 means the checksum
                     * is disabled. */
                    if( pxTCPPacket->xTCPHeader.usChecksum == 0U )
                    {
                        pxTCPPacket->xTCPHeader.usChecksum = 0xffffU;
                    }
                }
            #endif /* if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 ) */

            #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
                {
                    pxNetworkBuffer->pxNextBuffer = NULL;
                }
            #endif

            /* Fill in the destination MAC addresses. */
            ( void ) memcpy( ( void * ) ( &( pxEthernetHeader->xDestinationAddress ) ),
                             ( const void * ) ( &( pxEthernetHeader->xSourceAddress ) ),
                             sizeof( pxEthernetHeader->xDestinationAddress ) );

            /*
             * Use helper variables for memcpy() to remain
             * compliant with MISRA Rule 21.15.  These should be
             * optimized away.
             */
            /* The source MAC addresses is fixed to 'ipLOCAL_MAC_ADDRESS'. */
            pvCopySource = ipLOCAL_MAC_ADDRESS;
            pvCopyDest = &pxEthernetHeader->xSourceAddress;
            ( void ) memcpy( pvCopyDest, pvCopySource, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

            #if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES )
                {
                    if( pxNetworkBuffer->xDataLength < ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES )
                    {
                        BaseType_t xIndex;

                        for( xIndex = ( BaseType_t ) pxNetworkBuffer->xDataLength; xIndex < ( BaseType_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES; xIndex++ )
                        {
                            pxNetworkBuffer->pucEthernetBuffer[ xIndex ] = 0U;
                        }

                        pxNetworkBuffer->xDataLength = ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES;
                    }
                }
            #endif /* if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES ) */

            /* Send! */
            iptraceNETWORK_INTERFACE_OUTPUT( pxNetworkBuffer->xDataLength, pxNetworkBuffer->pucEthernetBuffer );
            ( void ) xNetworkInterfaceOutput( pxNetworkBuffer, xDoRelease );

            if( xDoRelease == pdFALSE )
            {
                /* Swap-back some fields, as pxBuffer probably points to a socket field
                 * containing the packet header. */
                vFlip_16( pxTCPPacket->xTCPHeader.usSourcePort, pxTCPPacket->xTCPHeader.usDestinationPort );
                pxTCPPacket->xIPHeader.ulSourceIPAddress = pxTCPPacket->xIPHeader.ulDestinationIPAddress;
                ( void ) memcpy( ( void * ) ( pxEthernetHeader->xSourceAddress.ucBytes ), ( const void * ) ( pxEthernetHeader->xDestinationAddress.ucBytes ), ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
            }
            else
            {
                /* Nothing to do: the buffer has been passed to DMA and will be released after use */
            }
        } /* if( pxNetworkBuffer != NULL ) */
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Duplicates a socket after a listening socket receives a connection and bind
 *        the new socket to the same port as the listening socket.
 *        Also, let the new socket inherit all properties from the listening socket.
 *
 * @param[in] pxNewSocket: Pointer to the new socket.
 * @param[in] pxSocket: Pointer to the socket being duplicated.
 *
 * @return If all steps all successful, then pdTRUE is returned. Else, pdFALSE.
 */
    BaseType_t prvTCPSocketCopy( FreeRTOS_Socket_t * pxNewSocket,
                                 FreeRTOS_Socket_t * pxSocket )
    {
        struct freertos_sockaddr xAddress;
        BaseType_t xResult;

        pxNewSocket->xReceiveBlockTime = pxSocket->xReceiveBlockTime;
        pxNewSocket->xSendBlockTime = pxSocket->xSendBlockTime;
        pxNewSocket->ucSocketOptions = pxSocket->ucSocketOptions;
        pxNewSocket->u.xTCP.uxRxStreamSize = pxSocket->u.xTCP.uxRxStreamSize;
        pxNewSocket->u.xTCP.uxTxStreamSize = pxSocket->u.xTCP.uxTxStreamSize;
        pxNewSocket->u.xTCP.uxLittleSpace = pxSocket->u.xTCP.uxLittleSpace;
        pxNewSocket->u.xTCP.uxEnoughSpace = pxSocket->u.xTCP.uxEnoughSpace;
        pxNewSocket->u.xTCP.uxRxWinSize = pxSocket->u.xTCP.uxRxWinSize;
        pxNewSocket->u.xTCP.uxTxWinSize = pxSocket->u.xTCP.uxTxWinSize;

        #if ( ipconfigSOCKET_HAS_USER_SEMAPHORE == 1 )
            {
                pxNewSocket->pxUserSemaphore = pxSocket->pxUserSemaphore;
            }
        #endif /* ipconfigSOCKET_HAS_USER_SEMAPHORE */

        #if ( ipconfigUSE_CALLBACKS == 1 )
            {
                /* In case call-backs are used, copy them from parent to child. */
                pxNewSocket->u.xTCP.pxHandleConnected = pxSocket->u.xTCP.pxHandleConnected;
                pxNewSocket->u.xTCP.pxHandleReceive = pxSocket->u.xTCP.pxHandleReceive;
                pxNewSocket->u.xTCP.pxHandleSent = pxSocket->u.xTCP.pxHandleSent;
            }
        #endif /* ipconfigUSE_CALLBACKS */

        #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
            {
                /* Child socket of listening sockets will inherit the Socket Set
                 * Otherwise the owner has no chance of including it into the set. */
                if( pxSocket->pxSocketSet != NULL )
                {
                    pxNewSocket->pxSocketSet = pxSocket->pxSocketSet;
                    pxNewSocket->xSelectBits = pxSocket->xSelectBits | ( ( EventBits_t ) eSELECT_READ ) | ( ( EventBits_t ) eSELECT_EXCEPT );
                }
            }
        #endif /* ipconfigSUPPORT_SELECT_FUNCTION */

        /* And bind it to the same local port as its parent. */
        xAddress.sin_addr = *ipLOCAL_IP_ADDRESS_POINTER;
        xAddress.sin_port = FreeRTOS_htons( pxSocket->usLocalPort );

        #if ( ipconfigTCP_HANG_PROTECTION == 1 )
            {
                /* Only when there is anti-hanging protection, a socket may become an
                 * orphan temporarily.  Once this socket is really connected, the owner of
                 * the server socket will be notified. */

                /* When bPassQueued is true, the socket is an orphan until it gets
                 * connected. */
                pxNewSocket->u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;
                pxNewSocket->u.xTCP.pxPeerSocket = pxSocket;
            }
        #else
            {
                /* A reference to the new socket may be stored and the socket is marked
                 * as 'passable'. */

                /* When bPassAccept is true, this socket may be returned in a call to
                 * accept(). */
                pxNewSocket->u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;

                if( pxSocket->u.xTCP.pxPeerSocket == NULL )
                {
                    pxSocket->u.xTCP.pxPeerSocket = pxNewSocket;
                }
            }
        #endif /* if ( ipconfigTCP_HANG_PROTECTION == 1 ) */

        pxSocket->u.xTCP.usChildCount++;

        FreeRTOS_debug_printf( ( "Gain: Socket %u now has %u / %u child%s\n",
                                 pxSocket->usLocalPort,
                                 pxSocket->u.xTCP.usChildCount,
                                 pxSocket->u.xTCP.usBacklog,
                                 ( pxSocket->u.xTCP.usChildCount == 1U ) ? "" : "ren" ) );

        /* Now bind the child socket to the same port as the listening socket. */
        if( vSocketBind( pxNewSocket, &xAddress, sizeof( xAddress ), pdTRUE ) != 0 )
        {
            FreeRTOS_debug_printf( ( "TCP: Listen: new socket bind error\n" ) );
            vSocketClose( pxNewSocket );
            xResult = pdFALSE;
        }
        else
        {
            xResult = pdTRUE;
        }

        return xResult;
    }
    /*-----------------------------------------------------------*/


    #if ( ipconfigUSE_TCP_WIN == 1 )

/**
 * @brief Skip past TCP header options when doing Selective ACK, until there are no
 *        more options left.
 *
 * @param[in] pucPtr: Pointer to the TCP packet options.
 * @param[in] uxIndex: Index of options in the TCP packet options.
 * @param[in] pxSocket: Socket handling the TCP connection.
 */
        void prvReadSackOption( const uint8_t * const pucPtr,
                                size_t uxIndex,
                                FreeRTOS_Socket_t * const pxSocket )
        {
            uint32_t ulFirst = ulChar2u32( &( pucPtr[ uxIndex ] ) );
            uint32_t ulLast = ulChar2u32( &( pucPtr[ uxIndex + 4U ] ) );
            uint32_t ulCount = ulTCPWindowTxSack( &( pxSocket->u.xTCP.xTCPWindow ), ulFirst, ulLast );

            /* ulTCPWindowTxSack( ) returns the number of bytes which have been acked
             * starting from the head position.  Advance the tail pointer in txStream.
             */
            if( ( pxSocket->u.xTCP.txStream != NULL ) && ( ulCount > 0U ) )
            {
                /* Just advancing the tail index, 'ulCount' bytes have been confirmed. */
                ( void ) uxStreamBufferGet( pxSocket->u.xTCP.txStream, 0, NULL, ( size_t ) ulCount, pdFALSE );
                pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_SEND;

                #if ipconfigSUPPORT_SELECT_FUNCTION == 1
                    {
                        if( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_WRITE ) != 0U )
                        {
                            /* The field 'xEventBits' is used to store regular socket events
                             * (at most 8), as well as 'select events', which will be left-shifted.
                             */
                            pxSocket->xEventBits |= ( ( EventBits_t ) eSELECT_WRITE ) << SOCKET_EVENT_BIT_COUNT;
                        }
                    }
                #endif

                /* In case the socket owner has installed an OnSent handler,
                 * call it now. */
                #if ( ipconfigUSE_CALLBACKS == 1 )
                    {
                        if( ipconfigIS_VALID_PROG_ADDRESS( pxSocket->u.xTCP.pxHandleSent ) )
                        {
                            pxSocket->u.xTCP.pxHandleSent( pxSocket, ulCount );
                        }
                    }
                #endif /* ipconfigUSE_CALLBACKS == 1  */
            }
        }

    #endif /* ( ipconfigUSE_TCP_WIN != 0 ) */
    /*-----------------------------------------------------------*/

/**
 * @brief When opening a TCP connection, while SYN's are being sent, the  parties may
 *        communicate what MSS (Maximum Segment Size) they intend to use, whether Selective
 *        ACK's ( SACK ) are supported, and the size of the reception window ( WSOPT ).
 *
 * @param[in] pxSocket: The socket being used for communication. It is used to set
 *                      the MSS.
 * @param[in,out] pxTCPHeader: The TCP packet header being used in the SYN transmission.
 *                             The MSS and corresponding options shall be set in this
 *                             header itself.
 *
 * @return The option length after the TCP header was updated.
 *
 * @note MSS is the net size of the payload, an is always smaller than MTU.
 */
    UBaseType_t prvSetSynAckOptions( FreeRTOS_Socket_t * pxSocket,
                                     TCPHeader_t * pxTCPHeader )
    {
        uint16_t usMSS = pxSocket->u.xTCP.usInitMSS;
        UBaseType_t uxOptionsLength;

        /* We send out the TCP Maximum Segment Size option with our SYN[+ACK]. */

        pxTCPHeader->ucOptdata[ 0 ] = ( uint8_t ) tcpTCP_OPT_MSS;
        pxTCPHeader->ucOptdata[ 1 ] = ( uint8_t ) tcpTCP_OPT_MSS_LEN;
        pxTCPHeader->ucOptdata[ 2 ] = ( uint8_t ) ( usMSS >> 8 );
        pxTCPHeader->ucOptdata[ 3 ] = ( uint8_t ) ( usMSS & 0xffU );

        #if ( ipconfigUSE_TCP_WIN != 0 )
            {
                pxSocket->u.xTCP.ucMyWinScaleFactor = prvWinScaleFactor( pxSocket );

                pxTCPHeader->ucOptdata[ 4 ] = tcpTCP_OPT_NOOP;
                pxTCPHeader->ucOptdata[ 5 ] = ( uint8_t ) ( tcpTCP_OPT_WSOPT );
                pxTCPHeader->ucOptdata[ 6 ] = ( uint8_t ) ( tcpTCP_OPT_WSOPT_LEN );
                pxTCPHeader->ucOptdata[ 7 ] = ( uint8_t ) pxSocket->u.xTCP.ucMyWinScaleFactor;
                uxOptionsLength = 8U;
            }
        #else
            {
                uxOptionsLength = 4U;
            }
        #endif /* if ( ipconfigUSE_TCP_WIN != 0 ) */

        #if ( ipconfigUSE_TCP_WIN != 0 )
            {
                pxTCPHeader->ucOptdata[ uxOptionsLength ] = tcpTCP_OPT_NOOP;
                pxTCPHeader->ucOptdata[ uxOptionsLength + 1U ] = tcpTCP_OPT_NOOP;
                pxTCPHeader->ucOptdata[ uxOptionsLength + 2U ] = tcpTCP_OPT_SACK_P; /* 4: Sack-Permitted Option. */
                pxTCPHeader->ucOptdata[ uxOptionsLength + 3U ] = 2U;                /* 2: length of this option. */
                uxOptionsLength += 4U;
            }
        #endif /* ipconfigUSE_TCP_WIN == 0 */
        return uxOptionsLength; /* bytes, not words. */
    }

#endif /* if ipconfigUSE_TCP == 1 */
