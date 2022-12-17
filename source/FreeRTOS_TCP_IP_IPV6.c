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
    static FreeRTOS_Socket_t * xSocketToListen = NULL;

    #if ( ipconfigHAS_DEBUG_PRINTF != 0 )

/*
 * For logging and debugging: make a string showing the TCP flags.
 */
        const char * prvTCPFlagMeaning( UBaseType_t xFlags );
    #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */


/*-----------------------------------------------------------*/


/**
 * @brief Process the received TCP packet.
 *
 * @param[in] pxDescriptor: The descriptor in which the TCP packet is held.
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
    BaseType_t xProcessReceivedTCPPacket_IPV6( NetworkBufferDescriptor_t * pxDescriptor )
    {
        /* Function might modify the parameter. */
        NetworkBufferDescriptor_t * pxNetworkBuffer = pxDescriptor;

        configASSERT( pxNetworkBuffer != NULL );
        configASSERT( pxNetworkBuffer->pucEthernetBuffer != NULL );

        /* Map the buffer onto a ProtocolHeaders_t struct for easy access to the fields. */

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        const ProtocolHeaders_t * pxProtocolHeaders = ( ( const ProtocolHeaders_t * )
                                                        &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizePacket( pxNetworkBuffer ) ] ) );
        FreeRTOS_Socket_t * pxSocket;
        uint16_t ucTCPFlags = pxProtocolHeaders->xTCPHeader.ucTCPFlags;
        uint32_t ulLocalIP;
        uint16_t usLocalPort = FreeRTOS_htons( pxProtocolHeaders->xTCPHeader.usDestinationPort );
        uint16_t usRemotePort = FreeRTOS_htons( pxProtocolHeaders->xTCPHeader.usSourcePort );
        IP_Address_t ulRemoteIP;
        uint32_t ulSequenceNumber = FreeRTOS_ntohl( pxProtocolHeaders->xTCPHeader.ulSequenceNumber );
        uint32_t ulAckNumber = FreeRTOS_ntohl( pxProtocolHeaders->xTCPHeader.ulAckNr );
        BaseType_t xResult = pdPASS;

        /* Check for a minimum packet size. */
        if( pxNetworkBuffer->xDataLength < ( ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) + ipSIZE_OF_TCP_HEADER ) )
        {
            xResult = pdFAIL;
        }
        else
        {
            /* Map the ethernet buffer onto the IPHeader_t struct for easy access to the fields. */

            /* MISRA Ref 11.3.1 [Misaligned access] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */

            IPHeader_IPv6_t * pxIPHeader_IPv6;
            ulLocalIP = *ipLOCAL_IP_ADDRESS_POINTER;
            pxIPHeader_IPv6 = ( ( IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );
            ( void ) memcpy( &( ulRemoteIP.xIP_IPv6 ), &( pxIPHeader_IPv6->xSourceAddress ), sizeof( IPv6_Address_t ) );
            ulRemoteIP.xIP_IPv4 = 0;

            /* Find the destination socket, and if not found: return a socket listing to
             * the destination PORT. */
            pxSocket = ( FreeRTOS_Socket_t * ) pxTCPSocketLookup( ulLocalIP, usLocalPort, ulRemoteIP, usRemotePort );

            if( ( pxSocket == NULL ) || ( prvTCPSocketIsActive( pxSocket->u.xTCP.eTCPState ) == pdFALSE ) )
            {
                /* A TCP messages is received but either there is no socket with the
                 * given port number or the there is a socket, but it is in one of these
                 * non-active states:  eCLOSED, eCLOSE_WAIT, eFIN_WAIT_2, eCLOSING, or
                 * eTIME_WAIT. */

                FreeRTOS_debug_printf( ( "TCP: No active socket on port %d (%xip:%d)\n", usLocalPort, ( unsigned ) ulRemoteIP, usRemotePort ) );

                /* Send a RST to all packets that can not be handled.  As a result
                 * the other party will get a ECONN error.  There are two exceptions:
                 * 1) A packet that already has the RST flag set.
                 * 2) A packet that only has the ACK flag set.
                 * A packet with only the ACK flag set might be the last ACK in
                 * a three-way hand-shake that closes a connection. */
                if( ( ( ucTCPFlags & tcpTCP_FLAG_CTRL ) != tcpTCP_FLAG_ACK ) &&
                    ( ( ucTCPFlags & tcpTCP_FLAG_RST ) == 0U ) )
                {
                    ( void ) prvTCPSendReset( pxNetworkBuffer );
                }

                /* The packet can't be handled. */
                xResult = pdFAIL;
            }
            else
            {
                pxSocket->u.xTCP.ucRepCount = 0U;

                if( pxSocket->u.xTCP.eTCPState == eTCP_LISTEN )
                {
                    /* The matching socket is in a listening state.  Test if the peer
                     * has set the SYN flag. */
                    if( ( ucTCPFlags & tcpTCP_FLAG_CTRL ) != tcpTCP_FLAG_SYN )
                    {
                        /* What happens: maybe after a reboot, a client doesn't know the
                         * connection had gone.  Send a RST in order to get a new connect
                         * request. */
                        #if ( ipconfigHAS_DEBUG_PRINTF == 1 )
                            {
                                FreeRTOS_debug_printf( ( "TCP: Server can't handle flags: %s from %xip:%u to port %u\n",
                                                         prvTCPFlagMeaning( ( UBaseType_t ) ucTCPFlags ), ( unsigned ) ulRemoteIP, usRemotePort, usLocalPort ) );
                            }
                        #endif /* ipconfigHAS_DEBUG_PRINTF */

                        if( ( ucTCPFlags & tcpTCP_FLAG_RST ) == 0U )
                        {
                            ( void ) prvTCPSendReset( pxNetworkBuffer );
                        }

                        xResult = pdFAIL;
                    }
                    else
                    {
                        /* prvHandleListen() will either return a newly created socket
                         * (if bReuseSocket is false), otherwise it returns the current
                         * socket which will later get connected. */
                        pxSocket = prvHandleListen( pxSocket, pxNetworkBuffer );

                        if( pxSocket == NULL )
                        {
                            xResult = pdFAIL;
                        }
                    }
                } /* if( pxSocket->u.xTCP.eTCPState == eTCP_LISTEN ). */
                else
                {
                    /* This is not a socket in listening mode. Check for the RST
                     * flag. */
                    if( ( ucTCPFlags & tcpTCP_FLAG_RST ) != 0U )
                    {
                        FreeRTOS_debug_printf( ( "TCP: RST received from %xip:%u for %u\n", ( unsigned ) ulRemoteIP, usRemotePort, usLocalPort ) );

                        /* Implement https://tools.ietf.org/html/rfc5961#section-3.2. */
                        if( pxSocket->u.xTCP.eTCPState == eCONNECT_SYN )
                        {
                            /* Per the above RFC, "In the SYN-SENT state ... the RST is
                             * acceptable if the ACK field acknowledges the SYN." */
                            if( ulAckNumber == ( pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber + 1U ) )
                            {
                                vTCPStateChange( pxSocket, eCLOSED );
                            }
                        }
                        else
                        {
                            /* Check whether the packet matches the next expected sequence number. */
                            if( ulSequenceNumber == pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber )
                            {
                                vTCPStateChange( pxSocket, eCLOSED );
                            }
                            /* Otherwise, check whether the packet is within the receive window. */
                            else if( ( xSequenceGreaterThan( ulSequenceNumber, pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber ) != pdFALSE ) &&
                                     ( xSequenceLessThan( ulSequenceNumber, pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber +
                                                          pxSocket->u.xTCP.xTCPWindow.xSize.ulRxWindowLength ) != pdFALSE ) )
                            {
                                /* Send a challenge ACK. */
                                ( void ) prvTCPSendChallengeAck( pxNetworkBuffer );
                            }
                            else
                            {
                                /* Nothing. */
                            }
                        }

                        /* Otherwise, do nothing. In any case, the packet cannot be handled. */
                        xResult = pdFAIL;
                    }
                    /* Check whether there is a pure SYN amongst the TCP flags while the connection is established. */
                    else if( ( ( ucTCPFlags & tcpTCP_FLAG_CTRL ) == tcpTCP_FLAG_SYN ) && ( pxSocket->u.xTCP.eTCPState >= eESTABLISHED ) )
                    {
                        /* SYN flag while this socket is already connected. */
                        FreeRTOS_debug_printf( ( "TCP: SYN unexpected from %xip:%u\n", ( unsigned ) ulRemoteIP, usRemotePort ) );

                        /* The packet cannot be handled. */
                        xResult = pdFAIL;
                    }
                    else
                    {
                        /* Update the copy of the TCP header only (skipping eth and IP
                         * headers).  It might be used later on, whenever data must be sent
                         * to the peer. */
                        const size_t uxOffset = ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket );
                        ( void ) memcpy( ( void * ) ( &( pxSocket->u.xTCP.xPacket.u.ucLastPacket[ uxOffset ] ) ),
                                         ( const void * ) ( &( pxNetworkBuffer->pucEthernetBuffer[ uxOffset ] ) ),
                                         ipSIZE_OF_TCP_HEADER );
                        /* Clear flags that are set by the peer, and set the ACK flag. */
                        pxSocket->u.xTCP.xPacket.u.ucLastPacket[ uxOffset + ipTCP_FLAGS_OFFSET ] = tcpTCP_FLAG_ACK;
                    }
                }
            }

            if( xResult != pdFAIL )
            {
                uint16_t usWindow;

                /* pxSocket is not NULL when xResult != pdFAIL. */
                configASSERT( pxSocket != NULL ); /* LCOV_EXCL_LINE ,this branch will not be hit*/

                /* Touch the alive timers because we received a message for this
                 * socket. */
                prvTCPTouchSocket( pxSocket );

                /* Parse the TCP option(s), if present. */

                /* _HT_ : if we're in the SYN phase, and peer does not send a MSS option,
                 * then we MUST assume an MSS size of 536 bytes for backward compatibility. */

                /* When there are no TCP options, the TCP offset equals 20 bytes, which is stored as
                 * the number 5 (words) in the higher nibble of the TCP-offset byte. */
                if( ( pxProtocolHeaders->xTCPHeader.ucTCPOffset & tcpTCP_OFFSET_LENGTH_BITS ) > tcpTCP_OFFSET_STANDARD_LENGTH )
                {
                    xResult = prvCheckOptions( pxSocket, pxNetworkBuffer );
                }

                if( xResult != pdFAIL )
                {
                    usWindow = FreeRTOS_ntohs( pxProtocolHeaders->xTCPHeader.usWindow );
                    pxSocket->u.xTCP.ulWindowSize = ( uint32_t ) usWindow;
                    #if ( ipconfigUSE_TCP_WIN == 1 )
                        {
                            /* rfc1323 : The Window field in a SYN (i.e., a <SYN> or <SYN,ACK>)
                             * segment itself is never scaled. */
                            if( ( ucTCPFlags & ( uint8_t ) tcpTCP_FLAG_SYN ) == 0U )
                            {
                                pxSocket->u.xTCP.ulWindowSize =
                                    ( pxSocket->u.xTCP.ulWindowSize << pxSocket->u.xTCP.ucPeerWinScaleFactor );
                            }
                        }
                    #endif /* ipconfigUSE_TCP_WIN */

                    /* In prvTCPHandleState() the incoming messages will be handled
                     * depending on the current state of the connection. */
                    if( prvTCPHandleState( pxSocket, &pxNetworkBuffer ) > 0 )
                    {
                        /* prvTCPHandleState() has sent a message, see if there are more to
                         * be transmitted. */
                        #if ( ipconfigUSE_TCP_WIN == 1 )
                            {
                                ( void ) prvTCPSendRepeated( pxSocket, &pxNetworkBuffer );
                            }
                        #endif /* ipconfigUSE_TCP_WIN */
                    }

                    if( pxNetworkBuffer != NULL )
                    {
                        /* We must check if the buffer is unequal to NULL, because the
                         * socket might keep a reference to it in case a delayed ACK must be
                         * sent. */
                        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
                        #ifndef _lint
                            /* Clear pointers that are freed. */
                            pxNetworkBuffer = NULL;
                        #endif
                    }

                    /* And finally, calculate when this socket wants to be woken up. */
                    ( void ) prvTCPNextTimeout( pxSocket );
                }
            }
        }

        /* pdPASS being returned means the buffer has been consumed. */
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
