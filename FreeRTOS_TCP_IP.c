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
 * @file FreeRTOS_TCP_IP.c
 *
 * In this group of modules all TCP communication is handled.
 * The functions will be called either because a TCP packet was received,
 * or because a socket timer expired.
 * Although most functions are declared as global functions, none of them
 * is designed to be called by an application. The IP-task will call them
 * when needed.
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
#include "FreeRTOS_TCP_WIN.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"

/* Private includes. */
#include "FreeRTOS_TCP_IP_StateHandling.h"
#include "FreeRTOS_TCP_IP_utils.h"
#include "FreeRTOS_TCP_IP_Reception.h"
#include "FreeRTOS_TCP_IP_TimerWork.h"

/* Just make sure the contents doesn't get compiled if TCP is not enabled. */
#if ipconfigUSE_TCP == 1

/** @brief Close the socket another time.
 *
 * @param[in] pxSocket: The socket to be checked.
 */
    void vSocketCloseNextTime( FreeRTOS_Socket_t * pxSocket )
    {
        static FreeRTOS_Socket_t * xPreviousSocket = NULL;

        if( ( xPreviousSocket != NULL ) && ( xPreviousSocket != pxSocket ) )
        {
            vSocketClose( xPreviousSocket );
        }

        xPreviousSocket = pxSocket;
    }
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
    BaseType_t xTCPSocketCheck( FreeRTOS_Socket_t * pxSocket )
    {
        BaseType_t xResult = 0;
        BaseType_t xReady = pdFALSE;

        if( ( pxSocket->u.xTCP.ucTCPState >= ( uint8_t ) eESTABLISHED ) && ( pxSocket->u.xTCP.txStream != NULL ) )
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
                        if( pxSocket->u.xTCP.ucTCPState != ( uint8_t ) eCLOSED )
                        {
                            if( ( xTCPWindowLoggingLevel > 1 ) && ipconfigTCP_MAY_LOG_PORT( pxSocket->usLocalPort ) )
                            {
                                FreeRTOS_debug_printf( ( "Send[%u->%u] del ACK %lu SEQ %lu (len %u)\n",
                                                         pxSocket->usLocalPort,
                                                         pxSocket->u.xTCP.usRemotePort,
                                                         pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber - pxSocket->u.xTCP.xTCPWindow.rx.ulFirstSequenceNumber,
                                                         pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber - pxSocket->u.xTCP.xTCPWindow.tx.ulFirstSequenceNumber,
                                                         ( unsigned ) ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER ) );
                            }

                            prvTCPReturnPacket( pxSocket, pxSocket->u.xTCP.pxAckMessage, ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER, ipconfigZERO_COPY_TX_DRIVER );

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
            if( ( pxSocket->u.xTCP.ucTCPState >= ( uint8_t ) eESTABLISHED ) ||
                ( pxSocket->u.xTCP.ucTCPState == ( uint8_t ) eCONNECT_SYN ) )
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


/* For logging and debugging: make a string showing the TCP flags
 */
    #if ( ipconfigHAS_DEBUG_PRINTF != 0 )

/**
 * @brief Print out the value of flags in a human readable manner.
 *
 * @param[in] xFlags: The TCP flags.
 *
 * @return The string containing the flags.
 */
        const char * prvTCPFlagMeaning( UBaseType_t xFlags )
        {
            static char retString[ 10 ];
            size_t uxFlags = ( size_t ) xFlags;

            ( void ) snprintf( retString,
                               sizeof( retString ), "%c%c%c%c%c%c%c%c",
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_FIN ) != 0 ) ? 'F' : '.',   /* 0x0001: No more data from sender */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_SYN ) != 0 ) ? 'S' : '.',   /* 0x0002: Synchronize sequence numbers */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_RST ) != 0 ) ? 'R' : '.',   /* 0x0004: Reset the connection */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_PSH ) != 0 ) ? 'P' : '.',   /* 0x0008: Push function: please push buffered data to the recv application */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_ACK ) != 0 ) ? 'A' : '.',   /* 0x0010: Acknowledgment field is significant */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_URG ) != 0 ) ? 'U' : '.',   /* 0x0020: Urgent pointer field is significant */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_ECN ) != 0 ) ? 'E' : '.',   /* 0x0040: ECN-Echo */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_CWR ) != 0 ) ? 'C' : '.' ); /* 0x0080: Congestion Window Reduced */
            return retString;
        }
        /*-----------------------------------------------------------*/

    #endif /* ipconfigHAS_DEBUG_PRINTF */

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
    BaseType_t xProcessReceivedTCPPacket( NetworkBufferDescriptor_t * pxDescriptor )
    {
        /* Function might modify the parameter. */
        NetworkBufferDescriptor_t * pxNetworkBuffer = pxDescriptor;

        configASSERT( pxNetworkBuffer != NULL );
        configASSERT( pxNetworkBuffer->pucEthernetBuffer != NULL );

        /* Map the buffer onto a ProtocolHeaders_t struct for easy access to the fields. */
        const ProtocolHeaders_t * pxProtocolHeaders = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( ProtocolHeaders_t,
                                                                                          &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
        FreeRTOS_Socket_t * pxSocket;
        uint16_t ucTCPFlags = pxProtocolHeaders->xTCPHeader.ucTCPFlags;
        uint32_t ulLocalIP;
        uint16_t xLocalPort = FreeRTOS_htons( pxProtocolHeaders->xTCPHeader.usDestinationPort );
        uint16_t xRemotePort = FreeRTOS_htons( pxProtocolHeaders->xTCPHeader.usSourcePort );
        uint32_t ulRemoteIP;
        uint32_t ulSequenceNumber = FreeRTOS_ntohl( pxProtocolHeaders->xTCPHeader.ulSequenceNumber );
        uint32_t ulAckNumber = FreeRTOS_ntohl( pxProtocolHeaders->xTCPHeader.ulAckNr );
        BaseType_t xResult = pdPASS;

        const IPHeader_t * pxIPHeader;

        /* Check for a minimum packet size. */
        if( pxNetworkBuffer->xDataLength < ( ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) + ipSIZE_OF_TCP_HEADER ) )
        {
            xResult = pdFAIL;
        }
        else
        {
            /* Map the ethernet buffer onto the IPHeader_t struct for easy access to the fields. */
            pxIPHeader = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( IPHeader_t, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );
            ulLocalIP = FreeRTOS_htonl( pxIPHeader->ulDestinationIPAddress );
            ulRemoteIP = FreeRTOS_htonl( pxIPHeader->ulSourceIPAddress );

            /* Find the destination socket, and if not found: return a socket listing to
             * the destination PORT. */
            pxSocket = ( FreeRTOS_Socket_t * ) pxTCPSocketLookup( ulLocalIP, xLocalPort, ulRemoteIP, xRemotePort );

            if( ( pxSocket == NULL ) || ( prvTCPSocketIsActive( ipNUMERIC_CAST( eIPTCPState_t, pxSocket->u.xTCP.ucTCPState ) ) == pdFALSE ) )
            {
                /* A TCP messages is received but either there is no socket with the
                 * given port number or the there is a socket, but it is in one of these
                 * non-active states:  eCLOSED, eCLOSE_WAIT, eFIN_WAIT_2, eCLOSING, or
                 * eTIME_WAIT. */

                FreeRTOS_debug_printf( ( "TCP: No active socket on port %d (%lxip:%d)\n", xLocalPort, ulRemoteIP, xRemotePort ) );

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

                if( pxSocket->u.xTCP.ucTCPState == ( uint8_t ) eTCP_LISTEN )
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
                                FreeRTOS_debug_printf( ( "TCP: Server can't handle flags: %s from %lxip:%u to port %u\n",
                                                         prvTCPFlagMeaning( ( UBaseType_t ) ucTCPFlags ), ulRemoteIP, xRemotePort, xLocalPort ) );
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
                } /* if( pxSocket->u.xTCP.ucTCPState == eTCP_LISTEN ). */
                else
                {
                    /* This is not a socket in listening mode. Check for the RST
                     * flag. */
                    if( ( ucTCPFlags & tcpTCP_FLAG_RST ) != 0U )
                    {
                        FreeRTOS_debug_printf( ( "TCP: RST received from %lxip:%u for %u\n", ulRemoteIP, xRemotePort, xLocalPort ) );

                        /* Implement https://tools.ietf.org/html/rfc5961#section-3.2. */
                        if( pxSocket->u.xTCP.ucTCPState == ( uint8_t ) eCONNECT_SYN )
                        {
                            /* Per the above RFC, "In the SYN-SENT state ... the RST is
                             * acceptable if the ACK field acknowledges the SYN." */
                            if( ulAckNumber == ( pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber + 1UL ) )
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
                            else if( ( xSequenceGreaterThan( ulSequenceNumber, pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber ) ) &&
                                     ( xSequenceLessThan( ulSequenceNumber, ( pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber +
                                                                              pxSocket->u.xTCP.xTCPWindow.xSize.ulRxWindowLength ) ) ) )
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
                    else if( ( ( ucTCPFlags & tcpTCP_FLAG_CTRL ) == tcpTCP_FLAG_SYN ) && ( pxSocket->u.xTCP.ucTCPState >= ( uint8_t ) eESTABLISHED ) )
                    {
                        /* SYN flag while this socket is already connected. */
                        FreeRTOS_debug_printf( ( "TCP: SYN unexpected from %lxip:%u\n", ulRemoteIP, xRemotePort ) );

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
                    }
                }
            }

            if( xResult != pdFAIL )
            {
                uint16_t usWindow;

                /* pxSocket is not NULL when xResult != pdFAIL. */
                configASSERT( pxSocket != NULL );

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
                    prvCheckOptions( pxSocket, pxNetworkBuffer );
                }

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
                /* Return pdPASS to tell that the network buffer is 'consumed'. */
                xResult = pdPASS;
            }
        }

        /* pdPASS being returned means the buffer has been consumed. */
        return xResult;
    }
    /*-----------------------------------------------------------*/



    #if ( ( ipconfigHAS_DEBUG_PRINTF != 0 ) || ( ipconfigHAS_PRINTF != 0 ) )

        const char * FreeRTOS_GetTCPStateName( UBaseType_t ulState )
        {
            static const char * const pcStateNames[] =
            {
                "eCLOSED",
                "eTCP_LISTEN",
                "eCONNECT_SYN",
                "eSYN_FIRST",
                "eSYN_RECEIVED",
                "eESTABLISHED",
                "eFIN_WAIT_1",
                "eFIN_WAIT_2",
                "eCLOSE_WAIT",
                "eCLOSING",
                "eLAST_ACK",
                "eTIME_WAIT",
                "eUNKNOWN",
            };
            BaseType_t xIndex = ( BaseType_t ) ulState;

            if( ( xIndex < 0 ) || ( xIndex >= ARRAY_SIZE( pcStateNames ) ) )
            {
                /* The last item is called 'eUNKNOWN' */
                xIndex = ARRAY_SIZE( pcStateNames );
                xIndex--;
            }

            return pcStateNames[ xIndex ];
        }

    #endif /* ( ( ipconfigHAS_DEBUG_PRINTF != 0 ) || ( ipconfigHAS_PRINTF != 0 ) ) */
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
        const ListItem_t * pxEndTCP = listGET_END_MARKER( &xBoundTCPSocketsList );

        /* Here xBoundTCPSocketsList can be accessed safely IP-task is the only one
         * who has access. */
        for( pxIterator = ( const ListItem_t * ) listGET_HEAD_ENTRY( &xBoundTCPSocketsList );
             pxIterator != pxEndTCP;
             pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator ) )
        {
            if( listGET_LIST_ITEM_VALUE( pxIterator ) == ( configLIST_VOLATILE TickType_t ) uxLocalPort )
            {
                pxFound = ipCAST_PTR_TO_TYPE_PTR( FreeRTOS_Socket_t, listGET_LIST_ITEM_OWNER( pxIterator ) );

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
