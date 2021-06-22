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
 * @file FreeRTOS_TCP_IP_Reception.c
 *
 * The functions in this module are called when a TCP packet is received.
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
#include "FreeRTOS_TCP_IP_StateHandling.h"
#include "FreeRTOS_TCP_IP_utils.h"
#include "FreeRTOS_TCP_IP_Reception.h"


/* Just make sure the contents doesn't get compiled if TCP is not enabled. */
#if ipconfigUSE_TCP == 1

/**
 * @brief Parse the TCP option(s) received, if present.
 *
 * @param[in] pxSocket: The socket handling the connection.
 * @param[in] pxNetworkBuffer: The network buffer containing the TCP
 *                             packet.
 *
 * @note It has already been verified that:
 *       ((pxTCPHeader->ucTCPOffset & 0xf0) > 0x50), meaning that
 *       the TP header is longer than the usual 20 (5 x 4) bytes.
 */
    void prvCheckOptions( FreeRTOS_Socket_t * pxSocket,
                          const NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer );
        const ProtocolHeaders_t * pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                              &( pxNetworkBuffer->pucEthernetBuffer[ uxTCPHeaderOffset ] ) );
        const TCPHeader_t * pxTCPHeader;
        const uint8_t * pucPtr;
        BaseType_t xHasSYNFlag;
        /* Offset in the network packet where the first option byte is stored. */
        size_t uxOptionOffset = uxTCPHeaderOffset + ( sizeof( TCPHeader_t ) - sizeof( pxTCPHeader->ucOptdata ) );
        size_t uxOptionsLength;
        size_t uxResult;
        uint8_t ucLength;

        pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );


        /* A character pointer to iterate through the option data */
        pucPtr = pxTCPHeader->ucOptdata;

        if( pxTCPHeader->ucTCPOffset <= ( 5U << 4U ) )
        {
            /* Avoid integer underflow in computation of ucLength. */
        }
        else
        {
            ucLength = ( ( ( pxTCPHeader->ucTCPOffset >> 4U ) - 5U ) << 2U );
            uxOptionsLength = ( size_t ) ucLength;

            if( pxNetworkBuffer->xDataLength > uxOptionOffset )
            {
                /* Validate options size calculation. */
                if( ( pxNetworkBuffer->xDataLength > uxOptionOffset ) &&
                    ( uxOptionsLength <= ( pxNetworkBuffer->xDataLength - uxOptionOffset ) ) )
                {
                    if( ( pxTCPHeader->ucTCPFlags & tcpTCP_FLAG_SYN ) != ( uint8_t ) 0U )
                    {
                        xHasSYNFlag = pdTRUE;
                    }
                    else
                    {
                        xHasSYNFlag = pdFALSE;
                    }

                    /* The length check is only necessary in case the option data are
                     *  corrupted, we don't like to run into invalid memory and crash. */
                    for( ; ; )
                    {
                        if( uxOptionsLength == 0U )
                        {
                            /* coverity[break_stmt] : Break statement terminating the loop */
                            break;
                        }

                        uxResult = prvSingleStepTCPHeaderOptions( pucPtr, uxOptionsLength, pxSocket, xHasSYNFlag );

                        if( uxResult == 0UL )
                        {
                            break;
                        }

                        uxOptionsLength -= uxResult;
                        pucPtr = &( pucPtr[ uxResult ] );
                    }
                }
            }
        }
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Identify and deal with a single TCP header option, advancing the pointer to
 *        the header.
 *
 * @param[in] pucPtr: Pointer to the TCP packet options.
 * @param[in] uxTotalLength: Length of the TCP packet options.
 * @param[in] pxSocket: Socket handling the connection.
 * @param[in] xHasSYNFlag: Whether the header has SYN flag or not.
 *
 * @return This function returns pdTRUE or pdFALSE depending on whether the caller
 *         should continue to parse more header options or break the loop.
 */
    size_t prvSingleStepTCPHeaderOptions( const uint8_t * const pucPtr,
                                          size_t uxTotalLength,
                                          FreeRTOS_Socket_t * const pxSocket,
                                          BaseType_t xHasSYNFlag )
    {
        UBaseType_t uxNewMSS;
        size_t uxRemainingOptionsBytes = uxTotalLength;
        uint8_t ucLen;
        size_t uxIndex;
        TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );
        BaseType_t xReturn = pdFALSE;

        if( pucPtr[ 0U ] == tcpTCP_OPT_END )
        {
            /* End of options. */
            uxIndex = 0U;
        }
        else if( pucPtr[ 0U ] == tcpTCP_OPT_NOOP )
        {
            /* NOP option, inserted to make the length a multiple of 4. */
            uxIndex = 1U;
        }
        else if( uxRemainingOptionsBytes < 2U )
        {
            /* Any other well-formed option must be at least two bytes: the option
             * type byte followed by a length byte. */
            uxIndex = 0U;
        }

        #if ( ipconfigUSE_TCP_WIN != 0 )
            else if( pucPtr[ 0 ] == tcpTCP_OPT_WSOPT )
            {
                /* The TCP Window Scale Option. */
                /* Confirm that the option fits in the remaining buffer space. */
                if( ( uxRemainingOptionsBytes < tcpTCP_OPT_WSOPT_LEN ) || ( pucPtr[ 1 ] != tcpTCP_OPT_WSOPT_LEN ) )
                {
                    uxIndex = 0U;
                }
                else
                {
                    /* Option is only valid in SYN phase. */
                    if( xHasSYNFlag != 0 )
                    {
                        pxSocket->u.xTCP.ucPeerWinScaleFactor = pucPtr[ 2 ];
                        pxSocket->u.xTCP.bits.bWinScaling = pdTRUE_UNSIGNED;
                    }

                    uxIndex = tcpTCP_OPT_WSOPT_LEN;
                }
            }
        #endif /* ipconfigUSE_TCP_WIN */
        else if( pucPtr[ 0 ] == tcpTCP_OPT_MSS )
        {
            /* Confirm that the option fits in the remaining buffer space. */
            if( ( uxRemainingOptionsBytes < tcpTCP_OPT_MSS_LEN ) || ( pucPtr[ 1 ] != tcpTCP_OPT_MSS_LEN ) )
            {
                uxIndex = 0U;
            }
            else
            {
                /* An MSS option with the correct option length.  FreeRTOS_htons()
                 * is not needed here because usChar2u16() already returns a host
                 * endian number. */
                uxNewMSS = usChar2u16( &( pucPtr[ 2 ] ) );

                if( pxSocket->u.xTCP.usInitMSS != uxNewMSS )
                {
                    /* Perform a basic check on the the new MSS. */
                    if( uxNewMSS == 0U )
                    {
                        uxIndex = 0U;

                        /* Return Condition found. */
                        xReturn = pdTRUE;
                    }
                    else
                    {
                        FreeRTOS_debug_printf( ( "MSS change %u -> %lu\n", pxSocket->u.xTCP.usInitMSS, uxNewMSS ) );
                    }
                }

                /* If a 'return' condition has not been found. */
                if( xReturn == pdFALSE )
                {
                    if( pxSocket->u.xTCP.usInitMSS > uxNewMSS )
                    {
                        /* our MSS was bigger than the MSS of the other party: adapt it. */
                        pxSocket->u.xTCP.bits.bMssChange = pdTRUE_UNSIGNED;

                        if( pxSocket->u.xTCP.usCurMSS > uxNewMSS )
                        {
                            /* The peer advertises a smaller MSS than this socket was
                             * using.  Use that as well. */
                            FreeRTOS_debug_printf( ( "Change mss %d => %lu\n", pxSocket->u.xTCP.usCurMSS, uxNewMSS ) );
                            pxSocket->u.xTCP.usCurMSS = ( uint16_t ) uxNewMSS;
                        }

                        pxTCPWindow->xSize.ulRxWindowLength = ( ( uint32_t ) uxNewMSS ) * ( pxTCPWindow->xSize.ulRxWindowLength / ( ( uint32_t ) uxNewMSS ) );
                        pxTCPWindow->usMSSInit = ( uint16_t ) uxNewMSS;
                        pxTCPWindow->usMSS = ( uint16_t ) uxNewMSS;
                        pxSocket->u.xTCP.usInitMSS = ( uint16_t ) uxNewMSS;
                        pxSocket->u.xTCP.usCurMSS = ( uint16_t ) uxNewMSS;
                    }

                    uxIndex = tcpTCP_OPT_MSS_LEN;
                }
            }
        }
        else
        {
            /* All other options have a length field, so that we easily
             * can skip past them. */
            ucLen = pucPtr[ 1 ];
            uxIndex = 0U;

            if( ( ucLen < ( uint8_t ) 2U ) || ( uxRemainingOptionsBytes < ( size_t ) ucLen ) )
            {
                /* If the length field is too small or too big, the options are
                 * malformed, don't process them further.
                 */
            }
            else
            {
                #if ( ipconfigUSE_TCP_WIN == 1 )
                    {
                        /* Selective ACK: the peer has received a packet but it is missing
                         * earlier packets. At least this packet does not need retransmission
                         * anymore. ulTCPWindowTxSack( ) takes care of this administration.
                         */
                        if( pucPtr[ 0U ] == tcpTCP_OPT_SACK_A )
                        {
                            ucLen -= 2U;
                            uxIndex += 2U;

                            while( ucLen >= ( uint8_t ) 8U )
                            {
                                prvReadSackOption( pucPtr, uxIndex, pxSocket );
                                uxIndex += 8U;
                                ucLen -= 8U;
                            }

                            /* ucLen should be 0 by now. */
                        }
                    }
                #endif /* ipconfigUSE_TCP_WIN == 1 */

                uxIndex += ( size_t ) ucLen;
            }
        }

        #if ( ipconfigUSE_TCP_WIN == 0 )
            /* Avoid compiler warnings when TCP window is not used. */
            ( void ) xHasSYNFlag;
        #endif

        return uxIndex;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief A "challenge ACK" is as per https://tools.ietf.org/html/rfc5961#section-3.2,
 *        case #3. In summary, an RST was received with a sequence number that is
 *        unexpected but still within the window.
 *
 * @param[in] pxNetworkBuffer: The network buffer descriptor with the packet.
 *
 * @return Returns the value back from #prvTCPSendSpecialPacketHelper.
 */
    BaseType_t prvTCPSendChallengeAck( NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        return prvTCPSendSpecialPacketHelper( pxNetworkBuffer, tcpTCP_FLAG_ACK );
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Send a RST (Reset) to peer in case the packet cannot be handled.
 *
 * @param[in] pxNetworkBuffer: The network buffer descriptor with the packet.
 *
 * @return Returns the value back from #prvTCPSendSpecialPacketHelper.
 */
    BaseType_t prvTCPSendReset( NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        return prvTCPSendSpecialPacketHelper( pxNetworkBuffer,
                                              ( uint8_t ) tcpTCP_FLAG_ACK | ( uint8_t ) tcpTCP_FLAG_RST );
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Handle 'listen' event on the given socket.
 *
 * @param[in] pxSocket: The socket on which the listen occurred.
 * @param[in] pxNetworkBuffer: The network buffer carrying the packet.
 *
 * @return If a new socket/duplicate socket is created, then the pointer to
 *         that socket is returned or else, a NULL pointer is returned.
 */
    FreeRTOS_Socket_t * prvHandleListen( FreeRTOS_Socket_t * pxSocket,
                                         NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        /* Map the ethernet buffer onto a TCPPacket_t struct for easy access to the fields. */
        const TCPPacket_t * pxTCPPacket = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( TCPPacket_t, pxNetworkBuffer->pucEthernetBuffer );
        FreeRTOS_Socket_t * pxReturn = NULL;
        uint32_t ulInitialSequenceNumber;

        /* Assume that a new Initial Sequence Number will be required. Request
         * it now in order to fail out if necessary. */
        ulInitialSequenceNumber = ulApplicationGetNextSequenceNumber( *ipLOCAL_IP_ADDRESS_POINTER,
                                                                      pxSocket->usLocalPort,
                                                                      pxTCPPacket->xIPHeader.ulSourceIPAddress,
                                                                      pxTCPPacket->xTCPHeader.usSourcePort );

        /* A pure SYN (without ACK) has come in, create a new socket to answer
         * it. */
        if( ulInitialSequenceNumber != 0UL )
        {
            if( pxSocket->u.xTCP.bits.bReuseSocket != pdFALSE_UNSIGNED )
            {
                /* The flag bReuseSocket indicates that the same instance of the
                 * listening socket should be used for the connection. */
                pxReturn = pxSocket;
                pxSocket->u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;
                pxSocket->u.xTCP.pxPeerSocket = pxSocket;
            }
            else
            {
                /* The socket does not have the bReuseSocket flag set meaning create a
                 * new socket when a connection comes in. */
                pxReturn = NULL;

                if( pxSocket->u.xTCP.usChildCount >= pxSocket->u.xTCP.usBacklog )
                {
                    FreeRTOS_printf( ( "Check: Socket %u already has %u / %u child%s\n",
                                       pxSocket->usLocalPort,
                                       pxSocket->u.xTCP.usChildCount,
                                       pxSocket->u.xTCP.usBacklog,
                                       ( pxSocket->u.xTCP.usChildCount == 1U ) ? "" : "ren" ) );
                    ( void ) prvTCPSendReset( pxNetworkBuffer );
                }
                else
                {
                    FreeRTOS_Socket_t * pxNewSocket = ( FreeRTOS_Socket_t * )
                                                      FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP );

                    if( ( pxNewSocket == NULL ) || ( pxNewSocket == FREERTOS_INVALID_SOCKET ) )
                    {
                        FreeRTOS_debug_printf( ( "TCP: Listen: new socket failed\n" ) );
                        ( void ) prvTCPSendReset( pxNetworkBuffer );
                    }
                    else if( prvTCPSocketCopy( pxNewSocket, pxSocket ) != pdFALSE )
                    {
                        /* The socket will be connected immediately, no time for the
                         * owner to setsockopt's, therefore copy properties of the server
                         * socket to the new socket.  Only the binding might fail (due to
                         * lack of resources). */
                        pxReturn = pxNewSocket;
                    }
                    else
                    {
                        /* Copying failed somehow. */
                    }
                }
            }
        }

        if( ( ulInitialSequenceNumber != 0U ) && ( pxReturn != NULL ) )
        {
            /* Map the byte stream onto the ProtocolHeaders_t for easy access to the fields. */
            const ProtocolHeaders_t * pxProtocolHeaders = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( ProtocolHeaders_t,
                                                                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );

            pxReturn->u.xTCP.usRemotePort = FreeRTOS_htons( pxTCPPacket->xTCPHeader.usSourcePort );
            pxReturn->u.xTCP.ulRemoteIP = FreeRTOS_htonl( pxTCPPacket->xIPHeader.ulSourceIPAddress );
            pxReturn->u.xTCP.xTCPWindow.ulOurSequenceNumber = ulInitialSequenceNumber;

            /* Here is the SYN action. */
            pxReturn->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber = FreeRTOS_ntohl( pxProtocolHeaders->xTCPHeader.ulSequenceNumber );
            prvSocketSetMSS( pxReturn );

            prvTCPCreateWindow( pxReturn );

            vTCPStateChange( pxReturn, eSYN_FIRST );

            /* Make a copy of the header up to the TCP header.  It is needed later
             * on, whenever data must be sent to the peer. */
            ( void ) memcpy( ( void * ) pxReturn->u.xTCP.xPacket.u.ucLastPacket,
                             ( const void * ) pxNetworkBuffer->pucEthernetBuffer,
                             sizeof( pxReturn->u.xTCP.xPacket.u.ucLastPacket ) );
        }

        return pxReturn;
    }
    /*-----------------------------------------------------------*/


/**
 * @brief Check incoming packets for valid data and handle the state of the
 *        TCP connection and respond according to the situation.
 *
 * @param[in] pxSocket: The socket whose connection state is being handled.
 * @param[in] ppxNetworkBuffer: The network buffer descriptor holding the
 *            packet received from the peer.
 *
 * @return If the data is correct and some packet was sent to the peer, then
 *         the number of bytes sent is returned, or else a negative value is
 *         returned indicating an error.
 *
 * @note prvTCPHandleState() is the most important function of this TCP stack
 * We've tried to keep it (relatively short) by putting a lot of code in
 * the functions above:
 *
 *      prvCheckRxData()
 *      prvStoreRxData()
 *      prvSetOptions()
 *      prvHandleSynReceived()
 *      prvHandleEstablished()
 *      prvSendData()
 *
 * As these functions are declared static, and they're called from one location
 * only, most compilers will inline them, thus avoiding a call and return.
 */
    BaseType_t prvTCPHandleState( FreeRTOS_Socket_t * pxSocket,
                                  NetworkBufferDescriptor_t ** ppxNetworkBuffer )
    {
        /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
        ProtocolHeaders_t * pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                        &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( *ppxNetworkBuffer ) ] ) );
        TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
        BaseType_t xSendLength = 0;
        uint32_t ulReceiveLength; /* Number of bytes contained in the TCP message. */
        uint8_t * pucRecvData;
        uint32_t ulSequenceNumber = FreeRTOS_ntohl( pxTCPHeader->ulSequenceNumber );

        /* uxOptionsLength: the size of the options to be sent (always a multiple of
         * 4 bytes)
         * 1. in the SYN phase, we shall communicate the MSS
         * 2. in case of a SACK, Selective ACK, ack a segment which comes in
         * out-of-order. */
        UBaseType_t uxOptionsLength = 0U;
        uint8_t ucTCPFlags = pxTCPHeader->ucTCPFlags;
        TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );
        UBaseType_t uxIntermediateResult = 0;

        /* First get the length and the position of the received data, if any.
         * pucRecvData will point to the first byte of the TCP payload. */
        ulReceiveLength = ( uint32_t ) prvCheckRxData( *ppxNetworkBuffer, &pucRecvData );

        if( pxSocket->u.xTCP.ucTCPState >= ( uint8_t ) eESTABLISHED )
        {
            if( pxTCPWindow->rx.ulCurrentSequenceNumber == ( ulSequenceNumber + 1UL ) )
            {
                /* This is most probably a keep-alive message from peer.  Setting
                 * 'bWinChange' doesn't cause a window-size-change, the flag is used
                 * here to force sending an immediate ACK. */
                pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
            }
        }

        /* Keep track of the highest sequence number that might be expected within
         * this connection. */
        if( ( ( int32_t ) ( ulSequenceNumber + ulReceiveLength - pxTCPWindow->rx.ulHighestSequenceNumber ) ) > 0L )
        {
            pxTCPWindow->rx.ulHighestSequenceNumber = ulSequenceNumber + ulReceiveLength;
        }

        /* Storing data may result in a fatal error if malloc() fails. */
        if( prvStoreRxData( pxSocket, pucRecvData, *ppxNetworkBuffer, ulReceiveLength ) < 0 )
        {
            xSendLength = -1;
        }
        else
        {
            uxOptionsLength = prvSetOptions( pxSocket, *ppxNetworkBuffer );

            if( ( pxSocket->u.xTCP.ucTCPState == ( uint8_t ) eSYN_RECEIVED ) && ( ( ucTCPFlags & ( uint8_t ) tcpTCP_FLAG_CTRL ) == ( uint8_t ) tcpTCP_FLAG_SYN ) )
            {
                FreeRTOS_debug_printf( ( "eSYN_RECEIVED: ACK expected, not SYN: peer missed our SYN+ACK\n" ) );

                /* In eSYN_RECEIVED a simple ACK is expected, but apparently the
                 * 'SYN+ACK' didn't arrive.  Step back to the previous state in which
                 * a first incoming SYN is handled.  The SYN was counted already so
                 * decrease it first. */
                vTCPStateChange( pxSocket, eSYN_FIRST );
            }

            if( ( ( ucTCPFlags & tcpTCP_FLAG_FIN ) != 0U ) && ( pxSocket->u.xTCP.bits.bFinRecv == pdFALSE_UNSIGNED ) )
            {
                /* It's the first time a FIN has been received, remember its
                 * sequence number. */
                pxTCPWindow->rx.ulFINSequenceNumber = ulSequenceNumber + ulReceiveLength;
                pxSocket->u.xTCP.bits.bFinRecv = pdTRUE_UNSIGNED;

                /* Was peer the first one to send a FIN? */
                if( pxSocket->u.xTCP.bits.bFinSent == pdFALSE_UNSIGNED )
                {
                    /* If so, don't send the-last-ACK. */
                    pxSocket->u.xTCP.bits.bFinLast = pdTRUE_UNSIGNED;
                }
            }

            switch( ipNUMERIC_CAST( eIPTCPState_t, pxSocket->u.xTCP.ucTCPState ) )
            {
                case eCLOSED: /* (server + client) no connection state at all. */

                    /* Nothing to do for a closed socket, except waiting for the
                     * owner. */
                    break;

                case eTCP_LISTEN: /* (server) waiting for a connection request from
                                   * any remote TCP and port. */

                    /* The listen state was handled in xProcessReceivedTCPPacket().
                     * Should not come here. */
                    break;

                case eSYN_FIRST: /* (server) Just received a SYN request for a server
                                  * socket. */

                    /* A new socket has been created, reply with a SYN+ACK.
                     * Acknowledge with seq+1 because the SYN is seen as pseudo data
                     * with len = 1. */
                    uxOptionsLength = prvSetSynAckOptions( pxSocket, pxTCPHeader );
                    pxTCPHeader->ucTCPFlags = ( uint8_t ) tcpTCP_FLAG_SYN | ( uint8_t ) tcpTCP_FLAG_ACK;

                    uxIntermediateResult = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength;
                    xSendLength = ( BaseType_t ) uxIntermediateResult;

                    /* Set the TCP offset field:  ipSIZE_OF_TCP_HEADER equals 20 and
                     * uxOptionsLength is a multiple of 4.  The complete expression is:
                     * ucTCPOffset = ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) / 4 ) << 4 */
                    pxTCPHeader->ucTCPOffset = ( uint8_t ) ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 );
                    vTCPStateChange( pxSocket, eSYN_RECEIVED );

                    pxTCPWindow->rx.ulHighestSequenceNumber = ulSequenceNumber + 1UL;
                    pxTCPWindow->rx.ulCurrentSequenceNumber = ulSequenceNumber + 1UL;
                    pxTCPWindow->ulNextTxSequenceNumber = pxTCPWindow->tx.ulFirstSequenceNumber + 1UL;
                    pxTCPWindow->tx.ulCurrentSequenceNumber = pxTCPWindow->tx.ulFirstSequenceNumber + 1UL; /* because we send a TCP_SYN. */
                    break;

                case eCONNECT_SYN:  /* (client) also called SYN_SENT: we've just send a
                                     * SYN, expect a SYN+ACK and send a ACK now. */
                /* Fall through */
                case eSYN_RECEIVED: /* (server) we've had a SYN, replied with SYN+SCK
                                     * expect a ACK and do nothing. */
                    xSendLength = prvHandleSynReceived( pxSocket, *( ppxNetworkBuffer ), ulReceiveLength, uxOptionsLength );
                    break;

                case eESTABLISHED: /* (server + client) an open connection, data
                                    * received can be delivered to the user. The normal
                                    * state for the data transfer phase of the connection
                                    * The closing states are also handled here with the
                                    * use of some flags. */
                    xSendLength = prvHandleEstablished( pxSocket, ppxNetworkBuffer, ulReceiveLength, uxOptionsLength );
                    break;

                case eLAST_ACK:   /* (server + client) waiting for an acknowledgement
                                   * of the connection termination request previously
                                   * sent to the remote TCP (which includes an
                                   * acknowledgement of its connection termination
                                   * request). */
                /* Fall through */
                case eFIN_WAIT_1: /* (server + client) waiting for a connection termination request from the remote TCP,
                                   * or an acknowledgement of the connection termination request previously sent. */
                /* Fall through */
                case eFIN_WAIT_2: /* (server + client) waiting for a connection termination request from the remote TCP. */
                    xSendLength = prvTCPHandleFin( pxSocket, *ppxNetworkBuffer );
                    break;

                case eCLOSE_WAIT: /* (server + client) waiting for a connection
                                   * termination request from the local user.  Nothing to
                                   * do, connection is closed, wait for owner to close
                                   * this socket. */
                    break;

                case eCLOSING: /* (server + client) waiting for a connection
                                * termination request acknowledgement from the remote
                                * TCP. */
                    break;

                case eTIME_WAIT: /* (either server or client) waiting for enough time
                                  * to pass to be sure the remote TCP received the
                                  * acknowledgement of its connection termination
                                  * request. [According to RFC 793 a connection can stay
                                  * in TIME-WAIT for a maximum of four minutes known as
                                  * a MSL (maximum segment lifetime).]  These states are
                                  * implemented implicitly by settings flags like
                                  * 'bFinSent', 'bFinRecv', and 'bFinAcked'. */
                    break;

                default:
                    /* No more known states. */
                    break;
            }
        }

        if( xSendLength > 0 )
        {
            xSendLength = prvSendData( pxSocket, ppxNetworkBuffer, ulReceiveLength, xSendLength );
        }

        return xSendLength;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief prvTCPSendRepeated will try to send a series of messages, as
 *        long as there is data to be sent and as long as the transmit
 *        window isn't full.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[in,out] ppxNetworkBuffer: Pointer to pointer to the network buffer.
 *
 * @return Total number of bytes sent.
 */
    int32_t prvTCPSendRepeated( FreeRTOS_Socket_t * pxSocket,
                                NetworkBufferDescriptor_t ** ppxNetworkBuffer )
    {
        UBaseType_t uxIndex;
        int32_t lResult = 0;
        UBaseType_t uxOptionsLength = 0U;
        int32_t xSendLength;

        for( uxIndex = 0U; uxIndex < ( UBaseType_t ) SEND_REPEATED_COUNT; uxIndex++ )
        {
            /* prvTCPPrepareSend() might allocate a network buffer if there is data
             * to be sent. */
            xSendLength = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

            if( xSendLength <= 0 )
            {
                break;
            }

            /* And return the packet to the peer. */
            prvTCPReturnPacket( pxSocket, *ppxNetworkBuffer, ( uint32_t ) xSendLength, ipconfigZERO_COPY_TX_DRIVER );

            #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
                {
                    *ppxNetworkBuffer = NULL;
                }
            #endif /* ipconfigZERO_COPY_TX_DRIVER */

            lResult += xSendLength;
        }

        /* Return the total number of bytes sent. */
        return lResult;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Prepare an outgoing message, in case anything has to be sent.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[in,out] ppxNetworkBuffer: Pointer to the pointer to the network buffer.
 * @param[in] uxOptionsLength: The length of the TCP options.
 *
 * @return Length of the data to be sent if everything is correct. Else, -1
 *         is returned in case of any error.
 */
    int32_t prvTCPPrepareSend( FreeRTOS_Socket_t * pxSocket,
                               NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                               UBaseType_t uxOptionsLength )
    {
        int32_t lDataLen;
        uint8_t * pucEthernetBuffer, * pucSendData;
        ProtocolHeaders_t * pxProtocolHeaders;
        size_t uxOffset;
        uint32_t ulDataGot, ulDistance;
        TCPWindow_t * pxTCPWindow;
        NetworkBufferDescriptor_t * pxNewBuffer;
        int32_t lStreamPos;
        UBaseType_t uxIntermediateResult = 0;

        if( ( *ppxNetworkBuffer ) != NULL )
        {
            /* A network buffer descriptor was already supplied */
            pucEthernetBuffer = ( *ppxNetworkBuffer )->pucEthernetBuffer;
        }
        else
        {
            /* For now let it point to the last packet header */
            pucEthernetBuffer = pxSocket->u.xTCP.xPacket.u.ucLastPacket;
        }

        /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
        pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] ) );
        pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );
        lDataLen = 0;
        lStreamPos = 0;
        pxProtocolHeaders->xTCPHeader.ucTCPFlags |= tcpTCP_FLAG_ACK;

        if( pxSocket->u.xTCP.txStream != NULL )
        {
            /* ulTCPWindowTxGet will return the amount of data which may be sent
             * along with the position in the txStream.
             * Why check for MSS > 1 ?
             * Because some TCP-stacks (like uIP) use it for flow-control. */
            if( pxSocket->u.xTCP.usCurMSS > 1U )
            {
                lDataLen = ( int32_t ) ulTCPWindowTxGet( pxTCPWindow, pxSocket->u.xTCP.ulWindowSize, &lStreamPos );
            }

            if( lDataLen > 0 )
            {
                /* Check if the current network buffer is big enough, if not,
                 * resize it. */
                pxNewBuffer = prvTCPBufferResize( pxSocket, *ppxNetworkBuffer, lDataLen, uxOptionsLength );

                if( pxNewBuffer != NULL )
                {
                    *ppxNetworkBuffer = pxNewBuffer;
                    pucEthernetBuffer = pxNewBuffer->pucEthernetBuffer;

                    /* Map the byte stream onto ProtocolHeaders_t struct for easy
                     * access to the fields. */
                    pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] ) );

                    pucSendData = &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength ] );

                    /* Translate the position in txStream to an offset from the tail
                     * marker. */
                    uxOffset = uxStreamBufferDistance( pxSocket->u.xTCP.txStream, pxSocket->u.xTCP.txStream->uxTail, ( size_t ) lStreamPos );

                    /* Here data is copied from the txStream in 'peek' mode.  Only
                     * when the packets are acked, the tail marker will be updated. */
                    ulDataGot = ( uint32_t ) uxStreamBufferGet( pxSocket->u.xTCP.txStream, uxOffset, pucSendData, ( size_t ) lDataLen, pdTRUE );

                    #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
                        {
                            if( ulDataGot != ( uint32_t ) lDataLen )
                            {
                                FreeRTOS_debug_printf( ( "uxStreamBufferGet: pos %d offs %u only %u != %d\n",
                                                         ( int ) lStreamPos, ( unsigned ) uxOffset, ( unsigned ) ulDataGot, ( int ) lDataLen ) );
                            }
                        }
                    #endif

                    /* If the owner of the socket requests a closure, add the FIN
                     * flag to the last packet. */
                    if( ( pxSocket->u.xTCP.bits.bCloseRequested != pdFALSE_UNSIGNED ) && ( pxSocket->u.xTCP.bits.bFinSent == pdFALSE_UNSIGNED ) )
                    {
                        ulDistance = ( uint32_t ) uxStreamBufferDistance( pxSocket->u.xTCP.txStream, ( size_t ) lStreamPos, pxSocket->u.xTCP.txStream->uxHead );

                        if( ulDistance == ulDataGot )
                        {
                            #if ( ipconfigHAS_DEBUG_PRINTF == 1 )
                                {
                                    /* the order of volatile accesses is undefined
                                     *  so such workaround */
                                    size_t uxHead = pxSocket->u.xTCP.txStream->uxHead;
                                    size_t uxMid = pxSocket->u.xTCP.txStream->uxMid;
                                    size_t uxTail = pxSocket->u.xTCP.txStream->uxTail;

                                    FreeRTOS_debug_printf( ( "CheckClose %u <= %u (%u <= %u <= %u)\n",
                                                             ( unsigned ) ulDataGot, ( unsigned ) ulDistance,
                                                             ( unsigned ) uxTail, ( unsigned ) uxMid, ( unsigned ) uxHead ) );
                                }
                            #endif /* if ( ipconfigHAS_DEBUG_PRINTF == 1 ) */

                            /* Although the socket sends a FIN, it will stay in
                             * ESTABLISHED until all current data has been received or
                             * delivered. */
                            pxProtocolHeaders->xTCPHeader.ucTCPFlags |= tcpTCP_FLAG_FIN;
                            pxTCPWindow->tx.ulFINSequenceNumber = pxTCPWindow->ulOurSequenceNumber + ( uint32_t ) lDataLen;
                            pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
                        }
                    }
                }
                else
                {
                    lDataLen = -1;
                }
            }
        }

        if( ( lDataLen >= 0 ) && ( pxSocket->u.xTCP.ucTCPState == ( uint8_t ) eESTABLISHED ) )
        {
            /* See if the socket owner wants to shutdown this connection. */
            if( ( pxSocket->u.xTCP.bits.bUserShutdown != pdFALSE_UNSIGNED ) &&
                ( xTCPWindowTxDone( pxTCPWindow ) != pdFALSE ) )
            {
                pxSocket->u.xTCP.bits.bUserShutdown = pdFALSE_UNSIGNED;
                pxProtocolHeaders->xTCPHeader.ucTCPFlags |= tcpTCP_FLAG_FIN;
                pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
                pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
                pxTCPWindow->tx.ulFINSequenceNumber = pxTCPWindow->tx.ulCurrentSequenceNumber;
                vTCPStateChange( pxSocket, eFIN_WAIT_1 );
            }

            #if ( ipconfigTCP_KEEP_ALIVE != 0 )
                {
                    if( pxSocket->u.xTCP.ucKeepRepCount > 3U ) /*_RB_ Magic number. */
                    {
                        FreeRTOS_debug_printf( ( "keep-alive: giving up %lxip:%u\n",
                                                 pxSocket->u.xTCP.ulRemoteIP,       /* IP address of remote machine. */
                                                 pxSocket->u.xTCP.usRemotePort ) ); /* Port on remote machine. */
                        vTCPStateChange( pxSocket, eCLOSE_WAIT );
                        lDataLen = -1;
                    }

                    if( ( lDataLen == 0 ) && ( pxSocket->u.xTCP.bits.bWinChange == pdFALSE_UNSIGNED ) )
                    {
                        /* If there is no data to be sent, and no window-update message,
                         * we might want to send a keep-alive message. */
                        TickType_t xAge = xTaskGetTickCount() - pxSocket->u.xTCP.xLastAliveTime;
                        TickType_t xMax;
                        xMax = ( ( TickType_t ) ipconfigTCP_KEEP_ALIVE_INTERVAL * ( TickType_t ) configTICK_RATE_HZ );

                        if( pxSocket->u.xTCP.ucKeepRepCount != ( uint8_t ) 0U )
                        {
                            xMax = ( TickType_t ) ( 3U * configTICK_RATE_HZ );
                        }

                        if( xAge > xMax )
                        {
                            pxSocket->u.xTCP.xLastAliveTime = xTaskGetTickCount();

                            if( xTCPWindowLoggingLevel != 0 )
                            {
                                FreeRTOS_debug_printf( ( "keep-alive: %lxip:%u count %u\n",
                                                         pxSocket->u.xTCP.ulRemoteIP,
                                                         pxSocket->u.xTCP.usRemotePort,
                                                         pxSocket->u.xTCP.ucKeepRepCount ) );
                            }

                            pxSocket->u.xTCP.bits.bSendKeepAlive = pdTRUE_UNSIGNED;
                            pxSocket->u.xTCP.usTimeout = ( ( uint16_t ) pdMS_TO_TICKS( 2500U ) );
                            pxSocket->u.xTCP.ucKeepRepCount++;
                        }
                    }
                }
            #endif /* ipconfigTCP_KEEP_ALIVE */
        }

        /* Anything to send, a change of the advertised window size, or maybe send a
         * keep-alive message? */
        if( ( lDataLen > 0 ) ||
            ( pxSocket->u.xTCP.bits.bWinChange != pdFALSE_UNSIGNED ) ||
            ( pxSocket->u.xTCP.bits.bSendKeepAlive != pdFALSE_UNSIGNED ) )
        {
            pxProtocolHeaders->xTCPHeader.ucTCPFlags &= ( ( uint8_t ) ~tcpTCP_FLAG_PSH );
            pxProtocolHeaders->xTCPHeader.ucTCPOffset = ( uint8_t ) ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 ); /*_RB_ "2" needs comment. */

            pxProtocolHeaders->xTCPHeader.ucTCPFlags |= ( uint8_t ) tcpTCP_FLAG_ACK;

            if( lDataLen != 0L )
            {
                pxProtocolHeaders->xTCPHeader.ucTCPFlags |= ( uint8_t ) tcpTCP_FLAG_PSH;
            }

            uxIntermediateResult = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength;
            lDataLen += ( int32_t ) uxIntermediateResult;
        }

        return lDataLen;
    }
    /*-----------------------------------------------------------*/

#endif /* if ipconfigUSE_TCP == 1 */
