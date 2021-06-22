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
 * @file FreeRTOS_TCP_IP_StateHandling.c
 *
 * All TCP events and actions that are related to the current state
 * like TCP options, SYN, FIN, transmission and reception.
 * 
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
 * @brief prvCheckRxData(): called from prvTCPHandleState(). The
 *        first thing that will be done is find the TCP payload data
 *        and check the length of this data.
 *
 * @param[in] pxNetworkBuffer: The network buffer holding the received data.
 * @param[out] ppucRecvData: It will point to first byte of the TCP payload.
 *
 * @return Length of the received buffer.
 */
    BaseType_t prvCheckRxData( const NetworkBufferDescriptor_t * pxNetworkBuffer,
                                      uint8_t ** ppucRecvData )
    {
        /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
        const ProtocolHeaders_t * pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                              &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
        const TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
        int32_t lLength, lTCPHeaderLength, lReceiveLength, lUrgentLength;

        /* Map the buffer onto an IPHeader_t struct for easy access to fields. */
        const IPHeader_t * pxIPHeader = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( IPHeader_t, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );
        const size_t xIPHeaderLength = ipSIZE_OF_IPv4_HEADER;
        uint16_t usLength;
        uint8_t ucIntermediateResult = 0;

        /* Determine the length and the offset of the user-data sent to this
         * node.
         *
         * The size of the TCP header is given in a multiple of 4-byte words (single
         * byte, needs no ntoh() translation).  A shift-right 2: is the same as
         * (offset >> 4) * 4. */
        ucIntermediateResult = ( pxTCPHeader->ucTCPOffset & tcpVALID_BITS_IN_TCP_OFFSET_BYTE ) >> 2;
        lTCPHeaderLength = ( int32_t ) ucIntermediateResult;

        /* Let pucRecvData point to the first byte received. */
        *ppucRecvData = &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + xIPHeaderLength + ( size_t ) lTCPHeaderLength ] );

        /* Calculate lReceiveLength - the length of the TCP data received.  This is
         * equal to the total packet length minus:
         * ( LinkLayer length (14) + IP header length (20) + size of TCP header(20 +) ).*/
        lReceiveLength = ipNUMERIC_CAST( int32_t, pxNetworkBuffer->xDataLength ) - ( int32_t ) ipSIZE_OF_ETH_HEADER;

        usLength = FreeRTOS_htons( pxIPHeader->usLength );
        lLength = ( int32_t ) usLength;

        if( lReceiveLength > lLength )
        {
            /* More bytes were received than the reported length, often because of
             * padding bytes at the end. */
            lReceiveLength = lLength;
        }

        /* Subtract the size of the TCP and IP headers and the actual data size is
         * known. */
        if( lReceiveLength > ( lTCPHeaderLength + ( int32_t ) xIPHeaderLength ) )
        {
            lReceiveLength -= ( lTCPHeaderLength + ( int32_t ) xIPHeaderLength );
        }
        else
        {
            lReceiveLength = 0;
        }

        /* Urgent Pointer:
         * This field communicates the current value of the urgent pointer as a
         * positive offset from the sequence number in this segment.  The urgent
         * pointer points to the sequence number of the octet following the urgent
         * data.  This field is only be interpreted in segments with the URG control
         * bit set. */
        if( ( pxTCPHeader->ucTCPFlags & tcpTCP_FLAG_URG ) != 0U )
        {
            /* Although we ignore the urgent data, we have to skip it. */
            lUrgentLength = ( int32_t ) FreeRTOS_htons( pxTCPHeader->usUrgent );
            *ppucRecvData += lUrgentLength;
            lReceiveLength -= FreeRTOS_min_int32( lReceiveLength, lUrgentLength );
        }

        return ( BaseType_t ) lReceiveLength;
    }
    /*-----------------------------------------------------------*/


/**
 * @brief prvHandleEstablished(): called from prvTCPHandleState()
 *        Called if the status is eESTABLISHED. Data reception has been handled
 *        earlier. Here the ACK's from peer will be checked, and if a FIN is received,
 *        the code will check if it may be accepted, i.e. if all expected data has been
 *        completely received.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[in,out] ppxNetworkBuffer: Pointer to pointer to the network buffer.
 * @param[in] ulReceiveLength: The length of the received packet.
 * @param[in] uxOptionsLength: Length of TCP options.
 *
 * @return The send length of the packet to be sent.
 */
    BaseType_t prvHandleEstablished( FreeRTOS_Socket_t * pxSocket,
                                            NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                                            uint32_t ulReceiveLength,
                                            UBaseType_t uxOptionsLength )
    {
        /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
        ProtocolHeaders_t * pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                        &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] ) );
        TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
        TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
        uint8_t ucTCPFlags = pxTCPHeader->ucTCPFlags;
        uint32_t ulSequenceNumber = FreeRTOS_ntohl( pxTCPHeader->ulSequenceNumber ), ulCount, ulIntermediateResult = 0;
        BaseType_t xSendLength = 0, xMayClose = pdFALSE, bRxComplete, bTxDone;
        int32_t lDistance, lSendResult;
        uint16_t usWindow;
        UBaseType_t uxIntermediateResult = 0;

        /* Remember the window size the peer is advertising. */
        usWindow = FreeRTOS_ntohs( pxTCPHeader->usWindow );
        pxSocket->u.xTCP.ulWindowSize = ( uint32_t ) usWindow;
        #if ( ipconfigUSE_TCP_WIN != 0 )
            {
                pxSocket->u.xTCP.ulWindowSize =
                    ( pxSocket->u.xTCP.ulWindowSize << pxSocket->u.xTCP.ucPeerWinScaleFactor );
            }
        #endif /* ipconfigUSE_TCP_WIN */

        if( ( ucTCPFlags & ( uint8_t ) tcpTCP_FLAG_ACK ) != 0U )
        {
            ulCount = ulTCPWindowTxAck( pxTCPWindow, FreeRTOS_ntohl( pxTCPHeader->ulAckNr ) );

            /* ulTCPWindowTxAck() returns the number of bytes which have been acked,
             * starting at 'tx.ulCurrentSequenceNumber'.  Advance the tail pointer in
             * txStream. */
            if( ( pxSocket->u.xTCP.txStream != NULL ) && ( ulCount > 0U ) )
            {
                /* Just advancing the tail index, 'ulCount' bytes have been
                 * confirmed, and because there is new space in the txStream, the
                 * user/owner should be woken up. */
                /* _HT_ : only in case the socket's waiting? */
                if( uxStreamBufferGet( pxSocket->u.xTCP.txStream, 0U, NULL, ( size_t ) ulCount, pdFALSE ) != 0U )
                {
                    pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_SEND;

                    #if ipconfigSUPPORT_SELECT_FUNCTION == 1
                        {
                            if( ( pxSocket->xSelectBits & ( ( EventBits_t ) eSELECT_WRITE ) ) != 0U )
                            {
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
                                pxSocket->u.xTCP.pxHandleSent( ( Socket_t ) pxSocket, ulCount );
                            }
                        }
                    #endif /* ipconfigUSE_CALLBACKS == 1  */
                }
            }
        }

        /* If this socket has a stream for transmission, add the data to the
         * outgoing segment(s). */
        if( pxSocket->u.xTCP.txStream != NULL )
        {
            prvTCPAddTxData( pxSocket );
        }

        pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = pxTCPWindow->tx.ulCurrentSequenceNumber;

        if( ( pxSocket->u.xTCP.bits.bFinAccepted != pdFALSE_UNSIGNED ) || ( ( ucTCPFlags & ( uint8_t ) tcpTCP_FLAG_FIN ) != 0U ) )
        {
            /* Peer is requesting to stop, see if we're really finished. */
            xMayClose = pdTRUE;

            /* Checks are only necessary if we haven't sent a FIN yet. */
            if( pxSocket->u.xTCP.bits.bFinSent == pdFALSE_UNSIGNED )
            {
                /* xTCPWindowTxDone returns true when all Tx queues are empty. */
                bRxComplete = xTCPWindowRxEmpty( pxTCPWindow );
                bTxDone = xTCPWindowTxDone( pxTCPWindow );

                if( ( bRxComplete == 0 ) || ( bTxDone == 0 ) )
                {
                    /* Refusing FIN: Rx incomplete 1 optlen 4 tx done 1. */
                    FreeRTOS_debug_printf( ( "Refusing FIN[%u,%u]: RxCompl %lu tx done %ld\n",
                                             pxSocket->usLocalPort,
                                             pxSocket->u.xTCP.usRemotePort,
                                             bRxComplete, bTxDone ) );
                    xMayClose = pdFALSE;
                }
                else
                {
                    ulIntermediateResult = ulSequenceNumber + ulReceiveLength - pxTCPWindow->rx.ulCurrentSequenceNumber;
                    lDistance = ( int32_t ) ulIntermediateResult;

                    if( lDistance > 1 )
                    {
                        FreeRTOS_debug_printf( ( "Refusing FIN: Rx not complete %ld (cur %lu high %lu)\n",
                                                 lDistance, pxTCPWindow->rx.ulCurrentSequenceNumber - pxTCPWindow->rx.ulFirstSequenceNumber,
                                                 pxTCPWindow->rx.ulHighestSequenceNumber - pxTCPWindow->rx.ulFirstSequenceNumber ) );

                        xMayClose = pdFALSE;
                    }
                }
            }

            if( xTCPWindowLoggingLevel > 0 )
            {
                FreeRTOS_debug_printf( ( "TCP: FIN received, mayClose = %ld (Rx %lu Len %ld, Tx %lu)\n",
                                         xMayClose, ulSequenceNumber - pxSocket->u.xTCP.xTCPWindow.rx.ulFirstSequenceNumber, ulReceiveLength,
                                         pxTCPWindow->tx.ulCurrentSequenceNumber - pxSocket->u.xTCP.xTCPWindow.tx.ulFirstSequenceNumber ) );
            }

            if( xMayClose != pdFALSE )
            {
                pxSocket->u.xTCP.bits.bFinAccepted = pdTRUE_UNSIGNED;
                xSendLength = prvTCPHandleFin( pxSocket, *ppxNetworkBuffer );
            }
        }

        if( xMayClose == pdFALSE )
        {
            pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;

            if( ulReceiveLength != 0U )
            {
                uxIntermediateResult = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength;
                xSendLength = ( BaseType_t ) uxIntermediateResult;
                /* TCP-offset equals '( ( length / 4 ) << 4 )', resulting in a shift-left 2 */
                pxTCPHeader->ucTCPOffset = ( uint8_t ) ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 );

                if( pxSocket->u.xTCP.bits.bFinSent != pdFALSE_UNSIGNED )
                {
                    pxTCPWindow->tx.ulCurrentSequenceNumber = pxTCPWindow->tx.ulFINSequenceNumber;
                }
            }

            /* Now get data to be transmitted. */

            /* _HT_ patch: since the MTU has be fixed at 1500 in stead of 1526, TCP
             * can not send-out both TCP options and also a full packet. Sending
             * options (SACK) is always more urgent than sending data, which can be
             * sent later. */
            if( uxOptionsLength == 0U )
            {
                /* prvTCPPrepareSend might allocate a bigger network buffer, if
                 * necessary. */
                lSendResult = prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );

                if( lSendResult > 0 )
                {
                    xSendLength = ( BaseType_t ) lSendResult;
                }
            }
        }

        return xSendLength;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief prvTCPHandleFin() will be called to handle connection closure. The
 *        closure starts when either a FIN has been received and accepted,
 *        or when the socket has sent a FIN flag to the peer. Before being
 *        called, it has been checked that both reception and transmission
 *        are complete.
 *
 * @param[in] pxSocket: Socket owning the the connection.
 * @param[in] pxNetworkBuffer: The network buffer carrying the TCP packet.
 *
 * @return Length of the packet to be sent.
 */
    BaseType_t prvTCPHandleFin( FreeRTOS_Socket_t * pxSocket,
                                       const NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
        ProtocolHeaders_t * pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                        &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
        TCPHeader_t * pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );
        uint8_t ucIntermediateResult = 0, ucTCPFlags = pxTCPHeader->ucTCPFlags;
        TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
        BaseType_t xSendLength = 0;
        uint32_t ulAckNr = FreeRTOS_ntohl( pxTCPHeader->ulAckNr );

        if( ( ucTCPFlags & tcpTCP_FLAG_FIN ) != 0U )
        {
            pxTCPWindow->rx.ulCurrentSequenceNumber = pxTCPWindow->rx.ulFINSequenceNumber + 1U;
        }

        if( pxSocket->u.xTCP.bits.bFinSent == pdFALSE_UNSIGNED )
        {
            /* We haven't yet replied with a FIN, do so now. */
            pxTCPWindow->tx.ulFINSequenceNumber = pxTCPWindow->tx.ulCurrentSequenceNumber;
            pxSocket->u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
        }
        else
        {
            /* We did send a FIN already, see if it's ACK'd. */
            if( ulAckNr == ( pxTCPWindow->tx.ulFINSequenceNumber + 1UL ) )
            {
                pxSocket->u.xTCP.bits.bFinAcked = pdTRUE_UNSIGNED;
            }
        }

        if( pxSocket->u.xTCP.bits.bFinAcked == pdFALSE_UNSIGNED )
        {
            pxTCPWindow->tx.ulCurrentSequenceNumber = pxTCPWindow->tx.ulFINSequenceNumber;
            pxTCPHeader->ucTCPFlags = ( uint8_t ) tcpTCP_FLAG_ACK | ( uint8_t ) tcpTCP_FLAG_FIN;

            /* And wait for the final ACK. */
            vTCPStateChange( pxSocket, eLAST_ACK );
        }
        else
        {
            /* Our FIN has been ACK'd, the outgoing sequence number is now fixed. */
            pxTCPWindow->tx.ulCurrentSequenceNumber = pxTCPWindow->tx.ulFINSequenceNumber + 1U;

            if( pxSocket->u.xTCP.bits.bFinRecv == pdFALSE_UNSIGNED )
            {
                /* We have sent out a FIN but the peer hasn't replied with a FIN
                 * yet. Do nothing for the moment. */
                pxTCPHeader->ucTCPFlags = 0U;
            }
            else
            {
                if( pxSocket->u.xTCP.bits.bFinLast == pdFALSE_UNSIGNED )
                {
                    /* This is the third of the three-way hand shake: the last
                     * ACK. */
                    pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;
                }
                else
                {
                    /* The other party started the closure, so we just wait for the
                     * last ACK. */
                    pxTCPHeader->ucTCPFlags = 0U;
                }

                /* And wait for the user to close this socket. */
                vTCPStateChange( pxSocket, eCLOSE_WAIT );
            }
        }

        pxTCPWindow->ulOurSequenceNumber = pxTCPWindow->tx.ulCurrentSequenceNumber;

        if( pxTCPHeader->ucTCPFlags != 0U )
        {
            ucIntermediateResult = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + pxTCPWindow->ucOptionLength;
            xSendLength = ( BaseType_t ) ucIntermediateResult;
        }

        pxTCPHeader->ucTCPOffset = ( uint8_t ) ( ( ipSIZE_OF_TCP_HEADER + pxTCPWindow->ucOptionLength ) << 2 );

        if( xTCPWindowLoggingLevel != 0 )
        {
            FreeRTOS_debug_printf( ( "TCP: send FIN+ACK (ack %lu, cur/nxt %lu/%lu) ourSeqNr %lu | Rx %lu\n",
                                     ulAckNr - pxTCPWindow->tx.ulFirstSequenceNumber,
                                     pxTCPWindow->tx.ulCurrentSequenceNumber - pxTCPWindow->tx.ulFirstSequenceNumber,
                                     pxTCPWindow->ulNextTxSequenceNumber - pxTCPWindow->tx.ulFirstSequenceNumber,
                                     pxTCPWindow->ulOurSequenceNumber - pxTCPWindow->tx.ulFirstSequenceNumber,
                                     pxTCPWindow->rx.ulCurrentSequenceNumber - pxTCPWindow->rx.ulFirstSequenceNumber ) );
        }

        return xSendLength;
    }
    /*-----------------------------------------------------------*/


/**
 * @brief prvHandleSynReceived(): called from prvTCPHandleState(). Called
 *        from the states: eSYN_RECEIVED and eCONNECT_SYN. If the flags
 *        received are correct, the socket will move to eESTABLISHED.
 *
 * @param[in] pxSocket: The socket handling the connection.
 * @param[in] pxNetworkBuffer: The pointer to the network buffer carrying
 *                             the packet.
 * @param[in] ulReceiveLength: Length in bytes of the data received.
 * @param[in] uxOptionsLength: Length of the TCP options in bytes.
 *
 * @return Length of the data to be sent.
 */
    BaseType_t prvHandleSynReceived( FreeRTOS_Socket_t * pxSocket,
                                            const NetworkBufferDescriptor_t * pxNetworkBuffer,
                                            uint32_t ulReceiveLength,
                                            UBaseType_t uxOptionsLength )
    {
        /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
        ProtocolHeaders_t * pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                        &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] ) );
        TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
        TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
        uint8_t ucTCPFlags = pxTCPHeader->ucTCPFlags;
        uint32_t ulSequenceNumber = FreeRTOS_ntohl( pxTCPHeader->ulSequenceNumber );
        BaseType_t xSendLength = 0;
        UBaseType_t uxIntermediateResult = 0U;

        /* Either expect a ACK or a SYN+ACK. */
        uint8_t ucExpect = tcpTCP_FLAG_ACK;
        const uint8_t ucFlagsMask = tcpTCP_FLAG_ACK | tcpTCP_FLAG_RST | tcpTCP_FLAG_SYN | tcpTCP_FLAG_FIN;

        if( pxSocket->u.xTCP.ucTCPState == ( uint8_t ) eCONNECT_SYN )
        {
            ucExpect |= tcpTCP_FLAG_SYN;
        }

        if( ( ucTCPFlags & ucFlagsMask ) != ucExpect )
        {
            /* eSYN_RECEIVED: flags 0010 expected, not 0002. */
            /* eSYN_RECEIVED: flags ACK  expected, not SYN. */
            FreeRTOS_debug_printf( ( "%s: flags %04X expected, not %04X\n",
                                     ( pxSocket->u.xTCP.ucTCPState == ( uint8_t ) eSYN_RECEIVED ) ? "eSYN_RECEIVED" : "eCONNECT_SYN",
                                     ucExpect, ucTCPFlags ) );

            /* In case pxSocket is not yet owned by the application, a closure
             * of the socket will be scheduled for the next cycle. */
            vTCPStateChange( pxSocket, eCLOSE_WAIT );

            /* Send RST with the expected sequence and ACK numbers,
             * otherwise the packet will be ignored. */
            pxTCPWindow->ulOurSequenceNumber = FreeRTOS_htonl( pxTCPHeader->ulAckNr );
            pxTCPWindow->rx.ulCurrentSequenceNumber = ulSequenceNumber;

            pxTCPHeader->ucTCPFlags |= tcpTCP_FLAG_RST;

            uxIntermediateResult = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength;
            xSendLength = ( BaseType_t ) uxIntermediateResult;

            pxTCPHeader->ucTCPOffset = ( uint8_t ) ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 );
        }
        else
        {
            pxTCPWindow->usPeerPortNumber = pxSocket->u.xTCP.usRemotePort;
            pxTCPWindow->usOurPortNumber = pxSocket->usLocalPort;

            if( pxSocket->u.xTCP.ucTCPState == ( uint8_t ) eCONNECT_SYN )
            {
                /* Map the Last packet onto the ProtocolHeader_t struct for easy access to the fields. */
                ProtocolHeaders_t * pxLastHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                            &( pxSocket->u.xTCP.xPacket.u.ucLastPacket[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] ) );

                /* Clear the SYN flag in lastPacket. */
                pxLastHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_ACK;
                pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_ACK;

                /* This socket was the one connecting actively so now perform the
                 * synchronisation. */
                vTCPWindowInit( &pxSocket->u.xTCP.xTCPWindow,
                                ulSequenceNumber, pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber, ( uint32_t ) pxSocket->u.xTCP.usCurMSS );
                pxTCPWindow->rx.ulHighestSequenceNumber = ulSequenceNumber + 1U;
                pxTCPWindow->rx.ulCurrentSequenceNumber = ulSequenceNumber + 1U;
                pxTCPWindow->tx.ulCurrentSequenceNumber++; /* because we send a TCP_SYN [ | TCP_ACK ]; */
                pxTCPWindow->ulNextTxSequenceNumber++;
            }
            else if( ulReceiveLength == 0U )
            {
                pxTCPWindow->rx.ulCurrentSequenceNumber = ulSequenceNumber;
            }
            else
            {
                /* Nothing. */
            }

            /* The SYN+ACK has been confirmed, increase the next sequence number by
             * 1. */
            pxTCPWindow->ulOurSequenceNumber = pxTCPWindow->tx.ulFirstSequenceNumber + 1U;

            #if ( ipconfigUSE_TCP_WIN == 1 )
                {
                    FreeRTOS_debug_printf( ( "TCP: %s %d => %lxip:%d set ESTAB (scaling %u)\n",
                                             ( pxSocket->u.xTCP.ucTCPState == ( uint8_t ) eCONNECT_SYN ) ? "active" : "passive",
                                             pxSocket->usLocalPort,
                                             pxSocket->u.xTCP.ulRemoteIP,
                                             pxSocket->u.xTCP.usRemotePort,
                                             ( unsigned ) pxSocket->u.xTCP.bits.bWinScaling ) );
                }
            #endif /* ipconfigUSE_TCP_WIN */

            if( ( pxSocket->u.xTCP.ucTCPState == ( EventBits_t ) eCONNECT_SYN ) || ( ulReceiveLength != 0UL ) )
            {
                pxTCPHeader->ucTCPFlags = tcpTCP_FLAG_ACK;

                uxIntermediateResult = uxIPHeaderSizeSocket( pxSocket ) + ( size_t ) ipSIZE_OF_TCP_HEADER + uxOptionsLength;
                xSendLength = ( BaseType_t ) uxIntermediateResult;
                pxTCPHeader->ucTCPOffset = ( uint8_t ) ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 );
            }

            #if ( ipconfigUSE_TCP_WIN != 0 )
                {
                    if( pxSocket->u.xTCP.bits.bWinScaling == pdFALSE_UNSIGNED )
                    {
                        /* The other party did not send a scaling factor.
                         * A shifting factor in this side must be canceled. */
                        pxSocket->u.xTCP.ucMyWinScaleFactor = 0;
                        pxSocket->u.xTCP.ucPeerWinScaleFactor = 0;
                    }
                }
            #endif /* ipconfigUSE_TCP_WIN */

            /* This was the third step of connecting: SYN, SYN+ACK, ACK so now the
             * connection is established. */
            vTCPStateChange( pxSocket, eESTABLISHED );
        }

        return xSendLength;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Set the TCP options (if any) for the outgoing packet.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[in] pxNetworkBuffer: The network buffer holding the packet.
 *
 * @return Length of the TCP options after they are set.
 */
    UBaseType_t prvSetOptions( FreeRTOS_Socket_t * pxSocket,
                                      const NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
        ProtocolHeaders_t * pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                        &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
        TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
        const TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
        UBaseType_t uxOptionsLength = pxTCPWindow->ucOptionLength;

        #if ( ipconfigUSE_TCP_WIN == 1 )
            /* memcpy() helper variables for MISRA Rule 21.15 compliance*/
            const void * pvCopySource;
            void * pvCopyDest;

            if( uxOptionsLength != 0U )
            {
                /* TCP options must be sent because a packet which is out-of-order
                 * was received. */
                if( xTCPWindowLoggingLevel >= 0 )
                {
                    FreeRTOS_debug_printf( ( "SACK[%d,%d]: optlen %lu sending %lu - %lu\n",
                                             pxSocket->usLocalPort,
                                             pxSocket->u.xTCP.usRemotePort,
                                             uxOptionsLength,
                                             FreeRTOS_ntohl( pxTCPWindow->ulOptionsData[ 1 ] ) - pxSocket->u.xTCP.xTCPWindow.rx.ulFirstSequenceNumber,
                                             FreeRTOS_ntohl( pxTCPWindow->ulOptionsData[ 2 ] ) - pxSocket->u.xTCP.xTCPWindow.rx.ulFirstSequenceNumber ) );
                }

                /*
                 * Use helper variables for memcpy() source & dest to remain
                 * compliant with MISRA Rule 21.15.  These should be
                 * optimized away.
                 */
                pvCopySource = pxTCPWindow->ulOptionsData;
                pvCopyDest = pxTCPHeader->ucOptdata;
                ( void ) memcpy( pvCopyDest, pvCopySource, ( size_t ) uxOptionsLength );

                /* The header length divided by 4, goes into the higher nibble,
                 * effectively a shift-left 2. */
                pxTCPHeader->ucTCPOffset = ( uint8_t ) ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 );
            }
            else
        #endif /* ipconfigUSE_TCP_WIN */

        if( ( pxSocket->u.xTCP.ucTCPState >= ( EventBits_t ) eESTABLISHED ) && ( pxSocket->u.xTCP.bits.bMssChange != pdFALSE_UNSIGNED ) )
        {
            /* TCP options must be sent because the MSS has changed. */
            pxSocket->u.xTCP.bits.bMssChange = pdFALSE_UNSIGNED;

            if( xTCPWindowLoggingLevel >= 0 )
            {
                FreeRTOS_debug_printf( ( "MSS: sending %d\n", pxSocket->u.xTCP.usCurMSS ) );
            }

            pxTCPHeader->ucOptdata[ 0 ] = tcpTCP_OPT_MSS;
            pxTCPHeader->ucOptdata[ 1 ] = tcpTCP_OPT_MSS_LEN;
            pxTCPHeader->ucOptdata[ 2 ] = ( uint8_t ) ( ( pxSocket->u.xTCP.usCurMSS ) >> 8 );
            pxTCPHeader->ucOptdata[ 3 ] = ( uint8_t ) ( ( pxSocket->u.xTCP.usCurMSS ) & 0xffU );
            uxOptionsLength = 4U;
            pxTCPHeader->ucTCPOffset = ( uint8_t ) ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 );
        }
        else
        {
            /* Nothing. */
        }

        return uxOptionsLength;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Called from prvTCPHandleState(). There is data to be sent. If
 *        ipconfigUSE_TCP_WIN is defined, and if only an ACK must be sent, it will be
 *        checked if it would better be postponed for efficiency.
 *
 * @param[in] pxSocket: The socket owning the TCP connection.
 * @param[in] ppxNetworkBuffer: Pointer to pointer to the network buffer.
 * @param[in] ulReceiveLength: The length of the received buffer.
 * @param[in] xByteCount: Length of the data to be sent.
 *
 * @return The number of bytes actually sent.
 */
    BaseType_t prvSendData( FreeRTOS_Socket_t * pxSocket,
                                   NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                                   uint32_t ulReceiveLength,
                                   BaseType_t xByteCount )
    {
        /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */
        const ProtocolHeaders_t * pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                              &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( *ppxNetworkBuffer ) ] ) );
        const TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
        const TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
        /* Find out what window size we may advertised. */
        int32_t lRxSpace;
        BaseType_t xSendLength = xByteCount;
        uint32_t ulRxBufferSpace;

        #if ( ipconfigUSE_TCP_WIN == 1 )
            #if ( ipconfigTCP_ACK_EARLIER_PACKET == 0 )
                const int32_t lMinLength = 0;
            #else
                int32_t lMinLength;
            #endif
        #endif

        /* Set the time-out field, so that we'll be called by the IP-task in case no
         * next message will be received. */
        ulRxBufferSpace = pxSocket->u.xTCP.ulHighestRxAllowed - pxTCPWindow->rx.ulCurrentSequenceNumber;
        lRxSpace = ( int32_t ) ulRxBufferSpace;

        #if ipconfigUSE_TCP_WIN == 1
            {
                #if ( ipconfigTCP_ACK_EARLIER_PACKET != 0 )
                    {
                        lMinLength = ( ( int32_t ) 2 ) * ( ( int32_t ) pxSocket->u.xTCP.usCurMSS );
                    }
                #endif /* ipconfigTCP_ACK_EARLIER_PACKET */

                /* In case we're receiving data continuously, we might postpone sending
                 * an ACK to gain performance. */
                /* lint e9007 is OK because 'uxIPHeaderSizeSocket()' has no side-effects. */
                if( ( ulReceiveLength > 0U ) &&                                                   /* Data was sent to this socket. */
                    ( lRxSpace >= lMinLength ) &&                                                 /* There is Rx space for more data. */
                    ( pxSocket->u.xTCP.bits.bFinSent == pdFALSE_UNSIGNED ) &&                     /* Not in a closure phase. */
                    ( xSendLength == uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER ) && /* No Tx data or options to be sent. */
                    ( pxSocket->u.xTCP.ucTCPState == ( uint8_t ) eESTABLISHED ) &&                /* Connection established. */
                    ( pxTCPHeader->ucTCPFlags == tcpTCP_FLAG_ACK ) )                              /* There are no other flags than an ACK. */
                {
                    if( pxSocket->u.xTCP.pxAckMessage != *ppxNetworkBuffer )
                    {
                        /* There was still a delayed in queue, delete it. */
                        if( pxSocket->u.xTCP.pxAckMessage != NULL )
                        {
                            vReleaseNetworkBufferAndDescriptor( pxSocket->u.xTCP.pxAckMessage );
                        }

                        pxSocket->u.xTCP.pxAckMessage = *ppxNetworkBuffer;
                    }

                    if( ( ulReceiveLength < ( uint32_t ) pxSocket->u.xTCP.usCurMSS ) ||            /* Received a small message. */
                        ( lRxSpace < ipNUMERIC_CAST( int32_t, 2U * pxSocket->u.xTCP.usCurMSS ) ) ) /* There are less than 2 x MSS space in the Rx buffer. */
                    {
                        pxSocket->u.xTCP.usTimeout = ( uint16_t ) tcpDELAYED_ACK_SHORT_DELAY_MS;
                    }
                    else
                    {
                        /* Normally a delayed ACK should wait 200 ms for a next incoming
                         * packet.  Only wait 20 ms here to gain performance.  A slow ACK
                         * for full-size message. */
                        pxSocket->u.xTCP.usTimeout = ( uint16_t ) ipMS_TO_MIN_TICKS( tcpDELAYED_ACK_LONGER_DELAY_MS );
                    }

                    if( ( xTCPWindowLoggingLevel > 1 ) && ( ipconfigTCP_MAY_LOG_PORT( pxSocket->usLocalPort ) ) )
                    {
                        FreeRTOS_debug_printf( ( "Send[%u->%u] del ACK %lu SEQ %lu (len %lu) tmout %u d %lu\n",
                                                 pxSocket->usLocalPort,
                                                 pxSocket->u.xTCP.usRemotePort,
                                                 pxTCPWindow->rx.ulCurrentSequenceNumber - pxTCPWindow->rx.ulFirstSequenceNumber,
                                                 pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber - pxTCPWindow->tx.ulFirstSequenceNumber,
                                                 xSendLength,
                                                 pxSocket->u.xTCP.usTimeout, lRxSpace ) );
                    }

                    *ppxNetworkBuffer = NULL;
                    xSendLength = 0;
                }
                else if( pxSocket->u.xTCP.pxAckMessage != NULL )
                {
                    /* As an ACK is not being delayed, remove any earlier delayed ACK
                     * message. */
                    if( pxSocket->u.xTCP.pxAckMessage != *ppxNetworkBuffer )
                    {
                        vReleaseNetworkBufferAndDescriptor( pxSocket->u.xTCP.pxAckMessage );
                    }

                    pxSocket->u.xTCP.pxAckMessage = NULL;
                }
                else
                {
                    /* The ack will not be postponed, and there was no stored ack ( in 'pxAckMessage' ). */
                }
            }
        #else /* if ipconfigUSE_TCP_WIN == 1 */
            {
                /* Remove compiler warnings. */
                ( void ) ulReceiveLength;
                ( void ) pxTCPHeader;
                ( void ) lRxSpace;
            }
        #endif /* ipconfigUSE_TCP_WIN */

        if( xSendLength != 0 )
        {
            if( ( xTCPWindowLoggingLevel > 1 ) && ( ipconfigTCP_MAY_LOG_PORT( pxSocket->usLocalPort ) ) )
            {
                FreeRTOS_debug_printf( ( "Send[%u->%u] imm ACK %lu SEQ %lu (len %lu)\n",
                                         pxSocket->usLocalPort,
                                         pxSocket->u.xTCP.usRemotePort,
                                         pxTCPWindow->rx.ulCurrentSequenceNumber - pxTCPWindow->rx.ulFirstSequenceNumber,
                                         pxTCPWindow->ulOurSequenceNumber - pxTCPWindow->tx.ulFirstSequenceNumber,
                                         xSendLength ) );
            }

            /* Set the parameter 'xReleaseAfterSend' to the value of
             * ipconfigZERO_COPY_TX_DRIVER. */
            prvTCPReturnPacket( pxSocket, *ppxNetworkBuffer, ( uint32_t ) xSendLength, ipconfigZERO_COPY_TX_DRIVER );
            #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
                {
                    /* The driver has taken ownership of the Network Buffer. */
                    *ppxNetworkBuffer = NULL;
                }
            #endif
        }

        return xSendLength;
    }
    /*-----------------------------------------------------------*/


/**
 * @brief prvStoreRxData(): called from prvTCPHandleState().
 *        The second thing is to do is check if the payload data may
 *        be accepted. If so, they will be added to the reception queue.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[in] pucRecvData: Pointer to received data.
 * @param[in] pxNetworkBuffer: The network buffer descriptor.
 * @param[in] ulReceiveLength: The length of the received data.
 *
 * @return 0 on success, -1 on failure of storing data.
 */
    BaseType_t prvStoreRxData( FreeRTOS_Socket_t * pxSocket,
                                      const uint8_t * pucRecvData,
                                      NetworkBufferDescriptor_t * pxNetworkBuffer,
                                      uint32_t ulReceiveLength )
    {
        /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */
        const ProtocolHeaders_t * pxProtocolHeaders = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( ProtocolHeaders_t,
                                                                                          &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer ) ] ) );
        const TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
        TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
        uint32_t ulSequenceNumber, ulSpace;
        int32_t lOffset, lStored;
        BaseType_t xResult = 0;

        ulSequenceNumber = FreeRTOS_ntohl( pxTCPHeader->ulSequenceNumber );

        if( ( ulReceiveLength > 0U ) && ( pxSocket->u.xTCP.ucTCPState >= ( uint8_t ) eSYN_RECEIVED ) )
        {
            /* See if way may accept the data contents and forward it to the socket
             * owner.
             *
             * If it can't be "accept"ed it may have to be stored and send a selective
             * ack (SACK) option to confirm it.  In that case, lTCPAddRxdata() will be
             * called later to store an out-of-order packet (in case lOffset is
             * negative). */
            if( pxSocket->u.xTCP.rxStream != NULL )
            {
                ulSpace = ( uint32_t ) uxStreamBufferGetSpace( pxSocket->u.xTCP.rxStream );
            }
            else
            {
                ulSpace = ( uint32_t ) pxSocket->u.xTCP.uxRxStreamSize;
            }

            lOffset = lTCPWindowRxCheck( pxTCPWindow, ulSequenceNumber, ulReceiveLength, ulSpace );

            if( lOffset >= 0 )
            {
                /* New data has arrived and may be made available to the user.  See
                 * if the head marker in rxStream may be advanced, only if lOffset == 0.
                 * In case the low-water mark is reached, bLowWater will be set
                 * "low-water" here stands for "little space". */
                lStored = lTCPAddRxdata( pxSocket, ( uint32_t ) lOffset, pucRecvData, ulReceiveLength );

                if( lStored != ( int32_t ) ulReceiveLength )
                {
                    FreeRTOS_debug_printf( ( "lTCPAddRxdata: stored %ld / %lu bytes? ?\n", lStored, ulReceiveLength ) );

                    /* Received data could not be stored.  The socket's flag
                     * bMallocError has been set.  The socket now has the status
                     * eCLOSE_WAIT and a RST packet will be sent back. */
                    ( void ) prvTCPSendReset( pxNetworkBuffer );
                    xResult = -1;
                }
            }

            /* After a missing packet has come in, higher packets may be passed to
             * the user. */
            #if ( ipconfigUSE_TCP_WIN == 1 )
                {
                    /* Now lTCPAddRxdata() will move the rxHead pointer forward
                     * so data becomes available to the user immediately
                     * In case the low-water mark is reached, bLowWater will be set. */
                    if( ( xResult == 0 ) && ( pxTCPWindow->ulUserDataLength > 0UL ) )
                    {
                        ( void ) lTCPAddRxdata( pxSocket, 0UL, NULL, pxTCPWindow->ulUserDataLength );
                        pxTCPWindow->ulUserDataLength = 0;
                    }
                }
            #endif /* ipconfigUSE_TCP_WIN */
        }
        else
        {
            pxTCPWindow->ucOptionLength = 0U;
        }

        return xResult;
    }
    /*-----------------------------------------------------------*/

#endif