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
 * @file FreeRTOS_TCP_Transmission.c
 * @brief Module which prepares the packet to be sent through
 * a socket for FreeRTOS+TCP.
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
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOSIPConfigDefaults.h"

#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_TCP_Reception.h"
#include "FreeRTOS_TCP_Transmission.h"
#include "FreeRTOS_TCP_State_Handling.h"
#include "FreeRTOS_TCP_Utils.h"

/* Just make sure the contents doesn't get compiled if TCP is not enabled. */
#if ipconfigUSE_TCP == 1

/*
 * Common code for sending a TCP protocol control packet (i.e. no options, no
 * payload, just flags).
 */
    static BaseType_t prvTCPSendSpecialPacketHelper( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                     uint8_t ucTCPFlags );

/*
 * Let ARP look-up the MAC-address of the peer and initialise the first SYN
 * packet.
 */
    static BaseType_t prvTCPPrepareConnect( FreeRTOS_Socket_t * pxSocket );

/*------------------------------------------------------------------------*/

/**
 * @brief Check if the outgoing connection is already prepared, if not
 *         call prvTCPPrepareConnect() to continue the preparation.
 * @param[in] pxSocket The socket that wants to connect.
 * @return Returns pdTRUE if the connection is prepared, i.e. the MAC-
 *         address of the peer is already known. */
    static BaseType_t prvTCPMakeSurePrepared( FreeRTOS_Socket_t * pxSocket )
    {
        BaseType_t xReturn = pdTRUE;

        if( pxSocket->u.xTCP.bits.bConnPrepared == pdFALSE_UNSIGNED )
        {
            if( prvTCPPrepareConnect( pxSocket ) != pdTRUE )
            {
                /* The preparation of a connection ( ARP resolution ) is not yet ready. */
                xReturn = pdFALSE;
            }
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief prvTCPSendPacket() will be called when the socket time-out has been reached.
 *
 * @param[in] pxSocket The socket owning the connection.
 *
 * @return Number of bytes to be sent.
 *
 * @note It is only called by xTCPSocketCheck().
 */
    int32_t prvTCPSendPacket( FreeRTOS_Socket_t * pxSocket )
    {
        int32_t lResult = 0;
        UBaseType_t uxOptionsLength, uxIntermediateResult = 0;
        NetworkBufferDescriptor_t * pxNetworkBuffer;

        if( pxSocket->u.xTCP.eTCPState != eCONNECT_SYN )
        {
            /* The connection is in a state other than SYN. */
            pxNetworkBuffer = NULL;

            /* prvTCPSendRepeated() will only create a network buffer if necessary,
             * i.e. when data must be sent to the peer. */
            lResult = prvTCPSendRepeated( pxSocket, &pxNetworkBuffer );

            if( pxNetworkBuffer != NULL )
            {
                vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
            }
        }
        else
        {
            if( pxSocket->u.xTCP.ucRepCount >= 3U )
            {
                /* The connection is in the SYN status. The packet will be repeated
                 * to most 3 times.  When there is no response, the socket get the
                 * status 'eCLOSE_WAIT'. */
                FreeRTOS_debug_printf( ( "Connect: giving up %xip:%u\n",
                                         ( unsigned ) pxSocket->u.xTCP.ulRemoteIP, /* IP address of remote machine. */
                                         pxSocket->u.xTCP.usRemotePort ) );        /* Port on remote machine. */
                vTCPStateChange( pxSocket, eCLOSE_WAIT );
            }
            else if( prvTCPMakeSurePrepared( pxSocket ) == pdTRUE )
            {
                ProtocolHeaders_t * pxProtocolHeaders;
                const UBaseType_t uxHeaderSize = ipSIZE_OF_IPv4_HEADER;

                /* Or else, if the connection has been prepared, or can be prepared
                 * now, proceed to send the packet with the SYN flag.
                 * prvTCPPrepareConnect() prepares 'xPacket' and returns pdTRUE if
                 * the Ethernet address of the peer or the gateway is found. */

                /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                /* coverity[misra_c_2012_rule_11_3_violation] */
                pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxSocket->u.xTCP.xPacket.u.ucLastPacket[ ipSIZE_OF_ETH_HEADER + uxHeaderSize ] ) );

                /* About to send a SYN packet.  Call prvSetSynAckOptions() to set
                 * the proper options: The size of MSS and whether SACK's are
                 * allowed. */
                uxOptionsLength = prvSetSynAckOptions( pxSocket, &( pxProtocolHeaders->xTCPHeader ) );

                /* Return the number of bytes to be sent. */
                uxIntermediateResult = uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength;
                lResult = ( int32_t ) uxIntermediateResult;

                /* Set the TCP offset field:  ipSIZE_OF_TCP_HEADER equals 20 and
                 * uxOptionsLength is always a multiple of 4.  The complete expression
                 * would be:
                 * ucTCPOffset = ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) / 4 ) << 4 */
                pxProtocolHeaders->xTCPHeader.ucTCPOffset = ( uint8_t ) ( ( ipSIZE_OF_TCP_HEADER + uxOptionsLength ) << 2 );

                /* Repeat Count is used for a connecting socket, to limit the number
                 * of tries. */
                pxSocket->u.xTCP.ucRepCount++;

                /* Send the SYN message to make a connection.  The messages is
                 * stored in the socket field 'xPacket'.  It will be wrapped in a
                 * pseudo network buffer descriptor before it will be sent. */
                prvTCPReturnPacket( pxSocket, NULL, ( uint32_t ) lResult, pdFALSE );
            }
            else
            {
                /* Nothing to do. */
            }
        }

        /* Return the total number of bytes sent. */
        return lResult;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief prvTCPSendRepeated will try to send a series of messages, as
 *        long as there is data to be sent and as long as the transmit
 *        window isn't full.
 *
 * @param[in] pxSocket The socket owning the connection.
 * @param[in,out] ppxNetworkBuffer Pointer to pointer to the network buffer.
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
 * @brief  Return (or send) a packet to the peer. The data is stored in pxBuffer,
 *         which may either point to a real network buffer or to a TCP socket field
 *         called 'xTCP.xPacket'. A temporary xNetworkBuffer will be used to pass
 *         the data to the NIC.
 *
 * @param[in] pxSocket The socket owning the connection.
 * @param[in] pxDescriptor The network buffer descriptor carrying the packet.
 * @param[in] ulLen Length of the packet being sent.
 * @param[in] xReleaseAfterSend pdTRUE if the ownership of the descriptor is
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
            if( pxNetworkBuffer != NULL ) /* LCOV_EXCL_BR_LINE the 2nd branch will never be reached */
        #endif
        {
            /* Map the ethernet buffer onto a TCPPacket_t struct for easy access to the fields. */

            /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
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
                if( ( ulSpace < pxSocket->u.xTCP.usMSS ) && ( ulFrontSpace >= pxSocket->u.xTCP.usMSS ) )
                {
                    ulSpace = pxSocket->u.xTCP.usMSS;
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

                if( ulWinSize > 0xfffcU )
                {
                    ulWinSize = 0xfffcU;
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

                        pxTCPPacket->xTCPHeader.ulSequenceNumber = pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber - 1U;
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
                            FreeRTOS_debug_printf( ( "Suppress FIN for %u + %u < %u\n",
                                                     ( unsigned ) ( pxTCPWindow->ulOurSequenceNumber - pxTCPWindow->tx.ulFirstSequenceNumber ),
                                                     ( unsigned ) ulDataLen,
                                                     ( unsigned ) ( pxTCPWindow->tx.ulFINSequenceNumber - pxTCPWindow->tx.ulFirstSequenceNumber ) ) );
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

            if( ( pxSocket == NULL ) || ( *ipLOCAL_IP_ADDRESS_POINTER == 0U ) )
            {
                /* When pxSocket is NULL, this function is called by prvTCPSendReset()
                 * and the IP-addresses must be swapped.
                 * Also swap the IP-addresses in case the IP-tack doesn't have an
                 * IP-address yet, i.e. when ( *ipLOCAL_IP_ADDRESS_POINTER == 0U ). */
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
            pxNetworkBuffer->xDataLength = ( size_t ) ulLen;
            pxNetworkBuffer->xDataLength += ipSIZE_OF_ETH_HEADER;

            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
                {
                    /* calculate the IP header checksum, in case the driver won't do that. */
                    pxIPHeader->usHeaderChecksum = 0x00U;
                    pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
                    pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );

                    /* calculate the TCP checksum for an outgoing packet. */
                    ( void ) usGenerateProtocolChecksum( ( uint8_t * ) pxTCPPacket, pxNetworkBuffer->xDataLength, pdTRUE );
                }
            #endif /* if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 ) */

            #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
                {
                    pxNetworkBuffer->pxNextBuffer = NULL;
                }
            #endif


            {
                MACAddress_t xMACAddress;
                uint32_t ulDestinationIPAddress = pxIPHeader->ulDestinationIPAddress;
                eARPLookupResult_t eResult;

                eResult = eARPGetCacheEntry( &ulDestinationIPAddress, &xMACAddress );

                if( eResult == eARPCacheHit )
                {
                    pvCopySource = &xMACAddress;
                }
                else
                {
                    pvCopySource = &pxEthernetHeader->xSourceAddress;
                }

                /* Fill in the destination MAC addresses. */
                pvCopyDest = &pxEthernetHeader->xDestinationAddress;
                ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( pxEthernetHeader->xDestinationAddress ) );
            }

            /*
             * Use helper variables for memcpy() to remain
             * compliant with MISRA Rule 21.15.  These should be
             * optimized away.
             */
            /* The source MAC addresses is fixed to 'ipLOCAL_MAC_ADDRESS'. */
            pvCopySource = ipLOCAL_MAC_ADDRESS;
            pvCopyDest = &pxEthernetHeader->xSourceAddress;
            ( void ) memcpy( pvCopyDest, pvCopySource, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

            #if ( ipconfigETHERNET_MINIMUM_PACKET_BYTES > 0 )
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
            #endif /* if( ipconfigETHERNET_MINIMUM_PACKET_BYTES > 0 ) */

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
 * @brief Create the TCP window for the given socket.
 *
 * @param[in] pxSocket The socket for which the window is being created.
 *
 * @note The SYN event is very important: the sequence numbers, which have a kind of
 *       random starting value, are being synchronized. The sliding window manager
 *       (in FreeRTOS_TCP_WIN.c) needs to know them, along with the Maximum Segment
 *       Size (MSS).
 */
    void prvTCPCreateWindow( FreeRTOS_Socket_t * pxSocket )
    {
        uint32_t ulRxWindowSize = ( uint32_t ) pxSocket->u.xTCP.uxRxWinSize;
        uint32_t ulTxWindowSize = ( uint32_t ) pxSocket->u.xTCP.uxTxWinSize;

        if( xTCPWindowLoggingLevel != 0 )
        {
            FreeRTOS_debug_printf( ( "Limits (using): TCP Win size %u Water %u <= %u <= %u\n",
                                     ( unsigned ) ( pxSocket->u.xTCP.uxRxWinSize * ipconfigTCP_MSS ),
                                     ( unsigned ) pxSocket->u.xTCP.uxLittleSpace,
                                     ( unsigned ) pxSocket->u.xTCP.uxEnoughSpace,
                                     ( unsigned ) pxSocket->u.xTCP.uxRxStreamSize ) );
        }

        vTCPWindowCreate(
            &pxSocket->u.xTCP.xTCPWindow,
            ulRxWindowSize * ipconfigTCP_MSS,
            ulTxWindowSize * ipconfigTCP_MSS,
            pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber,
            pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber,
            ( uint32_t ) pxSocket->u.xTCP.usMSS );
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Let ARP look-up the MAC-address of the peer and initialise the first SYN
 *        packet.
 *
 * @param[in] pxSocket The socket owning the TCP connection. The first packet shall
 *               be created in this socket.
 *
 * @return pdTRUE: if the packet was successfully created and the first SYN can be sent.
 *         Else pdFALSE.
 *
 * @note Connecting sockets have a special state: eCONNECT_SYN. In this phase,
 *       the Ethernet address of the target will be found using ARP. In case the
 *       target IP address is not within the netmask, the hardware address of the
 *       gateway will be used.
 */
    static BaseType_t prvTCPPrepareConnect( FreeRTOS_Socket_t * pxSocket )
    {
        TCPPacket_t * pxTCPPacket;
        IPHeader_t * pxIPHeader;
        eARPLookupResult_t eReturned;
        uint32_t ulRemoteIP;
        MACAddress_t xEthAddress;
        BaseType_t xReturn = pdTRUE;
        uint32_t ulInitialSequenceNumber = 0;

        #if ( ipconfigHAS_PRINTF != 0 )
            {
                /* Only necessary for nicer logging. */
                ( void ) memset( xEthAddress.ucBytes, 0, sizeof( xEthAddress.ucBytes ) );
            }
        #endif /* ipconfigHAS_PRINTF != 0 */

        ulRemoteIP = FreeRTOS_htonl( pxSocket->u.xTCP.ulRemoteIP );

        /* Determine the ARP cache status for the requested IP address. */
        eReturned = eARPGetCacheEntry( &( ulRemoteIP ), &( xEthAddress ) );

        switch( eReturned )
        {
            case eARPCacheHit:    /* An ARP table lookup found a valid entry. */
                break;            /* We can now prepare the SYN packet. */

            case eARPCacheMiss:   /* An ARP table lookup did not find a valid entry. */
            case eCantSendPacket: /* There is no IP address, or an ARP is still in progress. */
            default:
                /* Count the number of times it could not find the ARP address. */
                pxSocket->u.xTCP.ucRepCount++;

                FreeRTOS_debug_printf( ( "ARP for %xip (using %xip): rc=%d %02X:%02X:%02X %02X:%02X:%02X\n",
                                         ( unsigned ) pxSocket->u.xTCP.ulRemoteIP,
                                         ( unsigned ) FreeRTOS_htonl( ulRemoteIP ),
                                         eReturned,
                                         xEthAddress.ucBytes[ 0 ],
                                         xEthAddress.ucBytes[ 1 ],
                                         xEthAddress.ucBytes[ 2 ],
                                         xEthAddress.ucBytes[ 3 ],
                                         xEthAddress.ucBytes[ 4 ],
                                         xEthAddress.ucBytes[ 5 ] ) );

                /* And issue a (new) ARP request */
                FreeRTOS_OutputARPRequest( ulRemoteIP );
                xReturn = pdFALSE;
                break;
        }

        if( xReturn != pdFALSE )
        {
            /* Get a difficult-to-predict initial sequence number for this 4-tuple. */
            ulInitialSequenceNumber = ulApplicationGetNextSequenceNumber( *ipLOCAL_IP_ADDRESS_POINTER,
                                                                          pxSocket->usLocalPort,
                                                                          pxSocket->u.xTCP.ulRemoteIP,
                                                                          pxSocket->u.xTCP.usRemotePort );

            /* Check for a random number generation error. */
            if( ulInitialSequenceNumber == 0U )
            {
                xReturn = pdFALSE;
            }
        }

        if( xReturn != pdFALSE )
        {
            uint16_t usLength;

            /* The MAC-address of the peer (or gateway) has been found,
             * now prepare the initial TCP packet and some fields in the socket. Map
             * the buffer onto the TCPPacket_t struct to easily access it's field. */

            /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            pxTCPPacket = ( ( TCPPacket_t * ) pxSocket->u.xTCP.xPacket.u.ucLastPacket );
            pxIPHeader = &pxTCPPacket->xIPHeader;

            /* reset the retry counter to zero. */
            pxSocket->u.xTCP.ucRepCount = 0U;

            /* And remember that the connect/SYN data are prepared. */
            pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;

            /* Now that the Ethernet address is known, the initial packet can be
             * prepared. */
            ( void ) memset( pxSocket->u.xTCP.xPacket.u.ucLastPacket, 0, sizeof( pxSocket->u.xTCP.xPacket.u.ucLastPacket ) );

            /* Write the Ethernet address in Source, because it will be swapped by
             * prvTCPReturnPacket(). */
            ( void ) memcpy( ( void * ) ( &pxTCPPacket->xEthernetHeader.xSourceAddress ), ( const void * ) ( &xEthAddress ), sizeof( xEthAddress ) );

            /* 'ipIPv4_FRAME_TYPE' is already in network-byte-order. */
            pxTCPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

            pxIPHeader->ucVersionHeaderLength = 0x45U;
            usLength = ( uint16_t ) ( sizeof( TCPPacket_t ) - sizeof( pxTCPPacket->xEthernetHeader ) );
            pxIPHeader->usLength = FreeRTOS_htons( usLength );
            pxIPHeader->ucTimeToLive = ( uint8_t ) ipconfigTCP_TIME_TO_LIVE;

            pxIPHeader->ucProtocol = ( uint8_t ) ipPROTOCOL_TCP;

            /* Addresses and ports will be stored swapped because prvTCPReturnPacket
             * will swap them back while replying. */
            pxIPHeader->ulDestinationIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
            pxIPHeader->ulSourceIPAddress = FreeRTOS_htonl( pxSocket->u.xTCP.ulRemoteIP );

            pxTCPPacket->xTCPHeader.usSourcePort = FreeRTOS_htons( pxSocket->u.xTCP.usRemotePort );
            pxTCPPacket->xTCPHeader.usDestinationPort = FreeRTOS_htons( pxSocket->usLocalPort );

            /* We are actively connecting, so the peer's Initial Sequence Number (ISN)
             * isn't known yet. */
            pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber = 0U;

            /* Start with ISN (Initial Sequence Number). */
            pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = ulInitialSequenceNumber;

            /* The TCP header size is 20 bytes, divided by 4 equals 5, which is put in
             * the high nibble of the TCP offset field. */
            pxTCPPacket->xTCPHeader.ucTCPOffset = 0x50U;

            /* Only set the SYN flag. */
            pxTCPPacket->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;

            /* Set the value of usMSS for this socket. */
            prvSocketSetMSS( pxSocket );

            /* The initial sequence numbers at our side are known.  Later
             * vTCPWindowInit() will be called to fill in the peer's sequence numbers, but
             * first wait for a SYN+ACK reply. */
            prvTCPCreateWindow( pxSocket );
        }

        return xReturn;
    }
    /*-----------------------------------------------------------*/

    #if ( ipconfigUSE_TCP_WIN != 0 )

/**
 * @brief Get the window scaling factor for the TCP connection.
 *
 * @param[in] pxSocket The socket owning the TCP connection.
 *
 * @return The scaling factor.
 */
        static uint8_t prvWinScaleFactor( const FreeRTOS_Socket_t * pxSocket )
        {
            size_t uxWinSize;
            uint8_t ucFactor;


            /* 'xTCP.uxRxWinSize' is the size of the reception window in units of MSS. */
            uxWinSize = pxSocket->u.xTCP.uxRxWinSize * ( size_t ) pxSocket->u.xTCP.usMSS;
            ucFactor = 0U;

            while( uxWinSize > 0xffffU )
            {
                /* Divide by two and increase the binary factor by 1. */
                uxWinSize >>= 1;
                ucFactor++;
            }

            FreeRTOS_debug_printf( ( "prvWinScaleFactor: uxRxWinSize %u MSS %u Factor %u\n",
                                     ( unsigned ) pxSocket->u.xTCP.uxRxWinSize,
                                     pxSocket->u.xTCP.usMSS,
                                     ucFactor ) );

            return ucFactor;
        }

    #endif /* if ( ipconfigUSE_TCP_WIN != 0 ) */
    /*-----------------------------------------------------------*/

/**
 * @brief When opening a TCP connection, while SYN's are being sent, the  parties may
 *        communicate what MSS (Maximum Segment Size) they intend to use, whether Selective
 *        ACK's ( SACK ) are supported, and the size of the reception window ( WSOPT ).
 *
 * @param[in] pxSocket The socket being used for communication. It is used to set
 *                      the MSS.
 * @param[in,out] pxTCPHeader The TCP packet header being used in the SYN transmission.
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
        uint16_t usMSS = pxSocket->u.xTCP.usMSS;
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

/**
 * @brief Check if the size of a network buffer is big enough to hold the outgoing message.
 *        Allocate a new bigger network buffer when necessary.
 *
 * @param[in] pxSocket Socket whose buffer is being resized.
 * @param[in] pxNetworkBuffer The network buffer whose size is being increased.
 * @param[in] lDataLen Length of the data to be put in the buffer.
 * @param[in] uxOptionsLength Length of options.
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
            uxNeeded = ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength;
            uxNeeded += ( size_t ) lDataLen;

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
            configASSERT( pxNetworkBuffer != NULL ); /* LCOV_EXCL_BR_LINE this branch will not be covered, since it would never be NULL. to tell lint: when xResize is false, pxNetworkBuffer is not NULL. */
            pxReturn = pxNetworkBuffer;

            pxNetworkBuffer->xDataLength = ( size_t ) ( ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) + ipSIZE_OF_TCP_HEADER + uxOptionsLength ) + ( size_t ) lDataLen;
        }

        return pxReturn;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Prepare an outgoing message, in case anything has to be sent.
 *
 * @param[in] pxSocket The socket owning the connection.
 * @param[in,out] ppxNetworkBuffer Pointer to the pointer to the network buffer.
 * @param[in] uxOptionsLength The length of the TCP options.
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

        /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] ) );
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
            if( pxSocket->u.xTCP.usMSS > 1U )
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

                    /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                    /* coverity[misra_c_2012_rule_11_3_violation] */
                    pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderSizeSocket( pxSocket ) ] ) );

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
                    if( pxSocket->u.xTCP.bits.bCloseRequested != pdFALSE_UNSIGNED )
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

        if( ( lDataLen >= 0 ) && ( pxSocket->u.xTCP.eTCPState == eESTABLISHED ) )
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
                        FreeRTOS_debug_printf( ( "keep-alive: giving up %xip:%u\n",
                                                 ( unsigned ) pxSocket->u.xTCP.ulRemoteIP, /* IP address of remote machine. */
                                                 pxSocket->u.xTCP.usRemotePort ) );        /* Port on remote machine. */
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

                        if( pxSocket->u.xTCP.ucKeepRepCount != 0U )
                        {
                            xMax = 3U * configTICK_RATE_HZ;
                        }

                        if( xAge > xMax )
                        {
                            pxSocket->u.xTCP.xLastAliveTime = xTaskGetTickCount();

                            if( xTCPWindowLoggingLevel != 0 )
                            {
                                FreeRTOS_debug_printf( ( "keep-alive: %xip:%u count %u\n",
                                                         ( unsigned ) pxSocket->u.xTCP.ulRemoteIP,
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

        if( lDataLen >= 0 )
        {
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
        }

        return lDataLen;
    }
    /*-----------------------------------------------------------*/


/**
 * @brief The API FreeRTOS_send() adds data to the TX stream. Add
 *        this data to the windowing system to it can be transmitted.
 *
 * @param[in] pxSocket The socket owning the connection.
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
 * @brief Set the TCP options (if any) for the outgoing packet.
 *
 * @param[in] pxSocket The socket owning the connection.
 * @param[in] pxNetworkBuffer The network buffer holding the packet.
 *
 * @return Length of the TCP options after they are set.
 */
    UBaseType_t prvSetOptions( FreeRTOS_Socket_t * pxSocket,
                               const NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        /* Map the ethernet buffer onto the ProtocolHeader_t struct for easy access to the fields. */

        /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
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
                    FreeRTOS_debug_printf( ( "SACK[%u,%u]: optlen %u sending %u - %u\n",
                                             pxSocket->usLocalPort,
                                             pxSocket->u.xTCP.usRemotePort,
                                             ( unsigned ) uxOptionsLength,
                                             ( unsigned ) ( FreeRTOS_ntohl( pxTCPWindow->ulOptionsData[ 1 ] ) - pxSocket->u.xTCP.xTCPWindow.rx.ulFirstSequenceNumber ),
                                             ( unsigned ) ( FreeRTOS_ntohl( pxTCPWindow->ulOptionsData[ 2 ] ) - pxSocket->u.xTCP.xTCPWindow.rx.ulFirstSequenceNumber ) ) );
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

        if( ( pxSocket->u.xTCP.eTCPState >= eESTABLISHED ) && ( pxSocket->u.xTCP.bits.bMssChange != pdFALSE_UNSIGNED ) )
        {
            /* TCP options must be sent because the MSS has changed. */
            pxSocket->u.xTCP.bits.bMssChange = pdFALSE_UNSIGNED;

            if( xTCPWindowLoggingLevel >= 0 )
            {
                FreeRTOS_debug_printf( ( "MSS: sending %u\n", pxSocket->u.xTCP.usMSS ) );
            }

            pxTCPHeader->ucOptdata[ 0 ] = tcpTCP_OPT_MSS;
            pxTCPHeader->ucOptdata[ 1 ] = tcpTCP_OPT_MSS_LEN;
            pxTCPHeader->ucOptdata[ 2 ] = ( uint8_t ) ( ( pxSocket->u.xTCP.usMSS ) >> 8 );
            pxTCPHeader->ucOptdata[ 3 ] = ( uint8_t ) ( ( pxSocket->u.xTCP.usMSS ) & 0xffU );
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
 * @param[in] pxSocket The socket owning the TCP connection.
 * @param[in] ppxNetworkBuffer Pointer to pointer to the network buffer.
 * @param[in] ulReceiveLength The length of the received buffer.
 * @param[in] xByteCount Length of the data to be sent.
 *
 * @return The number of bytes actually sent.
 */
    BaseType_t prvSendData( FreeRTOS_Socket_t * pxSocket,
                            NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                            uint32_t ulReceiveLength,
                            BaseType_t xByteCount )
    {
        /* Map the buffer onto the ProtocolHeader_t struct for easy access to the fields. */

        /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        const ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                                        &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + xIPHeaderSize( *ppxNetworkBuffer ) ] ) );
        const TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
        const TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
        /* Find out what window size we may advertised. */
        int32_t lRxSpace;
        BaseType_t xSendLength = xByteCount;
        uint32_t ulRxBufferSpace;
        /* Two steps to please MISRA. */
        size_t uxSize = ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER;
        BaseType_t xSizeWithoutData = ( BaseType_t ) uxSize;

        #if ( ipconfigUSE_TCP_WIN == 1 )
            int32_t lMinLength;
        #endif

        /* Set the time-out field, so that we'll be called by the IP-task in case no
         * next message will be received. */
        ulRxBufferSpace = pxSocket->u.xTCP.ulHighestRxAllowed - pxTCPWindow->rx.ulCurrentSequenceNumber;
        lRxSpace = ( int32_t ) ulRxBufferSpace;

        #if ipconfigUSE_TCP_WIN == 1
            {
                /* An ACK may be delayed if the peer has space for at least 2 x MSS. */
                lMinLength = ( ( int32_t ) 2 ) * ( ( int32_t ) pxSocket->u.xTCP.usMSS );

                /* In case we're receiving data continuously, we might postpone sending
                 * an ACK to gain performance. */
                /* lint e9007 is OK because 'uxIPHeaderSizeSocket()' has no side-effects. */
                if( ( ulReceiveLength > 0U ) &&                               /* Data was sent to this socket. */
                    ( lRxSpace >= lMinLength ) &&                             /* There is Rx space for more data. */
                    ( pxSocket->u.xTCP.bits.bFinSent == pdFALSE_UNSIGNED ) && /* Not in a closure phase. */
                    ( xSendLength == xSizeWithoutData ) &&                    /* No Tx data or options to be sent. */
                    ( pxSocket->u.xTCP.eTCPState == eESTABLISHED ) &&         /* Connection established. */
                    ( pxTCPHeader->ucTCPFlags == tcpTCP_FLAG_ACK ) )          /* There are no other flags than an ACK. */
                {
                    uint32_t ulCurMSS = ( uint32_t ) pxSocket->u.xTCP.usMSS;

                    if( pxSocket->u.xTCP.pxAckMessage != *ppxNetworkBuffer )
                    {
                        /* There was still a delayed in queue, delete it. */
                        if( pxSocket->u.xTCP.pxAckMessage != NULL )
                        {
                            vReleaseNetworkBufferAndDescriptor( pxSocket->u.xTCP.pxAckMessage );
                        }

                        pxSocket->u.xTCP.pxAckMessage = *ppxNetworkBuffer;
                    }

                    if( ulReceiveLength < ulCurMSS ) /* Received a small message. */
                    {
                        pxSocket->u.xTCP.usTimeout = ( uint16_t ) tcpDELAYED_ACK_SHORT_DELAY_MS;
                    }
                    else
                    {
                        /* Normally a delayed ACK should wait 200 ms for a next incoming
                         * packet.  Only wait 20 ms here to gain performance.  A slow ACK
                         * for full-size message. */
                        pxSocket->u.xTCP.usTimeout = ( uint16_t ) pdMS_TO_TICKS( tcpDELAYED_ACK_LONGER_DELAY_MS );

                        if( pxSocket->u.xTCP.usTimeout < 1U ) /* LCOV_EXCL_BR_LINE, the second branch will never be hit */
                        {
                            pxSocket->u.xTCP.usTimeout = 1U;  /* LCOV_EXCL_LINE, this line will not be reached */
                        }
                    }

                    if( ( xTCPWindowLoggingLevel > 1 ) && ( ipconfigTCP_MAY_LOG_PORT( pxSocket->usLocalPort ) ) )
                    {
                        FreeRTOS_debug_printf( ( "Send[%u->%u] del ACK %u SEQ %u (len %u) tmout %u d %d\n",
                                                 pxSocket->usLocalPort,
                                                 pxSocket->u.xTCP.usRemotePort,
                                                 ( unsigned ) ( pxTCPWindow->rx.ulCurrentSequenceNumber - pxTCPWindow->rx.ulFirstSequenceNumber ),
                                                 ( unsigned ) ( pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber - pxTCPWindow->tx.ulFirstSequenceNumber ),
                                                 ( unsigned ) xSendLength,
                                                 pxSocket->u.xTCP.usTimeout,
                                                 ( int ) lRxSpace ) );
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
                FreeRTOS_debug_printf( ( "Send[%u->%u] imm ACK %u SEQ %u (len %u)\n",
                                         pxSocket->usLocalPort,
                                         pxSocket->u.xTCP.usRemotePort,
                                         ( unsigned ) ( pxTCPWindow->rx.ulCurrentSequenceNumber - pxTCPWindow->rx.ulFirstSequenceNumber ),
                                         ( unsigned ) ( pxTCPWindow->ulOurSequenceNumber - pxTCPWindow->tx.ulFirstSequenceNumber ),
                                         ( unsigned ) xSendLength ) );
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
 * @brief Common code for sending a TCP protocol control packet (i.e. no options, no
 *        payload, just flags).
 *
 * @param[in] pxNetworkBuffer The network buffer received from the peer.
 * @param[in] ucTCPFlags The flags to determine what kind of packet this is.
 *
 * @return pdFAIL always indicating that the packet was not consumed.
 */
    static BaseType_t prvTCPSendSpecialPacketHelper( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                     uint8_t ucTCPFlags )
    {
        #if ( ipconfigIGNORE_UNKNOWN_PACKETS == 1 )
            /* Configured to ignore unknown packets just suppress a compiler warning. */
            ( void ) pxNetworkBuffer;
            ( void ) ucTCPFlags;
        #else
            {
                /* Map the ethernet buffer onto the TCPPacket_t struct for easy access to the fields. */

                /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                /* coverity[misra_c_2012_rule_11_3_violation] */
                TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
                const uint32_t ulSendLength =
                    ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER ); /* Plus 0 options. */
                uint8_t ucFlagsReceived = pxTCPPacket->xTCPHeader.ucTCPFlags;
                pxTCPPacket->xTCPHeader.ucTCPFlags = ucTCPFlags;
                pxTCPPacket->xTCPHeader.ucTCPOffset = ( ipSIZE_OF_TCP_HEADER ) << 2;

                if( ( ucFlagsReceived & tcpTCP_FLAG_SYN ) != 0U )
                {
                    /* A synchronize packet is received. It counts as 1 pseudo byte of data,
                     * so increase the variable with 1. Before sending a reply, the values of
                     * 'ulSequenceNumber' and 'ulAckNr' will be swapped. */
                    uint32_t ulSequenceNumber = FreeRTOS_ntohl( pxTCPPacket->xTCPHeader.ulSequenceNumber );
                    ulSequenceNumber++;
                    pxTCPPacket->xTCPHeader.ulSequenceNumber = FreeRTOS_htonl( ulSequenceNumber );
                }

                prvTCPReturnPacket( NULL, pxNetworkBuffer, ulSendLength, pdFALSE );
            }
        #endif /* !ipconfigIGNORE_UNKNOWN_PACKETS */

        /* The packet was not consumed. */
        return pdFAIL;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief A "challenge ACK" is as per https://tools.ietf.org/html/rfc5961#section-3.2,
 *        case #3. In summary, an RST was received with a sequence number that is
 *        unexpected but still within the window.
 *
 * @param[in] pxNetworkBuffer The network buffer descriptor with the packet.
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
 * @param[in] pxNetworkBuffer The network buffer descriptor with the packet.
 *
 * @return Returns the value back from #prvTCPSendSpecialPacketHelper.
 */
    BaseType_t prvTCPSendReset( NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        return prvTCPSendSpecialPacketHelper( pxNetworkBuffer,
                                              ( uint8_t ) tcpTCP_FLAG_ACK | ( uint8_t ) tcpTCP_FLAG_RST );
    }
    /*-----------------------------------------------------------*/

#endif /* ipconfigUSE_TCP == 1 */
