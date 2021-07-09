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
#include "FreeRTOS_TCP_IP_TimerWork.h"


/**
 * @file FreeRTOS_TCP_IP_TimerWork.c
 *
 * The functions in this module are called when the socket timer expires.
 * It will check if there are pending (re)transmissions, or protection
 * timers going off.
 */

/* Just make sure the contents doesn't get compiled if TCP is not enabled. */
#if ipconfigUSE_TCP == 1

/**
 * @brief Calculate after how much time this socket needs to be checked again.
 *
 * @param[in] pxSocket: The socket to be checked.
 *
 * @return The number of clock ticks before the timer expires.
 */
    TickType_t prvTCPNextTimeout( FreeRTOS_Socket_t * pxSocket )
    {
        TickType_t ulDelayMs = ( TickType_t ) tcpMAXIMUM_TCP_WAKEUP_TIME_MS;

        if( pxSocket->u.xTCP.ucTCPState == ( uint8_t ) eCONNECT_SYN )
        {
            /* The socket is actively connecting to a peer. */
            if( pxSocket->u.xTCP.bits.bConnPrepared != pdFALSE_UNSIGNED )
            {
                /* Ethernet address has been found, use progressive timeout for
                 * active connect(). */
                if( pxSocket->u.xTCP.ucRepCount < 3U )
                {
                    ulDelayMs = ( 3000UL << ( pxSocket->u.xTCP.ucRepCount - 1U ) );
                }
                else
                {
                    ulDelayMs = 11000UL;
                }
            }
            else
            {
                /* Still in the ARP phase: check every half second. */
                ulDelayMs = 500UL;
            }

            FreeRTOS_debug_printf( ( "Connect[%lxip:%u]: next timeout %u: %lu ms\n",
                                     pxSocket->u.xTCP.ulRemoteIP, pxSocket->u.xTCP.usRemotePort,
                                     pxSocket->u.xTCP.ucRepCount, ulDelayMs ) );
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
                    ulDelayMs = 1UL;
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

            pxSocket->u.xTCP.usTimeout = ( uint16_t ) ipMS_TO_MIN_TICKS( ulDelayMs );
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

    #if ( ipconfigTCP_HANG_PROTECTION == 1 )

/**
 * @brief Some of the TCP states may only last a certain amount of time.
 *        This function checks if the socket is 'hanging', i.e. staying
 *        too long in the same state.
 *
 * @param[in] The socket to be checked.
 *
 * @return pdFALSE if no checks are needed, pdTRUE if checks were done, or negative
 *         in case the socket has reached a critical time-out. The socket will go to
 *         the eCLOSE_WAIT state.
 */
        BaseType_t prvTCPStatusAgeCheck( FreeRTOS_Socket_t * pxSocket )
        {
            BaseType_t xResult;
            eIPTCPState_t eState = ipNUMERIC_CAST( eIPTCPState_t, pxSocket->u.xTCP.ucTCPState );

            switch( eState )
            {
                case eESTABLISHED:

                    /* If the 'ipconfigTCP_KEEP_ALIVE' option is enabled, sockets in
                     *  state ESTABLISHED can be protected using keep-alive messages. */
                    xResult = pdFALSE;
                    break;

                case eCLOSED:
                case eTCP_LISTEN:
                case eCLOSE_WAIT:
                    /* These 3 states may last for ever, up to the owner. */
                    xResult = pdFALSE;
                    break;

                case eCONNECT_SYN:
                case eSYN_FIRST:
                case eSYN_RECEIVED:
                case eFIN_WAIT_1:
                case eFIN_WAIT_2:
                case eCLOSING:
                case eLAST_ACK:
                case eTIME_WAIT:
                default:

                    /* All other (non-connected) states will get anti-hanging
                     * protection. */
                    xResult = pdTRUE;
                    break;
            }

            if( xResult != pdFALSE )
            {
                /* How much time has past since the last active moment which is
                 * defined as A) a state change or B) a packet has arrived. */
                TickType_t xAge = xTaskGetTickCount() - pxSocket->u.xTCP.xLastActTime;

                /* ipconfigTCP_HANG_PROTECTION_TIME is in units of seconds. */
                if( xAge > ( ( TickType_t ) ipconfigTCP_HANG_PROTECTION_TIME * ( TickType_t ) configTICK_RATE_HZ ) )
                {
                    #if ( ipconfigHAS_DEBUG_PRINTF == 1 )
                        {
                            FreeRTOS_debug_printf( ( "Inactive socket closed: port %u rem %lxip:%u status %s\n",
                                                     pxSocket->usLocalPort,
                                                     pxSocket->u.xTCP.ulRemoteIP,
                                                     pxSocket->u.xTCP.usRemotePort,
                                                     FreeRTOS_GetTCPStateName( ( UBaseType_t ) pxSocket->u.xTCP.ucTCPState ) ) );
                        }
                    #endif /* ipconfigHAS_DEBUG_PRINTF */

                    /* Move to eCLOSE_WAIT, user may close the socket. */
                    vTCPStateChange( pxSocket, eCLOSE_WAIT );

                    /* When 'bPassQueued' true, this socket is an orphan until it
                     * gets connected. */
                    if( pxSocket->u.xTCP.bits.bPassQueued != pdFALSE_UNSIGNED )
                    {
                        /* vTCPStateChange() has called vSocketCloseNextTime()
                         * in case the socket is not yet owned by the application.
                         * Return a negative value to inform the caller that
                         * the socket will be closed in the next cycle. */
                        xResult = -1;
                    }
                }
            }

            return xResult;
        }
        /*-----------------------------------------------------------*/

    #endif /* if ( ipconfigTCP_HANG_PROTECTION == 1 ) */

/**
 * @brief prvTCPSendPacket() will be called when the socket time-out has been reached.
 *
 * @param[in] pxSocket: The socket owning the connection.
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

        if( pxSocket->u.xTCP.ucTCPState != ( uint8_t ) eCONNECT_SYN )
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
                FreeRTOS_debug_printf( ( "Connect: giving up %lxip:%u\n",
                                         pxSocket->u.xTCP.ulRemoteIP,       /* IP address of remote machine. */
                                         pxSocket->u.xTCP.usRemotePort ) ); /* Port on remote machine. */
                vTCPStateChange( pxSocket, eCLOSE_WAIT );
            }
            else if( ( pxSocket->u.xTCP.bits.bConnPrepared != pdFALSE_UNSIGNED ) || ( prvTCPPrepareConnect( pxSocket ) == pdTRUE ) )
            {
                ProtocolHeaders_t * pxProtocolHeaders;
                const UBaseType_t uxHeaderSize = ipSIZE_OF_IPv4_HEADER;

                /* Or else, if the connection has been prepared, or can be prepared
                 * now, proceed to send the packet with the SYN flag.
                 * prvTCPPrepareConnect() prepares 'xPacket' and returns pdTRUE if
                 * the Ethernet address of the peer or the gateway is found. */
                pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t, &( pxSocket->u.xTCP.xPacket.u.ucLastPacket[ ipSIZE_OF_ETH_HEADER + uxHeaderSize ] ) );

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
 * @brief Let ARP look-up the MAC-address of the peer and initialise the first SYN
 *        packet.
 *
 * @param[in] pxSocket: The socket owning the TCP connection. The first packet shall
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
    BaseType_t prvTCPPrepareConnect( FreeRTOS_Socket_t * pxSocket )
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

                FreeRTOS_debug_printf( ( "ARP for %lxip (using %lxip): rc=%d %02X:%02X:%02X %02X:%02X:%02X\n",
                                         pxSocket->u.xTCP.ulRemoteIP,
                                         FreeRTOS_htonl( ulRemoteIP ),
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
            if( ulInitialSequenceNumber == 0UL )
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
            pxTCPPacket = ipCAST_PTR_TO_TYPE_PTR( TCPPacket_t, pxSocket->u.xTCP.xPacket.u.ucLastPacket );
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
            pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber = 0UL;

            /* Start with ISN (Initial Sequence Number). */
            pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = ulInitialSequenceNumber;

            /* The TCP header size is 20 bytes, divided by 4 equals 5, which is put in
             * the high nibble of the TCP offset field. */
            pxTCPPacket->xTCPHeader.ucTCPOffset = 0x50U;

            /* Only set the SYN flag. */
            pxTCPPacket->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;

            /* Set the values of usInitMSS / usCurMSS for this socket. */
            prvSocketSetMSS( pxSocket );

            /* The initial sequence numbers at our side are known.  Later
             * vTCPWindowInit() will be called to fill in the peer's sequence numbers, but
             * first wait for a SYN+ACK reply. */
            prvTCPCreateWindow( pxSocket );
        }

        return xReturn;
    }
    /*-----------------------------------------------------------*/

#endif /* if ipconfigUSE_TCP == 1 */
