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
 * @file FreeRTOS_UDP_IPv6.c
 * @brief This file has the source code for the UDP-IP functionality of the FreeRTOS+TCP
 *        network stack.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"
#include "event_groups.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DHCP.h"
#include "FreeRTOS_ND.h"
#include "FreeRTOS_IP_Utils.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"

#if ( ipconfigUSE_DNS == 1 )
    #include "FreeRTOS_DNS.h"
#endif

/* *INDENT-OFF* */
    #if( ipconfigUSE_IPv6 != 0 )
/* *INDENT-ON* */


/** @brief The expected IP version and header length coded into the IP header itself. */
#define ipIP_VERSION_AND_HEADER_LENGTH_BYTE    ( ( uint8_t ) 0x45 )

/*-----------------------------------------------------------*/

/* _HT_ this is a temporary aid while testing. In case an end-0point is not found,
 * this function will return the first end-point of the required type,
 * either 'ipTYPE_IPv4' or 'ipTYPE_IPv6' */
extern NetworkEndPoint_t * pxGetEndpoint( BaseType_t xIPType );

/**
 * @brief Get the first end point of the type (IPv4/IPv6) from the list
 *        the list of end points.
 *
 * @param[in] xIPType: IT type (ipTYPE_IPv6/ipTYPE_IPv4)
 *
 * @returns Pointer to the first end point of the given IP type from the
 *          list of end points.
 */
NetworkEndPoint_t * pxGetEndpoint( BaseType_t xIPType )
{
    NetworkEndPoint_t * pxEndPoint;

    for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
         pxEndPoint != NULL;
         pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
    {
        if( xIPType == ipTYPE_IPv6 )
        {
            if( pxEndPoint->bits.bIPv6 != 0U )
            {
                break;
            }
        }
        else
        {
            if( pxEndPoint->bits.bIPv6 == 0U )
            {
                break;
            }
        }
    }

    return pxEndPoint;
}

/**
 * @brief This function is called in case the IP-address was not found,
 *        i.e. in the cache 'eARPCacheMiss' was returned.
 *        Either an ARP request or a Neighbour solicitation will be emitted.
 *
 * @param[in] pxNetworkBuffer : The network buffer carrying the UDP or ICMP packet.
 *
 * @param[out] pxLostBuffer : The pointer will be set to true in case the network packet got released
 *                            ( the ownership was taken ).
 */
static eARPLookupResult_t prvStartLookup( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                          BaseType_t * pxLostBuffer )
{
    eARPLookupResult_t eReturned = eARPCacheMiss;
    uint32_t ulIPAddress;


    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
    {
        FreeRTOS_printf( ( "Looking up %pip with%s end-point\n",
                           pxNetworkBuffer->xIPAddress.xIP_IPv6.ucBytes,
                           ( pxNetworkBuffer->pxEndPoint != NULL ) ? "" : "out" ) );

        if( pxNetworkBuffer->pxEndPoint == NULL )
        {
            pxNetworkBuffer->pxEndPoint = pxGetEndpoint( ipTYPE_IPv6 );
            FreeRTOS_printf( ( "prvStartLookup: Got an end-point: %s\n", pxNetworkBuffer->pxEndPoint ? "yes" : "no" ) );
        }

        if( pxNetworkBuffer->pxEndPoint != NULL )
        {
            vNDSendNeighbourSolicitation( pxNetworkBuffer, &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ) );

            /* pxNetworkBuffer has been sent and released.
             * Make sure it won't be used again.. */
            *pxLostBuffer = pdTRUE;
        }
    }
    else
    {
        ulIPAddress = pxNetworkBuffer->xIPAddress.ulIP_IPv4;

        FreeRTOS_printf( ( "Looking up %xip with%s end-point\n",
                           ( unsigned ) FreeRTOS_ntohl( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ),
                           ( pxNetworkBuffer->pxEndPoint != NULL ) ? "" : "out" ) );

        /* Add an entry to the ARP table with a null hardware address.
         * This allows the ARP timer to know that an ARP reply is
         * outstanding, and perform retransmissions if necessary. */
        vARPRefreshCacheEntry( NULL, ulIPAddress, NULL );

        /* Generate an ARP for the required IP address. */
        iptracePACKET_DROPPED_TO_GENERATE_ARP( pxNetworkBuffer->xIPAddress.ulIP_IPv4 );

        /* 'ulIPAddress' might have become the address of the Gateway.
         * Find the route again. */

        pxNetworkBuffer->pxEndPoint = FreeRTOS_FindEndPointOnNetMask( pxNetworkBuffer->xIPAddress.ulIP_IPv4, 11 );

        if( pxNetworkBuffer->pxEndPoint == NULL )
        {
            eReturned = eCantSendPacket;
        }
        else
        {
            pxNetworkBuffer->xIPAddress.ulIP_IPv4 = ulIPAddress;
            vARPGenerateRequestPacket( pxNetworkBuffer );
        }
    }

    return eReturned;
}
/*-----------------------------------------------------------*/

/**
 * @brief Process the generated UDP packet and do other checks before sending the
 *        packet such as ARP cache check and address resolution.
 *
 * @param[in] pxNetworkBuffer: The network buffer carrying the packet.
 */
void vProcessGeneratedUDPPacket_IPv6( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    UDPPacket_IPv6_t * pxUDPPacket_IPv6;
    IPHeader_IPv6_t * pxIPHeader_IPv6;
    eARPLookupResult_t eReturned;
    size_t uxPayloadSize;
    /* memcpy() helper variables for MISRA Rule 21.15 compliance*/
    NetworkInterface_t * pxInterface = NULL;
    EthernetHeader_t * pxEthernetHeader = NULL;
    BaseType_t xLostBuffer = pdFALSE;
    NetworkEndPoint_t * pxEndPoint = pxNetworkBuffer->pxEndPoint;
    IPv6_Address_t xIPv6Address;

    /* Map the UDP packet onto the start of the frame. */

    /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
    /* coverity[misra_c_2012_rule_11_3_violation] */
    pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxIPHeader_IPv6 = &( pxUDPPacket_IPv6->xIPHeader );

    /* Remember the original address. It might get replaced with
     * the address of the gateway. */
    ( void ) memcpy( xIPv6Address.ucBytes, pxNetworkBuffer->xIPAddress.xIP_IPv6.ucBytes, sizeof( xIPv6Address.ucBytes ) );

    #if ipconfigSUPPORT_OUTGOING_PINGS == 1
        if( pxNetworkBuffer->usPort == ( uint16_t ) ipPACKET_CONTAINS_ICMP_DATA )
        {
            uxPayloadSize = pxNetworkBuffer->xDataLength - sizeof( ICMPPacket_IPv6_t );
        }
        else
    #endif
    {
        uxPayloadSize = pxNetworkBuffer->xDataLength - sizeof( UDPPacket_IPv6_t );
    }

    /* Look in the IPv6 MAC-address cache for the target IP-address. */
    eReturned = eNDGetCacheEntry( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxUDPPacket_IPv6->xEthernetHeader.xDestinationAddress ),
                                  &( pxEndPoint ) );

    if( eReturned != eCantSendPacket )
    {
        if( eReturned == eARPCacheHit )
        {
            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
                uint8_t ucSocketOptions;
            #endif
            iptraceSENDING_UDP_PACKET( pxNetworkBuffer->xIPAddress.ulIP_IPv4 );

            pxNetworkBuffer->pxEndPoint = pxEndPoint;

            #if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

                /* Is it possible that the packet is not actually a UDP packet
                 * after all, but an ICMP packet. */
                if( pxNetworkBuffer->usPort == ( uint16_t ) ipPACKET_CONTAINS_ICMP_DATA )
                {
                    pxIPHeader_IPv6->ucVersionTrafficClass = 0x60;
                    pxIPHeader_IPv6->ucNextHeader = ipPROTOCOL_ICMP_IPv6;
                    pxIPHeader_IPv6->ucHopLimit = 128;
                }
                else
            #endif /* ipconfigSUPPORT_OUTGOING_PINGS */
            {
                UDPHeader_t * pxUDPHeader = NULL;

                pxUDPHeader = &( pxUDPPacket_IPv6->xUDPHeader );

                pxIPHeader_IPv6->ucVersionTrafficClass = 0x60;
                pxIPHeader_IPv6->ucTrafficClassFlow = 0;
                pxIPHeader_IPv6->usFlowLabel = 0;
                pxIPHeader_IPv6->ucHopLimit = 255;
                pxUDPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ) );

                pxIPHeader_IPv6->ucNextHeader = ipPROTOCOL_UDP;
                pxIPHeader_IPv6->usPayloadLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - sizeof( IPPacket_IPv6_t ) );
                /* The total transmit size adds on the Ethernet header. */
                pxIPHeader_IPv6->usPayloadLength = FreeRTOS_htons( pxIPHeader_IPv6->usPayloadLength );

                pxUDPHeader->usDestinationPort = pxNetworkBuffer->usPort;
                pxUDPHeader->usSourcePort = pxNetworkBuffer->usBoundPort;
                pxUDPHeader->usLength = FreeRTOS_htons( pxUDPHeader->usLength );
                pxUDPHeader->usChecksum = 0U;
            }

            /* memcpy() the constant parts of the header information into
             * the correct location within the packet.  This fills in:
             *  xEthernetHeader.xSourceAddress
             *  xEthernetHeader.usFrameType
             *  xIPHeader.ucVersionHeaderLength
             *  xIPHeader.ucDifferentiatedServicesCode
             *  xIPHeader.usLength
             *  xIPHeader.usIdentification
             *  xIPHeader.usFragmentOffset
             *  xIPHeader.ucTimeToLive
             *  xIPHeader.ucProtocol
             * and
             *  xIPHeader.usHeaderChecksum
             */

            if( pxNetworkBuffer->pxEndPoint != NULL )
            {
                ( void ) memcpy( pxIPHeader_IPv6->xSourceAddress.ucBytes,
                                 pxNetworkBuffer->pxEndPoint->ipv6_settings.xIPAddress.ucBytes,
                                 ipSIZE_OF_IPv6_ADDRESS );
            }

            /* Save options now, as they will be overwritten by memcpy */
            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
                {
                    ucSocketOptions = pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ];
                }
            #endif

            #if ipconfigSUPPORT_OUTGOING_PINGS == 1
                if( pxNetworkBuffer->usPort == ( uint16_t ) ipPACKET_CONTAINS_ICMP_DATA )
                {
                    pxIPHeader_IPv6->usPayloadLength = FreeRTOS_htons( sizeof( ICMPEcho_IPv6_t ) + uxPayloadSize );
                }
                else
            #endif /* ipconfigSUPPORT_OUTGOING_PINGS */
            {
                pxIPHeader_IPv6->ucNextHeader = ipPROTOCOL_UDP;
                pxIPHeader_IPv6->usPayloadLength = FreeRTOS_htons( sizeof( UDPHeader_t ) + uxPayloadSize );
            }

            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
                {
                    if( ( ucSocketOptions & ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT ) != 0U )
                    {
                        ( void ) usGenerateProtocolChecksum( ( uint8_t * ) pxUDPPacket_IPv6, pxNetworkBuffer->xDataLength, pdTRUE );
                    }
                    else
                    {
                        pxUDPPacket_IPv6->xUDPHeader.usChecksum = 0U;
                    }
                }
            #endif /* if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 ) */
        }
        else if( eReturned == eARPCacheMiss )
        {
            eReturned = prvStartLookup( pxNetworkBuffer, &( xLostBuffer ) );

            if( pxNetworkBuffer->pxEndPoint != NULL )
            {
                vNDSendNeighbourSolicitation( pxNetworkBuffer, &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ) );

                /* pxNetworkBuffer has been sent and released.
                 * Make sure it won't be used again.. */
                xLostBuffer = pdTRUE;
            }
        }
        else
        {
            /* The lookup indicated that an ARP request has already been
             * sent out for the queried IP address. */
            eReturned = eCantSendPacket;
        }
    }

    if( xLostBuffer == pdTRUE )
    {
        /* An ND solicitation or ARP request has been sent. */
    }
    else if( eReturned != eCantSendPacket )
    {
        /* The network driver is responsible for freeing the network buffer
         * after the packet has been sent. */

        if( pxNetworkBuffer->pxEndPoint != NULL )
        {
            pxInterface = pxNetworkBuffer->pxEndPoint->pxNetworkInterface;
            pxEthernetHeader = ( ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );
            ( void ) memcpy( pxEthernetHeader->xSourceAddress.ucBytes,
                             pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes,
                             ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

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
            iptraceNETWORK_INTERFACE_OUTPUT( pxNetworkBuffer->xDataLength, pxNetworkBuffer->pucEthernetBuffer );
            ( void ) pxInterface->pfOutput( pxInterface, pxNetworkBuffer, pdTRUE );
        }
        else
        {
            /* The packet can't be sent (no route found).  Drop the packet. */
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
        }
    }
    else
    {
        /* The packet can't be sent (DHCP not completed?).  Just drop the
         * packet. */
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Process the received UDP packet.
 *
 * @param[in] pxNetworkBuffer: The network buffer carrying the UDP packet.
 * @param[in] usPort: The port number on which this packet was received.
 * @param[out] pxIsWaitingForARPResolution: If the packet is awaiting ARP resolution,
 *             this pointer will be set to pdTRUE. pdFALSE otherwise.
 *
 * @return pdPASS in case the UDP packet could be processed. Else pdFAIL is returned.
 */
BaseType_t xProcessReceivedUDPPacket_IPv6( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                           uint16_t usPort,
                                           BaseType_t * pxIsWaitingForARPResolution )
{
    BaseType_t xReturn = pdPASS;
    FreeRTOS_Socket_t * pxSocket;

    configASSERT( pxNetworkBuffer != NULL );
    configASSERT( pxNetworkBuffer->pucEthernetBuffer != NULL );
    UDPPacket_IPv6_t * pxUDPPacket_IPv6;

    /* Caller must check for minimum packet size. */
    pxSocket = pxUDPSocketLookup( usPort );

    *pxIsWaitingForARPResolution = pdFALSE;

    do
    {
        if( pxSocket != NULL )
        {
            if( *ipLOCAL_IP_ADDRESS_POINTER != 0U )
            {
                /* When refreshing the ARP/ND cache with received UDP packets we must be
                 * careful;  hundreds of broadcast messages may pass and if we're not
                 * handling them, no use to fill the ARP cache with those IP addresses. */
                pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
                vNDRefreshCacheEntry( &( pxUDPPacket_IPv6->xEthernetHeader.xSourceAddress ), &( pxUDPPacket_IPv6->xIPHeader.xSourceAddress ),
                                      pxNetworkBuffer->pxEndPoint );
            }
            else
            {
                /* During DHCP, IP address is not assigned and therefore ARP verification
                 * is not possible. */
            }

            #if ( ipconfigUSE_CALLBACKS == 1 )
                {
                    size_t uxIPLength = uxIPHeaderSizePacket( pxNetworkBuffer );
                    size_t uxPayloadSize;

                    /* Did the owner of this socket register a reception handler ? */
                    if( ipconfigIS_VALID_PROG_ADDRESS( pxSocket->u.xUDP.pxHandleReceive ) )
                    {
                        struct freertos_sockaddr xSourceAddress, destinationAddress;
                        /* The application hook needs to know the from- and to-addresses. */

                        void * pcData = &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPLength + ipSIZE_OF_UDP_HEADER ] );
                        FOnUDPReceive_t xHandler = ( FOnUDPReceive_t ) pxSocket->u.xUDP.pxHandleReceive;

                        xSourceAddress.sin_port = pxNetworkBuffer->usPort;
                        destinationAddress.sin_port = usPort;
                        ( void ) memcpy( xSourceAddress.sin_addr6.ucBytes, pxUDPPacket_IPv6->xIPHeader.xSourceAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                        ( void ) memcpy( destinationAddress.sin_addr6.ucBytes, pxUDPPacket_IPv6->xIPHeader.xDestinationAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                        xSourceAddress.sin_family = ( uint8_t ) FREERTOS_AF_INET6;
                        destinationAddress.sin_family = ( uint8_t ) FREERTOS_AF_INET6;
                        xSourceAddress.sin_len = ( uint8_t ) sizeof( xSourceAddress );
                        destinationAddress.sin_len = ( uint8_t ) sizeof( destinationAddress );
                        uxPayloadSize = pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER + ( size_t ) ipSIZE_OF_IPv6_HEADER );

                        /* The value of 'xDataLength' was proven to be at least the size of a UDP packet in prvProcessIPPacket(). */
                        if( xHandler( ( Socket_t ) pxSocket,
                                      ( void * ) pcData,
                                      uxPayloadSize,
                                      &( xSourceAddress ),
                                      &( destinationAddress ) ) != 0 )
                        {
                            xReturn = pdFAIL; /* xHandler has consumed the data, do not add it to .xWaitingPacketsList'. */
                        }
                    }
                }
            #endif /* ipconfigUSE_CALLBACKS */

            #if ( ipconfigUDP_MAX_RX_PACKETS > 0U )
                {
                    if( xReturn == pdPASS )
                    {
                        if( listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) ) >= pxSocket->u.xUDP.uxMaxPackets )
                        {
                            FreeRTOS_debug_printf( ( "xProcessReceivedUDPPacket: buffer full %ld >= %ld port %u\n",
                                                     listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) ),
                                                     pxSocket->u.xUDP.uxMaxPackets, pxSocket->usLocalPort ) );
                            xReturn = pdFAIL; /* we did not consume or release the buffer */
                        }
                    }
                }
            #endif /* if ( ipconfigUDP_MAX_RX_PACKETS > 0U ) */

            #if ( ipconfigUSE_CALLBACKS == 1 ) || ( ipconfigUDP_MAX_RX_PACKETS > 0U )
                if( xReturn == pdPASS ) /*lint !e774: Boolean within 'if' always evaluates to True, depending on configuration. [MISRA 2012 Rule 14.3, required. */
            #else
                /* xReturn is still pdPASS. */
            #endif
            {
                vTaskSuspendAll();
                {
                    taskENTER_CRITICAL();
                    {
                        /* Add the network packet to the list of packets to be
                         * processed by the socket. */
                        vListInsertEnd( &( pxSocket->u.xUDP.xWaitingPacketsList ), &( pxNetworkBuffer->xBufferListItem ) );
                    }
                    taskEXIT_CRITICAL();
                }
                ( void ) xTaskResumeAll();

                /* Set the socket's receive event */
                if( pxSocket->xEventGroup != NULL )
                {
                    ( void ) xEventGroupSetBits( pxSocket->xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE );
                }

                #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
                    {
                        if( ( pxSocket->pxSocketSet != NULL ) && ( ( pxSocket->xSelectBits & ( ( EventBits_t ) eSELECT_READ ) ) != 0U ) )
                        {
                            ( void ) xEventGroupSetBits( pxSocket->pxSocketSet->xSelectGroup, ( EventBits_t ) eSELECT_READ );
                        }
                    }
                #endif

                #if ( ipconfigSOCKET_HAS_USER_SEMAPHORE == 1 )
                    {
                        if( pxSocket->pxUserSemaphore != NULL )
                        {
                            ( void ) xSemaphoreGive( pxSocket->pxUserSemaphore );
                        }
                    }
                #endif

                #if ( ipconfigUSE_DHCP == 1 )
                    {
                        if( xIsDHCPSocket( pxSocket ) != 0 )
                        {
                            ( void ) xSendDHCPEvent( pxNetworkBuffer->pxEndPoint );
                        }
                    }
                #endif
            }
        }
        else
        {
            ProtocolHeaders_t * pxProtocolHeaders;
            size_t uxIPLength;

            uxIPLength = uxIPHeaderSizePacket( pxNetworkBuffer );
            pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + uxIPLength ] ) );

            /* There is no socket listening to the target port, but still it might
             * be for this node. */

            #if ( ipconfigUSE_DNS == 1 ) && ( ipconfigDNS_USE_CALLBACKS == 1 )

                /* A DNS reply, check for the source port.  Although the DNS client
                 * does open a UDP socket to send a messages, this socket will be
                 * closed after a short timeout.  Messages that come late (after the
                 * socket is closed) will be treated here. */
                if( FreeRTOS_ntohs( pxProtocolHeaders->xUDPHeader.usSourcePort ) == ( uint16_t ) ipDNS_PORT )
                {
                    xReturn = ( BaseType_t ) ulDNSHandlePacket( pxNetworkBuffer );
                }
                else
            #endif

            #if ( ipconfigUSE_LLMNR == 1 )
                /* A LLMNR request, check for the destination port. */
                if( ( usPort == FreeRTOS_ntohs( ipLLMNR_PORT ) ) ||
                    ( pxProtocolHeaders->xUDPHeader.usSourcePort == FreeRTOS_ntohs( ipLLMNR_PORT ) ) )
                {
                    xReturn = ( BaseType_t ) ulDNSHandlePacket( pxNetworkBuffer );
                }
                else
            #endif /* ipconfigUSE_LLMNR */

            #if ( ipconfigUSE_NBNS == 1 )
                /* a NetBIOS request, check for the destination port */
                if( ( usPort == FreeRTOS_ntohs( ipNBNS_PORT ) ) ||
                    ( pxUDPPacket_IPv6->xUDPHeader.usSourcePort == FreeRTOS_ntohs( ipNBNS_PORT ) ) )
                {
                    xReturn = ( BaseType_t ) ulNBNSHandlePacket( pxNetworkBuffer );
                }
                else
            #endif /* ipconfigUSE_NBNS */
            {
                xReturn = pdFAIL;
            }
        }
    } while( ipFALSE_BOOL );

    return xReturn;
}
/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
    #endif /* ipconfigUSE_IPv6 != 0 ) */
/* *INDENT-ON* */
