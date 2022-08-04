/*
 * FreeRTOS+TCP V2.3.3
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/**
 * @file FreeRTOS_UDP_IP.c
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

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_IP_Utils.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_Routing.h"
#include "FreeRTOS_ND.h"

#if ( ipconfigUSE_DNS == 1 ) || ( ipconfigUSE_NBNS == 1 )
    #include "FreeRTOS_DNS.h"
#endif

/** @brief The expected IP version and header length coded into the IP header itself. */
#define ipIP_VERSION_AND_HEADER_LENGTH_BYTE    ( ( uint8_t ) 0x45 )

/*-----------------------------------------------------------*/

static eARPLookupResult_t prvLookupIPInCache( NetworkBufferDescriptor_t * const pxNetworkBuffer );

static void prvSetIPHeaderForICMP( NetworkBufferDescriptor_t * const pxNetworkBuffer );

static void prvSetIPHeaderForUDP( NetworkBufferDescriptor_t * const pxNetworkBuffer );

static eARPLookupResult_t prvStartLookup( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                          BaseType_t * pxLostBuffer );

static void prvUDPSendPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

static void prvFindIPv4Endpoint( NetworkBufferDescriptor_t * const pxNetworkBuffer );

static BaseType_t prvHandleUDPPacketWithoutSocket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                   uint16_t usPort );

/*-----------------------------------------------------------*/


/**
 * @brief Look-up the target IP-address, works for both IPv4 and IPv6.
 *
 * @param[in,out] pxNetworkBuffer: The network buffer carrying the UDP or ICMP packet.
 *                                 It is also an "out" parameter: in case the target can only
 *                                 be reached through a gateway, the gateway's address will be
 *                                 filled in.
 *
 * @return When the IP-address is found: eARPCacheHit, when not found: eARPCacheMiss,
 *         and when waiting for a ARP reply: eCantSendPacket.
 */
static eARPLookupResult_t prvLookupIPInCache( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    eARPLookupResult_t eReturned;
    /* Map the UDP packet onto the start of the frame. */
    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    NetworkEndPoint_t * pxEndPoint = pxNetworkBuffer->pxEndPoint;

    #if ( ipconfigUSE_IPv6 != 0 )
        if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
        {
            eReturned = eNDGetCacheEntry( &( pxNetworkBuffer->xIPv6Address ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), &( pxEndPoint ) );
        }
        else
    #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
    {
        pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

        ( void ) memset( &( pxUDPPacket->xIPHeader ), 0, sizeof( pxUDPPacket->xIPHeader ) );
        pxUDPPacket->xIPHeader.ucVersionHeaderLength = ipIP_VERSION_AND_HEADER_LENGTH_BYTE;
        pxUDPPacket->xIPHeader.ucTimeToLive = ipconfigUDP_TIME_TO_LIVE;
        #if ( ipconfigUSE_LLMNR == 1 )
            {
                /* LLMNR messages are typically used on a LAN and they're
                 * not supposed to cross routers */
                if( pxNetworkBuffer->ulIPAddress == ipLLMNR_IP_ADDR )
                {
                    pxUDPPacket->xIPHeader.ucTimeToLive = 0x01;
                }
            }
        #endif
        #if ( ipconfigUSE_MDNS == 1 )
            {
                /* mDNS messages have a hop-count of 255, see RFC 6762, section 11. */
                if( pxNetworkBuffer->ulIPAddress == ipMDNS_IP_ADDRESS )
                {
                    pxUDPPacket->xIPHeader.ucTimeToLive = 0xffU;
                }
            }
        #endif

        eReturned = eARPGetCacheEntry( &( pxNetworkBuffer->ulIPAddress ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), &( pxEndPoint ) );
    }

    if( pxNetworkBuffer->pxEndPoint == NULL )
    {
        pxNetworkBuffer->pxEndPoint = pxEndPoint;
    }

    return eReturned;
}
/*-----------------------------------------------------------*/

/**
 * @brief Set the fields in the IP-header in a ICMP-packet.
 *
 * @param[in] pxNetworkBuffer: The network buffer carrying the ICMP packet.
 */
static void prvSetIPHeaderForICMP( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    #if ( ipconfigUSE_IPv6 != 0 )
        UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

        if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
        {
            IPHeader_IPv6_t * pxIPHeader_IPv6;

            pxIPHeader_IPv6 = ( ( IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );
            pxIPHeader_IPv6->ucVersionTrafficClass = 0x60;
            pxIPHeader_IPv6->ucNextHeader = ipPROTOCOL_ICMP_IPv6;
            pxIPHeader_IPv6->ucHopLimit = 128;
        }
        else
    #endif /* ( ipconfigUSE_IPv6 != 0 ) */
    {
        IPHeader_t * pxIPHeader;

        pxIPHeader = ( ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );
        pxIPHeader->ucProtocol = ipPROTOCOL_ICMP;
        pxIPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );
        pxIPHeader->usLength = FreeRTOS_htons( pxIPHeader->usLength );
        pxIPHeader->ulDestinationIPAddress = pxNetworkBuffer->ulIPAddress;
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Set the fields in the IP-header in a UDP-packet.
 *
 * @param[in] pxNetworkBuffer: The network buffer carrying the UDP packet.
 */
static void prvSetIPHeaderForUDP( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    UDPPacket_t * pxUDPPacket;
    UDPHeader_t * pxUDPHeader;
    IPHeader_t * pxIPHeader;

    #if ( ipconfigUSE_IPv6 != 0 )
        UDPPacket_IPv6_t * pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    #endif

    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    /* Create short cuts to the data within the packet. */
    pxIPHeader = &( pxUDPPacket->xIPHeader );

    #if ( ipconfigUSE_IPv6 != 0 )
        if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
        {
            pxUDPHeader = &( pxUDPPacket_IPv6->xUDPHeader );

            pxUDPPacket_IPv6->xIPHeader.ucVersionTrafficClass = 0x60;
            pxUDPPacket_IPv6->xIPHeader.ucTrafficClassFlow = 0;
            pxUDPPacket_IPv6->xIPHeader.usFlowLabel = 0;
            pxUDPPacket_IPv6->xIPHeader.ucHopLimit = 255;
            pxUDPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ) );

            pxUDPPacket_IPv6->xIPHeader.ucNextHeader = ipPROTOCOL_UDP;
            pxUDPPacket_IPv6->xIPHeader.usPayloadLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - sizeof( IPPacket_IPv6_t ) );
            /* The total transmit size adds on the Ethernet header. */
            pxUDPPacket_IPv6->xIPHeader.usPayloadLength = FreeRTOS_htons( pxUDPPacket_IPv6->xIPHeader.usPayloadLength );
        }
        else
    #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
    {
        pxUDPHeader = &( pxUDPPacket->xUDPHeader );
        pxUDPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ) );

        pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
        pxIPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );
        pxIPHeader->usLength = FreeRTOS_htons( pxIPHeader->usLength );
        pxIPHeader->ulDestinationIPAddress = pxNetworkBuffer->ulIPAddress;
    }

    pxUDPHeader->usDestinationPort = pxNetworkBuffer->usPort;
    pxUDPHeader->usSourcePort = pxNetworkBuffer->usBoundPort;

    pxUDPHeader->usLength = FreeRTOS_htons( pxUDPHeader->usLength );
    pxUDPHeader->usChecksum = 0U;
}
/*-----------------------------------------------------------*/

/**
 * @brief This function is called in case the IP-address was not found,
 *        i.e. in the cache 'eARPCacheMiss' was returned.
 *        Either an ARP request or a Neighbour solicitation will be emitted.
 *
 * @param[in] pxNetworkBuffer : The network buffer carrying the UDP or ICMP packet.
 *
 * @param[out] pxLostBuffer : The pointee will be set to true in case the network packet got released
 *                            ( the ownership was taken ).
 */
static eARPLookupResult_t prvStartLookup( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                          BaseType_t * pxLostBuffer )
{
    eARPLookupResult_t eReturned = eARPCacheMiss;

    #if ( ipconfigUSE_IPv6 != 0 )
        UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

        if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
        {
            FreeRTOS_printf( ( "Looking up %pip with%s end-point\n",
                               pxNetworkBuffer->xIPv6Address.ucBytes,
                               ( pxNetworkBuffer->pxEndPoint != NULL ) ? "" : "out" ) );

            if( pxNetworkBuffer->pxEndPoint != NULL )
            {
                vNDSendNeighbourSolicitation( pxNetworkBuffer, &( pxNetworkBuffer->xIPv6Address ) );

                /* pxNetworkBuffer has been sent and released.
                 * Make sure it won't be used again.. */
                *pxLostBuffer = pdTRUE;
            }
        }
        else
    #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
    {
        FreeRTOS_printf( ( "Looking up %xip with%s end-point\n",
                           ( unsigned ) FreeRTOS_ntohl( pxNetworkBuffer->ulIPAddress ),
                           ( pxNetworkBuffer->pxEndPoint != NULL ) ? "" : "out" ) );

        /* Add an entry to the ARP table with a null hardware address.
         * This allows the ARP timer to know that an ARP reply is
         * outstanding, and perform retransmissions if necessary. */
        vARPRefreshCacheEntry( NULL, pxNetworkBuffer->ulIPAddress, NULL );

        /* Generate an ARP for the required IP address. */
        iptracePACKET_DROPPED_TO_GENERATE_ARP( pxNetworkBuffer->ulIPAddress );

        /* 'ulIPAddress' might have become the address of the Gateway.
         * Find the route again. */
        pxNetworkBuffer->pxEndPoint = FreeRTOS_FindEndPointOnNetMask( pxNetworkBuffer->ulIPAddress, 11 ); /* ARP request */

        if( pxNetworkBuffer->pxEndPoint == NULL )
        {
            eReturned = eCantSendPacket;
        }
        else
        {
            vARPGenerateRequestPacket( pxNetworkBuffer );
        }
    }

    return eReturned;
}
/*-----------------------------------------------------------*/

/**
 * @brief Call the method 'pfOutput' of the interface found to send the packet.
 *
 * @param[in] pxNetworkBuffer: The network buffer carrying the UDP or ICMP packet.
 */
static void prvUDPSendPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    NetworkInterface_t * pxInterface = pxNetworkBuffer->pxEndPoint->pxNetworkInterface;
    EthernetHeader_t * pxEthernetHeader = ( ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );

    ( void ) memcpy( pxEthernetHeader->xSourceAddress.ucBytes, pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
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

    iptraceNETWORK_INTERFACE_OUTPUT( pxNetworkBuffer->xDataLength, pxNetworkBuffer->pucEthernetBuffer );
    ( void ) pxInterface->pfOutput( pxInterface, pxNetworkBuffer, pdTRUE );
}
/*-----------------------------------------------------------*/

/**
 * @brief Find an IPv4 end-point that matches with the address found in a network buffer.
 * @param[in] pxNetworkBuffer: the network buffer containing a received packet.
 */
static void prvFindIPv4Endpoint( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    if( pxNetworkBuffer->pxEndPoint == NULL )
    {
        pxNetworkBuffer->pxEndPoint = FreeRTOS_FindEndPointOnNetMask( pxNetworkBuffer->ulIPAddress, 10 );

        if( pxNetworkBuffer->pxEndPoint == NULL )
        {
            pxNetworkBuffer->pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( 0U, 26 );

            if( pxNetworkBuffer->pxEndPoint == NULL )
            {
                FreeRTOS_printf( ( "vProcessGeneratedUDPPacket: No pxEndPoint found? Using %lxip\n",
                                   ( pxNetworkBuffer->pxEndPoint != NULL ) ? FreeRTOS_ntohl( pxNetworkBuffer->pxEndPoint->ipv4_settings.ulIPAddress ) : 0U ) );
            }
        }
    }
}

/**
 * @brief Process the generated UDP packet and do other checks before sending the
 *        packet such as ARP cache check and address resolution.
 *
 * @param[in] pxNetworkBuffer: The network buffer carrying the packet.
 */
void vProcessGeneratedUDPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;

    #if ( ipconfigUSE_IPv6 != 0 )
        BaseType_t xIsIPV6 = pdFALSE;
        IPv6_Address_t xIPv6Address;
    #endif
    eARPLookupResult_t eReturned;
    uint32_t ulIPAddress = pxNetworkBuffer->ulIPAddress;
    BaseType_t xLostBuffer = pdFALSE;

    /* Map the UDP packet onto the start of the frame. */
    pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    #if ( ipconfigUSE_IPv6 != 0 )
        if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
        {
            xIsIPV6 = pdTRUE;

            /* Remember the original address. It might get replaced with
             * the address of the gateway. */
            ( void ) memcpy( xIPv6Address.ucBytes, pxNetworkBuffer->xIPv6Address.ucBytes, sizeof( xIPv6Address.ucBytes ) );
        }
        else
    #endif
    {
        /* Remember the original IPv4 address. */
        ulIPAddress = pxNetworkBuffer->ulIPAddress;
    }

    /* Create short cuts to the data within the packet. */
    pxIPHeader = &( pxUDPPacket->xIPHeader );

    /* Look in the IPv4 or IPv6 MAC-address cache for the target IP-address. */
    eReturned = prvLookupIPInCache( pxNetworkBuffer );

    if( eReturned == eARPCacheHit )
    {
        /* As the MAC-address was found in the cache, the IP-address
         * can be restored to its original. */
        #if ( ipconfigUSE_IPv6 != 0 )
            if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
            {
                xIsIPV6 = pdTRUE;
                ( void ) memcpy( pxNetworkBuffer->xIPv6Address.ucBytes, xIPv6Address.ucBytes, sizeof( pxNetworkBuffer->xIPv6Address.ucBytes ) );
            }
            else
        #endif
        {
            pxNetworkBuffer->ulIPAddress = ulIPAddress;
        }

        #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
            uint8_t ucSocketOptions = pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ];
        #endif

        iptraceSENDING_UDP_PACKET( pxNetworkBuffer->ulIPAddress );

        /* It is possible that the packet is not actually a UDP packet
         * after all, but an ICMP packet. */
        if( pxNetworkBuffer->usPort == ( uint16_t ) ipPACKET_CONTAINS_ICMP_DATA )
        {
            prvSetIPHeaderForICMP( pxNetworkBuffer );
        }
        else
        {
            prvSetIPHeaderForUDP( pxNetworkBuffer );
        }

        #if ( ipconfigUSE_IPv6 != 0 )
            if( xIsIPV6 == pdFALSE )
        #endif
        {
            prvFindIPv4Endpoint( pxNetworkBuffer );
        }

        if( pxNetworkBuffer->pxEndPoint != NULL )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                if( xIsIPV6 != pdFALSE )
                {
                    IPHeader_IPv6_t * pxIPHeader_IPv6 = ( ( IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );
                    ( void ) memcpy( pxIPHeader_IPv6->xSourceAddress.ucBytes, pxNetworkBuffer->pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                }
                else
            #endif
            {
                pxIPHeader->ulSourceIPAddress = pxNetworkBuffer->pxEndPoint->ipv4_settings.ulIPAddress;
            }
        }

        #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
            {
                #if ( ipconfigUSE_IPv6 != 0 )
                    if( xIsIPV6 == pdFALSE )
                #endif
                {
                    pxIPHeader->usHeaderChecksum = 0U;
                    pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0U, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ), ipSIZE_OF_IPv4_HEADER );
                    pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );
                }

                if( ( ucSocketOptions & ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT ) != 0U )
                {
                    ( void ) usGenerateProtocolChecksum( ( uint8_t * ) pxUDPPacket, pxNetworkBuffer->xDataLength, pdTRUE );
                }
                else
                {
                    pxUDPPacket->xUDPHeader.usChecksum = 0U;
                }
            }
        #endif /* if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 ) */
    } /* if( eReturned == eARPCacheHit ) */
    else if( eReturned == eARPCacheMiss )
    {
        eReturned = prvStartLookup( pxNetworkBuffer, &( xLostBuffer ) );
    }
    else
    {
        /* The lookup indicated that an ARP request has already been
         * sent out for the queried IP address. */
        eReturned = eCantSendPacket;
    }

    if( xLostBuffer == pdTRUE )
    {
        /* An ND solicitation or ARP request has been sent. */
    }
    else if( eReturned != eCantSendPacket )
    {
        /* eReturned equals eARPCacheHit or eARPCacheMiss. */

        /* The network driver is responsible for freeing the network buffer
         * after the packet has been sent. */
        if( pxNetworkBuffer->pxEndPoint != NULL )
        {
            prvUDPSendPacket( pxNetworkBuffer );
        }
        else
        {
            /* The packet can't be sent (no route found).  Drop the packet. */
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
        }
    }
    else
    {
        /* eReturned equals eCantSendPacket:
         * The packet can't be sent (DHCP not completed?).  Just drop the
         * packet. */
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief A UDP packet has been received. Check if the message is for either DNS/NBNS or LLMNR.
 * @param[in] pxNetworkBuffer : the packet received.
 * @param[in] usPort: The port number on which this packet was received.
 */
static BaseType_t prvHandleUDPPacketWithoutSocket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                   uint16_t usPort )
{
    size_t uxIPLength;
    BaseType_t xReturn = pdPASS;
    ProtocolHeaders_t * pxProtocolHeaders;

    #if ( ( ( ipconfigUSE_DNS == 1 ) && ( ipconfigDNS_USE_CALLBACKS == 1 ) ) || ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_NBNS == 1 ) )
        UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    #endif

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
            #if ( ipconfigUSE_IPv6 != 0 )
                if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
                {
                }
                else
            #endif
            {
                vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress,
                                       pxNetworkBuffer->pxEndPoint );
            }

            xReturn = ( BaseType_t ) ulDNSHandlePacket( pxNetworkBuffer );
        }
        else
    #endif /* if ( ipconfigUSE_DNS == 1 ) && ( ipconfigDNS_USE_CALLBACKS == 1 ) */

    #if ( ipconfigUSE_LLMNR == 1 )
        /* A LLMNR request, check for the destination port. */
        if( ( usPort == FreeRTOS_ntohs( ipLLMNR_PORT ) ) ||
            ( pxProtocolHeaders->xUDPHeader.usSourcePort == FreeRTOS_ntohs( ipLLMNR_PORT ) ) )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
                {
                }
                else
            #endif
            {
                vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress,
                                       pxNetworkBuffer->pxEndPoint );
            }

            xReturn = ( BaseType_t ) ulDNSHandlePacket( pxNetworkBuffer );
        }
        else
    #endif /* ipconfigUSE_LLMNR */

    #if ( ipconfigUSE_MDNS == 1 )
        /* A MDNS request, check for the destination port. */
        if( ( usPort == FreeRTOS_ntohs( ipMDNS_PORT ) ) ||
            ( pxProtocolHeaders->xUDPHeader.usSourcePort == FreeRTOS_ntohs( ipMDNS_PORT ) ) )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
                {
                }
                else
            #endif
            {
                vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress,
                                       pxNetworkBuffer->pxEndPoint );
            }

            xReturn = ( BaseType_t ) ulDNSHandlePacket( pxNetworkBuffer );
        }
        else
    #endif /* ipconfigUSE_MDNS */

    #if ( ipconfigUSE_NBNS == 1 )
        /* a NetBIOS request, check for the destination port */
        if( ( usPort == FreeRTOS_ntohs( ipNBNS_PORT ) ) ||
            ( pxProtocolHeaders->xUDPHeader.usSourcePort == FreeRTOS_ntohs( ipNBNS_PORT ) ) )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
                {
                }
                else
            #endif
            {
                vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress,
                                       pxNetworkBuffer->pxEndPoint );
            }

            xReturn = ( BaseType_t ) ulNBNSHandlePacket( pxNetworkBuffer );
        }
        else
    #endif /* ipconfigUSE_NBNS */
    {
        xReturn = pdFAIL;
    }

    return xReturn;
}

#if ( ipconfigUSE_CALLBACKS == 1 )
    static BaseType_t prvCallUDPApplicationHook( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                 FreeRTOS_Socket_t * pxSocket )
    {
        BaseType_t xReturn = pdPASS;
        size_t uxIPLength = uxIPHeaderSizePacket( pxNetworkBuffer );
        void * pcData = &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPLength + ipSIZE_OF_UDP_HEADER ] );
        FOnUDPReceive_t xHandler = ( FOnUDPReceive_t ) pxSocket->u.xUDP.pxHandleReceive;

        #if ( ipconfigUSE_IPv6 != 0 )
            UDPPacket_IPv6_t * pxUDPPacket_IPv6;
        #endif
        size_t uxPayloadSize;

        #if ( ipconfigUSE_IPv6 != 0 )
            struct freertos_sockaddr6 xSourceAddress, destinationAddress;
        #else
            struct freertos_sockaddr xSourceAddress, destinationAddress;
        #endif

        /* The application hook needs to know the from- and to-addresses. */

        xSourceAddress.sin_port = pxNetworkBuffer->usPort;
        destinationAddress.sin_port = FreeRTOS_htons( pxSocket->usLocalPort );

        #if ( ipconfigUSE_IPv6 != 0 )
            pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );

            if( pxUDPPacket_IPv6->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
            {
                ( void ) memcpy( xSourceAddress.sin_addrv6.ucBytes, pxUDPPacket_IPv6->xIPHeader.xSourceAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                ( void ) memcpy( destinationAddress.sin_addrv6.ucBytes, pxUDPPacket_IPv6->xIPHeader.xDestinationAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                xSourceAddress.sin_family = ( uint8_t ) FREERTOS_AF_INET6;
                destinationAddress.sin_family = ( uint8_t ) FREERTOS_AF_INET6;
                xSourceAddress.sin_len = ( uint8_t ) sizeof( xSourceAddress );
                destinationAddress.sin_len = ( uint8_t ) sizeof( destinationAddress );
                uxPayloadSize = pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER + ( size_t ) ipSIZE_OF_IPv6_HEADER );
            }
            else
        #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
        {
            struct freertos_sockaddr * xSourceAddress4 = ( ( sockaddr4_t * ) &( xSourceAddress ) );
            struct freertos_sockaddr * destinationAddress4 = ( ( sockaddr4_t * ) &( destinationAddress ) );
            UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

            xSourceAddress4->sin_addr = pxNetworkBuffer->ulIPAddress;
            destinationAddress4->sin_addr = pxUDPPacket->xIPHeader.ulDestinationIPAddress;
            xSourceAddress4->sin_family = ( uint8_t ) FREERTOS_AF_INET;
            destinationAddress4->sin_family = ( uint8_t ) FREERTOS_AF_INET;
            xSourceAddress4->sin_len = ( uint8_t ) sizeof( xSourceAddress );
            destinationAddress4->sin_len = ( uint8_t ) sizeof( destinationAddress );
            uxPayloadSize = pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER + ( size_t ) ipSIZE_OF_IPv4_HEADER );
        }

        if( xHandler( pxSocket,
                      pcData, ( size_t ) uxPayloadSize,
                      ( ( sockaddr4_t * ) &( xSourceAddress ) ),
                      ( ( sockaddr4_t * ) &( destinationAddress ) ) ) != pdFALSE )
        {
            xReturn = pdFAIL; /* xHandler has consumed the data, do not add it to .xWaitingPacketsList'. */
        }

        return xReturn;
    }
#endif /* ( ipconfigUSE_CALLBACKS == 1 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Process the received UDP packet.
 *
 * @param[in] pxNetworkBuffer: The network buffer carrying the UDP packet.
 * @param[in] usPort: The port number on which this packet was received.
 * @param[out] pxIsWaitingARPResolution: If the packet is awaiting ARP resolution, this
 *                                    pointer will be set to pdTRUE. pdFALSE otherwise.
 *
 * @return pdPASS in case the UDP packet could be processed. Else pdFAIL is returned.
 */
BaseType_t xProcessReceivedUDPPacket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                      uint16_t usPort,
                                      BaseType_t * pxIsWaitingARPResolution )
{
    BaseType_t xReturn = pdPASS;
    FreeRTOS_Socket_t * pxSocket;
    ProtocolHeaders_t * pxProtocolHeaders;
    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    size_t uxIPLength;

    #if ( ipconfigUSE_IPv6 != 0 )
        UDPPacket_IPv6_t * pxUDPPacket_IPv6;
    #endif

    *pxIsWaitingARPResolution = pdFALSE;

    /* Caller must check for minimum packet size. */
    pxSocket = pxUDPSocketLookup( usPort );

    configASSERT( pxNetworkBuffer->pucEthernetBuffer != NULL );

    uxIPLength = uxIPHeaderSizePacket( pxNetworkBuffer );

    pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + uxIPLength ] ) );

    /* Introduce a do while ( true ) loop in order to reduce the complexity of the function. */
    do
    {
        if( pxSocket == NULL )
        {
            /* The UDP port number does not belong to a socket.
             * It might be s DNS response. */
            xReturn = prvHandleUDPPacketWithoutSocket( pxNetworkBuffer, usPort );
            break;
        }

        /* When refreshing the ARP/ND cache with received UDP packets we must be
         * careful;  hundreds of broadcast messages may pass and if we're not
         * handling them, no use to fill the ARP cache with those IP addresses. */
        #if ( ipconfigUSE_IPv6 != 0 )
            pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );

            if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
            {
                vNDRefreshCacheEntry( &( pxUDPPacket_IPv6->xEthernetHeader.xSourceAddress ), &( pxUDPPacket_IPv6->xIPHeader.xSourceAddress ), pxNetworkBuffer->pxEndPoint );
            }
            else
        #endif
        {
            if( xCheckRequiresARPResolution( pxNetworkBuffer ) == pdTRUE )
            {
                /* Mark this packet as waiting for ARP resolution. */
                *pxIsWaitingARPResolution = pdTRUE;

                /* Return a fail to show that the frame will not be processed right now. */
                xReturn = pdFAIL;
                break;
            }
            else
            {
                /* IP address is not on the same subnet, ARP table can be updated. */
                vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, pxNetworkBuffer->pxEndPoint );
            }
        }

        #if ( ipconfigUSE_CALLBACKS == 1 )
            {
                /* Did the owner of this socket register a reception handler ? */
                if( ipconfigIS_VALID_PROG_ADDRESS( pxSocket->u.xUDP.pxHandleReceive ) )
                {
                    xReturn = prvCallUDPApplicationHook( pxNetworkBuffer, pxSocket );

                    if( xReturn == pdFAIL )
                    {
                        /* The packet has been consumed by the application hook. */
                        break;
                    }
                }
            }
        #endif /* ipconfigUSE_CALLBACKS */

        #if ( ipconfigUDP_MAX_RX_PACKETS > 0U )
            {
                if( listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) ) >= pxSocket->u.xUDP.uxMaxPackets )
                {
                    FreeRTOS_debug_printf( ( "xProcessReceivedUDPPacket: buffer full %ld >= %ld port %u\n",
                                             listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) ),
                                             pxSocket->u.xUDP.uxMaxPackets, pxSocket->usLocalPort ) );
                    /* Indicate to the caller that the packet must still be released. */
                    xReturn = pdFAIL;
                    break;
                }
            }
        #endif /* if ( ipconfigUDP_MAX_RX_PACKETS > 0U ) */

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
                    /* This is the DHCP clients socket, bound to port 68. */
                    /* Can call this function directly, because this code is running from the IP-task. */
                    if( pxNetworkBuffer->pxEndPoint != NULL )
                    {
                        ( void ) xSendDHCPEvent( pxNetworkBuffer->pxEndPoint );
                    }
                }
            }
        #endif /* if ( ipconfigUSE_DHCP == 1 ) */
    }
    while( ipFALSE_BOOL );

    /* This local variable might not be used, depending on the enabled protocols. */
    ( void ) pxProtocolHeaders;

    return xReturn;
}
/*-----------------------------------------------------------*/
