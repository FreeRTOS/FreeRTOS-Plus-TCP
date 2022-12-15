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
#include "FreeRTOS_IP_Utils.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"

#if ( ipconfigUSE_DNS == 1 )
    #include "FreeRTOS_DNS.h"
#endif

/** @brief The expected IP version and header length coded into the IP header itself. */
#define ipIP_VERSION_AND_HEADER_LENGTH_BYTE    ( ( uint8_t ) 0x45 )

/** @brief Part of the Ethernet and IP headers are always constant when sending an IPv4
 * UDP packet.  This array defines the constant parts, allowing this part of the
 * packet to be filled in using a simple memcpy() instead of individual writes. */
/*lint -e708 (Info -- union initialization). */
UDPPacketHeader_t xDefaultPartUDPPacketHeader =
{
    /* .ucBytes : */
    {
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  /* Ethernet source MAC address. */
        0x08, 0x00,                          /* Ethernet frame type. */
        ipIP_VERSION_AND_HEADER_LENGTH_BYTE, /* ucVersionHeaderLength. */
        0x00,                                /* ucDifferentiatedServicesCode. */
        0x00, 0x00,                          /* usLength. */
        0x00, 0x00,                          /* usIdentification. */
        0x00, 0x00,                          /* usFragmentOffset. */
        ipconfigUDP_TIME_TO_LIVE,            /* ucTimeToLive */
        ipPROTOCOL_UDP,                      /* ucProtocol. */
        0x00, 0x00,                          /* usHeaderChecksum. */
        0x00, 0x00, 0x00, 0x00               /* Source IP address. */
    }
};
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
    uint32_t ulIPAddress;
    /* Map the UDP packet onto the start of the frame. */
    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    NetworkEndPoint_t * pxEndPoint = pxNetworkBuffer->pxEndPoint;

    if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
    {
        eReturned = eNDGetCacheEntry( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), &( pxEndPoint ) );
    }
    else
    {
        pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
        ulIPAddress = pxNetworkBuffer->xIPAddress.xIP_IPv4;

        eReturned = eARPGetCacheEntry( &( ulIPAddress ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), &( pxEndPoint ) );
    }

    if( pxNetworkBuffer->pxEndPoint == NULL )
    {
        pxNetworkBuffer->pxEndPoint = pxEndPoint;
    }

    return eReturned;
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
        pxNetworkBuffer->pxEndPoint = FreeRTOS_FindEndPointOnNetMask( pxNetworkBuffer->xIPAddress.xIP_IPv4, 10 );

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
    uint32_t ulIPAddress;


    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
    {
        FreeRTOS_printf( ( "Looking up %pip with%s end-point\n",
                           pxNetworkBuffer->xIPv6Address.ucBytes,
                           ( pxNetworkBuffer->pxEndPoint != NULL ) ? "" : "out" ) );

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
        ulIPAddress = pxNetworkBuffer->xIPAddress.xIP_IPv4;

        FreeRTOS_printf( ( "Looking up %xip with%s end-point\n",
                           ( unsigned ) FreeRTOS_ntohl( pxNetworkBuffer->xIPAddress.xIP_IPv4 ),
                           ( pxNetworkBuffer->pxEndPoint != NULL ) ? "" : "out" ) );

        /* Add an entry to the ARP table with a null hardware address.
         * This allows the ARP timer to know that an ARP reply is
         * outstanding, and perform retransmissions if necessary. */
        vARPRefreshCacheEntry( NULL, ulIPAddress, NULL );

        /* Generate an ARP for the required IP address. */
        iptracePACKET_DROPPED_TO_GENERATE_ARP( pxNetworkBuffer->xIPAddress.xIP_IPv4 );

        /* 'ulIPAddress' might have become the address of the Gateway.
         * Find the route again. */

        pxNetworkBuffer->pxEndPoint = FreeRTOS_FindEndPointOnNetMask( pxNetworkBuffer->xIPAddress.xIP_IPv4, 11 );

        if( pxNetworkBuffer->pxEndPoint == NULL )
        {
            eReturned = eCantSendPacket;
        }
        else
        {
            pxNetworkBuffer->xIPAddress.xIP_IPv4 = ulIPAddress;
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
void vProcessGeneratedUDPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;
    eARPLookupResult_t eReturned;
    uint32_t ulIPAddress;
    size_t uxPayloadSize;
    /* memcpy() helper variables for MISRA Rule 21.15 compliance*/
    const void * pvCopySource;
    void * pvCopyDest;
    BaseType_t xLostBuffer = pdFALSE;

    /* Map the UDP packet onto the start of the frame. */

    /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
    /* coverity[misra_c_2012_rule_11_3_violation] */
    pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
    {
        eReturned = vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );
    }
    else
    {
        pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
        eReturned = vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );
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
BaseType_t xProcessReceivedUDPPacket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                      uint16_t usPort,
                                      BaseType_t * pxIsWaitingForARPResolution )
{
    BaseType_t xReturn = pdPASS;
    FreeRTOS_Socket_t * pxSocket;

    configASSERT( pxNetworkBuffer != NULL );
    configASSERT( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Map the ethernet buffer to the UDPPacket_t struct for easy access to the fields. */

    /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
    /* coverity[misra_c_2012_rule_11_3_violation] */
    const UDPPacket_t * pxUDPPacket = ( ( const UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

    /* Caller must check for minimum packet size. */
    pxSocket = pxUDPSocketLookup( usPort );

    if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE )
    {
        xProcessReceivedUDPPacket_IPv4( pxNetworkBuffer,
                                        usPort, pxIsWaitingForARPResolution );
    }

    if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
    {
        xProcessReceivedUDPPacket_IPv6( pxNetworkBuffer,
                                        usPort, pxIsWaitingForARPResolution );
    }

    return xReturn;
}
/*-----------------------------------------------------------*/
