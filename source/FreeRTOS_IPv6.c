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
 * @file FreeRTOS_IPv6.c
 * @brief Implements the basic functionality for the FreeRTOS+TCP network stack.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"

/* *INDENT-OFF* */
#if( ipconfigUSE_IPv6 != 0 )
/* *INDENT-ON* */

/**
 * This variable is initialized by the system to contain the wildcard IPv6 address.
 */
const struct xIPv6_Address in6addr_any = { 0 };

/**
 * This variable is initialized by the system to contain the loopback IPv6 address.
 */
const struct xIPv6_Address in6addr_loopback = { { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 } };

/**
 * @brief Check whether this IPv6 address is a multicast address or not.
 *
 * @param[in] pxIPAddress: The IP address to be checked.
 *
 * @return Returns pdTRUE if pxIPAddress is a multicast address, pdFALSE if not .
 */
BaseType_t xIsIPv6Multicast( const IPv6_Address_t * pxIPAddress )
{
    BaseType_t xReturn;

    if( pxIPAddress->ucBytes[ 0 ] == 0xffU )
    {
        xReturn = pdTRUE;
    }
    else
    {
        xReturn = pdFALSE;
    }

    return xReturn;
}


/*-----------------------------------------------------------*/

/**
 * @brief Compares 2 IPv6 addresses and checks if the one
 * on the left can handle the one on right. Note that 'xCompareIPv6_Address' will also check if 'pxRight' is
 * the special unicast address: ff02::1:ffnn:nnnn, where nn:nnnn are
 * the last 3 bytes of the IPv6 address.
 *
 * @param[in] pxLeft: First IP address.
 * @param[in] pxRight: Second IP address.
 * @param[in] uxPrefixLength: The IP address prefix length in bits.
 *
 * @return Returns 0 if it can handle it, else non zero .
 */
BaseType_t xCompareIPv6_Address( const IPv6_Address_t * pxLeft,
                                 const IPv6_Address_t * pxRight,
                                 size_t uxPrefixLength )
{
    BaseType_t xResult;

    /* 0    2    4    6    8    10   12   14 */
    /* ff02:0000:0000:0000:0000:0001:ff66:4a81 */
    if( ( pxRight->ucBytes[ 0 ] == 0xffU ) &&
        ( pxRight->ucBytes[ 1 ] == 0x02U ) &&
        ( pxRight->ucBytes[ 12 ] == 0xffU ) )
    {
        /* This is an LLMNR address. */
        xResult = memcmp( &( pxLeft->ucBytes[ 13 ] ), &( pxRight->ucBytes[ 13 ] ), 3 );
    }
    else
    if( ( pxRight->ucBytes[ 0 ] == 0xffU ) &&
        ( pxRight->ucBytes[ 1 ] == 0x02U ) )
    {
        /* FF02::1 is all node address to reach out all nodes in the same link. */
        xResult = 0;
    }
    else
    if( ( pxRight->ucBytes[ 0 ] == 0xfeU ) &&
        ( pxRight->ucBytes[ 1 ] == 0x80U ) &&
        ( pxLeft->ucBytes[ 0 ] == 0xfeU ) &&
        ( pxLeft->ucBytes[ 1 ] == 0x80U ) )
    {
        /* Both are local addresses. */
        xResult = 0;
    }
    else
    {
        if( uxPrefixLength == 0U )
        {
            xResult = 0;
        }
        else if( uxPrefixLength == ( 8U * ipSIZE_OF_IPv6_ADDRESS ) )
        {
            xResult = memcmp( pxLeft->ucBytes, pxRight->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
        }
        else
        {
            size_t uxLength = uxPrefixLength / 8U;

            xResult = 0;

            if( uxLength > 0U )
            {
                xResult = memcmp( pxLeft->ucBytes, pxRight->ucBytes, uxLength );
            }

            if( ( xResult == 0 ) && ( ( uxPrefixLength % 8U ) != 0U ) )
            {
                /* One byte has both a network- and a host-address. */
                size_t uxBits = uxPrefixLength % 8U;
                size_t uxHostLen = 8U - uxBits;
                uint32_t uxHostMask = ( ( ( uint32_t ) 1U ) << uxHostLen ) - 1U;
                uint8_t ucNetMask = ( uint8_t ) ~( uxHostMask );

                if( ( pxLeft->ucBytes[ uxLength ] & ucNetMask ) != ( pxRight->ucBytes[ uxLength ] & ucNetMask ) )
                {
                    xResult = 1;
                }
            }
        }
    }

    return xResult;
}


/*-----------------------------------------------------------*/


/**
 * @brief Check whether this IPv6 packet is to be allowed or to be dropped.
 *
 * @param[in] pxIPv6Header: The IP packet under consideration.
 * @param[in] pxNetworkBuffer: The whole network buffer.
 * @param[in] uxHeaderLength: The length of the header.
 *
 * @return Whether the packet should be processed or dropped.
 */
eFrameProcessingResult_t prvAllowIPPacketIPv6( const IPHeader_IPv6_t * const pxIPv6Header,
                                               const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                               UBaseType_t uxHeaderLength )
{
    eFrameProcessingResult_t eReturn;

    #if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 0 )
        {
            /* In systems with a very small amount of RAM, it might be advantageous
             * to have incoming messages checked earlier, by the network card driver.
             * This method may decrease the usage of sparse network buffers. */
            const IPv6_Address_t * pxDestinationIPAddress = &( pxIPv6Header->xDestinationAddress );

            /* Is the packet for this IP address? */
            if( ( pxNetworkBuffer->pxEndPoint != NULL ) ||
                /* Is it the multicast address FF00::/8 ? */
                ( xIsIPv6Multicast( pxDestinationIPAddress ) != pdFALSE ) ||
                /* Or (during DHCP negotiation) we have no IP-address yet? */
                ( FreeRTOS_IsNetworkUp() == 0 ) )
            {
                /* Packet is not for this node, or the network is still not up,
                 * release it */
                eReturn = eProcessBuffer;
            }
            else
            {
                eReturn = eReleaseBuffer;
                FreeRTOS_printf( ( "prvAllowIPPacketIPv6: drop %pip (from %pip)\n", pxDestinationIPAddress->ucBytes, pxIPv6Header->xSourceAddress.ucBytes ) );
            }
        }
    #else /* if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 0 ) */
        {
            ( void ) pxIPv6Header;
            /* The packet has been checked by the network interface. */
            eReturn = eProcessBuffer;
        }
    #endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */

    #if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 )
        {
            /* Some drivers of NIC's with checksum-offloading will enable the above
             * define, so that the checksum won't be checked again here */
            if( eReturn == eProcessBuffer )
            {
                /* MISRA Ref 11.3.1 [Misaligned access] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                /* coverity[misra_c_2012_rule_11_3_violation] */
                const IPPacket_t * pxIPPacket = ( ( const IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
                const NetworkEndPoint_t * pxEndPoint = FreeRTOS_FindEndPointOnMAC( &( pxIPPacket->xEthernetHeader.xSourceAddress ), NULL );

                /* IPv6 does not have a separate checksum in the IP-header */
                /* Is the upper-layer checksum (TCP/UDP/ICMP) correct? */
                /* Do not check the checksum of loop-back messages. */
                if( pxEndPoint == NULL )
                {
                    if( usGenerateProtocolChecksum( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE ) != ipCORRECT_CRC )
                    {
                        /* Protocol checksum not accepted. */
                        eReturn = eReleaseBuffer;
                    }
                }
            }
        }
    #else /* if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 ) */
        {
            /* to avoid warning unused parameters */
            ( void ) pxNetworkBuffer;
        }
    #endif /* ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 */
    ( void ) uxHeaderLength;

    return eReturn;
}

/*-----------------------------------------------------------*/

/**
 * @brief Check extension header and next header and return their order.
 *
 * @param[in] ucProtocol: Extension header ID.
 * @param[in] ucNextHeader: Next header ID.
 *
 * @return Extension header order in the packet.
 */
BaseType_t xGetExtensionOrder( uint8_t ucProtocol,
                               uint8_t ucNextHeader )
{
    BaseType_t xReturn;

    switch( ucProtocol )
    {
        case ipIPv6_EXT_HEADER_HOP_BY_HOP:
            xReturn = 1;
            break;

        case ipIPv6_EXT_HEADER_DESTINATION_OPTIONS:
            xReturn = 7;

            if( ucNextHeader == ipIPv6_EXT_HEADER_ROUTING_HEADER )
            {
                xReturn = 2;
            }

            break;

        case ipIPv6_EXT_HEADER_ROUTING_HEADER:
            xReturn = 3;
            break;

        case ipIPv6_EXT_HEADER_FRAGMENT_HEADER:
            xReturn = 4;
            break;

        case ipIPv6_EXT_HEADER_AUTHEN_HEADER:
            xReturn = 5;
            break;

        case ipIPv6_EXT_HEADER_SECURE_PAYLOAD:
            xReturn = 6;
            break;

        /* Destination options may follow here in case there are no routing options. */
        case ipIPv6_EXT_HEADER_MOBILITY_HEADER:
            xReturn = 8;
            break;

        default:
            xReturn = -1;
            break;
    }

    return xReturn;
}


/*-----------------------------------------------------------*/



/**
 * @brief Handle the IPv6 extension headers.
 *
 * @param[in,out] pxNetworkBuffer: The received packet that contains IPv6 extension headers.
 * @param[in] xDoRemove: Function removes the extension header if xDoRemove is set to pdTRUE.
 *
 * @return eProcessBuffer in case the options are removed successfully, otherwise
 *         eReleaseBuffer.
 */
eFrameProcessingResult_t eHandleIPv6ExtensionHeaders( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                      BaseType_t xDoRemove )
{
    eFrameProcessingResult_t eResult = eReleaseBuffer;
    const size_t uxMaxLength = pxNetworkBuffer->xDataLength;
    const uint8_t * pucSource = pxNetworkBuffer->pucEthernetBuffer;
    /* MISRA Ref 11.3.1 [Misaligned access] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
    /* coverity[misra_c_2012_rule_11_3_violation] */
    IPPacket_IPv6_t * pxIPPacket_IPv6 = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    size_t uxIndex = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;
    size_t uxHopSize = 0U;
    size_t xMoveLen = 0U;
    size_t uxRemovedBytes = 0U;
    uint8_t ucCurrentHeader = pxIPPacket_IPv6->xIPHeader.ucNextHeader;
    uint8_t ucNextHeader = 0U;
    BaseType_t xNextOrder = 0;
    BaseType_t xExtHeaderCount = 0;

    while( ( uxIndex + 8U ) < uxMaxLength )
    {
        BaseType_t xCurrentOrder;
        ucNextHeader = pucSource[ uxIndex ];

        xCurrentOrder = xGetExtensionOrder( ucCurrentHeader, ucNextHeader );

        /* Read the length expressed in number of octets. */
        uxHopSize = ( size_t ) pucSource[ uxIndex + 1U ];
        /* And multiply by 8 and add the minimum size of 8. */
        uxHopSize = ( uxHopSize * 8U ) + 8U;

        if( ( uxIndex + uxHopSize ) >= uxMaxLength )
        {
            uxIndex = uxMaxLength;
            break;
        }

        uxIndex = uxIndex + uxHopSize;

        if( ( ucNextHeader == ipPROTOCOL_TCP ) ||
            ( ucNextHeader == ipPROTOCOL_UDP ) ||
            ( ucNextHeader == ipPROTOCOL_ICMP_IPv6 ) )
        {
            FreeRTOS_debug_printf( ( "Stop at header %u\n", ucNextHeader ) );
            break;
        }

        xNextOrder = xGetExtensionOrder( ucNextHeader, pucSource[ uxIndex ] );

        FreeRTOS_debug_printf( ( "Going from header %2u (%d) to %2u (%d)\n",
                                 ucCurrentHeader,
                                 ( int ) xCurrentOrder,
                                 ucNextHeader,
                                 ( int ) xNextOrder ) );

        xExtHeaderCount += 1;

        /*
        * IPv6 nodes must accept and attempt to process extension headers in
        * any order and occurring any number of times in the same packet,
        * except for the Hop-by-Hop Options header which is restricted to
        * appear immediately after an IPv6 header only. Outlined
        * by RFC 2460 section 4.1  Extension Header Order.
        */
        if ( xExtHeaderCount > 1 && xCurrentOrder == 1 ) /* ipIPv6_EXT_HEADER_HOP_BY_HOP */
        {
            FreeRTOS_printf( ( "Wrong order. Hop-by-Hop Options header restricted to appear immediately after an IPv6 header\n" ) );
            uxIndex = uxMaxLength;
            break;
        }

        ucCurrentHeader = ucNextHeader;
    }

    if( uxIndex < uxMaxLength )
    {
        uint8_t * pucTo;
        const uint8_t * pucFrom;
        uint16_t usPayloadLength = FreeRTOS_ntohs( pxIPPacket_IPv6->xIPHeader.usPayloadLength );

        uxRemovedBytes = uxIndex - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

        if( uxRemovedBytes >= ( size_t ) usPayloadLength )
        {
            /* Can not remove more bytes than the payload length. */
        }
        else if( xDoRemove == pdTRUE )
        {
            pxIPPacket_IPv6->xIPHeader.ucNextHeader = ucNextHeader;
            pucTo = &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] );
            pucFrom = &( pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] );
            xMoveLen = uxMaxLength - uxIndex;
            ( void ) memmove( pucTo, pucFrom, xMoveLen );
            pxNetworkBuffer->xDataLength -= uxRemovedBytes;

            usPayloadLength -= ( uint16_t ) uxRemovedBytes;
            pxIPPacket_IPv6->xIPHeader.usPayloadLength = FreeRTOS_htons( usPayloadLength );
            eResult = eProcessBuffer;
        }
        else
        {
            /* xDoRemove is false, so the function is not supposed to
             * remove extension headers. */
        }
    }

    FreeRTOS_printf( ( "Extension headers : %s Truncated %u bytes. Removed %u, Payload %u xDataLength now %u\n",
                       ( eResult == eProcessBuffer ) ? "good" : "bad",
                       xMoveLen,
                       uxRemovedBytes,
                       FreeRTOS_ntohs( pxIPPacket_IPv6->xIPHeader.usPayloadLength ),
                       pxNetworkBuffer->xDataLength ) );
    return eResult;
}


/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
#endif /* ( ipconfigUSE_IPv6 != 0 ) */
/* *INDENT-ON* */
