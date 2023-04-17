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
 * @file FreeRTOS_IPv6_Utils.c
 * @brief Implements the basic functionality for the FreeRTOS+TCP network stack functions for IPv6.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"

/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
#if( ipconfigUSE_IPv6 != 0 )
/* *INDENT-ON* */

/**
 * @brief Set multicast MAC address.
 *
 * @param[in] pxAddress IPv6 address.
 * @param[out] pxMACAddress Pointer to MAC address.
 */
void vSetMultiCastIPv6MacAddress( const IPv6_Address_t * pxAddress,
                                  MACAddress_t * pxMACAddress )
{
    pxMACAddress->ucBytes[ 0 ] = 0x33U;
    pxMACAddress->ucBytes[ 1 ] = 0x33U;
    pxMACAddress->ucBytes[ 2 ] = pxAddress->ucBytes[ 12 ];
    pxMACAddress->ucBytes[ 3 ] = pxAddress->ucBytes[ 13 ];
    pxMACAddress->ucBytes[ 4 ] = pxAddress->ucBytes[ 14 ];
    pxMACAddress->ucBytes[ 5 ] = pxAddress->ucBytes[ 15 ];
}
/*-----------------------------------------------------------*/

/** @brief Do the first IPv6 length checks at the IP-header level.
 * @param[in] pucEthernetBuffer The buffer containing the packet.
 * @param[in] uxBufferLength The number of bytes to be sent or received.
 * @param[in] pxSet A struct describing this packet.
 *
 * @return Non-zero in case of an error.
 */
BaseType_t prvChecksumIPv6Checks( uint8_t * pucEthernetBuffer,
                                  size_t uxBufferLength,
                                  struct xPacketSummary * pxSet )
{
    BaseType_t xReturn = 0;

    pxSet->xIsIPv6 = pdTRUE;

    pxSet->uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;

    /* Check for minimum packet size: ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER (54 bytes) */
    if( uxBufferLength < sizeof( IPPacket_IPv6_t ) )
    {
        pxSet->usChecksum = ipINVALID_LENGTH;
        xReturn = 1;
    }
    else
    {
        pxSet->ucProtocol = pxSet->pxIPPacket_IPv6->ucNextHeader;
        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        pxSet->pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] ) );
        pxSet->usPayloadLength = FreeRTOS_ntohs( pxSet->pxIPPacket_IPv6->usPayloadLength );
        /* For IPv6, the number of bytes in the protocol is indicated. */
        pxSet->usProtocolBytes = pxSet->usPayloadLength;

        size_t uxNeeded = ( size_t ) pxSet->usPayloadLength;
        uxNeeded += ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;

        if( uxBufferLength < uxNeeded )
        {
            /* The packet does not contain a complete IPv6 packet. */
            pxSet->usChecksum = ipINVALID_LENGTH;
            xReturn = 2;
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Check the buffer lengths of an ICMPv6 packet.
 * @param[in] uxBufferLength The total length of the packet.
 * @param[in] pxSet A struct describing this packet.
 * @return Non-zero in case of an error.
 */
BaseType_t prvChecksumICMPv6Checks( size_t uxBufferLength,
                                    struct xPacketSummary * pxSet )
{
    BaseType_t xReturn = 0;
    size_t xICMPLength;

    switch( pxSet->pxProtocolHeaders->xICMPHeaderIPv6.ucTypeOfMessage )
    {
        case ipICMP_PING_REQUEST_IPv6:
        case ipICMP_PING_REPLY_IPv6:
            xICMPLength = sizeof( ICMPEcho_IPv6_t );
            break;

        case ipICMP_ROUTER_SOLICITATION_IPv6:
            xICMPLength = sizeof( ICMPRouterSolicitation_IPv6_t );
            break;

        default:
            xICMPLength = ipSIZE_OF_ICMPv6_HEADER;
            break;
    }

    if( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + pxSet->uxIPHeaderLength + xICMPLength ) )
    {
        pxSet->usChecksum = ipINVALID_LENGTH;
        xReturn = 10;
    }

    if( xReturn == 0 )
    {
        pxSet->uxProtocolHeaderLength = xICMPLength;
        #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
            {
                pxSet->pcType = "ICMP_IPv6";
            }
        #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
#endif /* ( ipconfigUSE_IPv6 != 0 ) */
/* *INDENT-ON* */
