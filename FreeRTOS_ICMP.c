/*
 * FreeRTOS+TCP V2.3.4
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file FreeRTOS_ICMP.c
 * @brief Implements the Internet Control Message Protocol for the FreeRTOS+TCP network stack.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"

/* ICMP protocol definitions. */
#define ipICMP_ECHO_REQUEST                 ( ( uint8_t ) 8 ) /**< ICMP echo request. */
#define ipICMP_ECHO_REPLY                   ( ( uint8_t ) 0 ) /**< ICMP echo reply. */

#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

/*
 * Process incoming ICMP packets.
 */
    eFrameProcessingResult_t prvProcessICMPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );
#endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */

/*
 * Turns around an incoming ping request to convert it into a ping reply.
 */
#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 )
    static eFrameProcessingResult_t prvProcessICMPEchoRequest( ICMPPacket_t * const pxICMPPacket,
                                                               NetworkBufferDescriptor_t * const pxNetworkBuffer );
#endif /* ipconfigREPLY_TO_INCOMING_PINGS */

/*
 * Processes incoming ping replies.  The application callback function
 * vApplicationPingReplyHook() is called with the results.
 */
#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
    static void prvProcessICMPEchoReply( ICMPPacket_t * const pxICMPPacket );
#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

/**
 * @brief Cast a given pointer to ICMPHeader_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( ICMPHeader_t )
{
    return ( ICMPHeader_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to ICMPHeader_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( ICMPHeader_t )
{
    return ( const ICMPHeader_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

/**
 * @brief Process an ICMP packet. Only echo requests and echo replies are recognised and handled.
 *
 * @param[in,out] pxICMPPacket: The IP packet that contains the ICMP message.
 *
 * @return eReleaseBuffer when the message buffer should be released, or eReturnEthernetFrame
 *                        when the packet should be returned.
 */
    static eFrameProcessingResult_t prvProcessICMPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
    {
        eFrameProcessingResult_t eReturn = eReleaseBuffer;

        iptraceICMP_PACKET_RECEIVED();

        configASSERT( pxNetworkBuffer->xDataLength >= sizeof( ICMPPacket_t ) );

        if( pxNetworkBuffer->xDataLength >= sizeof( ICMPPacket_t ) )
        {
            /* Map the buffer onto a ICMP-Packet struct to easily access the
             * fields of ICMP packet. */
            ICMPPacket_t * pxICMPPacket = ipCAST_PTR_TO_TYPE_PTR( ICMPPacket_t, pxNetworkBuffer->pucEthernetBuffer );

            switch( pxICMPPacket->xICMPHeader.ucTypeOfMessage )
            {
                case ipICMP_ECHO_REQUEST:
                    #if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 )
                        {
                            eReturn = prvProcessICMPEchoRequest( pxICMPPacket, pxNetworkBuffer );
                        }
                    #endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) */
                    break;

                case ipICMP_ECHO_REPLY:
                    #if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
                        {
                            prvProcessICMPEchoReply( pxICMPPacket );
                        }
                    #endif /* ipconfigSUPPORT_OUTGOING_PINGS */
                    break;

                default:
                    /* Only ICMP echo packets are handled. */
                    break;
            }
        }

        return eReturn;
    }

#endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 )

/**
 * @brief Process an ICMP echo request.
 *
 * @param[in,out] pxICMPPacket: The IP packet that contains the ICMP message.
 */
    static eFrameProcessingResult_t prvProcessICMPEchoRequest( ICMPPacket_t * const pxICMPPacket,
                                                               NetworkBufferDescriptor_t * const pxNetworkBuffer )
    {
        ICMPHeader_t * pxICMPHeader;
        IPHeader_t * pxIPHeader;

        pxICMPHeader = &( pxICMPPacket->xICMPHeader );
        pxIPHeader = &( pxICMPPacket->xIPHeader );

        /* HT:endian: changed back */
        iptraceSENDING_PING_REPLY( pxIPHeader->ulSourceIPAddress );

        /* The checksum can be checked here - but a ping reply should be
         * returned even if the checksum is incorrect so the other end can
         * tell that the ping was received - even if the ping reply contains
         * invalid data. */
        pxICMPHeader->ucTypeOfMessage = ( uint8_t ) ipICMP_ECHO_REPLY;
        pxIPHeader->ulDestinationIPAddress = pxIPHeader->ulSourceIPAddress;
        pxIPHeader->ulSourceIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
        /* Update the TTL field. */
        pxIPHeader->ucTimeToLive = ipconfigICMP_TIME_TO_LIVE;

        /* The stack doesn't support fragments, so the fragment offset field must always be zero.
         * The header was never memset to zero, so set both the fragment offset and fragmentation flags in one go.
         */
        #if ( ipconfigFORCE_IP_DONT_FRAGMENT != 0 )
            pxIPHeader->usFragmentOffset = ipFRAGMENT_FLAGS_DONT_FRAGMENT;
        #else
            pxIPHeader->usFragmentOffset = 0U;
        #endif

        #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
            {
                /* calculate the IP header checksum, in case the driver won't do that. */
                pxIPHeader->usHeaderChecksum = 0x00U;
                pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
                pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );

                /* calculate the ICMP checksum for an outgoing packet. */
                ( void ) usGenerateProtocolChecksum( ( uint8_t * ) pxICMPPacket, pxNetworkBuffer->xDataLength, pdTRUE );
            }
        #else
            {
                /* Many EMAC peripherals will only calculate the ICMP checksum
                 * correctly if the field is nulled beforehand. */
                pxICMPHeader->usChecksum = 0U;
            }
        #endif /* if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 ) */

        return eReturnEthernetFrame;
    }

#endif /* ipconfigREPLY_TO_INCOMING_PINGS == 1 */
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

/**
 * @brief Process an ICMP echo reply.
 *
 * @param[in] pxICMPPacket: The IP packet that contains the ICMP message.
 */
    static void prvProcessICMPEchoReply( ICMPPacket_t * const pxICMPPacket )
    {
        ePingReplyStatus_t eStatus = eSuccess;
        uint16_t usDataLength, usCount;
        uint8_t * pucByte;

        /* Find the total length of the IP packet. */
        usDataLength = pxICMPPacket->xIPHeader.usLength;
        usDataLength = FreeRTOS_ntohs( usDataLength );

        /* Remove the length of the IP headers to obtain the length of the ICMP
         * message itself. */
        usDataLength = ( uint16_t ) ( ( ( uint32_t ) usDataLength ) - ipSIZE_OF_IPv4_HEADER );

        /* Remove the length of the ICMP header, to obtain the length of
         * data contained in the ping. */
        usDataLength = ( uint16_t ) ( ( ( uint32_t ) usDataLength ) - ipSIZE_OF_ICMP_HEADER );

        /* Checksum has already been checked before in prvProcessIPPacket */

        /* Find the first byte of the data within the ICMP packet. */
        pucByte = ( uint8_t * ) pxICMPPacket;
        pucByte = &( pucByte[ sizeof( ICMPPacket_t ) ] );

        /* Check each byte. */
        for( usCount = 0; usCount < usDataLength; usCount++ )
        {
            if( *pucByte != ( uint8_t ) ipECHO_DATA_FILL_BYTE )
            {
                eStatus = eInvalidData;
                break;
            }

            pucByte++;
        }

        /* Call back into the application to pass it the result. */
        vApplicationPingReplyHook( eStatus, pxICMPPacket->xICMPHeader.usIdentifier );
    }

#endif /* if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */
/*-----------------------------------------------------------*/

