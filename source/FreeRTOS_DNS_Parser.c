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
 * https://github.com/FreeRTOS
 * https://www.FreeRTOS.org
 */

/**
 * @file FreeRTOS_DNS_Parser.c
 * @brief Implements the DNS message parser
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

#include "FreeRTOS_DNS_Globals.h"
#include "FreeRTOS_DNS_Parser.h"
#include "FreeRTOS_DNS_Cache.h"
#include "FreeRTOS_DNS_Callback.h"

#include "NetworkBufferManagement.h"

#include <string.h>

#if ( ipconfigUSE_DNS != 0 )

    static BaseType_t prvParseDNS_ReadQuestions( ParseSet_t * pxSet );

/** @brief Parse the array of answers that are received from a DNS server. */
    static BaseType_t prvParseDNS_ReadAnswers( ParseSet_t * pxSet,
                                               struct freertos_addrinfo ** ppxAddressInfo );

    #if ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) )

/** @brief An LLMNR or an mDNS lookup of a host was received. The application code
 *         is consulted by calling xApplicationDNSQueryHook(), which returns true
 *         in case the driver should reply to the lookup. */
        static void prvParseDNS_HandleLLMNRRequest( ParseSet_t * pxSet,
                                                    uint8_t * pucUDPPayloadBuffer );
    #endif /* #if ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) ) */

/*
 * The NBNS and the LLMNR protocol share this reply function.
 */
    #if ( ( ipconfigUSE_NBNS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) )
        static void prvReplyDNSMessage( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                        BaseType_t lNetLength );
    #endif /*
            */

    static void prvParseDNS_StoreAnswer( ParseSet_t * pxSet,
                                         IPv46_Address_t * pxIP_Address,
                                         struct freertos_addrinfo ** ppxAddressInfo );

    #if ( ( ipconfigUSE_NBNS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) )
        static NetworkEndPoint_t * prvFindEndPointOnNetMask( NetworkBufferDescriptor_t * pxNetworkBuffer );
    #endif
/*-----------------------------------------------------------*/

/**
 * @brief Parse the array of questions that are received from a DNS server.
 * @param[in,out] pxSet: a set of variables that are shared among the helper functions.
 * @return pdTRUE when parsing was successful, otherwise pdFALSE.
 */
    static BaseType_t prvParseDNS_ReadQuestions( ParseSet_t * pxSet )
    {
        size_t x;
        size_t uxResult;
        BaseType_t xReturn = pdTRUE;

        for( x = 0U; x < pxSet->usQuestions; x++ )
        {
            #if ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) )
                {
                    if( x == 0U )
                    {
                        pxSet->pcRequestedName = ( char * ) pxSet->pucByte;
                    }
                }
            #endif /* ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) ) */

            {
                uxResult = DNS_ReadNameField( pxSet,
                                              sizeof( pxSet->pcName ) );

                /* Check for a malformed response. */
                if( uxResult == 0U )
                {
                    xReturn = pdFALSE;
                    break;
                }

                pxSet->pucByte = &( pxSet->pucByte[ uxResult ] );
                pxSet->uxSourceBytesRemaining -= uxResult;
            }

            /* Check the remaining buffer size. */
            if( pxSet->uxSourceBytesRemaining >= sizeof( uint32_t ) )
            {
                #if ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) )
                    {
                        /* usChar2u16 returns value in host endianness. */
                        pxSet->usType = usChar2u16( pxSet->pucByte );
                        pxSet->usClass = usChar2u16( &( pxSet->pucByte[ 2 ] ) );
                    }
                #endif /* ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) ) */

                /* Skip the type and class fields. */
                pxSet->pucByte = &( pxSet->pucByte[ sizeof( uint32_t ) ] );
                pxSet->uxSourceBytesRemaining -= sizeof( uint32_t );
            }
            else
            {
                xReturn = pdFALSE;
                break;
            }
        } /* for( x = 0U; x < pxSet->usQuestions; x++ ) */

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Parse the array of answers that are received from a DNS server.
 * @param[in] pxSet: a set of variables that are shared among the helper functions.
 * @param[out] ppxAddressInfo: a linked list storing the DNS answers.
 * @return pdTRUE when successful, otherwise pdFALSE.
 */
    static BaseType_t prvParseDNS_ReadAnswers( ParseSet_t * pxSet,
                                               struct freertos_addrinfo ** ppxAddressInfo )
    {
        const uint16_t usCount = ( uint16_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
        size_t x;
        size_t uxResult;
        BaseType_t xReturn = pdTRUE;
        const DNSAnswerRecord_t * pxDNSAnswerRecord;
        IPv46_Address_t xIP_Address;

        for( x = 0U; x < pxSet->pxDNSMessageHeader->usAnswers; x++ )
        {
            BaseType_t xDoAccept = pdFALSE;

            if( pxSet->usNumARecordsStored >= usCount )
            {
                /* Only count ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY number of records. */
                break;
            }

            uxResult = DNS_ReadNameField( pxSet,
                                          sizeof( pxSet->pcName ) );

            /* Check for a malformed response. */
            if( uxResult == 0U )
            {
                xReturn = pdFALSE;
                break;
            }

            pxSet->pucByte = &( pxSet->pucByte[ uxResult ] );
            pxSet->uxSourceBytesRemaining -= uxResult;

            /* Is there enough data for an IPv4 A record answer and, if so,
             * is this an A record? */
            if( pxSet->uxSourceBytesRemaining < sizeof( uint16_t ) )
            {
                xReturn = pdFALSE;
                break;
            }

            pxSet->usType = usChar2u16( pxSet->pucByte );

            #if ( ipconfigUSE_IPv6 != 0 )
                if( pxSet->usType == ( uint16_t ) dnsTYPE_AAAA_HOST )
                {
                    pxSet->uxAddressLength = ipSIZE_OF_IPv6_ADDRESS;

                    if( pxSet->uxSourceBytesRemaining >= ( sizeof( DNSAnswerRecord_t ) + pxSet->uxAddressLength ) )
                    {
                        xDoAccept = pdTRUE;
                    }
                }
                else
            #endif /* #if( ipconfigUSE_IPv6 != 0 ) */

            if( pxSet->usType == ( uint16_t ) dnsTYPE_A_HOST )
            {
                /* uxAddressLength is already ipSIZE_OF_IPv4_ADDRESS. */
                if( pxSet->uxSourceBytesRemaining >= ( sizeof( DNSAnswerRecord_t ) + pxSet->uxAddressLength ) )
                {
                    xDoAccept = pdTRUE;
                }
            }
            else
            {
                /* A unknown type is received that is not handled. xDoAccept is pdFALSE. */
            }

            if( xDoAccept == pdTRUE )
            {
                /* This is the required record type and is of sufficient size. */

                /* Mapping pucByte to a DNSAnswerRecord allows easy access of the
                 * fields of the structure. */
                pxDNSAnswerRecord = ( ( DNSAnswerRecord_t * ) pxSet->pucByte );

                /* Sanity check the data length of an IPv4 answer. */
                if( FreeRTOS_ntohs( pxDNSAnswerRecord->usDataLength ) == ( uint16_t ) pxSet->uxAddressLength )
                {
                    prvParseDNS_StoreAnswer( pxSet, &( xIP_Address ), ppxAddressInfo );

                    #if ( ipconfigDNS_USE_CALLBACKS == 1 )
                        {
                            BaseType_t xCallbackResult;

                            #if ( ipconfigUSE_IPv6 != 0 )
                                {
                                    xCallbackResult = xDNSDoCallback( pxSet, ( ppxAddressInfo != NULL ) ? *( ppxAddressInfo ) : NULL );
                                }
                            #else
                                {
                                    xCallbackResult = xDNSDoCallback( pxSet, pxSet->ulIPAddress );
                                }
                            #endif /* ( ipconfigUSE_IPv6 != 0 ) */

                            /* See if any asynchronous call was made to FreeRTOS_gethostbyname_a() */
                            if( xCallbackResult != pdFALSE )
                            {
                                /* This device has requested this DNS look-up.
                                 * The result may be stored in the DNS cache. */
                                pxSet->xDoStore = pdTRUE;
                            }
                        }
                    #endif /* ipconfigDNS_USE_CALLBACKS == 1 */
                    #if ( ipconfigUSE_DNS_CACHE == 1 )
                        {
                            ParseDNS_StoreToCache( pxSet, &( xIP_Address ), pxDNSAnswerRecord->ulTTL );
                        }
                    #endif /* ipconfigUSE_DNS_CACHE */
                }
                else
                {
                    FreeRTOS_printf( ( "DNS sanity check failed: %u != %u\n",
                                       FreeRTOS_ntohs( pxDNSAnswerRecord->usDataLength ),
                                       ( unsigned ) pxSet->uxAddressLength ) );
                }

                pxSet->pucByte = &( pxSet->pucByte[ sizeof( DNSAnswerRecord_t ) + pxSet->uxAddressLength ] );
                pxSet->uxSourceBytesRemaining -= ( sizeof( DNSAnswerRecord_t ) + pxSet->uxAddressLength );
            }
            else if( pxSet->uxSourceBytesRemaining >= sizeof( DNSAnswerRecord_t ) )
            {
                uint16_t usDataLength;

                /* It's not an A record, so skip it. Get the header location
                 * and then jump over the header. */
                /* Cast the response to DNSAnswerRecord for easy access to fields of the DNS response. */
                pxDNSAnswerRecord = ( ( DNSAnswerRecord_t * ) pxSet->pucByte );

                pxSet->pucByte = &( pxSet->pucByte[ sizeof( DNSAnswerRecord_t ) ] );
                pxSet->uxSourceBytesRemaining -= sizeof( DNSAnswerRecord_t );

                /* Determine the length of the answer data from the header. */
                usDataLength = FreeRTOS_ntohs( pxDNSAnswerRecord->usDataLength );

                /* Jump over the answer. */
                if( pxSet->uxSourceBytesRemaining >= usDataLength )
                {
                    pxSet->pucByte = &( pxSet->pucByte[ usDataLength ] );
                    pxSet->uxSourceBytesRemaining -= usDataLength;
                }
                else
                {
                    /* Malformed response. */
                    xReturn = pdFALSE;
                    break;
                }
            }
            else
            {
                /* Do nothing */
            }
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

    #if ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) )

/** @brief An LLMNR lookup of a host was received. The application code is consulted
 *        by calling xApplicationDNSQueryHook(), which returns true in case the
 *        driver should reply to the lookup.
 * @param[in] pxSet: a set of variables that are shared among the helper functions.
 * @param[in] pucUDPPayloadBuffer: a pointer to the first byte of the LLMNR
 *            lookup message.
 */
        static void prvParseDNS_HandleLLMNRRequest( ParseSet_t * pxSet,
                                                    uint8_t * pucUDPPayloadBuffer )
        {
            /* If this is not a reply to our DNS request, it might an LLMNR
             * request. */
            NetworkBufferDescriptor_t * pxNetworkBuffer;
            NetworkEndPoint_t * pxEndPoint, xEndPoint;
            int16_t usLength;
            LLMNRAnswer_t * pxAnswer;
            size_t uxDataLength;
            size_t uxExtraLength;
            size_t uxOffsets[ 3 ];
            uint8_t * pucNewBuffer = NULL;

            do
            {
                #if ( ipconfigUSE_IPv6 == 0 )
                    if( pxSet->usType != dnsTYPE_A_HOST )
                    {
                        /* Only allow IPv4 format, because ipconfigUSE_IPv6 is not defined. */
                        break;
                    }
                #endif /* ipconfigUSE_IPv6 */

                pxNetworkBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pucUDPPayloadBuffer );

                /* This test could be replaced with a assert(). */
                if( pxNetworkBuffer == NULL )
                {
                    break;
                }

                if( pxNetworkBuffer->pxEndPoint == NULL )
                {
                    /* NetworkInterface is obliged to set 'pxEndPoint' in every received packet,
                     * but in case this has not be done, set it here. */

                    pxNetworkBuffer->pxEndPoint = prvFindEndPointOnNetMask( pxNetworkBuffer );
                    FreeRTOS_printf( ( "prvParseDNS_HandleLLMNRRequest: No pxEndPoint yet? Using %lxip\n",
                                       FreeRTOS_ntohl( pxNetworkBuffer->pxEndPoint ? pxNetworkBuffer->pxEndPoint->ipv4_settings.ulIPAddress : 0U ) ) );

                    if( pxNetworkBuffer->pxEndPoint == NULL )
                    {
                        break;
                    }
                }

                pxEndPoint = pxNetworkBuffer->pxEndPoint;

                /* Make a copy of the end-point because xApplicationDNSQueryHook() is allowed
                 * to write into it. */
                ( void ) memcpy( &( xEndPoint ), pxEndPoint, sizeof( xEndPoint ) );
                #if ( ipconfigUSE_IPv6 != 0 )
                    {
                        /*logging*/
                        FreeRTOS_printf( ( "prvParseDNS_HandleLLMNRRequest[%s]: type %04X\n", pxSet->pcName, pxSet->usType ) );

                        xEndPoint.usDNSType = pxSet->usType;
                    }
                #endif /* ( ipconfigUSE_IPv6 != 0 ) */

                if( xApplicationDNSQueryHook( &xEndPoint, pxSet->pcName ) == pdFALSE )
                {
                    /* This device doesn't have this name. */
                    break;
                }

                /* The IP-header size depends on what was received in 'pxNetworkBuffer'. */
                uxDataLength = ipSIZE_OF_ETH_HEADER + uxIPHeaderSizePacket( pxNetworkBuffer ) + sizeof( UDPHeader_t ) + pxNetworkBuffer->xDataLength;

                #if ( ipconfigUSE_IPv6 != 0 )
                    if( pxSet->usType == dnsTYPE_AAAA_HOST )
                    {
                        uxExtraLength = sizeof( LLMNRAnswer_t ) + ipSIZE_OF_IPv6_ADDRESS - sizeof( pxAnswer->ulIPAddress );
                    }
                    else
                #endif /* ( ipconfigUSE_IPv6 != 0 ) */
                {
                    uxExtraLength = sizeof( LLMNRAnswer_t );
                }

                /* The field xDataLength was set to the length of the UDP
                 * payload.  The answer (reply) will be longer than the
                 * request, so the packet must be resized. */
                uxOffsets[ 0 ] = ( size_t ) ( pucUDPPayloadBuffer - pxNetworkBuffer->pucEthernetBuffer );
                uxOffsets[ 1 ] = ( size_t ) ( pxSet->pcRequestedName - ( ( char * ) pxNetworkBuffer->pucEthernetBuffer ) );
                uxOffsets[ 2 ] = ( size_t ) ( pxSet->pucByte - pxNetworkBuffer->pucEthernetBuffer );

                /* Restore the 'xDataLength' field. */
                pxNetworkBuffer->xDataLength = uxDataLength;
                pxNetworkBuffer = pxResizeNetworkBufferWithDescriptor( pxNetworkBuffer, uxDataLength + uxExtraLength );

                if( pxNetworkBuffer == NULL )
                {
                    break;
                }

                pucNewBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ ( BaseType_t ) uxOffsets[ 0 ] ] );
                pxSet->pcRequestedName = ( char * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxOffsets[ 1 ] ] );
                pxSet->pucByte = &( pxNetworkBuffer->pucEthernetBuffer[ uxOffsets[ 2 ] ] );

                pxAnswer = ( ( LLMNRAnswer_t * ) pxSet->pucByte );

                /* Leave 'usIdentifier' and 'usQuestions' untouched. */

                vSetField16( pucNewBuffer, DNSMessage_t, usFlags, dnsLLMNR_FLAGS_IS_REPONSE ); /* Set the response flag */
                vSetField16( pucNewBuffer, DNSMessage_t, usAnswers, 1 );                       /* Provide a single answer */
                vSetField16( pucNewBuffer, DNSMessage_t, usAuthorityRRs, 0 );                  /* No authority */
                vSetField16( pucNewBuffer, DNSMessage_t, usAdditionalRRs, 0 );                 /* No additional info */

                pxAnswer->ucNameCode = dnsNAME_IS_OFFSET;
                pxAnswer->ucNameOffset = ( uint8_t ) ( pxSet->pcRequestedName - ( char * ) pucNewBuffer );

                vSetField16( pxSet->pucByte, LLMNRAnswer_t, usType, pxSet->usType ); /* Type A: host */
                vSetField16( pxSet->pucByte, LLMNRAnswer_t, usClass, dnsCLASS_IN );  /* 1: Class IN */
                vSetField32( pxSet->pucByte, LLMNRAnswer_t, ulTTL, dnsLLMNR_TTL_VALUE );

                #if ( ipconfigUSE_IPv6 != 0 )
                    if( pxSet->usType == dnsTYPE_AAAA_HOST )
                    {
                        size_t uxDistance;
                        NetworkEndPoint_t * pxReplyEndpoint = FreeRTOS_FirstEndPoint_IPv6( NULL );

                        if( pxReplyEndpoint == NULL )
                        {
                            break;
                        }

                        vSetField16( pxSet->pucByte, LLMNRAnswer_t, usDataLength, ipSIZE_OF_IPv6_ADDRESS );
                        ( void ) memcpy( &( pxAnswer->ulIPAddress ), pxReplyEndpoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                        uxDistance = ( size_t ) ( pxSet->pucByte - pucNewBuffer );
                        usLength = ipNUMERIC_CAST( int16_t, sizeof( *pxAnswer ) + uxDistance + ipSIZE_OF_IPv6_ADDRESS - sizeof( pxAnswer->ulIPAddress ) );
                    }
                    else
                #endif /* ( ipconfigUSE_IPv6 != 0 ) */
                {
                    /*logging*/
                    FreeRTOS_printf( ( "LLMNR return IPv4 %lxip\n", FreeRTOS_ntohl( xEndPoint.ipv4_settings.ulIPAddress ) ) );
                    vSetField16( pxSet->pucByte, LLMNRAnswer_t, usDataLength, ( uint16_t ) sizeof( pxAnswer->ulIPAddress ) );
                    vSetField32( pxSet->pucByte, LLMNRAnswer_t, ulIPAddress, FreeRTOS_ntohl( xEndPoint.ipv4_settings.ulIPAddress ) );

                    usLength = ( int16_t ) ( sizeof( *pxAnswer ) + ( size_t ) ( pxSet->pucByte - pucNewBuffer ) );
                }

                #if ( ipconfigUSE_IPv6 == 0 )
                    if( pxSet->usType == dnsTYPE_A_HOST )
                #else
                    if( ( pxSet->usType == dnsTYPE_A_HOST ) || ( pxSet->usType == dnsTYPE_AAAA_HOST ) )
                #endif /* ipconfigUSE_IPv6 */
                {
                    prvReplyDNSMessage( pxNetworkBuffer, usLength );
                }
            } while( ipFALSE_BOOL );
        }
    #endif /* ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) ) */
/*-----------------------------------------------------------*/

    #if ( ( ipconfigUSE_NBNS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) )

/**
 * @brief Find the best matching end-point given a reply that was received.
 * @param[in] pxNetworkBuffer: The Ethernet packet that was received.
 * @return An end-point.
 */
        static NetworkEndPoint_t * prvFindEndPointOnNetMask( NetworkBufferDescriptor_t * pxNetworkBuffer )
        {
            NetworkEndPoint_t * pxEndPoint;

            #if ( ipconfigUSE_IPv6 != 0 )
                IPPacket_IPv6_t * xIPPacket_IPv6 = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );

                if( xIPPacket_IPv6->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
                {
                    pxEndPoint = FreeRTOS_FindEndPointOnNetMask_IPv6( &xIPPacket_IPv6->xIPHeader.xSourceAddress );
                }
                else
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */
            {
                IPPacket_t * xIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

                pxEndPoint = FreeRTOS_FindEndPointOnNetMask( xIPPacket->xIPHeader.ulSourceIPAddress, 6 );
            }

            if( pxEndPoint != NULL )
            {
                pxNetworkBuffer->pxEndPoint = pxEndPoint;
            }

            return pxEndPoint;
        }
    #endif /* ( ( ipconfigUSE_NBNS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) ) */
/*-----------------------------------------------------------*/

    #if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )

/**
 * @brief Read the Name field out of a DNS response packet.
 *
 * @param[in,out] pxSet: a set of variables that are shared among the helper functions.
 * @param[in] uxDestLen: Size of the pcName array.
 *
 * @return If a fully formed name was found, then return the number of bytes processed in pucByte.
 */
        size_t DNS_ReadNameField( ParseSet_t * pxSet,
                                  size_t uxDestLen )
        {
            /* 'uxNameLen' counts characters written to 'pxSet->pcName'. */
            size_t uxNameLen = 0U;
            /* The index within .pxSet->pcName'. */
            size_t uxIndex = 0U;
            size_t uxReturnIndex = 0U;
            size_t uxSourceLen = pxSet->uxSourceBytesRemaining;
            size_t uxOffset;
            const uint8_t * pucByte = pxSet->pucByte;

            /* uxCount gets the values from pucByte and counts down to 0.
             * No need to have a different type than that of pucByte */
            size_t uxCount;

            if( uxSourceLen == ( size_t ) 0U )
            {
                /* Return 0 value in case of error. */
                uxIndex = 0U;
            }

            else
            {
                /* 'uxIndex' points to the full name. Walk over the string. */
                while( ( uxIndex < uxSourceLen ) && ( pucByte[ uxIndex ] != ( uint8_t ) 0x00U ) )
                {
                    /* If this is not the first time through the loop, then add a
                     * separator in the output. */
                    if( ( uxNameLen > 0U ) )
                    {
                        if( uxNameLen >= uxDestLen )
                        {
                            uxIndex = 0U;
                            /* coverity[break_stmt] : Break statement terminating the loop */
                            break;
                        }

                        pxSet->pcName[ uxNameLen ] = '.';
                        uxNameLen++;
                    }

                    /* Process the first/next sub-string. */
                    uxCount = ( size_t ) pucByte[ uxIndex ];

                    /* uxIndex should point to the first character now, unless uxCount
                     * is an offset field. */
                    uxIndex++;

                    /* Determine if the name is the fully coded name, or an offset to the name
                     * elsewhere in the message. */
                    if( ( uxCount & dnsNAME_IS_OFFSET ) == dnsNAME_IS_OFFSET )
                    {
                        /* Check if there are enough bytes left. */
                        if( ( uxIndex + 2U ) < uxSourceLen )
                        {
                            /* Only accept a single offset command. */
                            if( uxReturnIndex != 0U )
                            {
                                /* There was a 0xC0 sequence already. */
                                uxIndex = 0U;
                                break;
                            }

                            /* Remember the offset to return. */
                            uxReturnIndex = uxIndex + 1U;
                            /* The offset byte 0xC0 is followed by an offset in the DNS record. */
                            uxOffset = ( size_t ) pucByte[ uxIndex ];

                            if( ( uxOffset + 2U ) > pxSet->uxBufferLength )
                            {
                                uxIndex = 0U;
                                break;
                            }

                            uxSourceLen = pxSet->uxBufferLength - uxOffset;

                            if( ( ( uxOffset + 2U ) < uxSourceLen ) && ( uxOffset >= sizeof( DNSMessage_t ) ) )
                            {
                                /* Process the first/next sub-string. */
                                pucByte = &( pxSet->pucUDPPayloadBuffer[ uxOffset ] );
                                uxCount = ( size_t ) pucByte[ 0 ];
                                uxIndex = 1U;
                            }
                            else
                            {
                                uxIndex = 0U;
                                break;
                            }
                        }
                        else
                        {
                            uxIndex = 0U;
                            break;
                        }
                    }

                    if( ( uxIndex + uxCount ) > uxSourceLen )
                    {
                        uxIndex = 0U;
                        break;
                    }

                    if( ( uxNameLen + uxCount ) >= uxDestLen )
                    {
                        uxIndex = 0U;
                        break;
                    }

                    while( ( uxCount-- != 0U ) && ( uxIndex < uxSourceLen ) )
                    {
                        pxSet->pcName[ uxNameLen ] = ( char ) pucByte[ uxIndex ];
                        uxNameLen++;
                        uxIndex++;
                    }
                } /* while( ( uxIndex < uxSourceLen ) && ( pucByte[ uxIndex ] != ( uint8_t ) 0x00U ) ) */

                /* Confirm that a fully formed name was found. */
                if( uxIndex > 0U )
                {
                    if( ( uxNameLen < uxDestLen ) && ( uxIndex < uxSourceLen ) && ( pucByte[ uxIndex ] == 0U ) )
                    {
                        pxSet->pcName[ uxNameLen ] = 0;
                        uxIndex++;
                    }
                    else
                    {
                        uxIndex = 0U;
                    }
                }
            }

            if( ( uxReturnIndex != 0U ) && ( uxIndex != 0U ) )
            {
                uxIndex = uxReturnIndex;
            }

            return uxIndex;
        }
    #endif /* ipconfigUSE_DNS_CACHE || ipconfigDNS_USE_CALLBACKS */
/*-----------------------------------------------------------*/

/**
 * @brief Process a response packet from a DNS server, or an mDNS or LLMNR reply.
 *
 * @param[in] pucUDPPayloadBuffer: The DNS response received as a UDP
 *                                 payload.
 * @param[in] uxBufferLength: Length of the UDP payload buffer.
 * @param[in] ppxAddressInfo: A pointer to a pointer where the results will be stored.
 * @param[in] xExpected: indicates whether the identifier in the reply
 *                       was expected, and thus if the DNS cache may be
 *                       updated with the reply.
 * @param[in] usPort: The server port number in order to identify the protocol.
 *
 * @return The IP address in the DNS response if present and if xExpected is set to pdTRUE.
 *         An error code (dnsPARSE_ERROR) if there was an error in the DNS response.
 *         0 if xExpected set to pdFALSE.
 */
    uint32_t DNS_ParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                                size_t uxBufferLength,
                                struct freertos_addrinfo ** ppxAddressInfo,
                                BaseType_t xExpected,
                                uint16_t usPort )
    {
        ParseSet_t xSet;

        BaseType_t xReturn = pdTRUE;

        ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
        xSet.usPortNumber = usPort;
        xSet.ppxLastAddress = &( xSet.pxLastAddress );

        xSet.uxAddressLength = ipSIZE_OF_IPv4_ADDRESS;

        #if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
            xSet.xDoStore = xExpected;
        #endif

        /* Ensure that the buffer is of at least minimal DNS message length. */
        if( uxBufferLength < sizeof( DNSMessage_t ) )
        {
            xReturn = pdFALSE;
        }
        else
        {
            xSet.uxBufferLength = uxBufferLength;
            xSet.uxSourceBytesRemaining = uxBufferLength;

            /* Parse the DNS message header. Map the byte stream onto a structure
             * for easier access. */
            xSet.pxDNSMessageHeader = ( ( DNSMessage_t * ) pucUDPPayloadBuffer );

            /* Introduce a do {} while (0) to allow the use of breaks. */
            do
            {
                /* Start at the first byte after the header. */
                xSet.pucUDPPayloadBuffer = pucUDPPayloadBuffer;
                xSet.pucByte = &( pucUDPPayloadBuffer[ sizeof( DNSMessage_t ) ] );
                xSet.uxSourceBytesRemaining -= sizeof( DNSMessage_t );

                /* Skip any question records. */
                xSet.usQuestions = FreeRTOS_ntohs( xSet.pxDNSMessageHeader->usQuestions );

                xReturn = prvParseDNS_ReadQuestions( &( xSet ) );

                if( xReturn == pdFALSE )
                {
                    /* No need to proceed. Break out of the do-while loop. */
                    break;
                }

                #if ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) )
                    #if ( ipconfigUSE_IPv6 != 0 )
                        if( ( xSet.usQuestions != 0U ) &&
                            ( xSet.usType != ( uint16_t ) dnsTYPE_A_HOST ) &&
                            ( xSet.usType != ( uint16_t ) dnsTYPE_AAAA_HOST ) )
                        {
                            break;
                        }
                    #else
                        if( ( xSet.usQuestions != 0U ) &&
                            ( xSet.usType != ( uint16_t ) dnsTYPE_A_HOST ) )
                        {
                            break;
                        }
                    #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
                #endif /* if ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) ) */

                /* Search through the answer records. */
                xSet.pxDNSMessageHeader->usAnswers = FreeRTOS_ntohs( xSet.pxDNSMessageHeader->usAnswers );

                if( ( xSet.pxDNSMessageHeader->usFlags & dnsRX_FLAGS_MASK ) == dnsEXPECTED_RX_FLAGS )
                {
                    xReturn = prvParseDNS_ReadAnswers( &( xSet ), ppxAddressInfo );
                }

                #if ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) )
                    else if( ( xSet.usQuestions != ( uint16_t ) 0U ) &&
                             ( xSet.usClass == dnsCLASS_IN ) &&
                             ( xSet.pcRequestedName != NULL ) )
                    {
                        prvParseDNS_HandleLLMNRRequest( &( xSet ), pucUDPPayloadBuffer );
                    }
                    else
                    {
                        /* Not an expected reply. */
                    }
                #endif /* ( ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) ) */
            } while( ipFALSE_BOOL );
        }

        if( xReturn == pdFALSE )
        {
            /* There was an error while parsing the DNS response. Return error code. */
            xSet.ulIPAddress = dnsPARSE_ERROR;
        }
        else if( xExpected == pdFALSE )
        {
            /* Do not return a valid IP-address in case the reply was not expected. */
            xSet.ulIPAddress = 0U;
        }
        else
        {
            /* The IP-address was found in prvParseDNS_ReadAnswers(), and it will be returned. */
        }

        return xSet.ulIPAddress;
    }
/*-----------------------------------------------------------*/

    #if ( ( ipconfigUSE_NBNS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) )

/**
 * @brief Send a DNS message to be used in NBNS or LLMNR
 *
 * @param[in] pxNetworkBuffer: The network buffer descriptor with the DNS message.
 * @param[in] lNetLength: The length of the DNS message.
 */
        static void prvReplyDNSMessage( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                        BaseType_t lNetLength )
        {
            UDPPacket_t * pxUDPPacket;
            IPHeader_t * pxIPHeader;
            UDPHeader_t * pxUDPHeader;
            NetworkEndPoint_t * pxEndPoint = prvFindEndPointOnNetMask( pxNetworkBuffer );
            size_t uxDataLength;

            pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
            pxIPHeader = &pxUDPPacket->xIPHeader;

            #if ( ipconfigUSE_IPv6 != 0 )
                if( ( pxIPHeader->ucVersionHeaderLength & 0xf0U ) == 0x60U )
                {
                    UDPPacket_IPv6_t * xUDPPacket_IPv6;
                    IPHeader_IPv6_t * pxIPHeader_IPv6;

                    xUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
                    pxIPHeader_IPv6 = &( xUDPPacket_IPv6->xIPHeader );
                    pxUDPHeader = &xUDPPacket_IPv6->xUDPHeader;

                    pxIPHeader_IPv6->usPayloadLength = FreeRTOS_htons( ( uint16_t ) lNetLength + ipSIZE_OF_UDP_HEADER );

                    {
                        ( void ) memcpy( pxIPHeader_IPv6->xDestinationAddress.ucBytes, pxIPHeader_IPv6->xSourceAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                        ( void ) memcpy( pxIPHeader_IPv6->xSourceAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                    }

                    xUDPPacket_IPv6->xUDPHeader.usLength = FreeRTOS_htons( ( uint16_t ) lNetLength + ipSIZE_OF_UDP_HEADER );
                    vFlip_16( pxUDPHeader->usSourcePort, pxUDPHeader->usDestinationPort );
                    uxDataLength = ( size_t ) lNetLength + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_UDP_HEADER + ipSIZE_OF_ETH_HEADER;
                }
                else
            #endif /* ipconfigUSE_IPv6 */
            {
                pxUDPHeader = &pxUDPPacket->xUDPHeader;
                /* HT: started using defines like 'ipSIZE_OF_xxx' */
                pxIPHeader->usLength = FreeRTOS_htons( ( uint16_t ) lNetLength + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER );

                /* HT:endian: should not be translated, copying from packet to packet */
                if( pxIPHeader->ulDestinationIPAddress == ipMDNS_IP_ADDRESS )
                {
                    pxIPHeader->ulDestinationIPAddress = ipMDNS_IP_ADDRESS;
                }
                else
                {
                    pxIPHeader->ulDestinationIPAddress = pxIPHeader->ulSourceIPAddress;
                }

                pxIPHeader->ulSourceIPAddress = ( pxEndPoint != NULL ) ? pxEndPoint->ipv4_settings.ulIPAddress : 0U;
                pxIPHeader->ucTimeToLive = ipconfigUDP_TIME_TO_LIVE;
                pxIPHeader->usIdentification = FreeRTOS_htons( usPacketIdentifier );
                usPacketIdentifier++;
                pxUDPHeader->usLength = FreeRTOS_htons( ( uint32_t ) lNetLength + ipSIZE_OF_UDP_HEADER );
                vFlip_16( pxUDPHeader->usSourcePort, pxUDPHeader->usDestinationPort );

                /* Important: tell NIC driver how many bytes must be sent */
                uxDataLength = ( ( size_t ) lNetLength ) + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER + ipSIZE_OF_ETH_HEADER;
            }

            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
                {
                    #if ( ipconfigUSE_IPv6 != 0 )
                        /* IPv6 IP-headers have no checksum field. */
                        if( ( pxIPHeader->ucVersionHeaderLength & 0xf0U ) != 0x60U )
                    #endif
                    {
                        /* Calculate the IP header checksum. */
                        pxIPHeader->usHeaderChecksum = 0U;
                        pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
                        pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );
                    }

                    /* calculate the UDP checksum for outgoing package */
                    ( void ) usGenerateProtocolChecksum( ( uint8_t * ) pxUDPPacket, uxDataLength, pdTRUE );
                }
            #endif /* ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 ) */

            /* Important: tell NIC driver how many bytes must be sent */
            pxNetworkBuffer->xDataLength = uxDataLength;

            /* This function will fill in the eth addresses and send the packet */
            vReturnEthernetFrame( pxNetworkBuffer, pdFALSE );
        }

    #endif /* ( ( ipconfigUSE_NBNS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_MDNS == 1 ) ) */
/*-----------------------------------------------------------*/

/**
 * @brief Copy an IP-address to a variable, and add it to a linked list of IP-addresses.
 * @param[in] pxSet: a set of variables that are shared among the helper functions.
 * @param[out] pxIP_Address: The address found will be copied to 'pxIP_Address'.
 * @param[out] ppxAddressInfo: The address found will also be stored in this linked list.
 */
    static void prvParseDNS_StoreAnswer( ParseSet_t * pxSet,
                                         IPv46_Address_t * pxIP_Address,
                                         struct freertos_addrinfo ** ppxAddressInfo )
    {
        struct freertos_addrinfo * pxNewAddress = NULL;

        /* Copy the IP address out of the record. */
        #if ( ipconfigUSE_IPv6 != 0 )
            if( pxSet->usType == ( uint16_t ) dnsTYPE_AAAA_HOST )
            {
                ( void ) memcpy( pxIP_Address->xAddress_IPv6.ucBytes,
                                 &( pxSet->pucByte[ sizeof( DNSAnswerRecord_t ) ] ),
                                 ipSIZE_OF_IPv6_ADDRESS );

                if( ppxAddressInfo != NULL )
                {
                    pxNewAddress = pxNew_AddrInfo( pxSet->pcName, FREERTOS_AF_INET6, pxIP_Address->xAddress_IPv6.ucBytes );
                }

                pxIP_Address->xIs_IPv6 = pdTRUE;

                /* Return non-zero to inform the caller that a valid
                 * IPv6 address was found. */
                pxSet->ulIPAddress = 1U;
            }
            else
        #endif /* ( ipconfigUSE_IPv6 != 0 ) */
        {
            void * pvCopyDest;
            const void * pvCopySource;

            /* Copy the IP address out of the record. Using different pointers
             * to copy only the portion we want is intentional here. */
            pvCopyDest = &( pxSet->ulIPAddress );
            pvCopySource = &( pxSet->pucByte[ sizeof( DNSAnswerRecord_t ) ] );
            ( void ) memcpy( pvCopyDest,
                             pvCopySource,
                             ipSIZE_OF_IPv4_ADDRESS );

            if( ppxAddressInfo != NULL )
            {
                uint8_t * ucBytes = ( uint8_t * ) &( pxSet->ulIPAddress );

                pxNewAddress = pxNew_AddrInfo( pxSet->pcName, FREERTOS_AF_INET4, ucBytes );
            }

            pxIP_Address->ulIPAddress = pxSet->ulIPAddress;
            #if ( ipconfigUSE_IPv6 != 0 )
                pxIP_Address->xIs_IPv6 = pdFALSE;
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */
        }

        if( pxNewAddress != NULL )
        {
            if( *( ppxAddressInfo ) == NULL )
            {
                /* For the first address found. */
                *( ppxAddressInfo ) = pxNewAddress;
            }
            else
            {
                /* For the next address found. */
                *( pxSet->ppxLastAddress ) = pxNewAddress;
            }

            pxSet->ppxLastAddress = &( pxNewAddress->ai_next );
        }
    }
/*-----------------------------------------------------------*/

    #if ( ipconfigUSE_NBNS == 1 )

/**
 * @brief Respond to an NBNS query or an NBNS reply.
 *
 * @param[in] pucPayload: the UDP payload of the NBNS message.
 * @param[in] uxBufferLength: Length of the Buffer.
 * @param[in] ulIPAddress: IP address of the sender.
 */
        void DNS_TreatNBNS( uint8_t * pucPayload,
                            size_t uxBufferLength,
                            uint32_t ulIPAddress )
        {
            uint16_t usFlags, usType, usClass;
            uint8_t * pucSource, * pucTarget;
            uint8_t ucByte;
            uint8_t ucNBNSName[ 17 ];
            uint8_t * pucUDPPayloadBuffer = pucPayload;
            NetworkBufferDescriptor_t * pxNetworkBuffer;
            size_t uxBytesNeeded = sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t );

            do
            {
                NetworkEndPoint_t xEndPoint;
                BaseType_t xMustReply = pdFALSE;

                /* Check for minimum buffer size. */
                if( uxBufferLength < uxBytesNeeded )
                {
                    break;
                }

                /* Read the request flags in host endianness. */
                usFlags = usChar2u16( &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, usFlags ) ] ) );

                if( ( usFlags & dnsNBNS_FLAGS_OPCODE_MASK ) != dnsNBNS_FLAGS_OPCODE_QUERY )
                {
                    break;
                }

                usType = usChar2u16( &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, usType ) ] ) );
                usClass = usChar2u16( &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, usClass ) ] ) );

                /* Not used for now */
                ( void ) usClass;

                /* For NBNS a name is 16 bytes long, written with capitals only.
                 * Make sure that the copy is terminated with a zero. */
                pucTarget = &( ucNBNSName[ sizeof( ucNBNSName ) - 2U ] );
                pucTarget[ 1 ] = ( uint8_t ) 0U;

                /* Start with decoding the last 2 bytes. */
                pucSource = &( pucUDPPayloadBuffer[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + offsetof( NBNSRequest_t, ucName ) ] );

                for( ; ; )
                {
                    const uint8_t ucCharA = ( uint8_t ) 0x41U;

                    ucByte = ( ( uint8_t ) ( ( pucSource[ 0 ] - ucCharA ) << 4 ) ) | ( pucSource[ 1 ] - ucCharA );

                    /* Make sure there are no trailing spaces in the name. */
                    if( ( ucByte == ( uint8_t ) ' ' ) && ( pucTarget[ 1 ] == 0U ) )
                    {
                        ucByte = 0U;
                    }

                    *pucTarget = ucByte;

                    if( pucTarget == ucNBNSName )
                    {
                        break;
                    }

                    pucTarget -= 1;
                    pucSource -= 2;
                }

                #if ( ipconfigUSE_DNS_CACHE == 1 )
                    {
                        if( ( usFlags & dnsNBNS_FLAGS_RESPONSE ) != 0U )
                        {
                            /* If this is a response from another device,
                             * add the name to the DNS cache */
                            IPv46_Address_t xIPAddress;

                            xIPAddress.ulIPAddress = ulIPAddress;
                            #if ( ipconfigUSE_IPv6 != 0 )
                                {
                                    xIPAddress.xIs_IPv6 = pdFALSE;
                                }
                            #endif

                            ( void ) FreeRTOS_ProcessDNSCache( ( char * ) ucNBNSName, &( xIPAddress ), 0, pdFALSE, NULL );
                        }
                    }
                #else /* if ( ipconfigUSE_DNS_CACHE == 1 ) */
                    {
                        /* Avoid compiler warnings. */
                        ( void ) ulIPAddress;
                    }
                #endif /* ipconfigUSE_DNS_CACHE */

                pxNetworkBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pucUDPPayloadBuffer );

                /* When pxUDPPayloadBuffer_to_NetworkBuffer fails, there
                 * is a real problem, like data corruption. */
                configASSERT( pxNetworkBuffer != NULL );

                if( pxNetworkBuffer->pxEndPoint == NULL )
                {
                    pxNetworkBuffer->pxEndPoint = prvFindEndPointOnNetMask( pxNetworkBuffer );
                }

                if( pxNetworkBuffer->pxEndPoint != NULL )
                {
                    ( void ) memcpy( &xEndPoint, pxNetworkBuffer->pxEndPoint, sizeof( xEndPoint ) );
                }

                #if ( ipconfigUSE_IPv6 != 0 )
                    {
                        xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;
                    }
                #endif

                /* If this packet is not a response, and if it is an NBNS request. */
                if( ( ( usFlags & dnsNBNS_FLAGS_RESPONSE ) == 0U ) &&
                    ( usType == dnsNBNS_TYPE_NET_BIOS ) )
                {
                    if( xApplicationDNSQueryHook( &( xEndPoint ), ( const char * ) ucNBNSName ) != pdFALSE )
                    {
                        xMustReply = pdTRUE;
                    }
                }

                if( xMustReply == pdFALSE )
                {
                    break;
                }

                uint16_t usLength;
                NetworkBufferDescriptor_t * pxNewBuffer = NULL;

                /* Someone is looking for a device with ucNBNSName,
                 * prepare a positive reply. */

                if( xBufferAllocFixedSize == pdFALSE )
                {
                    /* The field xDataLength was set to the total length of the UDP packet,
                     * i.e. the payload size plus sizeof( UDPPacket_t ). */
                    pxNewBuffer = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, pxNetworkBuffer->xDataLength + sizeof( NBNSAnswer_t ) );

                    if( pxNewBuffer == NULL )
                    {
                        break;
                    }

                    pxNetworkBuffer = pxNewBuffer;
                }

                /* Should not occur: pucUDPPayloadBuffer is part of a xNetworkBufferDescriptor */

                /* As the fields in the structures are not word-aligned, we have to
                 * copy the values byte-by-byte using macro's vSetField16() and vSetField32() */
                vSetField16( pucUDPPayloadBuffer, DNSMessage_t, usFlags, dnsNBNS_QUERY_RESPONSE_FLAGS ); /* 0x8500 */
                vSetField16( pucUDPPayloadBuffer, DNSMessage_t, usQuestions, 0 );
                vSetField16( pucUDPPayloadBuffer, DNSMessage_t, usAnswers, 1 );
                vSetField16( pucUDPPayloadBuffer, DNSMessage_t, usAuthorityRRs, 0 );
                vSetField16( pucUDPPayloadBuffer, DNSMessage_t, usAdditionalRRs, 0 );

                uint8_t * pucByte = &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, usType ) ] );

                vSetField16( pucByte, NBNSAnswer_t, usType, usType );            /* Type */
                vSetField16( pucByte, NBNSAnswer_t, usClass, dnsNBNS_CLASS_IN ); /* Class */
                vSetField32( pucByte, NBNSAnswer_t, ulTTL, dnsNBNS_TTL_VALUE );
                vSetField16( pucByte, NBNSAnswer_t, usDataLength, 6 );           /* 6 bytes including the length field */
                vSetField16( pucByte, NBNSAnswer_t, usNbFlags, dnsNBNS_NAME_FLAGS );
                vSetField32( pucByte, NBNSAnswer_t, ulIPAddress, FreeRTOS_ntohl( xEndPoint.ipv4_settings.ulIPAddress ) );

                usLength = ( uint16_t ) ( sizeof( NBNSAnswer_t ) + ( size_t ) offsetof( NBNSRequest_t, usType ) );

                prvReplyDNSMessage( pxNetworkBuffer, ( BaseType_t ) usLength );

                if( pxNewBuffer != NULL )
                {
                    vReleaseNetworkBufferAndDescriptor( pxNewBuffer );
                }
            }  while( ipFALSE_BOOL );
        }

    #endif /* ipconfigUSE_NBNS */
/*-----------------------------------------------------------*/

#endif /* ipconfigUSE_DNS != 0 */
