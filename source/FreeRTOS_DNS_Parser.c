/*
 * FreeRTOS+TCP V3.1.0
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
 * @file FreeRTOS_DNS_Parser.c
 * @brief Implements the DNS message parser
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
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

/** @brief The list of all callback structures. */

/**
 * @brief Read the Name field out of a DNS response packet.
 *
 * @param[in] pucByte: Pointer to the DNS response.
 * @param[in] uxRemainingBytes: Length of the DNS response.
 * @param[out] pcName: The pointer in which the name in the DNS response will be returned.
 * @param[in] uxDestLen: Size of the pcName array.
 *
 * @return If a fully formed name was found, then return the number of bytes processed in pucByte.
 */
    size_t DNS_ReadNameField( const uint8_t * pucByte,
                              size_t uxRemainingBytes,
                              char * pcName,
                              size_t uxDestLen )
    {
        size_t uxNameLen = 0U;
        size_t uxIndex = 0U;
        size_t uxSourceLen = uxRemainingBytes;

        /* uxCount gets the values from pucByte and counts down to 0.
         * No need to have a different type than that of pucByte */
        size_t uxCount;

        if( uxSourceLen == ( size_t ) 0U )
        {
            /* Return 0 value in case of error. */
            uxIndex = 0U;
        }

        /* Determine if the name is the fully coded name, or an offset to the name
         * elsewhere in the message. */
        else if( ( pucByte[ uxIndex ] & dnsNAME_IS_OFFSET ) == dnsNAME_IS_OFFSET )
        {
            /* Jump over the two byte offset. */
            if( uxSourceLen > sizeof( uint16_t ) )
            {
                uxIndex += sizeof( uint16_t );
            }
            else
            {
                uxIndex = 0U;
            }
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

                    pcName[ uxNameLen ] = '.';
                    uxNameLen++;
                }

                /* Process the first/next sub-string. */
                uxCount = ( size_t ) pucByte[ uxIndex ];
                uxIndex++;

                if( ( uxIndex + uxCount ) > uxSourceLen )
                {
                    uxIndex = 0U;
                    break;
                }

                while( uxCount-- != 0U )
                {
                    if( uxNameLen >= uxDestLen )
                    {
                        uxIndex = 0U;
                        break;

                        /* break out of inner loop here
                         * break out of outer loop at the test uxNameLen >= uxDestLen. */
                    }

                    pcName[ uxNameLen ] = ( char ) pucByte[ uxIndex ];
                    uxNameLen++;
                    uxIndex++;
                }
            }

            /* Confirm that a fully formed name was found. */
            if( uxIndex > 0U )
            {
                /* Here, there is no need to check for pucByte[ uxindex ] == 0 because:
                 * When we break out of the above while loop, uxIndex is made 0 thereby
                 * failing above check. Whenever we exit the loop otherwise, either
                 * pucByte[ uxIndex ] == 0 (which makes the check here unnecessary) or
                 * uxIndex >= uxSourceLen (which makes sure that we do not go in the 'if'
                 * case).
                 */
                if( ( uxNameLen < uxDestLen ) && ( uxIndex < uxSourceLen ) )
                {
                    pcName[ uxNameLen ] = '\0';
                    uxIndex++;
                }
                else
                {
                    uxIndex = 0U;
                }
            }
        }

        return uxIndex;
    }

/**
 * @brief Simple routine that jumps over the NAME field of a resource record.
 *
 * @param[in] pucByte: The pointer to the resource record.
 * @param[in] uxLength: Length of the resource record.
 *
 * @return It returns the number of bytes read, or zero when an error has occurred.
 */
    size_t DNS_SkipNameField( const uint8_t * pucByte,
                              size_t uxLength )
    {
        size_t uxChunkLength;
        size_t uxSourceLenCpy = uxLength;
        size_t uxIndex = 0U;

        if( uxSourceLenCpy == 0U )
        {
            uxIndex = 0U;
        }

        /* Determine if the name is the fully coded name, or an offset to the name
         * elsewhere in the message. */
        else if( ( pucByte[ uxIndex ] & dnsNAME_IS_OFFSET ) == dnsNAME_IS_OFFSET )
        {
            /* Jump over the two byte offset. */
            if( uxSourceLenCpy > sizeof( uint16_t ) )
            {
                uxIndex += sizeof( uint16_t );
            }
            else
            {
                uxIndex = 0U;
            }
        }
        else
        {
            /* pucByte points to the full name. Walk over the string. */
            while( ( pucByte[ uxIndex ] != 0U ) && ( uxSourceLenCpy > 1U ) )
            {
                /* Conversion to size_t causes addition to be done
                 * in size_t */
                uxChunkLength = ( ( size_t ) pucByte[ uxIndex ] ) + 1U;

                if( uxSourceLenCpy > uxChunkLength )
                {
                    uxSourceLenCpy -= uxChunkLength;
                    uxIndex += uxChunkLength;
                }
                else
                {
                    uxIndex = 0U;
                    break;
                }
            }

            /* Confirm that a fully formed name was found. */
            if( uxIndex > 0U )
            {
                if( pucByte[ uxIndex ] == 0U )
                {
                    uxIndex++;
                }
                else
                {
                    uxIndex = 0U;
                }
            }
        }

        return uxIndex;
    }

/**
 * @brief Process a response packet from a DNS server, or an LLMNR reply.
 *
 * @param[in] pucUDPPayloadBuffer: The DNS response received as a UDP
 *                                 payload.
 * @param[in] uxBufferLength: Length of the UDP payload buffer.
 * @param[in] xExpected: indicates whether the identifier in the reply
 *                       was expected, and thus if the DNS cache may be
 *                       updated with the reply.
 *
 * @return The IP address in the DNS response if present and if xExpected is set to pdTRUE.
 *         An error code (dnsPARSE_ERROR) if there was an error in the DNS response.
 *         0 if xExpected set to pdFALSE.
 */
    uint32_t DNS_ParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                                size_t uxBufferLength,
                                BaseType_t xExpected )
    {
        DNSMessage_t * pxDNSMessageHeader;
        uint32_t ulIPAddress = 0U;

        #if ( ipconfigUSE_LLMNR == 1 )
            char * pcRequestedName = NULL;
        #endif
        uint8_t * pucByte;
        size_t uxSourceBytesRemaining;
        uint16_t x;
        uint16_t usQuestions;
        BaseType_t xReturn = pdTRUE;

        #if ( ipconfigUSE_LLMNR == 1 )
            uint16_t usType = 0U;
            uint16_t usClass = 0U;
        #endif
        #if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
            BaseType_t xDoStore = xExpected;
            char pcName[ ipconfigDNS_CACHE_NAME_LENGTH ] = "";
        #endif

        /* Ensure that the buffer is of at least minimal DNS message length. */
        if( uxBufferLength < sizeof( DNSMessage_t ) )
        {
            xReturn = pdFALSE;
        }
        else
        {
            uxSourceBytesRemaining = uxBufferLength;

            /* Parse the DNS message header. Map the byte stream onto a structure
             * for easier access. */

            /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            pxDNSMessageHeader = ( ( DNSMessage_t * )
                                   pucUDPPayloadBuffer );

            /* Introduce a do {} while (0) to allow the use of breaks. */
            do
            {
                size_t uxBytesRead = 0U;
                size_t uxResult;

                /* Start at the first byte after the header. */
                pucByte = &( pucUDPPayloadBuffer[ sizeof( DNSMessage_t ) ] );
                uxSourceBytesRemaining -= sizeof( DNSMessage_t );

                /* Skip any question records. */
                usQuestions = FreeRTOS_ntohs( pxDNSMessageHeader->usQuestions );

                for( x = 0U; x < usQuestions; x++ )
                {
                    #if ( ipconfigUSE_LLMNR == 1 )
                        {
                            if( x == 0U )
                            {
                                pcRequestedName = ( char * ) pucByte;
                            }
                        }
                    #endif

                    #if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
                        if( x == 0U )
                        {
                            uxResult = DNS_ReadNameField( pucByte,
                                                          uxSourceBytesRemaining,
                                                          pcName,
                                                          sizeof( pcName ) );
                        }
                        else
                    #endif /* ipconfigUSE_DNS_CACHE || ipconfigDNS_USE_CALLBACKS */
                    {
                        /* Skip the variable length pcName field. */
                        uxResult = DNS_SkipNameField( pucByte,
                                                      uxSourceBytesRemaining );
                    }

                    /* Check for a malformed response. */
                    if( uxResult == 0U )
                    {
                        xReturn = pdFALSE;
                        break;
                    }

                    uxBytesRead += uxResult;
                    pucByte = &( pucByte[ uxResult ] );
                    uxSourceBytesRemaining -= uxResult;

                    /* Check the remaining buffer size. */
                    if( uxSourceBytesRemaining >= sizeof( uint32_t ) )
                    {
                        #if ( ipconfigUSE_LLMNR == 1 )
                            {
                                /* usChar2u16 returns value in host endianness. */
                                usType = usChar2u16( pucByte );
                                usClass = usChar2u16( &( pucByte[ 2 ] ) );
                            }
                        #endif /* ipconfigUSE_LLMNR */

                        /* Skip the type and class fields. */
                        pucByte = &( pucByte[ sizeof( uint32_t ) ] );
                        uxSourceBytesRemaining -= sizeof( uint32_t );
                    }
                    else
                    {
                        xReturn = pdFALSE;
                        break;
                    }
                }

                if( xReturn == pdFALSE )
                {
                    /* No need to proceed. Break out of the do-while loop. */
                    break;
                }

                /* Search through the answer records. */
                pxDNSMessageHeader->usAnswers =
                    FreeRTOS_ntohs( pxDNSMessageHeader->usAnswers );

                if( ( pxDNSMessageHeader->usFlags & dnsRX_FLAGS_MASK )
                    == dnsEXPECTED_RX_FLAGS )
                {
                    ulIPAddress = parseDNSAnswer( pxDNSMessageHeader,
                                                  pucByte,
                                                  uxSourceBytesRemaining,
                                                  &uxBytesRead
                                                  #if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
                                                      ,
                                                      pcName,
                                                      xDoStore
                                                  #endif
                                                  );
                }

                #if ( ipconfigUSE_LLMNR == 1 )

                    /* No need to check that pcRequestedName != NULL since sQuestions != 0, then
                     * pcRequestedName is assigned with this statement
                     * "pcRequestedName = ( char * ) pucByte;" */
                    else if( ( usQuestions != ( uint16_t ) 0U ) &&
                             ( usType == dnsTYPE_A_HOST ) &&
                             ( usClass == dnsCLASS_IN ) )
                    {
                        /* If this is not a reply to our DNS request, it might an LLMNR
                         * request. */
                        if( xApplicationDNSQueryHook( &( pcRequestedName[ 1 ] ) ) != pdFALSE )
                        {
                            int16_t usLength;
                            NetworkBufferDescriptor_t * pxNewBuffer = NULL;
                            NetworkBufferDescriptor_t * pxNetworkBuffer =
                                pxUDPPayloadBuffer_to_NetworkBuffer( pucUDPPayloadBuffer );
                            LLMNRAnswer_t * pxAnswer;
                            uint8_t * pucNewBuffer = NULL;

                            if( pxNetworkBuffer != NULL )
                            {
                                if( xBufferAllocFixedSize == pdFALSE )
                                {
                                    size_t uxDataLength = uxBufferLength +
                                                          sizeof( UDPHeader_t ) +
                                                          sizeof( EthernetHeader_t ) +
                                                          sizeof( IPHeader_t );

                                    /* Set the size of the outgoing packet. */
                                    pxNetworkBuffer->xDataLength = uxDataLength;
                                    pxNewBuffer = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer,
                                                                                          uxDataLength +
                                                                                          sizeof( LLMNRAnswer_t ) );

                                    if( pxNewBuffer != NULL )
                                    {
                                        BaseType_t xOffset1, xOffset2;

                                        xOffset1 = ( BaseType_t ) ( pucByte - pucUDPPayloadBuffer );
                                        xOffset2 = ( BaseType_t ) ( ( ( uint8_t * ) pcRequestedName ) - pucUDPPayloadBuffer );

                                        pxNetworkBuffer = pxNewBuffer;
                                        pucNewBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );

                                        pucByte = &( pucNewBuffer[ xOffset1 ] );
                                        pcRequestedName = ( char * ) &( pucNewBuffer[ xOffset2 ] );
                                        pxDNSMessageHeader = ( ( DNSMessage_t * ) pucNewBuffer );
                                    }
                                    else
                                    {
                                        /* Just to indicate that the message may not be answered. */
                                        pxNetworkBuffer = NULL;
                                    }
                                }
                                else
                                {
                                    pucNewBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
                                }
                            }

                            if( ( pxNetworkBuffer != NULL ) )
                            {
                                pxAnswer = ( ( LLMNRAnswer_t * ) pucByte );
                                /* We leave 'usIdentifier' and 'usQuestions' untouched */
                                #ifndef _lint
                                    vSetField16( pxDNSMessageHeader, DNSMessage_t, usFlags, dnsLLMNR_FLAGS_IS_REPONSE ); /* Set the response flag */
                                    vSetField16( pxDNSMessageHeader, DNSMessage_t, usAnswers, 1 );                       /* Provide a single answer */
                                    vSetField16( pxDNSMessageHeader, DNSMessage_t, usAuthorityRRs, 0 );                  /* No authority */
                                    vSetField16( pxDNSMessageHeader, DNSMessage_t, usAdditionalRRs, 0 );                 /* No additional info */
                                #endif /* lint */

                                pxAnswer->ucNameCode = dnsNAME_IS_OFFSET;
                                pxAnswer->ucNameOffset = ( uint8_t ) ( pcRequestedName - ( char * ) pucNewBuffer );

                                #ifndef _lint
                                    vSetField16( pxAnswer, LLMNRAnswer_t, usType, dnsTYPE_A_HOST ); /* Type A: host */
                                    vSetField16( pxAnswer, LLMNRAnswer_t, usClass, dnsCLASS_IN );   /* 1: Class IN */
                                    vSetField32( pxAnswer, LLMNRAnswer_t, ulTTL, dnsLLMNR_TTL_VALUE );
                                    vSetField16( pxAnswer, LLMNRAnswer_t, usDataLength, 4 );
                                    vSetField32( pxAnswer, LLMNRAnswer_t,
                                                 ulIPAddress,
                                                 FreeRTOS_ntohl( *ipLOCAL_IP_ADDRESS_POINTER ) );
                                #endif /* lint */
                                usLength = ( int16_t ) ( sizeof( *pxAnswer ) + ( size_t ) ( pucByte - pucNewBuffer ) );

                                prepareReplyDNSMessage( pxNetworkBuffer, usLength );
                                /* This function will fill in the eth addresses and send the packet */
                                vReturnEthernetFrame( pxNetworkBuffer, pdFALSE );

                                if( pxNewBuffer != NULL )
                                {
                                    vReleaseNetworkBufferAndDescriptor( pxNewBuffer );
                                }
                            }
                        }
                    }
                    else
                    {
                        /* Not an expected reply. */
                    }
                #endif /* ipconfigUSE_LLMNR == 1 */
                ( void ) uxBytesRead;
            } while( ipFALSE_BOOL );
        }

        if( xReturn == pdFALSE )
        {
            /* There was an error while parsing the DNS response. Return error code. */
            ulIPAddress = ( uint32_t ) dnsPARSE_ERROR;
        }
        else if( xExpected == pdFALSE )
        {
            /* Do not return a valid IP-address in case the reply was not expected. */
            ulIPAddress = 0U;
        }
        else
        {
            /* The IP-address found will be returned. */
        }

        #if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
            ( void ) xDoStore;
        #endif

        return ulIPAddress;
    }

/**
 * @brief perform a dns lookup in the local cache
 * @param[in] pxDNSMessageHeader  DNS header
 * @param pucByte buffer
 * @param uxSourceBytesRemaining remaining bytes in pucByte
 * @param[out] uxBytesRead total bytes consumed by the function
 * @param pcName update the cache and /or send to callback
 * @param xDoStore whether to update the cache
 * @return ip address extracted from the frame or zero if not found
 */
    uint32_t parseDNSAnswer( const DNSMessage_t * pxDNSMessageHeader,
                             uint8_t * pucByte,
                             size_t uxSourceBytesRemaining,
                             size_t * uxBytesRead
    #if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
                                 ,
                                 const char * pcName,
                                 BaseType_t xDoStore
    #endif
                             )
    {
        uint16_t x;
        size_t uxResult;
        const uint16_t usCount = ( uint16_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
        uint16_t usNumARecordsStored = 0;
        BaseType_t xReturn = pdTRUE;
        uint16_t usType = 0U;
        const DNSAnswerRecord_t * pxDNSAnswerRecord;
        const void * pvCopySource;
        void * pvCopyDest;
        const size_t uxAddressLength = ipSIZE_OF_IPv4_ADDRESS;
        uint32_t ulIPAddress = 0U;
        uint32_t ulReturnIPAddress = 0U;
        uint16_t usDataLength;
        uint8_t * pucBuffer = pucByte;
        size_t uxRxSourceByteRemaining = uxSourceBytesRemaining;

        for( x = 0U; x < pxDNSMessageHeader->usAnswers; x++ )
        {
            BaseType_t xDoAccept;

            if( usNumARecordsStored >= usCount )
            {
                /* Only count ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY number of records. */
                break;
            }

            uxResult = DNS_SkipNameField( pucBuffer,
                                          uxRxSourceByteRemaining );

            /* Check for a malformed response. */
            if( uxResult == 0U )
            {
                xReturn = pdFALSE;
                break;
            }

            *uxBytesRead += uxResult;
            pucBuffer = &( pucBuffer[ uxResult ] );
            uxRxSourceByteRemaining -= uxResult;

            /* Is there enough data for an IPv4 A record answer and, if so,
             * is this an A record? */
            if( uxRxSourceByteRemaining < sizeof( uint16_t ) )
            {
                xReturn = pdFALSE;
                break;
            }

            usType = usChar2u16( pucBuffer );

            if( usType == ( uint16_t ) dnsTYPE_A_HOST )
            {
                if( uxRxSourceByteRemaining >= ( sizeof( DNSAnswerRecord_t ) + uxAddressLength ) )
                {
                    xDoAccept = pdTRUE;
                }
                else
                {
                    xDoAccept = pdFALSE;
                }
            }
            else
            {
                /* Unknown host type. */
                xDoAccept = pdFALSE;
            }

            if( xDoAccept != pdFALSE )
            {
                /* This is the required record type and is of sufficient size. */

                /* Mapping pucBuffer to a DNSAnswerRecord allows easy access of the
                 * fields of the structure. */

                /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                /* coverity[misra_c_2012_rule_11_3_violation] */
                pxDNSAnswerRecord = ( ( DNSAnswerRecord_t * ) pucBuffer );

                /* Sanity check the data length of an IPv4 answer. */
                if( FreeRTOS_ntohs( pxDNSAnswerRecord->usDataLength ) ==
                    ( uint16_t ) uxAddressLength )
                {
                    /* Copy the IP address out of the record. Using different pointers
                     * to copy only the portion we want is intentional here. */

                    /*
                     * Use helper variables for memcpy() to remain
                     * compliant with MISRA Rule 21.15.  These should be
                     * optimized away.
                     */
                    pvCopySource = &pucBuffer[ sizeof( DNSAnswerRecord_t ) ];
                    pvCopyDest = &ulIPAddress;
                    ( void ) memcpy( pvCopyDest, pvCopySource, uxAddressLength );

                    #if ( ipconfigDNS_USE_CALLBACKS == 1 )
                        {
                            /* See if any asynchronous call was made to FreeRTOS_gethostbyname_a() */
                            if( xDNSDoCallback( ( TickType_t ) pxDNSMessageHeader->usIdentifier,
                                                pcName,
                                                ulIPAddress ) != pdFALSE )
                            {
                                /* This device has requested this DNS look-up.
                                 * The result may be stored in the DNS cache. */
                                xDoStore = pdTRUE;
                            }
                        }
                    #endif /* ipconfigDNS_USE_CALLBACKS == 1 */
                    #if ( ipconfigUSE_DNS_CACHE == 1 )
                        {
                            char cBuffer[ 16 ];

                            /* The reply will only be stored in the DNS cache when the
                             * request was issued by this device. */
                            if( xDoStore != pdFALSE )
                            {
                                ( void ) FreeRTOS_dns_update(
                                    pcName,
                                    &ulIPAddress,
                                    pxDNSAnswerRecord->ulTTL );
                                usNumARecordsStored++; /* Track # of A records stored */
                            }

                            ( void ) FreeRTOS_inet_ntop( FREERTOS_AF_INET,
                                                         ( const void * ) &( ulIPAddress ),
                                                         cBuffer,
                                                         ( socklen_t ) sizeof( cBuffer ) );
                            /* Show what has happened. */
                            FreeRTOS_printf( ( "DNS[0x%04lX]: The answer to '%s' (%s) will%s be stored\n",
                                               ( UBaseType_t ) pxDNSMessageHeader->usIdentifier,
                                               pcName,
                                               cBuffer,
                                               ( xDoStore != 0 ) ? "" : " NOT" ) );
                        }
                    #endif /* ipconfigUSE_DNS_CACHE */

                    if( ( ulReturnIPAddress == 0U ) && ( ulIPAddress != 0U ) )
                    {
                        /* Remember the first IP-address that is found. */
                        ulReturnIPAddress = ulIPAddress;
                    }
                }

                pucBuffer = &( pucBuffer[ sizeof( DNSAnswerRecord_t ) + uxAddressLength ] );
                uxRxSourceByteRemaining -= ( sizeof( DNSAnswerRecord_t ) + uxAddressLength );
            }
            else if( uxRxSourceByteRemaining >= sizeof( DNSAnswerRecord_t ) )
            {
                /* It's not an A record, so skip it. Get the header location
                 * and then jump over the header. */
                /* Cast the response to DNSAnswerRecord for easy access to fields of the DNS response. */

                /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                /* coverity[misra_c_2012_rule_11_3_violation] */
                pxDNSAnswerRecord = ( ( DNSAnswerRecord_t * ) pucBuffer );

                pucBuffer = &( pucBuffer[ sizeof( DNSAnswerRecord_t ) ] );
                uxRxSourceByteRemaining -= sizeof( DNSAnswerRecord_t );

                /* Determine the length of the answer data from the header. */
                usDataLength = FreeRTOS_ntohs( pxDNSAnswerRecord->usDataLength );

                /* Jump over the answer. */
                if( uxRxSourceByteRemaining >= usDataLength )
                {
                    pucBuffer = &( pucBuffer[ usDataLength ] );
                    uxRxSourceByteRemaining -= usDataLength;
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

        return ( xReturn != 0 ) ? ulReturnIPAddress : 0U;
    }

    #if ( ( ipconfigUSE_NBNS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) )

/**
 * @brief Send a DNS message to be used in NBNS or LLMNR
 *
 * @param[in] pxNetworkBuffer: The network buffer descriptor with the DNS message.
 * @param[in] lNetLength: The length of the DNS message.
 */
        void prepareReplyDNSMessage( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                     BaseType_t lNetLength )
        {
            UDPPacket_t * pxUDPPacket;
            IPHeader_t * pxIPHeader;
            UDPHeader_t * pxUDPHeader;
            size_t uxDataLength;

            pxUDPPacket = ( ( UDPPacket_t * )
                            pxNetworkBuffer->pucEthernetBuffer );
            pxIPHeader = &pxUDPPacket->xIPHeader;
            pxUDPHeader = &pxUDPPacket->xUDPHeader;
            /* HT: started using defines like 'ipSIZE_OF_xxx' */
            pxIPHeader->usLength = FreeRTOS_htons( ( uint16_t ) lNetLength +
                                                   ipSIZE_OF_IPv4_HEADER +
                                                   ipSIZE_OF_UDP_HEADER );
            /* HT:endian: should not be translated, copying from packet to packet */
            pxIPHeader->ulDestinationIPAddress = pxIPHeader->ulSourceIPAddress;
            pxIPHeader->ulSourceIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
            pxIPHeader->ucTimeToLive = ipconfigUDP_TIME_TO_LIVE;
            pxIPHeader->usIdentification = FreeRTOS_htons( usPacketIdentifier );

            /* The stack doesn't support fragments, so the fragment offset field must always be zero.
             * The header was never memset to zero, so set both the fragment offset and fragmentation flags in one go.
             */
            #if ( ipconfigFORCE_IP_DONT_FRAGMENT != 0 )
                pxIPHeader->usFragmentOffset = ipFRAGMENT_FLAGS_DONT_FRAGMENT;
            #else
                pxIPHeader->usFragmentOffset = 0U;
            #endif
            usPacketIdentifier++;
            pxUDPHeader->usLength = FreeRTOS_htons( ( uint32_t ) lNetLength +
                                                    ipSIZE_OF_UDP_HEADER );
            vFlip_16( pxUDPHeader->usSourcePort, pxUDPHeader->usDestinationPort );

            /* Important: tell NIC driver how many bytes must be sent */
            uxDataLength = ( ( size_t ) lNetLength ) + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER + ipSIZE_OF_ETH_HEADER;

            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
                {
                    /* Calculate the IP header checksum. */
                    pxIPHeader->usHeaderChecksum = 0U;
                    pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
                    pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );

                    /* calculate the UDP checksum for outgoing package */
                    ( void ) usGenerateProtocolChecksum( ( uint8_t * ) pxUDPPacket, uxDataLength, pdTRUE );
                }
            #endif

            /* Important: tell NIC driver how many bytes must be sent */
            pxNetworkBuffer->xDataLength = uxDataLength;
        }

    #endif /* ipconfigUSE_NBNS == 1 || ipconfigUSE_LLMNR == 1 */

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
            uint16_t usFlags;
            uint16_t usType;
            uint16_t usClass;
            uint8_t * pucSource;
            uint8_t * pucTarget;
            uint8_t ucByte;
            uint8_t ucNBNSName[ 17 ];
            uint8_t * pucUDPPayloadBuffer = pucPayload;
            NetworkBufferDescriptor_t * pxNetworkBuffer;

            /* Read the request flags in host endianness. */
            usFlags = usChar2u16( &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, usFlags ) ] ) );

            if( ( usFlags & dnsNBNS_FLAGS_OPCODE_MASK ) == dnsNBNS_FLAGS_OPCODE_QUERY )
            {
                usType = usChar2u16( &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, usType ) ] ) );
                usClass = usChar2u16( &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, usClass ) ] ) );

                /* Not used for now */
                ( void ) usClass;

                /* For NBNS a name is 16 bytes long, written with capitals only.
                 * Make sure that the copy is terminated with a zero. */
                pucTarget = &( ucNBNSName[ sizeof( ucNBNSName ) - 2U ] );
                pucTarget[ 1 ] = ( uint8_t ) 0U;

                /* Start with decoding the last 2 bytes. */
                pucSource = &( pucUDPPayloadBuffer[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) +
                                                    offsetof( NBNSRequest_t, ucName ) ] );

                for( ; ; )
                {
                    const uint8_t ucCharA = ( uint8_t ) 0x41U;

                    ucByte = ( ( uint8_t ) ( ( pucSource[ 0 ] - ucCharA ) << 4 ) ) |
                             ( pucSource[ 1 ] - ucCharA );

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
                            ( void ) FreeRTOS_dns_update( ( char * ) ucNBNSName, &( ulIPAddress ), 0 );
                        }
                    }
                #else
                    {
                        /* Avoid compiler warnings. */
                        ( void ) ulIPAddress;
                    }
                #endif /* ipconfigUSE_DNS_CACHE */

                if( ( ( usFlags & dnsNBNS_FLAGS_RESPONSE ) == 0U ) &&
                    ( usType == dnsNBNS_TYPE_NET_BIOS ) &&
                    ( xApplicationDNSQueryHook( ( const char * ) ucNBNSName ) != pdFALSE ) )
                {
                    uint16_t usLength;
                    DNSMessage_t * pxMessage;
                    NBNSAnswer_t * pxAnswer;
                    NetworkBufferDescriptor_t * pxNewBuffer = NULL;

                    /* Someone is looking for a device with ucNBNSName,
                     * prepare a positive reply. */
                    pxNetworkBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pucUDPPayloadBuffer );

                    if( ( xBufferAllocFixedSize == pdFALSE ) &&
                        ( pxNetworkBuffer != NULL ) )
                    {
                        /* The field xDataLength was set to the total length of the UDP packet,
                         * i.e. the payload size plus sizeof( UDPPacket_t ). */
                        pxNewBuffer = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, pxNetworkBuffer->xDataLength + sizeof( NBNSAnswer_t ) );

                        if( pxNewBuffer != NULL )
                        {
                            pucUDPPayloadBuffer = &( pxNewBuffer->pucEthernetBuffer[ sizeof( UDPPacket_t ) ] );
                            pxNetworkBuffer = pxNewBuffer;
                        }
                        else
                        {
                            /* Just prevent that a reply will be sent */
                            pxNetworkBuffer = NULL;
                        }
                    }

                    /* Should not occur: pucUDPPayloadBuffer is part of a xNetworkBufferDescriptor */
                    if( pxNetworkBuffer != NULL )
                    {
                        pxMessage = ( ( DNSMessage_t * ) pucUDPPayloadBuffer );

                        /* As the fields in the structures are not word-aligned, we have to
                         * copy the values byte-by-byte using macro's vSetField16() and vSetField32() */
                        #ifndef _lint
                            vSetField16( pxMessage, DNSMessage_t, usFlags, dnsNBNS_QUERY_RESPONSE_FLAGS ); /* 0x8500 */
                            vSetField16( pxMessage, DNSMessage_t, usQuestions, 0 );
                            vSetField16( pxMessage, DNSMessage_t, usAnswers, 1 );
                            vSetField16( pxMessage, DNSMessage_t, usAuthorityRRs, 0 );
                            vSetField16( pxMessage, DNSMessage_t, usAdditionalRRs, 0 );
                        #else
                            ( void ) pxMessage;
                        #endif

                        pxAnswer = ( ( NBNSAnswer_t * ) &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, usType ) ] ) );

                        #ifndef _lint
                            vSetField16( pxAnswer, NBNSAnswer_t, usType, usType );            /* Type */
                            vSetField16( pxAnswer, NBNSAnswer_t, usClass, dnsNBNS_CLASS_IN ); /* Class */
                            vSetField32( pxAnswer, NBNSAnswer_t, ulTTL, dnsNBNS_TTL_VALUE );
                            vSetField16( pxAnswer, NBNSAnswer_t, usDataLength, 6 );           /* 6 bytes including the length field */
                            vSetField16( pxAnswer, NBNSAnswer_t, usNbFlags, dnsNBNS_NAME_FLAGS );
                            vSetField32( pxAnswer, NBNSAnswer_t, ulIPAddress, FreeRTOS_ntohl( *ipLOCAL_IP_ADDRESS_POINTER ) );
                        #else
                            ( void ) pxAnswer;
                        #endif

                        usLength = ( uint16_t ) ( sizeof( NBNSAnswer_t ) + ( size_t ) offsetof( NBNSRequest_t, usType ) );

                        prepareReplyDNSMessage( pxNetworkBuffer, ( BaseType_t ) usLength );
                        /* This function will fill in the eth addresses and send the packet */
                        vReturnEthernetFrame( pxNetworkBuffer, pdFALSE );

                        if( pxNewBuffer != NULL )
                        {
                            vReleaseNetworkBufferAndDescriptor( pxNewBuffer );
                        }
                    }
                }
            }
        }

    #endif /* ipconfigUSE_NBNS */
#endif /* ipconfigUSE_DNS != 0 */
