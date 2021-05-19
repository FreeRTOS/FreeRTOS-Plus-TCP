/*
 * FreeRTOS+TCP V2.3.2
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
 * https://github.com/FreeRTOS
 * https://www.FreeRTOS.org
 */

/**
 * @file DNS_Parser.c
 * @brief Implements the Domain Name System for the FreeRTOS+TCP network stack.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "DNS/DNS_Globals.h"

#include "DNS/DNS_Parser.h"
#include "DNS/DNS_Cache.h"
#include "DNS/DNS_Callback.h"

#include "NetworkBufferManagement.h"

#include <string.h>

#if ( ipconfigUSE_DNS != 0 )

/** @brief The list of all callback structures. */

/**
 * @brief Utility function to cast pointer of a type to pointer of type DNSCallback_t.
 *
 * @return The casted pointer.
 */
static portINLINE ipDECL_CAST_PTR_FUNC_FOR_TYPE( DNSCallback_t )
{
    return ( DNSCallback_t * ) pvArgument;
}
/**
 * @brief Utility function to cast pointer of a type to pointer of type DNSAnswerRecord_t.
 *
 * @return The casted pointer.
 */
static portINLINE ipDECL_CAST_PTR_FUNC_FOR_TYPE( DNSAnswerRecord_t )
{
    return ( DNSAnswerRecord_t * ) pvArgument;
}

/**
 * @brief Utility function to cast pointer of a type to pointer of type DNSMessage_t.
 *
 * @return The casted pointer.
 */
    static portINLINE ipDECL_CAST_PTR_FUNC_FOR_TYPE( DNSMessage_t )
    {
        return ( DNSMessage_t * ) pvArgument;
    }

/**
 * @brief Utility function to cast a const pointer of a type to a const pointer of type DNSMessage_t.
 *
 * @return The casted pointer.
 */
    static portINLINE ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( DNSMessage_t )
    {
        return ( const DNSMessage_t * ) pvArgument;
    }

    #if ( ipconfigUSE_LLMNR == 1 )

/**
 * @brief Utility function to cast pointer of a type to pointer of type LLMNRAnswer_t.
 *
 * @return The casted pointer.
 */
        static portINLINE ipDECL_CAST_PTR_FUNC_FOR_TYPE( LLMNRAnswer_t )
        {
            return ( LLMNRAnswer_t * ) pvArgument;
        }


    #endif /* ipconfigUSE_LLMNR == 1 */

    #if ( ipconfigUSE_NBNS == 1 )

/**
 * @brief Utility function to cast pointer of a type to pointer of type NBNSAnswer_t.
 *
 * @return The casted pointer.
 */
        static portINLINE ipDECL_CAST_PTR_FUNC_FOR_TYPE( NBNSAnswer_t )
        {
            return ( NBNSAnswer_t * ) pvArgument;
        }

    #endif /* ipconfigUSE_NBNS == 1 */

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
    /* This pointer is not used to modify anything */
    const DNSAnswerRecord_t * pxDNSAnswerRecord;
    uint32_t ulIPAddress = 0UL;

    #if ( ipconfigUSE_LLMNR == 1 )
        char * pcRequestedName = NULL;
    #endif
    uint8_t * pucByte;
    size_t uxSourceBytesRemaining;
    uint16_t x, usDataLength, usQuestions;
    uint16_t usType = 0U;
    BaseType_t xReturn = pdTRUE;
    /* memcpy() helper variables for MISRA Rule 21.15 compliance*/
    const void * pvCopySource;
    void * pvCopyDest;

    #if ( ipconfigUSE_LLMNR == 1 )
        uint16_t usClass = 0U;
    #endif
    #if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
        BaseType_t xDoStore = xExpected;
        char pcName[ ipconfigDNS_CACHE_NAME_LENGTH ] = "";
    #endif
    const size_t uxAddressLength = ipSIZE_OF_IPv4_ADDRESS;

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
        pxDNSMessageHeader = ipCAST_PTR_TO_TYPE_PTR( DNSMessage_t,
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

            //prvSkipQuestionRecords(usQuestions);

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
            pxDNSMessageHeader->usAnswers = FreeRTOS_ntohs( pxDNSMessageHeader->usAnswers );

            if( ( pxDNSMessageHeader->usFlags & dnsRX_FLAGS_MASK ) == dnsEXPECTED_RX_FLAGS )
            {
                const uint16_t usCount = ( uint16_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
                uint16_t usNumARecordsStored = 0;

                for( x = 0U; x < pxDNSMessageHeader->usAnswers; x++ )
                {
                    BaseType_t xDoAccept;

                    if( usNumARecordsStored >= usCount )
                    {
                        /* Only count ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY number of records. */
                        break;
                    }

                    uxResult = DNS_SkipNameField( pucByte,
                                                    uxSourceBytesRemaining );

                    /* Check for a malformed response. */
                    if( uxResult == 0U )
                    {
                        xReturn = pdFALSE;
                        break;
                    }

                    uxBytesRead += uxResult;
                    pucByte = &( pucByte[ uxResult ] );
                    uxSourceBytesRemaining -= uxResult;

                    /* Is there enough data for an IPv4 A record answer and, if so,
                        * is this an A record? */
                    if( uxSourceBytesRemaining < sizeof( uint16_t ) )
                    {
                        xReturn = pdFALSE;
                        break;
                    }

                    usType = usChar2u16( pucByte );

                    if( usType == ( uint16_t ) dnsTYPE_A_HOST )
                    {
                        if( uxSourceBytesRemaining >= ( sizeof( DNSAnswerRecord_t ) + uxAddressLength ) )
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

                        /* Mapping pucByte to a DNSAnswerRecord allows easy access of the
                            * fields of the structure. */
                        pxDNSAnswerRecord = ipCAST_PTR_TO_TYPE_PTR( DNSAnswerRecord_t, pucByte );

                        /* Sanity check the data length of an IPv4 answer. */
                        if( FreeRTOS_ntohs( pxDNSAnswerRecord->usDataLength ) == ( uint16_t ) uxAddressLength )
                        {
                            /* Copy the IP address out of the record. Using different pointers
                                * to copy only the portion we want is intentional here. */

                            /*
                                * Use helper variables for memcpy() to remain
                                * compliant with MISRA Rule 21.15.  These should be
                                * optimized away.
                                */
                            pvCopySource = &pucByte[ sizeof( DNSAnswerRecord_t ) ];
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
                                                    pxDNSAnswerRecord->ulTTL);
                                        usNumARecordsStored++; /* Track # of A records stored */
                                    }

                                    ( void ) FreeRTOS_inet_ntop( FREERTOS_AF_INET, ( const void * ) &( ulIPAddress ), cBuffer, sizeof( cBuffer ) );
                                    /* Show what has happened. */
                                    FreeRTOS_printf( ( "DNS[0x%04lX]: The answer to '%s' (%s) will%s be stored\n",
                                                        ( UBaseType_t ) pxDNSMessageHeader->usIdentifier,
                                                        pcName,
                                                        cBuffer,
                                                        ( xDoStore != 0 ) ? "" : " NOT" ) );
                                }
                            #endif /* ipconfigUSE_DNS_CACHE */
                        }

                        pucByte = &( pucByte[ sizeof( DNSAnswerRecord_t ) + uxAddressLength ] );
                        uxSourceBytesRemaining -= ( sizeof( DNSAnswerRecord_t ) + uxAddressLength );
                    }
                    else if( uxSourceBytesRemaining >= sizeof( DNSAnswerRecord_t ) )
                    {
                        /* It's not an A record, so skip it. Get the header location
                            * and then jump over the header. */
                        /* Cast the response to DNSAnswerRecord for easy access to fields of the DNS response. */
                        pxDNSAnswerRecord = ipCAST_PTR_TO_TYPE_PTR( DNSAnswerRecord_t, pucByte );

                        pucByte = &( pucByte[ sizeof( DNSAnswerRecord_t ) ] );
                        uxSourceBytesRemaining -= sizeof( DNSAnswerRecord_t );

                        /* Determine the length of the answer data from the header. */
                        usDataLength = FreeRTOS_ntohs( pxDNSAnswerRecord->usDataLength );

                        /* Jump over the answer. */
                        if( uxSourceBytesRemaining >= usDataLength )
                        {
                            pucByte = &( pucByte[ usDataLength ] );
                            uxSourceBytesRemaining -= usDataLength;
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
            }

            #if ( ipconfigUSE_LLMNR == 1 )

                /* No need to check that pcRequestedName != NULL since sQuestions != 0, then
                    * pcRequestedName is assigned with this statement
                    * "pcRequestedName = ( char * ) pucByte;" */
                else if( ( usQuestions != ( uint16_t ) 0U ) && ( usType == dnsTYPE_A_HOST ) && ( usClass == dnsCLASS_IN ) )
                {
                    /* If this is not a reply to our DNS request, it might an LLMNR
                        * request. */
                    if( xApplicationDNSQueryHook( &( pcRequestedName[ 1 ] ) ) != pdFALSE )
                    {
                        int16_t usLength;
                        NetworkBufferDescriptor_t * pxNewBuffer = NULL;
                        NetworkBufferDescriptor_t * pxNetworkBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pucUDPPayloadBuffer );
                        LLMNRAnswer_t * pxAnswer;
                        uint8_t * pucNewBuffer = NULL;

                        if( ( xBufferAllocFixedSize == pdFALSE ) && ( pxNetworkBuffer != NULL ) )
                        {
                            size_t uxDataLength = uxBufferLength + sizeof( UDPHeader_t ) + sizeof( EthernetHeader_t ) + sizeof( IPHeader_t );

                            /* Set the size of the outgoing packet. */
                            pxNetworkBuffer->xDataLength = uxDataLength;
                            pxNewBuffer = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, uxDataLength + sizeof( LLMNRAnswer_t ) );

                            if( pxNewBuffer != NULL )
                            {
                                BaseType_t xOffset1, xOffset2;

                                xOffset1 = ( BaseType_t ) ( pucByte - pucUDPPayloadBuffer );
                                xOffset2 = ( BaseType_t ) ( ( ( uint8_t * ) pcRequestedName ) - pucUDPPayloadBuffer );

                                pxNetworkBuffer = pxNewBuffer;
                                pucNewBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );

                                pucByte = &( pucNewBuffer[ xOffset1 ] );
                                pcRequestedName = ( char * ) &( pucNewBuffer[ xOffset2 ] );
                                pxDNSMessageHeader = ipCAST_PTR_TO_TYPE_PTR( DNSMessage_t, pucNewBuffer );
                            }
                            else
                            {
                                /* Just to indicate that the message may not be answered. */
                                pxNetworkBuffer = NULL;
                            }
                        }

                        /* The test on 'pucNewBuffer' is only to satisfy lint. */
                        if( ( pxNetworkBuffer != NULL ) && ( pucNewBuffer != NULL ) )
                        {
                            pxAnswer = ipCAST_PTR_TO_TYPE_PTR( LLMNRAnswer_t, pucByte );

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
                                vSetField32( pxAnswer, LLMNRAnswer_t, ulIPAddress, FreeRTOS_ntohl( *ipLOCAL_IP_ADDRESS_POINTER ) );
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
        ulIPAddress = dnsPARSE_ERROR;
    }
    else if( xExpected == pdFALSE )
    {
        /* Do not return a valid IP-address in case the reply was not expected. */
        ulIPAddress = 0UL;
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

            pxUDPPacket = ipCAST_PTR_TO_TYPE_PTR( UDPPacket_t, pxNetworkBuffer->pucEthernetBuffer );
            pxIPHeader = &pxUDPPacket->xIPHeader;
            pxUDPHeader = &pxUDPPacket->xUDPHeader;
            /* HT: started using defines like 'ipSIZE_OF_xxx' */
            pxIPHeader->usLength = FreeRTOS_htons( ( uint16_t ) lNetLength + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER );
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
            pxUDPHeader->usLength = FreeRTOS_htons( ( uint32_t ) lNetLength + ipSIZE_OF_UDP_HEADER );
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

#endif /* ipconfigUSE_DNS != 0 */
