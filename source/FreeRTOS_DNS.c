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
 * @file FreeRTOS_DNS.c
 * @brief Implements the Domain Name System for the FreeRTOS+TCP network stack.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_DNS_Globals.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "FreeRTOS_DNS_Cache.h"
#include "FreeRTOS_DNS_Parser.h"
#include "FreeRTOS_DNS_Networking.h"
#include "FreeRTOS_DNS_Callback.h"


/* Exclude the entire file if DNS is not enabled. */
#if ( ipconfigUSE_DNS != 0 )

/*
 * Create the DNS message in the zero copy buffer passed in the first parameter.
 */
    _static size_t prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                                        const char * pcHostName,
                                        TickType_t uxIdentifier );


/*
 * Check if hostname is already known. If not, call prvGetHostByName() to send a DNS request.
 */
    #if ( ipconfigDNS_USE_CALLBACKS == 1 )
        static uint32_t prvPrepareLookup( const char * pcHostName,
                                          FOnDNSEvent pCallback,
                                          void * pvSearchID,
                                          TickType_t uxTimeout );
    #else
        static uint32_t prvPrepareLookup( const char * pcHostName );
    #endif

/*
 * Prepare and send a message to a DNS server.  'uxReadTimeOut_ticks' will be passed as
 * zero, in case the user has supplied a call-back function.
 */
    static uint32_t prvGetHostByName( const char * pcHostName,
                                      TickType_t uxIdentifier,
                                      TickType_t uxReadTimeOut_ticks );

    #if ( ipconfigUSE_LLMNR == 1 )
        /** @brief The MAC address used for LLMNR. */
        const MACAddress_t xLLMNR_MacAdress = { { 0x01, 0x00, 0x5e, 0x00, 0x00, 0xfc } };
    #endif /* ipconfigUSE_LLMNR == 1 */

/*-----------------------------------------------------------*/

/**
 * @brief A DNS query consists of a header, as described in 'struct xDNSMessage'
 *        It is followed by 1 or more queries, each one consisting of a name and a tail,
 *        with two fields: type and class
 */
    #include "pack_struct_start.h"
    struct xDNSTail
    {
        uint16_t usType;  /**< Type of DNS message. */
        uint16_t usClass; /**< Class of DNS message. */
    }
    #include "pack_struct_end.h"
    typedef struct xDNSTail DNSTail_t;
/*-----------------------------------------------------------*/


    #if ( ipconfigDNS_USE_CALLBACKS == 1 )

/**
 * @brief Define FreeRTOS_gethostbyname() as a normal blocking call.
 * @param[in] pcHostName: The hostname whose IP address is being searched for.
 * @return The IP-address of the hostname.
 */
        uint32_t FreeRTOS_gethostbyname( const char * pcHostName )
        {
            return FreeRTOS_gethostbyname_a( pcHostName, NULL, ( void * ) NULL, 0U );
        }
        /*-----------------------------------------------------------*/

/** @brief Initialise the list of call-back structures.
 */
        void vDNSInitialise( void )
        {
            vDNSCallbackInitialise();
        }
        /*-----------------------------------------------------------*/


/**
 * @brief Remove the entry defined by the search ID to cancel a DNS request.
 * @param[in] pvSearchID: The search ID of the callback function associated with
 *                        the DNS request being cancelled. Note that the value of
 *                        the pointer matters, not the pointee.
 */
        void FreeRTOS_gethostbyname_cancel( void * pvSearchID )
        {
            /* _HT_ Should better become a new API call to have the IP-task remove the callback */
            vDNSCheckCallBack( pvSearchID );
        }
        /*-----------------------------------------------------------*/

/*-----------------------------------------------------------*/


    #endif /* ipconfigDNS_USE_CALLBACKS == 1 */
    /*-----------------------------------------------------------*/

    #if ( ipconfigDNS_USE_CALLBACKS == 0 )

/**
 * @brief Get the IP-address corresponding to the given hostname.
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 * @return The IP-address corresponding to the hostname. 0 is returned in
 *         case of failure.
 */
        uint32_t FreeRTOS_gethostbyname( const char * pcHostName )
        {
            return prvPrepareLookup( pcHostName );
        }
    #else

/**
 * @brief Get the IP-address corresponding to the given hostname.
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 * @param[in] pCallback: The callback function which will be called upon DNS response.
 * @param[in] pvSearchID: Search ID for the callback function.
 * @param[in] uxTimeout: Timeout for the callback function.
 * @return The IP-address corresponding to the hostname. 0 is returned in case of
 *         failure.
 */
        uint32_t FreeRTOS_gethostbyname_a( const char * pcHostName,
                                           FOnDNSEvent pCallback,
                                           void * pvSearchID,
                                           TickType_t uxTimeout )
        {
            return prvPrepareLookup( pcHostName, pCallback, pvSearchID, uxTimeout );
        }
    #endif /* if ( ipconfigDNS_USE_CALLBACKS == 0 ) */

    #if ( ipconfigDNS_USE_CALLBACKS == 1 )

/**
 * @brief Check if hostname is already known. If not, call prvGetHostByName() to send a DNS request.
 *
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 * @param[in] pCallback: The callback function which will be called upon DNS response.
 * @param[in] pvSearchID: Search ID for the callback function.
 * @param[in] uxTimeout: Timeout for the callback function.
 * @return The IP-address corresponding to the hostname.
 */
        static uint32_t prvPrepareLookup( const char * pcHostName,
                                          FOnDNSEvent pCallback,
                                          void * pvSearchID,
                                          TickType_t uxTimeout )
    #else

/**
 * @brief Check if hostname is already known. If not, call prvGetHostByName() to send a DNS request.
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 * @return The IP-address corresponding to the hostname.
 */
        static uint32_t prvPrepareLookup( const char * pcHostName )
    #endif
    {
        uint32_t ulIPAddress = 0U;
        TickType_t uxReadTimeOut_ticks = ipconfigDNS_RECEIVE_BLOCK_TIME_TICKS;

        /* Generate a unique identifier for this query. Keep it in a local variable
         * as gethostbyname() may be called from different threads */
        BaseType_t xHasRandom = pdFALSE;
        TickType_t uxIdentifier = 0U;

        BaseType_t xLengthOk = pdFALSE;

        if( pcHostName != NULL )
        {
            size_t xLength = strlen( pcHostName ) + 1U;

            #if ( ipconfigUSE_DNS_CACHE != 0 )
                if( xLength <= ipconfigDNS_CACHE_NAME_LENGTH )
            #else
                if( xLength <= dnsMAX_HOSTNAME_LENGTH )
            #endif
            {
                /* The name is not too long. */
                xLengthOk = pdTRUE;
            }
            else
            {
                FreeRTOS_printf( ( "prvPrepareLookup: name is too long ( %lu > %lu )\n",
                                   ( uint32_t ) xLength,
                                   ( uint32_t ) ipconfigDNS_CACHE_NAME_LENGTH ) );
            }
        }

        if( ( pcHostName != NULL ) && ( xLengthOk != pdFALSE ) )
        {
            /* If the supplied hostname is IP address, convert it to uint32_t
             * and return. */
            #if ( ipconfigINCLUDE_FULL_INET_ADDR == 1 )
                {
                    ulIPAddress = FreeRTOS_inet_addr( pcHostName );
                }
            #endif /* ipconfigINCLUDE_FULL_INET_ADDR == 1 */

            #if ( ipconfigUSE_DNS_CACHE == 1 )
                /* Check the cache before issuing another DNS request. */
                if( ulIPAddress == 0U )
                {
                    ulIPAddress = FreeRTOS_dnslookup( pcHostName );

                    if( ulIPAddress != 0U )
                    {
                        FreeRTOS_debug_printf( ( "FreeRTOS_gethostbyname: found '%s' in cache: %lxip\n", pcHostName, ulIPAddress ) );
                    }
                    else
                    {
                        /* prvGetHostByName will be called to start a DNS lookup. */
                    }
                }
            #endif /* if ( ipconfigUSE_DNS_CACHE == 1 ) */

            /* Generate a unique identifier. */
            if( ulIPAddress == 0U )
            {
                uint32_t ulNumber;

                xHasRandom = xApplicationGetRandomNumber( &( ulNumber ) );
                /* DNS identifiers are 16-bit. */
                uxIdentifier = ( TickType_t ) ( ulNumber & 0xffffU );
            }

            #if ( ipconfigDNS_USE_CALLBACKS == 1 )
                {
                    if( pCallback != NULL )
                    {
                        if( ulIPAddress == 0U )
                        {
                            /* The user has provided a callback function, so do not block on recvfrom() */
                            if( xHasRandom != pdFALSE )
                            {
                                uxReadTimeOut_ticks = 0U;
                                vDNSSetCallBack( pcHostName,
                                                 pvSearchID,
                                                 pCallback,
                                                 uxTimeout,
                                                 uxIdentifier );
                            }
                        }
                        else
                        {
                            /* The IP address is known, do the call-back now. */
                            pCallback( pcHostName, pvSearchID, ulIPAddress );
                        }
                    }
                }
            #endif /* if ( ipconfigDNS_USE_CALLBACKS == 1 ) */

            if( ( ulIPAddress == 0U ) && ( xHasRandom != pdFALSE ) )
            {
                ulIPAddress = prvGetHostByName( pcHostName,
                                                uxIdentifier,
                                                uxReadTimeOut_ticks );
            }
        }

        return ulIPAddress;
    }
    /*-----------------------------------------------------------*/

    #if ( ipconfigUSE_LLMNR == 1 )

/*!
 * @brief If LLMNR is being used then determine if the host name includes a '.'
 *        if not then LLMNR can be used as the lookup method.
 * @param [in] pcHostName hostname to check
 * @returns true if the hostname is a dotted format, else false
 *
 */
        static BaseType_t llmnr_has_dot( const char * pcHostName )
        {
            BaseType_t bHasDot = pdFALSE;
            const char * pucPtr;

            for( pucPtr = pcHostName; *pucPtr != ( char ) 0; pucPtr++ )
            {
                if( *pucPtr == '.' )
                {
                    bHasDot = pdTRUE;
                    break;
                }
            }

            return bHasDot;
        }
    #endif /* if ( ipconfigUSE_LLMNR == 1 ) */

/*!
 * @brief create a payload buffer and return it through the parameter
 * @param [out] ppxNetworkBuffer network buffer to create
 * @param [in] pcHostName hostname to get its length
 * @returns pointer address to the payload buffer
 *
 */
    static uint8_t * prvGetPayloadBuffer( NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                                          const char * pcHostName )
    {
        size_t uxExpectedPayloadLength;
        uint8_t * pucUDPPayloadBuffer = NULL;
        size_t uxHeaderBytes;

        uxHeaderBytes = ipSIZE_OF_ETH_HEADER +
                        ipSIZE_OF_IPv4_HEADER +
                        ipSIZE_OF_UDP_HEADER;

        uxExpectedPayloadLength = sizeof( DNSMessage_t ) +
                                  strlen( pcHostName ) +
                                  sizeof( uint16_t ) +
                                  sizeof( uint16_t ) + 2U;

        /* Get a buffer.  This uses a maximum delay, but the delay will be
         * capped to ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS so the return value
         * still needs to be tested. */
        *ppxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxExpectedPayloadLength +
                                                              uxHeaderBytes,
                                                              0U );

        if( *ppxNetworkBuffer != NULL )
        {
            pucUDPPayloadBuffer = &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ uxHeaderBytes ] );
        }

        return pucUDPPayloadBuffer;
    }

/*!
 * @brief fill  pxAddress from pucUDPPayloadBuffer
 * @param [out] pxAddress ip address and port ... structure
 * @param [in]  pcHostName hostname to get its length
 */
    static void prvFillSockAddress( struct freertos_sockaddr * pxAddress,
                                    const char * pcHostName )
    {
        uint32_t ulIPAddress = 0U;

        #if ( ipconfigUSE_LLMNR != 1 )
            ( void ) pcHostName;
        #endif

        /* Obtain the DNS server address. */
        FreeRTOS_GetAddressConfiguration( NULL, NULL, NULL, &ulIPAddress );
        #if ( ipconfigUSE_LLMNR == 1 )
            BaseType_t bHasDot = llmnr_has_dot( pcHostName );

            if( bHasDot == pdFALSE )
            {
                /* Use LLMNR addressing. */
                pxAddress->sin_addr = ipLLMNR_IP_ADDR; /* Is in network byte order. */
                pxAddress->sin_port = ipLLMNR_PORT;
                pxAddress->sin_port = FreeRTOS_ntohs( pxAddress->sin_port );
            }
            else
        #endif /* if ( ipconfigUSE_LLMNR == 1 ) */
        {
            /* Use DNS server. */
            pxAddress->sin_addr = ulIPAddress;
            pxAddress->sin_port = dnsDNS_PORT;
        }
    }

/*!
 * @brief return ip address from the dns reply message
 * @param [in] pxReceiveBuffer received buffer from the DNS server
 * @param [in] uxIdentifier matches sent and received packets
 * @returns ip address or zero on error
 *
 */
    static uint32_t prvDNSReply( const struct xDNSBuffer * pxReceiveBuffer,
                                 TickType_t uxIdentifier )
    {
        uint32_t ulIPAddress = 0U;
        BaseType_t xExpected;

        /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        const DNSMessage_t * pxDNSMessageHeader =
            ( ( const DNSMessage_t * )
              pxReceiveBuffer->pucPayloadBuffer );

        /* See if the identifiers match. */
        if( uxIdentifier == ( TickType_t ) pxDNSMessageHeader->usIdentifier )
        {
            xExpected = pdTRUE;
        }
        else
        {
            xExpected = pdFALSE;
        }

        /* The reply was received.  Process it. */
        #if ( ipconfigDNS_USE_CALLBACKS == 0 )

            /* It is useless to analyse the unexpected reply
             * unless asynchronous look-ups are enabled. */
            if( xExpected != pdFALSE )
        #endif /* ipconfigDNS_USE_CALLBACKS == 0 */
        {
            ulIPAddress = DNS_ParseDNSReply( pxReceiveBuffer->pucPayloadBuffer,
                                             pxReceiveBuffer->uxPayloadLength,
                                             xExpected );
        }

        return ulIPAddress;
    }

/*!
 * @brief prepare the buffer before sending
 * @param [in] pcHostName
 * @param [in] uxIdentifier  matches sent and received packets
 * @param [in] xDNSSocket a valid socket
 * @param [in] pxAddress address structure
 * @returns pdTRUE if sending the data was successful, pdFALSE otherwise.
 */
    static BaseType_t prvSendBuffer( const char * pcHostName,
                                     TickType_t uxIdentifier,
                                     Socket_t xDNSSocket,
                                     const struct freertos_sockaddr * pxAddress )
    {
        BaseType_t uxReturn = pdFAIL;
        struct xDNSBuffer xDNSBuf = { 0 };
        NetworkBufferDescriptor_t * pxNetworkBuffer = NULL;

        /*get dns message buffer */
        xDNSBuf.pucPayloadBuffer = prvGetPayloadBuffer( &pxNetworkBuffer,
                                                        pcHostName );

        if( xDNSBuf.pucPayloadBuffer != NULL )
        {
            xDNSBuf.uxPayloadSize = pxNetworkBuffer->xDataLength;

            #if ( ipconfigUSE_LLMNR == 1 )
                {
                    if( FreeRTOS_ntohs( pxAddress->sin_port ) == ipLLMNR_PORT )
                    {
                        ( ( ( DNSMessage_t * ) xDNSBuf.pucPayloadBuffer ) )->usFlags = 0;
                    }
                }
            #endif

            xDNSBuf.uxPayloadLength = prvCreateDNSMessage( xDNSBuf.pucPayloadBuffer,
                                                           pcHostName,
                                                           uxIdentifier );

            /* send the dns message */
            uxReturn = DNS_SendRequest( xDNSSocket,
                                        pxAddress,
                                        &xDNSBuf );

            if( uxReturn == pdFAIL )
            {
                vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
            }
        }

        return uxReturn;
    }

/*!
 * @brief main dns operation description function
 * @param [in] pcHostName hostname to get its ip address
 * @param [in] uxIdentifier Identifier to match sent and received packets
 * @param [in] xDNSSocket socket
 * @returns ip address or zero on error
 */
    static uint32_t prvGetHostByNameOp( const char * pcHostName,
                                        TickType_t uxIdentifier,
                                        Socket_t xDNSSocket )
    {
        uint32_t ulIPAddress = 0;

        struct freertos_sockaddr xAddress;
        DNSBuffer_t xReceiveBuffer = { 0 };
        BaseType_t uxReturn = pdFAIL;

        prvFillSockAddress( &xAddress, pcHostName );

        do
        {
            uxReturn = prvSendBuffer( pcHostName,
                                      uxIdentifier,
                                      xDNSSocket,
                                      &xAddress );

            if( uxReturn == pdFAIL )
            {
                break;
            }

            /* Create the message in the obtained buffer. */

            /* receive a dns reply message */
            DNS_ReadReply( xDNSSocket,
                           &xAddress,
                           &xReceiveBuffer );

            if( xReceiveBuffer.pucPayloadBuffer == NULL )
            {
                break;
            }

            ulIPAddress = prvDNSReply( &xReceiveBuffer, uxIdentifier );

            /* Finished with the buffer.  The zero copy interface
             * is being used, so the buffer must be freed by the
             * task. */
            FreeRTOS_ReleaseUDPPayloadBuffer( xReceiveBuffer.pucPayloadBuffer );
        } while( ipFALSE_BOOL );

        return ulIPAddress;
    }

/*!
 * @brief helper function to prvGetHostByNameOP with multiple retries equal to
 *        ipconfigDNS_REQUEST_ATTEMPTS
 *
 * @param [in] pcHostName hostname to get its ip address
 * @param [in] uxIdentifier Identifier to match sent and received packets
 * @param [in] xDNSSocket socket
 * @returns ip address or zero on error
 *
 */
    static uint32_t prvGetHostByNameOp_WithRetry( const char * pcHostName,
                                                  TickType_t uxIdentifier,
                                                  Socket_t xDNSSocket )
    {
        uint32_t ulIPAddress;
        BaseType_t xAttempt;

        for( xAttempt = 0; xAttempt < ipconfigDNS_REQUEST_ATTEMPTS; xAttempt++ )
        {
            ulIPAddress = prvGetHostByNameOp( pcHostName,
                                              uxIdentifier,
                                              xDNSSocket );

            if( ulIPAddress != 0U )
            { /* ip found, no need to retry */
                break;
            }
        }

        return ulIPAddress;
    }


/**
 * @brief Prepare and send a message to a DNS server.  'uxReadTimeOut_ticks' will be passed as
 *        zero, in case the user has supplied a call-back function.
 *
 * @param[in] pcHostName The hostname for which an IP address is required.
 * @param[in] uxIdentifier Identifier to match sent and received packets
 * @param[in] uxReadTimeOut_ticks The timeout in ticks for waiting. In case the user has supplied
 *                                 a call-back function, this value should be zero.
 * @return The IPv4 IP address for the hostname being queried. It will be zero if there is no reply.
 */
    static uint32_t prvGetHostByName( const char * pcHostName,
                                      TickType_t uxIdentifier,
                                      TickType_t uxReadTimeOut_ticks )
    {
        Socket_t xDNSSocket;
        uint32_t ulIPAddress = 0U;

        xDNSSocket = DNS_CreateSocket( uxReadTimeOut_ticks );

        if( xDNSSocket != NULL )
        {
            if( uxReadTimeOut_ticks == 0U )
            {
                ulIPAddress = prvGetHostByNameOp( pcHostName,
                                                  uxIdentifier,
                                                  xDNSSocket );
            }
            else
            {
                ulIPAddress = prvGetHostByNameOp_WithRetry( pcHostName,
                                                            uxIdentifier,
                                                            xDNSSocket );
            }

            /* Finished with the socket. */
            DNS_CloseSocket( xDNSSocket );
        }

        return ulIPAddress;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Create the DNS message in the zero copy buffer passed in the first parameter.
 * @param[in,out] pucUDPPayloadBuffer The zero copy buffer where the DNS message will be created.
 * @param[in] pcHostName Hostname to be looked up.
 * @param[in] uxIdentifier Identifier to match sent and received packets
 * @return Total size of the generated message, which is the space from the last written byte
 *         to the beginning of the buffer.
 */
    _static size_t prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                                        const char * pcHostName,
                                        TickType_t uxIdentifier )
    {
        DNSMessage_t * pxDNSMessageHeader;
        size_t uxStart, uxIndex;
        DNSTail_t const * pxTail;
        static const DNSMessage_t xDefaultPartDNSHeader =
        {
            0,                 /* The identifier will be overwritten. */
            dnsOUTGOING_FLAGS, /* Flags set for standard query. */
            dnsONE_QUESTION,   /* One question is being asked. */
            0,                 /* No replies are included. */
            0,                 /* No authorities. */
            0                  /* No additional authorities. */
        };

        /* memcpy() helper variables for MISRA Rule 21.15 compliance*/
        const void * pvCopySource;
        void * pvCopyDest;

        /* Copy in the const part of the header. Intentionally using different
         * pointers with memcpy() to put the information in to correct place. */

        /*
         * Use helper variables for memcpy() to remain
         * compliant with MISRA Rule 21.15.  These should be
         * optimized away.
         */
        pvCopySource = &xDefaultPartDNSHeader;
        pvCopyDest = pucUDPPayloadBuffer;
        ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( xDefaultPartDNSHeader ) );

        /* Write in a unique identifier. Cast the Payload Buffer to DNSMessage_t
         * to easily access fields of the DNS Message. */

        /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        pxDNSMessageHeader = ( ( DNSMessage_t * ) pucUDPPayloadBuffer );
        pxDNSMessageHeader->usIdentifier = ( uint16_t ) uxIdentifier;

        /* Create the resource record at the end of the header.  First
         * find the end of the header. */
        uxStart = sizeof( xDefaultPartDNSHeader );

        /* Leave a gap for the first length byte. */
        uxIndex = uxStart + 1U;

        /* Copy in the host name. */
        ( void ) strcpy( ( char * ) &( pucUDPPayloadBuffer[ uxIndex ] ), pcHostName );

        /* Walk through the string to replace the '.' characters with byte
         * counts.  pucStart holds the address of the byte count.  Walking the
         * string starts after the byte count position. */
        uxIndex = uxStart;

        do
        {
            size_t uxLength;

            /* Skip the length byte. */
            uxIndex++;

            while( ( pucUDPPayloadBuffer[ uxIndex ] != ( uint8_t ) 0U ) &&
                   ( pucUDPPayloadBuffer[ uxIndex ] != ( uint8_t ) ASCII_BASELINE_DOT ) )
            {
                uxIndex++;
            }

            /* Fill in the byte count, then move the pucStart pointer up to
             * the found byte position. */
            uxLength = uxIndex - ( uxStart + 1U );
            pucUDPPayloadBuffer[ uxStart ] = ( uint8_t ) uxLength;

            uxStart = uxIndex;
        } while( pucUDPPayloadBuffer[ uxIndex ] != ( uint8_t ) 0U );

        /* Finish off the record. Cast the record onto DNSTail_t structure to easily
         * access the fields of the DNS Message. */

        /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        pxTail = ( ( DNSTail_t * ) &( pucUDPPayloadBuffer[ uxStart + 1U ] ) );

        #if defined( _lint ) || defined( __COVERITY__ )
            ( void ) pxTail;
        #else
            vSetField16( pxTail, DNSTail_t, usType, dnsTYPE_A_HOST );
            vSetField16( pxTail, DNSTail_t, usClass, dnsCLASS_IN );
        #endif

        /* Return the total size of the generated message, which is the space from
         * the last written byte to the beginning of the buffer. */
        return uxIndex + sizeof( DNSTail_t ) + 1U;
    }

/*-----------------------------------------------------------*/

/* The function below will only be called :
 * when ipconfigDNS_USE_CALLBACKS == 1
 * when ipconfigUSE_LLMNR == 1
 * for testing purposes, by the module test_freertos_tcp.c
 */

/**
 * @brief Perform some preliminary checks and then parse the DNS packet.
 *
 * @param[in] pxNetworkBuffer: The network buffer to be parsed.
 *
 * @return pdFAIL Always to indicate that the packet was not consumed and must
 *         be released by the caller.
 */
    uint32_t ulDNSHandlePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        uint8_t * pucPayLoadBuffer;
        size_t uxPayloadSize;

        /* Only proceed if the payload length indicated in the header
         * appears to be valid. */
        if( pxNetworkBuffer->xDataLength >= sizeof( UDPPacket_t ) )
        {
            uxPayloadSize = pxNetworkBuffer->xDataLength - sizeof( UDPPacket_t );

            if( uxPayloadSize >= sizeof( DNSMessage_t ) )
            {
                pucPayLoadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_t ) ] );

                /* The parameter pdFALSE indicates that the reply was not expected. */
                ( void ) DNS_ParseDNSReply( pucPayLoadBuffer,
                                            uxPayloadSize,
                                            pdFALSE );
            }
        }

        /* The packet was not consumed. */
        return pdFAIL;
    }
    /*-----------------------------------------------------------*/


    #if ( ipconfigUSE_NBNS == 1 )

/**
 * @brief Handle an NBNS packet.
 *
 * @param[in] pxNetworkBuffer: The network buffer holding the NBNS packet.
 *
 * @return pdFAIL to show that the packet was not consumed.
 */
        uint32_t ulNBNSHandlePacket( NetworkBufferDescriptor_t * pxNetworkBuffer )
        {
            UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * )
                                          pxNetworkBuffer->pucEthernetBuffer );
            uint8_t * pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( *pxUDPPacket ) ] );

            size_t uxBytesNeeded = sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t );

            /* Check for minimum buffer size. */
            if( pxNetworkBuffer->xDataLength >= uxBytesNeeded )
            {
                DNS_TreatNBNS( pucUDPPayloadBuffer,
                               pxNetworkBuffer->xDataLength,
                               pxUDPPacket->xIPHeader.ulSourceIPAddress );
            }

            /* The packet was not consumed. */
            return pdFAIL;
        }

    #endif /* ipconfigUSE_NBNS */

/*-----------------------------------------------------------*/

#endif /* ipconfigUSE_DNS != 0 */

/*-----------------------------------------------------------*/

/* Provide access to private members for testing. */
#ifdef FREERTOS_ENABLE_UNIT_TESTS
    #include "freertos_tcp_test_access_dns_define.h"
#endif
