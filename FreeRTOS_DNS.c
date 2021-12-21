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
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "DNS_Cache.h"

/* Exclude the entire file if DNS is not enabled. */
#if ( ipconfigUSE_DNS != 0 )


/**
 * @brief structure to hold the buffer and its size
 */
    struct dns_buffer
    {
        uint8_t * pucPayloadBuffer; /*!< buffer to hold data */
        size_t uxPayloadLength;     /*!< size of the data in buffer */
    };

/*
 * Create a socket and bind it to the standard DNS port number.  Return the
 * the created socket - or NULL if the socket could not be created or bound.
 */
    static Socket_t prvCreateDNSSocket( TickType_t uxReadTimeOut_ticks );

/*
 * Create the DNS message in the zero copy buffer passed in the first parameter.
 */
    _static size_t prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                                        const char * pcHostName,
                                        TickType_t uxIdentifier );

/*
 * Simple routine that jumps over the NAME field of a resource record.
 * It returns the number of bytes read.
 */
    _static size_t prvSkipNameField( const uint8_t * pucByte,
                                     size_t uxLength );

/*
 * Process a response packet from a DNS server.
 * The parameter 'xExpected' indicates whether the identifier in the reply
 * was expected, and thus if the DNS cache may be updated with the reply.
 */
    _static uint32_t prvParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                                       size_t uxBufferLength,
                                       BaseType_t xExpected );

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

    #if ( ipconfigDNS_USE_CALLBACKS != 0 )
        static void vDNSSetCallBack( const char * pcHostName,
                                     void * pvSearchID,
                                     FOnDNSEvent pCallbackFunction,
                                     TickType_t uxTimeout,
                                     TickType_t uxIdentifier );
    #endif /* ipconfigDNS_USE_CALLBACKS */

    #if ( ipconfigDNS_USE_CALLBACKS != 0 )
        static BaseType_t xDNSDoCallback( TickType_t uxIdentifier,
                                          const char * pcName,
                                          uint32_t ulIPAddress );
    #endif /* ipconfigDNS_USE_CALLBACKS */

/*
 * The NBNS and the LLMNR protocol share this reply function.
 */
    #if ( ( ipconfigUSE_NBNS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) )
        static void prvReplyDNSMessage( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                        BaseType_t lNetLength );
    #endif

    #if ( ipconfigUSE_NBNS == 1 )
        static portINLINE void prvTreatNBNS( uint8_t * pucPayload,
                                             size_t uxBufferLength,
                                             uint32_t ulIPAddress );
    #endif /* ipconfigUSE_NBNS */


    #if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )

/*
 *      _static size_t prvReadNameField( const uint8_t * pucByte,
 *                                       size_t uxRemainingBytes,
 *                                       char * pcName,
 *                                       size_t uxDestLen );
 */
    #endif /* ipconfigUSE_DNS_CACHE || ipconfigDNS_USE_CALLBACKS */

    #if ( ipconfigUSE_LLMNR == 1 )
        /** @brief The MAC address used for LLMNR. */
        const MACAddress_t xLLMNR_MacAdress = { { 0x01, 0x00, 0x5e, 0x00, 0x00, 0xfc } };
    #endif /* ipconfigUSE_LLMNR == 1 */

/*-----------------------------------------------------------*/

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

/* A DNS query consists of a header, as described in 'struct xDNSMessage'
 * It is followed by 1 or more queries, each one consisting of a name and a tail,
 * with two fields: type and class
 */
    #include "pack_struct_start.h"
    struct xDNSTail
    {
        uint16_t usType;  /**< Type of DNS message. */
        uint16_t usClass; /**< Class of DNS message. */
    }
    #include "pack_struct_end.h"
    typedef struct xDNSTail DNSTail_t;

/**
 * @brief Utility function to cast pointer of a type to pointer of type DNSTail_t.
 *
 * @return The casted pointer.
 */
    static portINLINE ipDECL_CAST_PTR_FUNC_FOR_TYPE( DNSTail_t )
    {
        return ( DNSTail_t * ) pvArgument;
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

/*-----------------------------------------------------------*/

    #if ( ipconfigDNS_USE_CALLBACKS == 1 )

/**
 * @brief Utility function to cast pointer of a type to pointer of type DNSCallback_t.
 *
 * @return The casted pointer.
 */
        static portINLINE ipDECL_CAST_PTR_FUNC_FOR_TYPE( DNSCallback_t )
        {
            return ( DNSCallback_t * ) pvArgument;
        }

/** @brief The list of all callback structures. */
        _static List_t xCallbackList;

/**
 * @brief Define FreeRTOS_gethostbyname() as a normal blocking call.
 *
 * @param[in] pcHostName: The hostname whose IP address is being searched for.
 *
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
            vListInitialise( &xCallbackList );
        }
        /*-----------------------------------------------------------*/

/**
 * @brief Iterate through the list of call-back structures and remove
 *        old entries which have reached a timeout.
 *        As soon as the list has become empty, the DNS timer will be stopped.
 *        In case pvSearchID is supplied, the user wants to cancel a DNS request.
 *
 * @param[in] pvSearchID: The search ID of callback function whose associated
 *                 DNS request is being cancelled. If non-ID specific checking of
 *                 all requests is required, then this field should be kept as NULL.
 */
        void vDNSCheckCallBack( void * pvSearchID )
        {
            const ListItem_t * pxIterator;
            const ListItem_t * xEnd = listGET_END_MARKER( &xCallbackList );

            vTaskSuspendAll();
            {
                for( pxIterator = ( const ListItem_t * ) listGET_NEXT( xEnd );
                     pxIterator != xEnd;
                     )
                {
                    DNSCallback_t * pxCallback = ipCAST_PTR_TO_TYPE_PTR( DNSCallback_t, listGET_LIST_ITEM_OWNER( pxIterator ) );
                    /* Move to the next item because we might remove this item */
                    pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator );

                    if( ( pvSearchID != NULL ) && ( pvSearchID == pxCallback->pvSearchID ) )
                    {
                        ( void ) uxListRemove( &( pxCallback->xListItem ) );
                        vPortFree( pxCallback );
                    }
                    else if( xTaskCheckForTimeOut( &pxCallback->uxTimeoutState, &pxCallback->uxRemaningTime ) != pdFALSE )
                    {
                        pxCallback->pCallbackFunction( pxCallback->pcName, pxCallback->pvSearchID, 0 );
                        ( void ) uxListRemove( &( pxCallback->xListItem ) );
                        vPortFree( pxCallback );
                    }
                    else
                    {
                        /* This call-back is still waiting for a reply or a time-out. */
                    }
                }
            }
            ( void ) xTaskResumeAll();

            if( listLIST_IS_EMPTY( &xCallbackList ) != pdFALSE )
            {
                vIPSetDnsTimerEnableState( pdFALSE );
            }
        }
        /*-----------------------------------------------------------*/

/**
 * @brief Remove the entry defined by the search ID to cancel a DNS request.
 *
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

/**
 * @brief FreeRTOS_gethostbyname_a() was called along with callback parameters.
 *        Store them in a list for later reference.
 *
 * @param[in] pcHostName: The hostname whose IP address is being searched for.
 * @param[in] pvSearchID: The search ID of the DNS callback function to set.
 * @param[in] pCallbackFunction: The callback function pointer.
 * @param[in] uxTimeout: Timeout of the callback function.
 * @param[in] uxIdentifier: Random number used as ID in the DNS message.
 */
        static void vDNSSetCallBack( const char * pcHostName,
                                     void * pvSearchID,
                                     FOnDNSEvent pCallbackFunction,
                                     TickType_t uxTimeout,
                                     TickType_t uxIdentifier )
        {
            size_t lLength = strlen( pcHostName );
            DNSCallback_t * pxCallback = ipCAST_PTR_TO_TYPE_PTR( DNSCallback_t, pvPortMalloc( sizeof( *pxCallback ) + lLength ) );

            /* Translate from ms to number of clock ticks. */
            uxTimeout /= portTICK_PERIOD_MS;

            if( pxCallback != NULL )
            {
                if( listLIST_IS_EMPTY( &xCallbackList ) != pdFALSE )
                {
                    /* This is the first one, start the DNS timer to check for timeouts */
                    vIPReloadDNSTimer( FreeRTOS_min_uint32( 1000U, uxTimeout ) );
                }

                ( void ) strcpy( pxCallback->pcName, pcHostName );
                pxCallback->pCallbackFunction = pCallbackFunction;
                pxCallback->pvSearchID = pvSearchID;
                pxCallback->uxRemaningTime = uxTimeout;
                vTaskSetTimeOutState( &pxCallback->uxTimeoutState );
                listSET_LIST_ITEM_OWNER( &( pxCallback->xListItem ), ( void * ) pxCallback );
                listSET_LIST_ITEM_VALUE( &( pxCallback->xListItem ), uxIdentifier );
                vTaskSuspendAll();
                {
                    vListInsertEnd( &xCallbackList, &pxCallback->xListItem );
                }
                ( void ) xTaskResumeAll();
            }
            else
            {
                FreeRTOS_debug_printf( ( " vDNSSetCallBack : Could not allocate memory: %lu bytes",
                                         sizeof( *pxCallback ) + lLength ) );
            }
        }
        /*-----------------------------------------------------------*/

/**
 * @brief A DNS reply was received, see if there is any matching entry and
 *        call the handler.
 *
 * @param[in] uxIdentifier: Identifier associated with the callback function.
 * @param[in] pcName: The name associated with the callback function.
 * @param[in] ulIPAddress: IP-address obtained from the DNS server.
 *
 * @return Returns pdTRUE if uxIdentifier was recognized.
 */
        static BaseType_t xDNSDoCallback( TickType_t uxIdentifier,
                                          const char * pcName,
                                          uint32_t ulIPAddress )
        {
            BaseType_t xResult = pdFALSE;
            const ListItem_t * pxIterator;
            const ListItem_t * xEnd = listGET_END_MARKER( &xCallbackList );

            vTaskSuspendAll();
            {
                for( pxIterator = ( const ListItem_t * ) listGET_NEXT( xEnd );
                     pxIterator != ( const ListItem_t * ) xEnd;
                     pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator ) )
                {
                    if( listGET_LIST_ITEM_VALUE( pxIterator ) == uxIdentifier )
                    {
                        DNSCallback_t * pxCallback = ipCAST_PTR_TO_TYPE_PTR( DNSCallback_t,
                                                                             listGET_LIST_ITEM_OWNER( pxIterator ) );

                        pxCallback->pCallbackFunction( pcName, pxCallback->pvSearchID,
                                                       ulIPAddress );
                        ( void ) uxListRemove( &pxCallback->xListItem );
                        vPortFree( pxCallback );

                        if( listLIST_IS_EMPTY( &xCallbackList ) != pdFALSE )
                        {
                            /* The list of outstanding requests is empty. No need for periodic polling. */
                            vIPSetDnsTimerEnableState( pdFALSE );
                        }

                        xResult = pdTRUE;
                        break;
                    }
                }
            }
            ( void ) xTaskResumeAll();
            return xResult;
        }

    #endif /* ipconfigDNS_USE_CALLBACKS == 1 */
    /*-----------------------------------------------------------*/

    #if ( ipconfigDNS_USE_CALLBACKS == 0 )

/**
 * @brief Get the IP-address corresponding to the given hostname.
 *
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 *
 * @return The IP-address corresponding to the hostname.
 */
        uint32_t FreeRTOS_gethostbyname( const char * pcHostName )
        {
            return prvPrepareLookup( pcHostName );
        }
    #else

/**
 * @brief Get the IP-address corresponding to the given hostname.
 *
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 * @param[in] pCallback: The callback function which will be called upon DNS response.
 * @param[in] pvSearchID: Search ID for the callback function.
 * @param[in] uxTimeout: Timeout for the callback function.
 *
 * @return The IP-address corresponding to the hostname.
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
 *
 * @return The IP-address corresponding to the hostname.
 */
        static uint32_t prvPrepareLookup( const char * pcHostName,
                                          FOnDNSEvent pCallback,
                                          void * pvSearchID,
                                          TickType_t uxTimeout )
    #else

/**
 * @brief Check if hostname is already known. If not, call prvGetHostByName() to send a DNS request.
 *
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 *
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
            size_t uxLength = strlen( pcHostName ) + 1U;

            #if ( ipconfigUSE_DNS_CACHE != 0 )
                if( uxLength <= ipconfigDNS_CACHE_NAME_LENGTH )
            #else
                if( uxLength <= dnsMAX_HOSTNAME_LENGTH )
            #endif
            {
                /* The name is not too long. */
                xLengthOk = pdTRUE;
            }
            else
            {
                FreeRTOS_printf( ( "prvPrepareLookup: name is too long ( %u > %u )\n",
                                   ( unsigned ) uxLength,
                                   ( unsigned ) ipconfigDNS_CACHE_NAME_LENGTH ) );
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

            /* Check the cache before issuing another DNS request. */
            if( ulIPAddress == 0UL )
            {
                /* If caching is not defined dns lookup will return zero */
                ulIPAddress = FreeRTOS_dnslookup( pcHostName );

                if( ulIPAddress != 0UL )
                {
                    FreeRTOS_debug_printf( ( "FreeRTOS_gethostbyname: found '%s' in cache: %lxip\n", pcHostName, ulIPAddress ) );
                }
                else
                {
                    /* prvGetHostByName will be called to start a DNS lookup. */
                }
            }

            /* Generate a unique identifier. */
            if( ulIPAddress == 0U )
            {
                uint32_t ulNumber = 0U;

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
                                vDNSSetCallBack( pcHostName, pvSearchID, pCallback, uxTimeout, uxIdentifier );
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

/**
 * @brief If LLMNR is being used then determine if the host name includes a '.' -
 *        if not then LLMNR can be used as the lookup method.
 * @param pcHostName[in] name to search for a dot
 * @return pdTRUE if the name has a dot
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

/**
 * @brief  get a payload buffer
 * @param ppxNetworkBuffer[out] a new network descripto
 * @param pchostName[in] copy to the network buffer
 * @returns payload buffer or NULL
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
                                                              0UL );

        if( *ppxNetworkBuffer != NULL )
        {
            pucUDPPayloadBuffer = &( ( *ppxNetworkBuffer )->pucEthernetBuffer[ uxHeaderBytes ] );
        }

        return pucUDPPayloadBuffer;
    }

/**
 * @brief fill the address
 *
 */
    static void prvFillSockAddress( struct freertos_sockaddr * xAddress,
                                    uint8_t * pucUDPPayloadBuffer,
                                    const char * pcHostName )
    {
        uint32_t ulIPAddress = 0UL;

        /* Obtain the DNS server address. */
        FreeRTOS_GetAddressConfiguration( NULL, NULL, NULL, &ulIPAddress );
        #if ( ipconfigUSE_LLMNR == 1 )
            BaseType_t bHasDot = llmnr_has_dot( pcHostName );
        #endif /* ipconfigUSE_LLMNR == 1 */

        #if ( ipconfigUSE_LLMNR == 1 )
            if( bHasDot == pdFALSE )
            {
                /* Use LLMNR addressing. */
                ( ipCAST_PTR_TO_TYPE_PTR( DNSMessage_t, pucUDPPayloadBuffer ) )->usFlags = 0;
                xAddress->sin_addr = ipLLMNR_IP_ADDR; /* Is in network byte order. */
                xAddress->sin_port = ipLLMNR_PORT;
                xAddress->sin_port = FreeRTOS_ntohs( xAddress->sin_port );
            }
            else
        #endif
        {
            /* Use DNS server. */
            xAddress->sin_addr = ulIPAddress;
            xAddress->sin_port = dnsDNS_PORT;
        }
    }

/**
 * @brief  sends the dns request
 *
 */
    static uint32_t prvDNSRequest( const char * pcHostName,
                                   TickType_t uxIdentifier,
                                   Socket_t xDNSSocket,
                                   struct freertos_sockaddr * xAddress,
                                   struct dns_buffer * pxDNSBuf )
    {
        BaseType_t xReturn = pdFALSE;

        iptraceSENDING_DNS_REQUEST();

        /* Send the DNS message. */
        if( FreeRTOS_sendto( xDNSSocket,
                             pxDNSBuf->pucPayloadBuffer,
                             pxDNSBuf->uxPayloadLength,
                             FREERTOS_ZERO_COPY,
                             xAddress,
                             sizeof( *xAddress ) ) != 0 )
        {
            xReturn = pdTRUE;
        }
        else
        {
            /* The message was not sent so the stack will not be
             * releasing the zero copy - it must be released here. */
            xReturn = pdFALSE;
        }

        return xReturn;
    }

/**
 * @brief  parse the dns reply
 *
 */
    static uint32_t prvDNSReply( struct dns_buffer * pxReceiveBuffer,
                                 TickType_t uxIdentifier )
    {
        uint32_t ulIPAddress = 0UL;
        uint32_t ulAddressLength = sizeof( struct freertos_sockaddr );
        BaseType_t xExpected;
        const DNSMessage_t * pxDNSMessageHeader =
            ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( DNSMessage_t,
                                                pxReceiveBuffer->pucPayloadBuffer );

        /* See if the identifiers match. */
        if( uxIdentifier == ( TickType_t ) pxDNSMessageHeader->usIdentifier )
        {
            xExpected = pdTRUE;
        }
        else
        {
            /* The reply was not expected. */
            xExpected = pdFALSE;
        }

        /* The reply was received.  Process it. */
        #if ( ipconfigDNS_USE_CALLBACKS == 0 )

            /* It is useless to analyse the unexpected reply
             * unless asynchronous look-ups are enabled. */
            if( xExpected != pdFALSE )
        #endif /* ipconfigDNS_USE_CALLBACKS == 0 */
        {
            ulIPAddress = prvParseDNSReply( pxReceiveBuffer->pucPayloadBuffer,
                                            pxReceiveBuffer->uxPayloadLength,
                                            xExpected );
        }

        return ulIPAddress;
    }

/**
 * @brief read dns reply from the network
 *
 */
    static void prvReadDNSReply( Socket_t xDNSSocket,
                                 struct freertos_sockaddr * xAddress,
                                 struct dns_buffer * pxReceiveBuffer )
    {
        uint8_t * pucReceiveBuffer = NULL;
        int32_t lBytes;
        uint32_t ulAddressLength = sizeof( struct freertos_sockaddr );

        /* Wait for the reply. */
        pxReceiveBuffer->uxPayloadLength = FreeRTOS_recvfrom( xDNSSocket,
                                                              &pxReceiveBuffer->pucPayloadBuffer,
                                                              0,
                                                              FREERTOS_ZERO_COPY,
                                                              xAddress,
                                                              &ulAddressLength );
    }


/**
 * @brief main dns operation description function
 *
 */
    static uint32_t prvGetHostByNameOp( const char * pcHostName,
                                        TickType_t uxIdentifier,
                                        Socket_t xDNSSocket,
                                        struct dns_buffer * pxDNSBuf )
    {
        uint32_t ulIPAddress = 0UL;
        BaseType_t xReturn;
        struct freertos_sockaddr xAddress;
        struct dns_buffer xReceiveBuffer;

        prvFillSockAddress( &xAddress, pxDNSBuf->pucPayloadBuffer, pcHostName );

        do
        {
            /* Create the message in the obtained buffer. */
            pxDNSBuf->uxPayloadLength = prvCreateDNSMessage( pxDNSBuf->pucPayloadBuffer,
                                                             pcHostName,
                                                             uxIdentifier );

            if( pxDNSBuf->uxPayloadLength == 0 )
            {
                break;
            }

            /* send the dns message */
            xReturn = prvDNSRequest( pcHostName,
                                     uxIdentifier,
                                     xDNSSocket,
                                     &xAddress,
                                     pxDNSBuf );

            if( xReturn == pdFAIL )
            {
                break;
            }

            /* receive a dns reply message */
            prvReadDNSReply( xDNSSocket,
                             &xAddress,
                             &xReceiveBuffer );

            if( xReceiveBuffer.pucPayloadBuffer == NULL )
            {
                break;
            }

            ulIPAddress = prvDNSReply( &xReceiveBuffer, uxIdentifier );
            FreeRTOS_ReleaseUDPPayloadBuffer( xReceiveBuffer.pucPayloadBuffer );
        } while( 0 );

        return ulIPAddress;
    }

/**
 * @brief  get host by name with configured retires
 *
 */
    static uint32_t prvGetHostByNameOp_WithRetry( const char * pcHostName,
                                                  TickType_t uxIdentifier,
                                                  Socket_t xDNSSocket,
                                                  struct dns_buffer * pxDNSBuf )
    {
        BaseType_t xAttempt;
        uint32_t ulIPAddress = 0UL;

        for( xAttempt = 0; xAttempt < ipconfigDNS_REQUEST_ATTEMPTS; xAttempt++ )
        {
            ulIPAddress = prvGetHostByNameOp( pcHostName,
                                              uxIdentifier,
                                              xDNSSocket,
                                              pxDNSBuf );

            if( ulIPAddress != 0 )
            { /* ip found, no need to retry */
                break;
            }
        }

        return ulIPAddress;
    }

/**
 * @brief Prepare and send a message to a DNS server.  'uxReadTimeOut_ticks' will be passed as
 * zero, in case the user has supplied a call-back function.
 *
 * @param[in] pcHostName: The hostname for which an IP address is required.
 * @param[in] uxIdentifier: Identifier to send in the DNS message.
 * @param[in] uxReadTimeOut_ticks: The timeout in ticks for waiting. In case the user has supplied
 *                                 a call-back function, this value should be zero.
 *
 * @return The IPv4 IP address for the hostname being queried. It will be zero if there is no reply.
 */
    static uint32_t prvGetHostByName( const char * pcHostName,
                                      TickType_t uxIdentifier,
                                      TickType_t uxReadTimeOut_ticks )
    {
        Socket_t xDNSSocket;
        uint32_t ulIPAddress = 0UL;
        NetworkBufferDescriptor_t * pxNetworkBuffer;
        struct dns_buffer xDNSBuf;

        /*get dns message buffer */
        xDNSBuf.pucPayloadBuffer = prvGetPayloadBuffer( &pxNetworkBuffer,
                                                        pcHostName );

        if( xDNSBuf.pucPayloadBuffer != NULL )
        {
            xDNSSocket = prvCreateDNSSocket( uxReadTimeOut_ticks );

            if( xDNSSocket != NULL )
            {
                if( uxReadTimeOut_ticks == 0 )
                {
                    ulIPAddress = prvGetHostByNameOp( pcHostName,
                                                      uxIdentifier,
                                                      xDNSSocket,
                                                      &xDNSBuf );
                }
                else
                {
                    ulIPAddress = prvGetHostByNameOp_WithRetry( pcHostName,
                                                                uxIdentifier,
                                                                xDNSSocket,
                                                                &xDNSBuf );
                }

                /* Finished with the socket. */
                ( void ) FreeRTOS_closesocket( xDNSSocket );
            }

            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
        }

        return ulIPAddress;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Create the DNS message in the zero copy buffer passed in the first parameter.
 *
 * @param[in,out] pucUDPPayloadBuffer: The zero copy buffer where the DNS message will be created.
 * @param[in] pcHostName: Hostname to be looked up.
 * @param[in] uxIdentifier: The identifier to be added to the DNS message.
 *
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
        pxDNSMessageHeader = ipCAST_PTR_TO_TYPE_PTR( DNSMessage_t, pucUDPPayloadBuffer );
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
        pxTail = ipCAST_PTR_TO_TYPE_PTR( DNSTail_t, &( pucUDPPayloadBuffer[ uxStart + 1U ] ) );

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

    #if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )

    #endif /* ipconfigUSE_DNS_CACHE || ipconfigDNS_USE_CALLBACKS */
    /*-----------------------------------------------------------*/

/**
 * @brief Simple routine that jumps over the NAME field of a resource record.
 *
 * @param[in] pucByte: The pointer to the resource record.
 * @param[in] uxLength: Length of the resource record.
 *
 * @return It returns the number of bytes read, or zero when an error has occurred.
 */
    _static size_t prvSkipNameField( const uint8_t * pucByte,
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
 * @return Always pdFAIL to indicate that the packet was not consumed and must
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
                ( void ) prvParseDNSReply( pucPayLoadBuffer,
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
            UDPPacket_t * pxUDPPacket = ipCAST_PTR_TO_TYPE_PTR( UDPPacket_t, pxNetworkBuffer->pucEthernetBuffer );
            uint8_t * pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( *pxUDPPacket ) ] );

            prvTreatNBNS( pucUDPPayloadBuffer,
                          pxNetworkBuffer->xDataLength,
                          pxUDPPacket->xIPHeader.ulSourceIPAddress );

            /* The packet was not consumed. */
            return pdFAIL;
        }

    #endif /* ipconfigUSE_NBNS */
    /*-----------------------------------------------------------*/

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
    _static uint32_t prvParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                                       size_t uxBufferLength,
                                       BaseType_t xExpected )
    {
        DNSMessage_t * pxDNSMessageHeader;
        /* This pointer is not used to modify anything */
        const DNSAnswerRecord_t * pxDNSAnswerRecord;
        uint32_t ulIPAddress = 0U;

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
            pxDNSMessageHeader = ipCAST_PTR_TO_TYPE_PTR( DNSMessage_t, pucUDPPayloadBuffer );

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
                            uxResult = prvReadNameField( pucByte,
                                                         uxSourceBytesRemaining,
                                                         pcName,
                                                         sizeof( pcName ) );
                        }
                        else
                    #endif /* ipconfigUSE_DNS_CACHE || ipconfigDNS_USE_CALLBACKS */
                    {
                        /* Skip the variable length pcName field. */
                        uxResult = prvSkipNameField( pucByte,
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

                        uxResult = prvSkipNameField( pucByte,
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
                                        if( xDNSDoCallback( ( TickType_t ) pxDNSMessageHeader->usIdentifier, pcName, ulIPAddress ) != pdFALSE )
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

                                        ( void ) FreeRTOS_inet_ntop( FREERTOS_AF_INET, ( const void * ) &( ulIPAddress ), cBuffer, ( socklen_t ) sizeof( cBuffer ) );
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

                    /* No need to check that pcRequestedName != NULL since is usQuestions != 0, then
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

                            if( pxNetworkBuffer != NULL )
                            {
                                if( xBufferAllocFixedSize == pdFALSE )
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
                                else
                                {
                                    pucNewBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
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

                                prvReplyDNSMessage( pxNetworkBuffer, usLength );

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
    /*-----------------------------------------------------------*/

    #if ( ipconfigUSE_NBNS == 1 )

/**
 * @brief Respond to an NBNS query or an NBNS reply.
 *
 * @param[in] pucPayload: the UDP payload of the NBNS message.
 * @param[in] uxBufferLength: Length of the Buffer.
 * @param[in] ulIPAddress: IP address of the sender.
 */
        static void prvTreatNBNS( uint8_t * pucPayload,
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

            /* Check for minimum buffer size. */
            if( uxBufferLength < uxBytesNeeded )
            {
                return;
            }

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
                            /*( void ) prvProcessDNSCache( ( char * ) ucNBNSName, &( ulIPAddress ), 0, pdFALSE ); */
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

                    if( ( xBufferAllocFixedSize == pdFALSE ) && ( pxNetworkBuffer != NULL ) )
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
                        pxMessage = ipCAST_PTR_TO_TYPE_PTR( DNSMessage_t, pucUDPPayloadBuffer );

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

                        pxAnswer = ipCAST_PTR_TO_TYPE_PTR( NBNSAnswer_t, &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, usType ) ] ) );

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

                        prvReplyDNSMessage( pxNetworkBuffer, ( BaseType_t ) usLength );

                        if( pxNewBuffer != NULL )
                        {
                            vReleaseNetworkBufferAndDescriptor( pxNewBuffer );
                        }
                    }
                }
            }
        }

    #endif /* ipconfigUSE_NBNS */
    /*-----------------------------------------------------------*/

/**
 * @brief Create a socket and bind it to the standard DNS port number.
 *
 * @return The created socket - or NULL if the socket could not be created or could not be bound.
 */
    static Socket_t prvCreateDNSSocket( TickType_t uxReadTimeOut_ticks )
    {
        Socket_t xSocket;
        struct freertos_sockaddr xAddress;
        TickType_t uxWriteTimeOut_ticks = ipconfigDNS_SEND_BLOCK_TIME_TICKS;
        BaseType_t xReturn;

        /* This must be the first time this function has been called.  Create
         * the socket. */
        xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

        if( xSocketValid( xSocket ) == pdFALSE )
        {
            /* There was an error, return NULL. */
            xSocket = NULL;
        }
        else
        {
            /* Auto bind the port. */
            xAddress.sin_port = 0U;
            xReturn = FreeRTOS_bind( xSocket, &xAddress, ( socklen_t ) sizeof( xAddress ) );

            /* Check the bind was successful, and clean up if not. */
            if( xReturn != 0 )
            {
                ( void ) FreeRTOS_closesocket( xSocket );
                xSocket = NULL;
            }
            else
            {
                /* Ideally we should check for the return value. But since we are passing
                 * correct parameters, and xSocket is != NULL, the return value is
                 * going to be '0' i.e. success. Thus, return value is discarded */
                ( void ) FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, &( uxWriteTimeOut_ticks ), sizeof( TickType_t ) );
                ( void ) FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &( uxReadTimeOut_ticks ), sizeof( TickType_t ) );
            }
        }

        return xSocket;
    }
/*-----------------------------------------------------------*/

    #if ( ( ipconfigUSE_NBNS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) )

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

            /* This function will fill in the eth addresses and send the packet */
            vReturnEthernetFrame( pxNetworkBuffer, pdFALSE );
        }

    #endif /* ipconfigUSE_NBNS == 1 || ipconfigUSE_LLMNR == 1 */

/*-----------------------------------------------------------*/

#endif /* ipconfigUSE_DNS != 0 */

/*-----------------------------------------------------------*/

/* Provide access to private members for testing. */
#ifdef FREERTOS_ENABLE_UNIT_TESTS
    #include "freertos_tcp_test_access_dns_define.h"
#endif
