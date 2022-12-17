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
#include "FreeRTOS_IP_Timers.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_Routing.h"
#include "NetworkInterface.h"

#include "FreeRTOS_DNS_Globals.h"
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
                                        TickType_t uxIdentifier,
                                        UBaseType_t uxHostType );


/*
 * Check if hostname is already known. If not, call prvGetHostByName() to send a DNS request.
 */
    #if ( ipconfigDNS_USE_CALLBACKS == 1 )
        static uint32_t prvPrepareLookup( const char * pcHostName,
                                          struct freertos_addrinfo ** ppxAddressInfo,
                                          BaseType_t xFamily, /* FREERTOS_AF_INET4 / 6. */
                                          FOnDNSEvent pCallback,
                                          void * pvSearchID,
                                          TickType_t uxTimeout );
    #else
        static uint32_t prvPrepareLookup( const char * pcHostName,
                                          struct freertos_addrinfo ** ppxAddressInfo,
                                          BaseType_t xFamily ); /* FREERTOS_AF_INET4 / 6. */
    #endif

/*
 * Prepare and send a message to a DNS server.  'uxReadTimeOut_ticks' will be passed as
 * zero, in case the user has supplied a call-back function.
 */
    static uint32_t prvGetHostByName( const char * pcHostName,
                                      TickType_t uxIdentifier,
                                      TickType_t uxReadTimeOut_ticks,
                                      struct freertos_addrinfo ** ppxAddressInfo,
                                      BaseType_t xFamily );

    #if ( ipconfigUSE_LLMNR == 1 )
        /** @brief The MAC address used for LLMNR. */
        const MACAddress_t xLLMNR_MacAdress = { { 0x01, 0x00, 0x5e, 0x00, 0x00, 0xfc } };
    #endif /* ipconfigUSE_LLMNR == 1 */

/*-----------------------------------------------------------*/
    #if ( ipconfigUSE_LLMNR == 1 ) && ( ipconfigUSE_IPV6 != 0 )
        const IPv6_Address_t ipLLMNR_IP_ADDR_IPv6 =
        {
            #ifndef _MSC_VER
                /* MSC doesn't like this C-style initialisation. */
                ucBytes :
            #endif
            { /* ff02::1:3 */
                0xff, 0x02,
                0x00, 0x00,
                0x00, 0x00,
                0x00, 0x00,
                0x00, 0x00,
                0x00, 0x00,
                0x00, 0x01,
                0x00, 0x03,
            }
        };
        const MACAddress_t xLLMNR_MacAdressIPv6 = { { 0x33, 0x33, 0x00, 0x01, 0x00, 0x03 } };
    #endif /* ipconfigUSE_LLMNR && ipconfigUSE_IPV6 */

    #if ( ipconfigUSE_MDNS == 1 ) && ( ipconfigUSE_IPV6 != 0 )
        const IPv6_Address_t ipMDNS_IP_ADDR_IPv6 =
        {
            #ifndef _MSC_VER
                /* MSC doesn't like this C-style initialisation. */
                ucBytes :
            #endif
            { /* ff02::fb */
                0xff, 0x02,
                0x00, 0x00,
                0x00, 0x00,
                0x00, 0x00,
                0x00, 0x00,
                0x00, 0x00,
                0x00, 0x00,
                0x00, 0xfb,
            }
        };

/* The MAC-addresses are provided here in case a network
 * interface needs it. */
        const MACAddress_t xMDNS_MACAdressIPv6 = { { 0x33, 0x33, 0x00, 0x00, 0x00, 0xFB } };
    #endif /* ( ipconfigUSE_MDNS == 1 ) && ( ipconfigUSE_IPV6 != 0 ) */


    #if ( ipconfigUSE_MDNS == 1 )
        /** @brief The MAC address used for MDNS. */
        const MACAddress_t xMDNS_MacAdress = { { 0x01, 0x00, 0x5e, 0x00, 0x00, 0xfb } };
    #endif /* ipconfigUSE_MDNS == 1 */

/** @brief This global variable is being used to indicate to the driver which IP type
 *         is preferred for name service lookup, either IPv6 or IPv4. */
/* TODO: Fix IPv6 DNS query in Windows Simulator. */
    IPPreference_t xDNS_IP_Preference =
    #if ( ipconfigUSE_IPV6 != 0 )
            xPreferenceIPv6;
    #else
            xPreferenceIPv4;
    #endif /* ipconfigUSE_IPV6 != 0 */

/** @brief Used for additional error checking when asserts are enabled. */
        _static struct freertos_addrinfo * pxLastInfo = NULL;
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

/**
 * @brief Internal function: allocate and initialise a new struct of type freertos_addrinfo.
 *
 * @param[in] pcName: the name of the host.
 * @param[in] xFamily: the type of IP-address: FREERTOS_AF_INET4 or FREERTOS_AF_INET6.
 * @param[in] pucAddress: The IP-address of the host.
 *
 * @return A pointer to the newly allocated struct, or NULL in case malloc failed..
 */
    struct freertos_addrinfo * pxNew_AddrInfo( const char * pcName,
                                               BaseType_t xFamily,
                                               const uint8_t * pucAddress )
    {
        struct freertos_addrinfo * pxAddrInfo = NULL;
        void * pvBuffer;

        /* 'xFamily' might not be used when IPv6 is disabled. */
        ( void ) xFamily;
        pvBuffer = pvPortMalloc( sizeof( *pxAddrInfo ) );

        if( pvBuffer != NULL )
        {
            pxAddrInfo = ( struct freertos_addrinfo * ) pvBuffer;

            ( void ) memset( pxAddrInfo, 0, sizeof( *pxAddrInfo ) );
            pxAddrInfo->ai_canonname = pxAddrInfo->xPrivateStorage.ucName;
            ( void ) strncpy( pxAddrInfo->xPrivateStorage.ucName, pcName, sizeof( pxAddrInfo->xPrivateStorage.ucName ) );

            #if ( ipconfigUSE_IPv6 == 0 )
                pxAddrInfo->ai_addr = &( pxAddrInfo->xPrivateStorage.sockaddr );
            #else
                pxAddrInfo->ai_addr = ( ( xFreertosSocAddr * ) &( pxAddrInfo->xPrivateStorage.sockaddr ) );

                if( xFamily == ( BaseType_t ) FREERTOS_AF_INET6 )
                {
                    pxAddrInfo->ai_family = FREERTOS_AF_INET6;
                    pxAddrInfo->ai_addrlen = ipSIZE_OF_IPv6_ADDRESS;
                    ( void ) memcpy( pxAddrInfo->xPrivateStorage.sockaddr.sin_addrv6.ucBytes, pucAddress, ipSIZE_OF_IPv6_ADDRESS );
                }
                else
            #endif /* ( ipconfigUSE_IPv6 == 0 ) */
            {
                /* ulChar2u32 reads from big-endian to host-endian. */
                uint32_t ulIPAddress = ulChar2u32( pucAddress );
                /* Translate to network-endian. */
                pxAddrInfo->ai_addr->sin_addr.xIP_IPv4 = FreeRTOS_htonl( ulIPAddress );
                pxAddrInfo->ai_family = FREERTOS_AF_INET4;
                pxAddrInfo->ai_addrlen = ipSIZE_OF_IPv4_ADDRESS;
            }
        }

        return pxAddrInfo;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Free a chain of structs of type 'freertos_addrinfo'.
 * @param[in] pxInfo: The first find result.
 */
    void FreeRTOS_freeaddrinfo( struct freertos_addrinfo * pxInfo )
    {
        struct freertos_addrinfo * pxNext;
        struct freertos_addrinfo * pxIterator = pxInfo;

        configASSERT( pxLastInfo != pxInfo );

        while( pxIterator != NULL )
        {
            pxNext = pxIterator->ai_next;
            vPortFree( pxIterator );
            pxIterator = pxNext;
        }

        pxLastInfo = NULL;
    }
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
            return prvPrepareLookup( pcHostName, NULL, FREERTOS_AF_INET4 );
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
            uint32_t ulResult;
            struct freertos_addrinfo * pxAddressInfo = NULL;

            ulResult = prvPrepareLookup( pcHostName, &( pxAddressInfo ), FREERTOS_AF_INET4, pCallback, pvSearchID, uxTimeout );

            if( pxAddressInfo != NULL )
            {
                FreeRTOS_freeaddrinfo( pxAddressInfo );
            }

            return ulResult;
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
                                          struct freertos_addrinfo ** ppxAddressInfo,
                                          BaseType_t xFamily,
                                          FOnDNSEvent pCallback,
                                          void * pvSearchID,
                                          TickType_t uxTimeout )
    #else

/**
 * @brief Check if hostname is already known. If not, call prvGetHostByName() to send a DNS request.
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 * @return The IP-address corresponding to the hostname.
 */
        static uint32_t prvPrepareLookup( const char * pcHostName,
                                          struct freertos_addrinfo ** ppxAddressInfo,
                                          BaseType_t xFamily )
    #endif /* if ( ipconfigDNS_USE_CALLBACKS == 1 ) */
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
                    if( xFamily == FREERTOS_AF_INET6 )
                    {
                        IPv6_Address_t xAddress_IPv6;
                        BaseType_t xResult;

                        /* ulIPAddress does not represent an IPv4 address here. It becomes non-zero when the look-up succeeds. */
                        xResult = FreeRTOS_inet_pton6( pcHostName, xAddress_IPv6.ucBytes );

                        if( xResult == 1 )
                        {
                            /* This function returns either a valid IPv4 address, or
                             * in case of an IPv6 lookup, it will return a non-zero */
                            ulIPAddress = 1U;

                            if( ppxAddressInfo != NULL )
                            {
                                *( ppxAddressInfo ) = pxNew_AddrInfo( pcHostName, FREERTOS_AF_INET6, xAddress_IPv6.ucBytes );
                            }
                        }
                    }
                    else
                    {
                        ulIPAddress = FreeRTOS_inet_addr( pcHostName );

                        if( ( ulIPAddress != 0U ) && ( ppxAddressInfo != NULL ) )
                        {
                            uint8_t * ucBytes = ( uint8_t * ) &( ulIPAddress );

                            *( ppxAddressInfo ) = pxNew_AddrInfo( pcHostName, FREERTOS_AF_INET4, ucBytes );
                        }
                    }
                }
            #endif /* ipconfigINCLUDE_FULL_INET_ADDR == 1 */

            #if ( ipconfigUSE_DNS_CACHE == 1 )
                /* Check the cache before issuing another DNS request. */
                if( ulIPAddress == 0U )
                {
                    ulIPAddress = FreeRTOS_dnslookup( pcHostName ); /*TODO */

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
                                                 ( TickType_t ) uxIdentifier,
                                                 ( xFamily == FREERTOS_AF_INET6 ) ? pdTRUE : pdFALSE );
                            }
                        }
                        else if( ppxAddressInfo != NULL )
                        {
                            /* The IP address is known, do the call-back now. */
                            pCallback( pcHostName, pvSearchID, *( ppxAddressInfo ) );
                        }
                    }
                }
            #endif /* if ( ipconfigDNS_USE_CALLBACKS == 1 ) */

            if( ( ulIPAddress == 0U ) && ( xHasRandom != pdFALSE ) )
            {
                ulIPAddress = prvGetHostByName( pcHostName,
                                                uxIdentifier,
                                                uxReadTimeOut_ticks,
                                                ppxAddressInfo,
                                                xFamily );
            }
        }

        return ulIPAddress;
    }
    /*-----------------------------------------------------------*/


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

/*!
 * @brief create a payload buffer and return it through the parameter
 * @param [out] ppxNetworkBuffer network buffer to create
 * @param [in] pcHostName hostname to get its length
 * @returns pointer address to the payload buffer
 *
 */
    static uint8_t * prvGetPayloadBuffer( NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                                          const char * pcHostName,
                                          size_t uxHeaderBytes )
    {
        size_t uxExpectedPayloadLength;
        uint8_t * pucUDPPayloadBuffer = NULL;

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
 * @return The end-point that holds the DNS address.
 */
    static NetworkEndPoint_t * prvFillSockAddress( struct freertos_sockaddr * pxAddress,
                                                   const char * pcHostName )
    {
        uint32_t ulIPAddress = 0U;
        NetworkEndPoint_t * pxEndPoint = NULL;
        BaseType_t xNeed_Endpoint = pdFALSE;

        #if ( ipconfigUSE_LLMNR != 1 )
            ( void ) pcHostName;
        #endif

        /* Make sure all fields of the 'sockaddr' are cleared. */
        ( void ) memset( ( void * ) pxAddress, 0, sizeof( *pxAddress ) );

        /* 'sin_len' doesn't really matter, 'sockaddr' and 'sockaddr6'
         * have the same size. */
        pxAddress->sin_len = ( uint8_t ) sizeof( struct freertos_sockaddr );
        #if ( ipconfigCOMPATIBLE_WITH_SINGLE == 1 )
            /* Obtain the DNS server address. */
            FreeRTOS_GetAddressConfiguration( NULL, NULL, NULL, &ulIPAddress );
        #endif

        BaseType_t bHasDot = llmnr_has_dot( pcHostName );
        /* For local resolution, mDNS uses names ending with the string ".local" */
        BaseType_t bHasLocal = pdFALSE;
        char * pcDot = strchr( pcHostName, '.' );

        if( pcDot != NULL )
        {
            if( strcmp( pcDot, ".local" ) == 0 )
            {
                bHasLocal = pdTRUE;
            }
        }

        /* Is this a local lookup? */
        if( ( bHasDot == pdFALSE ) || ( bHasLocal == pdTRUE ) )
        {
            #if ( ipconfigUSE_MDNS == 1 )
                {
                    if( bHasLocal )
                    {
                        /* Looking up a name like "mydevice.local".
                         * Use mDNS addresses. */
                        pxAddress->sin_addr.xIP_IPv4 = ipMDNS_IP_ADDRESS; /* Is in network byte order. */
                        pxAddress->sin_port = ipMDNS_PORT;
                        pxAddress->sin_port = FreeRTOS_ntohs( pxAddress->sin_port );
                        xNeed_Endpoint = pdTRUE;
                        #if ( ipconfigUSE_IPV6 != 0 )
                            if( xDNS_IP_Preference == xPreferenceIPv6 )
                            {
                                struct freertos_sockaddr * pxAddressV6 = pxAddress;
                                memcpy( pxAddressV6->sin_addr.xIP_IPv6.ucBytes,
                                        ipMDNS_IP_ADDR_IPv6.ucBytes,
                                        ipSIZE_OF_IPv6_ADDRESS );
                                pxAddress->sin_family = FREERTOS_AF_INET6;
                            }
                        #endif
                    }
                }
            #endif /* if ( ipconfigUSE_MDNS == 1 ) */
            #if ( ipconfigUSE_LLMNR == 1 )
                if( bHasDot == pdFALSE )
                {
                    /* Use LLMNR addressing. */
                    pxAddress->sin_addr.xIP_IPv4 = ipLLMNR_IP_ADDR; /* Is in network byte order. TODO */
                    pxAddress->sin_port = ipLLMNR_PORT;
                    pxAddress->sin_port = FreeRTOS_ntohs( pxAddress->sin_port );
                    xNeed_Endpoint = pdTRUE;
                    #if ( ipconfigUSE_IPV6 != 0 )
                        if( xDNS_IP_Preference == xPreferenceIPv6 )
                        {
                            memcpy( pxAddress->sin_addr.xIP_IPv6.ucBytes,
                                    ipLLMNR_IP_ADDR_IPv6.ucBytes,
                                    ipSIZE_OF_IPv6_ADDRESS );
                            pxAddress->sin_family = FREERTOS_AF_INET6;
                        }
                    #endif
                }
                else
            #endif /* if ( ipconfigUSE_LLMNR == 1 ) */
            {
                /* Use DNS server. */
                pxAddress->sin_addr.xIP_IPv4 = ulIPAddress;     /*TODO */
                pxAddress->sin_port = dnsDNS_PORT;
            }

            if( xNeed_Endpoint == pdTRUE )
            {
                for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
                     pxEndPoint != NULL;
                     pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
                {
                    #if ( ipconfigUSE_IPV6 != 0 )
                        if( xDNS_IP_Preference == xPreferenceIPv6 )
                        {
                            if( ENDPOINT_IS_IPv6( pxEndPoint ) )
                            {
                                break;
                            }
                        }
                        else
                        {
                            if( ENDPOINT_IS_IPv4( pxEndPoint ) )
                            {
                                break;
                            }
                        }
                    #else /* if ( ipconfigUSE_IPV6 != 0 ) */
                        /* IPv6 is not included, so all end-points are IPv4. */
                        break;
                    #endif /* if ( ipconfigUSE_IPV6 != 0 ) */
                }
            }
        }
        else
        {
            /* Look for an end-point that has defined a DNS server address. */
            for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
                 pxEndPoint != NULL;
                 pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
            {
                if( ENDPOINT_IS_IPv6( pxEndPoint ) )
                {
                    uint8_t ucIndex = pxEndPoint->ipv6_settings.ucDNSIndex;
                    uint8_t * ucBytes = pxEndPoint->ipv6_settings.xDNSServerAddresses[ ucIndex ].ucBytes;

                    /* Test if the DNS entry is in used. */
                    if( ( ucBytes[ 0 ] != 0U ) && ( ucBytes[ 1 ] != 0U ) )
                    {
                        struct freertos_sockaddr * pxAddress6 = pxAddress;

                        pxAddress->sin_family = FREERTOS_AF_INET6;
                        pxAddress->sin_len = ( uint8_t ) sizeof( struct freertos_sockaddr );
                        ( void ) memcpy( pxAddress->sin_addr.xIP_IPv6.ucBytes,
                                         pxEndPoint->ipv6_settings.xDNSServerAddresses[ ucIndex ].ucBytes,
                                         ipSIZE_OF_IPv6_ADDRESS );
                        break;
                    }
                }
                else
                {
                    uint8_t ucIndex = pxEndPoint->ipv4_settings.ucDNSIndex;
                    uint32_t ulIPAddress = pxEndPoint->ipv4_settings.ulDNSServerAddresses[ ucIndex ];

                    if( ( ulIPAddress != 0U ) && ( ulIPAddress != ipBROADCAST_IP_ADDRESS ) )
                    {
                        pxAddress->sin_addr.xIP_IPv4 = ulIPAddress;
                        break;
                    }
                }
            }
        }

        return pxEndPoint;
    }

/*!
 * @brief return ip address from the dns reply message
 * @param [in] pxReceiveBuffer received buffer from the DNS server
 * @param [in] uxIdentifier matches sent and received packets
 * @returns ip address or zero on error
 *
 */
    static uint32_t prvDNSReply( const struct xDNSBuffer * pxReceiveBuffer,
                                 struct freertos_addrinfo ** ppxAddressInfo,
                                 TickType_t uxIdentifier,
                                 uint16_t usPort )
    {
        uint32_t ulIPAddress = 0U;
        BaseType_t xExpected;

        /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        const DNSMessage_t * pxDNSMessageHeader =
            ( ( const DNSMessage_t * )
              pxReceiveBuffer->pucPayloadBuffer );

        #if ( ipconfigUSE_MDNS == 1 )
            if( FreeRTOS_ntohs( pxReceiveBuffer.sin_port ) == ipMDNS_PORT )             /* mDNS port 5353. */
            {
                /* In mDNS, the query ID field is ignored. */
                xExpected = pdTRUE;
            }
            else
        #endif /* if ( ipconfigUSE_MDNS == 1 ) */

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
                                             ppxAddressInfo,
                                             xExpected,
                                             usPort );
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
        size_t uxHeaderBytes;
        UBaseType_t uxHostType;

        /* Calculate the size of the headers. */
        if( pxAddress->sin_family == FREERTOS_AF_INET6 )
        {
            uxHeaderBytes = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_UDP_HEADER;

            /* Note that 'dnsTYPE_ANY_HOST' could be used here as well,
             * but for testing, we want an IPv6 address. */
            uxHostType = dnsTYPE_AAAA_HOST;
        }
        else
        {
            uxHeaderBytes = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER;
            uxHostType = dnsTYPE_A_HOST;
        }

        /*get dns message buffer */
        xDNSBuf.pucPayloadBuffer = prvGetPayloadBuffer( &pxNetworkBuffer,
                                                        pcHostName, uxHeaderBytes );

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

            /* A two-step conversion to conform to MISRA. */
            size_t uxIndex = ipUDP_PAYLOAD_IP_TYPE_OFFSET;
            BaseType_t xIndex = ( BaseType_t ) uxIndex;

            /* Later when translating form UDP payload to a Network Buffer,
             * it is important to know whether this is an IPv4 packet. */
            if( pxAddress->sin_family == FREERTOS_AF_INET6 )
            {
                xDNSBuf.pucPayloadBuffer[ -xIndex ] = ( uint8_t ) ipTYPE_IPv6;
            }
            else
            {
                xDNSBuf.pucPayloadBuffer[ -xIndex ] = ( uint8_t ) ipTYPE_IPv4;
            }

            xDNSBuf.uxPayloadLength = prvCreateDNSMessage( xDNSBuf.pucPayloadBuffer,
                                                           pcHostName,
                                                           uxIdentifier,
                                                           uxHostType );

            /* ipLLMNR_IP_ADDR is in network byte order. */
            if( ( pxAddress->sin_addr.xIP_IPv4 == ipLLMNR_IP_ADDR ) || ( pxAddress->sin_addr.xIP_IPv4 == ipMDNS_IP_ADDRESS ) )
            {
                /* Use LLMNR addressing. */
                ( ( ( DNSMessage_t * ) xDNSBuf.pucPayloadBuffer ) )->usFlags = 0;
            }

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
                                        Socket_t xDNSSocket,
                                        struct freertos_addrinfo ** ppxAddressInfo,
                                        BaseType_t xFamily,
                                        BaseType_t xRetryIndex )
    {
        uint32_t ulIPAddress = 0;
        struct freertos_sockaddr xAddress;
        DNSBuffer_t xReceiveBuffer = { 0 };
        BaseType_t uxReturn = pdFAIL;


        /* Two is added at the end for the count of characters in the first
         * subdomain part and the string end byte.
         * The two shorts are described in 'DNSTail_t'. */
        size_t uxExpectedPayloadLength = sizeof( DNSMessage_t ) + strlen( pcHostName ) + sizeof( uint16_t ) + sizeof( uint16_t ) + 2U;
        TickType_t uxWriteTimeOut_ticks = ipconfigDNS_SEND_BLOCK_TIME_TICKS;
        UBaseType_t uxHostType;
        NetworkEndPoint_t * pxEndPoint;

        pxEndPoint = prvFillSockAddress( &xAddress, pcHostName );
        xAddress.sin_family = xFamily;

        if( pxEndPoint != NULL )
        {
            do
            {
                if( xRetryIndex == 0 )
                {
                    /* Bind the client socket to a random port number. */
                    uint16_t usPort = 0U;
                    #if ( ipconfigUSE_MDNS == 1 )
                        if( xAddress.sin_port == FreeRTOS_htons( ipMDNS_PORT ) )
                        {
                            /* For a mDNS lookup, bind to the mDNS port 5353. */
                            usPort = FreeRTOS_htons( ipMDNS_PORT );
                        }
                    #endif

                    if( DNS_BindSocket( xDNSSocket, usPort ) != 0 )
                    {
                        FreeRTOS_printf( ( "DNS bind to %u failed\n", FreeRTOS_ntohs( usPort ) ) );
                        break;
                    }

                    /* Increment retry Index to perform the bind operation only once */
                    xRetryIndex++;
                }

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

                ulIPAddress = prvDNSReply( &xReceiveBuffer, ppxAddressInfo, uxIdentifier, xAddress.sin_port );

                /* Finished with the buffer.  The zero copy interface
                 * is being used, so the buffer must be freed by the
                 * task. */
                FreeRTOS_ReleaseUDPPayloadBuffer( xReceiveBuffer.pucPayloadBuffer );
            } while( ipFALSE_BOOL );
        }
        else
        {
            /* No endpoint was found that defines a DNS address. */
            FreeRTOS_printf( ( "Can not find a DNS address, along with an end-point.\n" ) );
        }

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
                                                  Socket_t xDNSSocket,
                                                  struct freertos_addrinfo ** ppxAddressInfo,
                                                  BaseType_t xFamily )
    {
        uint32_t ulIPAddress;
        BaseType_t xAttempt;

        for( xAttempt = 0; xAttempt < ipconfigDNS_REQUEST_ATTEMPTS; xAttempt++ )
        {
            ulIPAddress = prvGetHostByNameOp( pcHostName,
                                              uxIdentifier,
                                              xDNSSocket,
                                              ppxAddressInfo,
                                              xFamily,
                                              xAttempt ); /* xAttempt maps to xRetryIndex */

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
 * @param[in,out] ppxAddressInfo: A pointer to a pointer where the find results
 *                will be stored.
 * @param[in] xFamily: Either FREERTOS_AF_INET4 or FREERTOS_AF_INET6.
 * @return The IPv4 IP address for the hostname being queried. It will be zero if there is no reply.
 */
    static uint32_t prvGetHostByName( const char * pcHostName,
                                      TickType_t uxIdentifier,
                                      TickType_t uxReadTimeOut_ticks,
                                      struct freertos_addrinfo ** ppxAddressInfo,
                                      BaseType_t xFamily )
    {
        Socket_t xDNSSocket;
        uint32_t ulIPAddress = 0U;
        /* xRetryIndex is used to track the first retry to bind the socket only the first time.*/
        BaseType_t xRetryIndex = 0;


        xDNSSocket = DNS_CreateSocket( uxReadTimeOut_ticks );

        if( xDNSSocket != NULL )
        {
            if( uxReadTimeOut_ticks == 0U )
            {
                ulIPAddress = prvGetHostByNameOp( pcHostName,
                                                  uxIdentifier,
                                                  xDNSSocket,
                                                  ppxAddressInfo,
                                                  xFamily,
                                                  xRetryIndex );
            }
            else
            {
                ulIPAddress = prvGetHostByNameOp_WithRetry( pcHostName,
                                                            uxIdentifier,
                                                            xDNSSocket,
                                                            ppxAddressInfo,
                                                            xFamily );
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
 * @param[in] uxHostType: dnsTYPE_A_HOST ( IPv4 ) or dnsTYPE_AAA_HOST ( IPv6 ).
 * @return Total size of the generated message, which is the space from the last written byte
 *         to the beginning of the buffer.
 */
    _static size_t prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                                        const char * pcHostName,
                                        TickType_t uxIdentifier,
                                        UBaseType_t uxHostType )
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
            vSetField16( pxTail, DNSTail_t, usType, ( uint16_t ) uxHostType );
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
 * @param[in] pxNetworkBuffer: The network buffer to be parsed.
 * @return Always pdFAIL to indicate that the packet was not consumed and must
 *         be released by the caller.
 */
    uint32_t ulDNSHandlePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        uint8_t * pucPayLoadBuffer;
        size_t uxPayloadSize;
        size_t uxUDPPacketSize = ipSIZE_OF_ETH_HEADER + uxIPHeaderSizePacket( pxNetworkBuffer ) + ipSIZE_OF_UDP_HEADER;

        /* Only proceed if the payload length indicated in the header
         * appears to be valid. */
        if( pxNetworkBuffer->xDataLength >= uxUDPPacketSize )
        {
            uxPayloadSize = pxNetworkBuffer->xDataLength - uxUDPPacketSize;

            if( uxPayloadSize >= sizeof( DNSMessage_t ) )
            {
                struct freertos_addrinfo * pxAddressInfo = NULL;
                pucPayLoadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ uxUDPPacketSize ] );

                /* The parameter pdFALSE indicates that the reply was not expected. */
                ( void ) DNS_ParseDNSReply( pucPayLoadBuffer,
                                            uxPayloadSize,
                                            &( pxAddressInfo ),
                                            pdFALSE,
                                            FreeRTOS_ntohs( pxNetworkBuffer->usPort ) );

                if( pxAddressInfo != NULL )
                {
                    FreeRTOS_freeaddrinfo( pxAddressInfo );
                }
            }
        }

        /* The packet was not consumed. */
        return pdFAIL;
    }
    /*-----------------------------------------------------------*/


    #if ( ipconfigUSE_NBNS == 1 )

/**
 * @brief Handle an NBNS packet.
 * @param[in] pxNetworkBuffer: The network buffer holding the NBNS packet.
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
