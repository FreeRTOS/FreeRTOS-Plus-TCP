/*
 * FreeRTOS+TCP V2.3.1
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

#include "FreeRTOS_DNS_Globals.h"
#include "FreeRTOS_DNS_Cache.h"
#include "FreeRTOS_DNS_Parser.h"
#include "FreeRTOS_DNS_Networking.h"
#include "FreeRTOS_DNS_Callback.h"

/* Exclude the entire file if DNS is not enabled. */
#if ( ipconfigUSE_DNS != 0 )

    #if ( ipconfigBYTE_ORDER == pdFREERTOS_LITTLE_ENDIAN )
        #define dnsDNS_PORT             0x3500U  /**< Little endian: Port used for DNS. */
        #define dnsONE_QUESTION         0x0100U  /**< Little endian representation of a DNS question.*/
        #define dnsOUTGOING_FLAGS       0x0001U  /**< Little endian representation of standard query. */
        #define dnsRX_FLAGS_MASK        0x0f80U  /**< Little endian:  The bits of interest in the flags field of incoming DNS messages. */
        #define dnsEXPECTED_RX_FLAGS    0x0080U  /**< Little Endian: Should be a response, without any errors. */
    #else
        #define dnsDNS_PORT             0x0035U  /**< Big endian: Port used for DNS. */
        #define dnsONE_QUESTION         0x0001U  /**< Big endian representation of a DNS question.*/
        #define dnsOUTGOING_FLAGS       0x0100U  /**< Big endian representation of standard query. */
        #define dnsRX_FLAGS_MASK        0x800fU  /**< Big endian: The bits of interest in the flags field of incoming DNS messages. */
        #define dnsEXPECTED_RX_FLAGS    0x8000U  /**< Big endian: Should be a response, without any errors. */

    #endif /* ipconfigBYTE_ORDER */

/** @brief The maximum number of times a DNS request should be sent out if a response
 * is not received, before giving up. */
    #ifndef ipconfigDNS_REQUEST_ATTEMPTS
        #define ipconfigDNS_REQUEST_ATTEMPTS    5
    #endif

/** @brief If the top two bits in the first character of a name field are set then the
 * name field is an offset to the string, rather than the string itself. */
    #define dnsNAME_IS_OFFSET    ( ( uint8_t ) 0xc0 )

/* NBNS flags. */
    #if ( ipconfigUSE_NBNS == 1 )
        #define dnsNBNS_FLAGS_RESPONSE        0x8000U /**< NBNS response flag. */
        #define dnsNBNS_FLAGS_OPCODE_MASK     0x7800U /**< NBNS opcode bitmask. */
        #define dnsNBNS_FLAGS_OPCODE_QUERY    0x0000U /**< NBNS opcode query. */
    #endif /* ( ipconfigUSE_NBNS == 1 ) */

/* LLMNR constants. */
    #define dnsLLMNR_FLAGS_IS_REPONSE    0x8000U  /**< LLMNR flag value for response. */

/* NBNS constants. */
    #if ( ipconfigUSE_NBNS != 0 )
        #define dnsNBNS_TTL_VALUE               3600U   /**< NBNS TTL: 1 hour valid. */
        #define dnsNBNS_TYPE_NET_BIOS           0x0020U /**< NBNS Type: NetBIOS. */
        #define dnsNBNS_CLASS_IN                0x01U   /**< NBNS Class: IN (Internet). */
        #define dnsNBNS_NAME_FLAGS              0x6000U /**< NBNS name flags. */
        #define dnsNBNS_ENCODED_NAME_LENGTH     32      /**< NBNS encoded name length. */

/** @brief If the queried NBNS name matches with the device's name,
 * the query will be responded to with these flags: */
        #define dnsNBNS_QUERY_RESPONSE_FLAGS    ( 0x8500U )
    #endif /* ( ipconfigUSE_NBNS != 0 ) */

    #if ( ipconfigUSE_DNS_CACHE == 0 )
        #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY != 1 )
            #error When DNS caching is disabled, please make ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY equal to 1.
        #endif
    #endif

/** @brief Define the ASCII value of '.' (Period/Full-stop). */
    #define ASCII_BASELINE_DOT    46U

/*
 * Create the DNS message in the zero copy buffer passed in the first parameter.
 * uxIdentifier is a random identifier for this look-up, uxHostType is the type
 * of host wanted, dnsTYPE_A_HOST or dnsTYPE_AAA_HOST, i.e. IPv4 or IPv6 resp.
 */
    static size_t prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                                       const char * pcHostName,
                                       TickType_t uxIdentifier,
                                       UBaseType_t uxHostType );

/*
 * Check if hostname is a literal IP-address, check if the host is found in
 * the DNS cache, and when still not resolved, call prvGetHostByName() to
 * send a DNS request.
 */
    #if ( ipconfigDNS_USE_CALLBACKS == 1 )
        static uint32_t prvPrepareLookup( const char * pcHostName,
                                          struct freertos_addrinfo ** ppxAddressInfo,
                                          BaseType_t xFamily, /* FREERTOS_AF_INET4 / 6. */
                                          FOnDNSEvent pCallbackFunction,
                                          void * pvSearchID,
                                          TickType_t uxTimeout );
    #else
        static uint32_t prvPrepareLookup( const char * pcHostName,
                                          struct freertos_addrinfo ** ppxAddressInfo,
                                          BaseType_t xFamily ); /* FREERTOS_AF_INET4 / 6. */
    #endif /* ( ipconfigDNS_USE_CALLBACKS == 1 ) */

/*
 * Prepare and send a message to a DNS server.  'uxReadTimeOut_ticks' will be passed as
 * zero, in case the user has supplied a call-back function.
 */
    static uint32_t prvGetHostByName( const char * pcHostName,
                                      TickType_t uxIdentifier,
                                      TickType_t uxReadTimeOut_ticks,
                                      struct freertos_addrinfo ** ppxAddressInfo,
                                      BaseType_t xFamily );

/** @brief This function is called by the macro 'vSetField16'. It store
 *         a 16-bit number in a buffer in big-endian format ( MSB first ).
 * @param[in] pucBase: A pointer to a buffer where to store a uint16_t.
 * @param[in] uxOffset: The offset within pucBase.
 * @param[in] usValue: The 16-bit value to be stored.
 */
    void vSetField16helper( uint8_t * pucBase,
                            size_t uxOffset,
                            uint16_t usValue )
    {
        pucBase[ uxOffset ] = ( uint8_t ) ( ( ( usValue ) >> 8 ) & 0xffU );
        pucBase[ uxOffset + 1U ] = ( uint8_t ) ( ( usValue ) & 0xffU );
    }

/** @brief This function is called by the macro 'vSetField32'. It store
 *         a 43-bit number in a buffer in big-endian format.
 * @param[in] pucBase: A pointer to a buffer where to store a uint32_t.
 * @param[in] uxOffset: The offset within pucBase.
 * @param[in] ulValue: The word to be stored.
 */
    void vSetField32helper( uint8_t * pucBase,
                            size_t uxOffset,
                            uint32_t ulValue )
    {
        pucBase[ uxOffset + 0U ] = ( uint8_t ) ( ( ulValue ) >> 24 );
        pucBase[ uxOffset + 1U ] = ( uint8_t ) ( ( ( ulValue ) >> 16 ) & 0xffU );
        pucBase[ uxOffset + 2U ] = ( uint8_t ) ( ( ( ulValue ) >> 8 ) & 0xffU );
        pucBase[ uxOffset + 3U ] = ( uint8_t ) ( ( ulValue ) & 0xffU );
    }

    #if ( ipconfigUSE_LLMNR == 1 )
        /** @brief The MAC address used for LLMNR. */
        const MACAddress_t xLLMNR_MacAdress = { { 0x01, 0x00, 0x5e, 0x00, 0x00, 0xfc } };
    #endif /* ipconfigUSE_LLMNR == 1 */

    #if ( ipconfigUSE_LLMNR == 1 ) && ( ipconfigUSE_IPv6 != 0 )
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
    #endif /* ipconfigUSE_LLMNR && ipconfigUSE_IPv6 */

    #if ( ipconfigUSE_MDNS == 1 ) && ( ipconfigUSE_IPv6 != 0 )
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
    #endif /* ( ipconfigUSE_MDNS == 1 ) && ( ipconfigUSE_IPv6 != 0 ) */


    #if ( ipconfigUSE_MDNS == 1 )
        /** @brief The MAC address used for MDNS. */
        const MACAddress_t xMDNS_MacAdress = { { 0x01, 0x00, 0x5e, 0x00, 0x00, 0xfb } };
    #endif /* ipconfigUSE_MDNS == 1 */

/** @brief This global variable is being used to indicate to the driver which IP type
 *         is preferred for name service lookup, either IPv6 or IPv4. */
/* TODO: Fix IPv6 DNS query in Windows Simulator. */
    IPPreference_t xDNS_IP_Preference =
    #if ( ipconfigUSE_IPv6 != 0 )
            xPreferenceIPv6;
    #else
            xPreferenceIPv4;
    #endif /* ipconfigUSE_IPv6 != 0 */
/*-----------------------------------------------------------*/

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

/** @brief Used for additional error checking when asserts are enabled. */
    _static struct freertos_addrinfo * pxLastInfo = NULL;

/** @brief See if pcHostName contains a valid IPv4 or IPv6 IP-address. */
    static uint32_t prvPrepare_ReadIPAddress( const char * pcHostName,
                                              BaseType_t xFamily,
                                              struct freertos_addrinfo ** ppxAddressInfo );

/** @brief Get an IP address ( IPv4 or IPv6 ) of a DNS server. */
    static NetworkEndPoint_t * prvGetDNSAddress( struct freertos_sockaddr * pxAddress,
                                                 const char * pcHostName );

/** @brief Increment the field 'ucDNSIndex', which is an index in the array */
    static void prvIncreaseDNS4Index( NetworkEndPoint_t * pxEndPoint );

    #if ( ipconfigUSE_IPv6 != 0 )
/** @brief Increment the field 'ucDNSIndex', which is an index in the array */
        static void prvIncreaseDNS6Index( NetworkEndPoint_t * pxEndPoint );
    #endif

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
    #endif /* ipconfigDNS_USE_CALLBACKS == 1 */
/*-----------------------------------------------------------*/

    #if ( ipconfigDNS_USE_CALLBACKS == 1 )

/** @brief Initialise the list of call-back structures.
 */
        void vDNSInitialise( void )
        {
            vDNSCallbackInitialise();
        }
    #endif /* ipconfigDNS_USE_CALLBACKS == 1 */
/*-----------------------------------------------------------*/

    #if ( ipconfigDNS_USE_CALLBACKS == 1 )

/**
 * @brief Remove the entry defined by the search ID to cancel a DNS request.
 * @param[in] pvSearchID: The search ID of the callback function associated with
 *                        the DNS request being cancelled. Note that the value of
 *                        the pointer matters, not the pointee.
 */
        void FreeRTOS_gethostbyname_cancel( void * pvSearchID )
        {
            vDNSCheckCallBack( pvSearchID );
        }

    #endif /* ipconfigDNS_USE_CALLBACKS == 1 */
/*-----------------------------------------------------------*/

    #if ( ipconfigDNS_USE_CALLBACKS == 1 )

/**
 * @brief Look-up the IP-address of a host.
 *
 * @param[in] pcName: The name of the node or device
 * @param[in] pcService: Ignored for now.
 * @param[in] pxHints: If not NULL: preferences. Can be used to indicate the preferred type if IP ( v4 or v6 ).
 * @param[out] ppxResult: An allocated struct, containing the results.
 *
 * @return Zero when the operation was successful, otherwise a negative errno value.
 */
        BaseType_t FreeRTOS_getaddrinfo( const char * pcName,                      /* The name of the node or device */
                                         const char * pcService,                   /* Ignored for now. */
                                         const struct freertos_addrinfo * pxHints, /* If not NULL: preferences. */
                                         struct freertos_addrinfo ** ppxResult )   /* An allocated struct, containing the results. */
        {
            /* Call the asynchronous version with NULL parameters. */
            return FreeRTOS_getaddrinfo_a( pcName, pcService, pxHints, ppxResult, NULL, NULL, 0U );
        }
    #endif /* ( ipconfigDNS_USE_CALLBACKS == 1 ) */
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
                pxAddrInfo->ai_addr = &( pxAddrInfo->xPrivateStorage.sockaddr4 );
            #else
                pxAddrInfo->ai_addr = ( ( sockaddr4_t * ) &( pxAddrInfo->xPrivateStorage.sockaddr6 ) );

                if( xFamily == ( BaseType_t ) FREERTOS_AF_INET6 )
                {
                    pxAddrInfo->ai_family = FREERTOS_AF_INET6;
                    pxAddrInfo->ai_addrlen = ipSIZE_OF_IPv6_ADDRESS;
                    ( void ) memcpy( pxAddrInfo->xPrivateStorage.sockaddr6.sin_addrv6.ucBytes, pucAddress, ipSIZE_OF_IPv6_ADDRESS );
                }
                else
            #endif /* ( ipconfigUSE_IPv6 == 0 ) */
            {
                /* ulChar2u32 reads from big-endian to host-endian. */
                uint32_t ulIPAddress = ulChar2u32( pucAddress );
                /* Translate to network-endian. */
                pxAddrInfo->ai_addr->sin_addr = FreeRTOS_htonl( ulIPAddress );
                pxAddrInfo->ai_family = FREERTOS_AF_INET4;
                pxAddrInfo->ai_addrlen = ipSIZE_OF_IPv4_ADDRESS;
            }
        }

        return pxAddrInfo;
    }
/*-----------------------------------------------------------*/

    #if ( ipconfigDNS_USE_CALLBACKS == 1 )

/**
 * @brief Asynchronous version of getaddrinfo().
 *
 * @param[in] pcName: The name of the node or device
 * @param[in] pcService: Ignored for now.
 * @param[in] pxHints: If not NULL: preferences. Can be used to indicate the preferred type if IP ( v4 or v6 ).
 * @param[out] ppxResult: An allocated struct, containing the results.
 * @param[in] pCallback: A user-defined function which will be called on completion, either when found or after a time-out.
 * @param[in] pvSearchID: A user provided void pointer that will be communicated on completion.
 * @param[in] uxTimeout: The maximum number of clock ticks that must be waited for a reply.
 *
 * @return Zero when the operation was successful, otherwise a negative errno value.
 */
        BaseType_t FreeRTOS_getaddrinfo_a( const char * pcName,                      /* The name of the node or device */
                                           const char * pcService,                   /* Ignored for now. */
                                           const struct freertos_addrinfo * pxHints, /* If not NULL: preferences. */
                                           struct freertos_addrinfo ** ppxResult,    /* An allocated struct, containing the results. */
                                           FOnDNSEvent pCallback,
                                           void * pvSearchID,
                                           TickType_t uxTimeout )
    #else

/**
 * @brief Look-up the IP-address of a host.
 * @param[in] pcName: The name of the node or device
 * @param[in] pcService: Ignored for now.
 * @param[in] pxHints: If not NULL: preferences. Can be used to indicate the preferred type if IP ( v4 or v6 ).
 * @param[out] ppxResult: An allocated struct, containing the results.
 * @return Zero when the operation was successful, otherwise a negative errno value.
 */
        BaseType_t FreeRTOS_getaddrinfo( const char * pcName,                      /* The name of the node or device */
                                         const char * pcService,                   /* Ignored for now. */
                                         const struct freertos_addrinfo * pxHints, /* If not NULL: preferences. */
                                         struct freertos_addrinfo ** ppxResult )   /* An allocated struct, containing the results. */
    #endif /* ipconfigDNS_USE_CALLBACKS == 1 */
    {
        BaseType_t xReturn = 0;
        uint32_t ulResult;
        BaseType_t xFamily = FREERTOS_AF_INET4;

        ( void ) pcService;
        ( void ) pxHints;

        if( ppxResult != NULL )
        {
            *( ppxResult ) = NULL;

            #if ( ipconfigUSE_IPv6 != 0 )
                if( pxHints != NULL )
                {
                    if( pxHints->ai_family == FREERTOS_AF_INET6 )
                    {
                        xFamily = FREERTOS_AF_INET6;
                    }
                    else if( pxHints->ai_family != FREERTOS_AF_INET4 )
                    {
                        xReturn = -pdFREERTOS_ERRNO_EINVAL;
                    }
                    else
                    {
                        /* This is FREERTOS_AF_INET4, carry on. */
                    }
                }
            #endif /* ( ipconfigUSE_IPv6 == 0 ) */

            #if ( ipconfigUSE_IPv6 != 0 )
                if( xReturn == 0 )
            #endif
            {
                #if ( ipconfigDNS_USE_CALLBACKS == 1 )
                    {
                        ulResult = prvPrepareLookup( pcName, ppxResult, xFamily, pCallback, pvSearchID, uxTimeout );
                    }
                #else
                    {
                        ulResult = prvPrepareLookup( pcName, ppxResult, xFamily );
                    }
                #endif /* ( ipconfigDNS_USE_CALLBACKS == 1 ) */

                if( ulResult != 0U )
                {
                    if( *( ppxResult ) != NULL )
                    {
                        xReturn = 0;
                    }
                    else
                    {
                        xReturn = -pdFREERTOS_ERRNO_ENOMEM;
                    }
                }
                else
                {
                    xReturn = -pdFREERTOS_ERRNO_ENOENT;
                }
            }
        }
        else
        {
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }

        return xReturn;
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

    #if ( ipconfigDNS_USE_CALLBACKS == 0 )

/**
 * @brief Get the IPv4 address corresponding to the given hostname. The function
 *        will block until there is an answer, or until a time-out is reached.
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 * @return The IPv4 address corresponding to the hostname.
 */
        uint32_t FreeRTOS_gethostbyname( const char * pcHostName )
        {
            return prvPrepareLookup( pcHostName, NULL, FREERTOS_AF_INET4 );
        }
    #else

/**
 * @brief Get the IPv4 address corresponding to the given hostname. The search will
 *        be done asynchronously.
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 * @param[in] pCallback: The callback function which will be called upon DNS response.
 * @param[in] pvSearchID: Search ID for the callback function.
 * @param[in] uxTimeout: Timeout for the callback function.
 * @return The IP-address corresponding to the hostname.
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
    #endif /* ( ipconfigDNS_USE_CALLBACKS == 0 ) */

    #if ( ipconfigINCLUDE_FULL_INET_ADDR == 1 )

/**
 * @brief See if pcHostName contains a valid IPv4 or IPv6 IP-address.
 * @param[in] pcHostName: The name to be looked up
 * @param[in] xFamily: the IP-type, either FREERTOS_AF_INET4 or FREERTOS_AF_INET6.
 * @param[in] ppxAddressInfo: A pointer to a pointer where the find results will
 *                            be stored.
 * @return Either 0 or an IP=address.
 */
        static uint32_t prvPrepare_ReadIPAddress( const char * pcHostName,
                                                  BaseType_t xFamily,
                                                  struct freertos_addrinfo ** ppxAddressInfo )
        {
            uint32_t ulIPAddress = 0U;

            ( void ) xFamily;

            /* Check if the hostname given is actually an IP-address. */
            #if ( ipconfigUSE_IPv6 != 0 )
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
            #endif /* ipconfigUSE_IPv6 */
            {
                ulIPAddress = FreeRTOS_inet_addr( pcHostName );

                if( ( ulIPAddress != 0U ) && ( ppxAddressInfo != NULL ) )
                {
                    uint8_t * ucBytes = ( uint8_t * ) &( ulIPAddress );

                    *( ppxAddressInfo ) = pxNew_AddrInfo( pcHostName, FREERTOS_AF_INET4, ucBytes );
                }
            }

            return ulIPAddress;
        }
    #endif /* ( ipconfigINCLUDE_FULL_INET_ADDR == 1 ) */
/*-----------------------------------------------------------*/

    #if ( ipconfigDNS_USE_CALLBACKS == 1 )

/**
 * @brief Check if hostname is already known. If not, call prvGetHostByName() to send a DNS request.
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 * @param[in] ppxAddressInfo: A pointer to a pointer where the find results will
 *                            be stored.
 * @param[in] xFamily: Either FREERTOS_AF_INET4 or FREERTOS_AF_INET6.
 * @param[in] pCallbackFunction: The callback function which will be called upon DNS response.
 * @param[in] pvSearchID: Search ID for the callback function.
 * @param[in] uxTimeout: Timeout for the callback function.
 * @return The IP-address corresponding to the hostname.
 */
        static uint32_t prvPrepareLookup( const char * pcHostName,
                                          struct freertos_addrinfo ** ppxAddressInfo,
                                          BaseType_t xFamily,
                                          FOnDNSEvent pCallbackFunction,
                                          void * pvSearchID,
                                          TickType_t uxTimeout )
    #else

/**
 * @brief Check if hostname is already known. If not, call prvGetHostByName() to send a DNS request.
 *        This function will block to wait for a reply.
 * @param[in] pcHostName: The hostname whose IP address is being queried.
 * @param[in] ppxAddressInfo: A pointer to a pointer where the find results will
 *                            be stored.
 * @param[in] xFamily: Either FREERTOS_AF_INET4 or FREERTOS_AF_INET6.
 * @return The IP-address corresponding to the hostname.
 */
        static uint32_t prvPrepareLookup( const char * pcHostName,
                                          struct freertos_addrinfo ** ppxAddressInfo,
                                          BaseType_t xFamily )
    #endif /* ( ipconfigDNS_USE_CALLBACKS == 1 ) */
    {
        uint32_t ulIPAddress = 0U;
        TickType_t uxReadTimeOut_ticks = ipconfigDNS_RECEIVE_BLOCK_TIME_TICKS;

/* Generate a unique identifier for this query. Keep it in a local variable
 * as gethostbyname() may be called from different threads */
        BaseType_t xHasRandom = pdFALSE;
        TickType_t uxIdentifier = 0U;

        #if ( ipconfigUSE_DNS_CACHE != 0 )
            BaseType_t xLengthOk = pdFALSE;
        #endif

        #if ( ipconfigUSE_DNS_CACHE != 0 )
            {
                if( pcHostName != NULL )
                {
                    size_t uxLength = strlen( pcHostName ) + 1U;

                    if( uxLength <= ipconfigDNS_CACHE_NAME_LENGTH )
                    {
                        /* The name is not too long. */
                        xLengthOk = pdTRUE;
                    }
                    else
                    {
                        FreeRTOS_printf( ( "prvPrepareLookup: name is too long ( %lu > %lu )\n",
                                           ( uint32_t ) uxLength,
                                           ( uint32_t ) ipconfigDNS_CACHE_NAME_LENGTH ) );
                    }
                }
            }

            if( ( pcHostName != NULL ) && ( xLengthOk != pdFALSE ) )
        #else /* if ( ipconfigUSE_DNS_CACHE != 0 ) */
            if( pcHostName != NULL )
        #endif /* ( ipconfigUSE_DNS_CACHE != 0 ) */
        {
            /* If the supplied hostname is an IP address, convert it to uint32_t
             * and return. */
            #if ( ipconfigINCLUDE_FULL_INET_ADDR == 1 )
                {
                    ulIPAddress = prvPrepare_ReadIPAddress( pcHostName, xFamily, ppxAddressInfo );
                }
            #endif /* ipconfigINCLUDE_FULL_INET_ADDR == 1 */

            /* If a DNS cache is used then check the cache before issuing another DNS
             * request. */
            #if ( ipconfigUSE_DNS_CACHE == 1 )
                if( ulIPAddress == 0U )
                {
                    ulIPAddress = Prepare_CacheLookup( pcHostName, xFamily, ppxAddressInfo );

                    if( ulIPAddress != 0UL )
                    {
                        FreeRTOS_debug_printf( ( "prvPrepareLookup: found '%s' in cache: %lxip\n", pcHostName, ulIPAddress ) );
                    }
                }
            #endif /* ipconfigUSE_DNS_CACHE == 1 */

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
                    if( pCallbackFunction != NULL )
                    {
                        if( ulIPAddress == 0U )
                        {
                            /* The user has provided a callback function, so do not block on recvfrom() */
                            if( xHasRandom != pdFALSE )
                            {
                                uxReadTimeOut_ticks = 0;
                                #if ( ipconfigUSE_IPv6 != 0 )
                                    {
                                        vDNSSetCallBack( pcHostName,
                                                         pvSearchID,
                                                         pCallbackFunction,
                                                         uxTimeout,
                                                         ( TickType_t ) uxIdentifier,
                                                         ( xFamily == FREERTOS_AF_INET6 ) ? pdTRUE : pdFALSE );
                                    }
                                #else
                                    {
                                        vDNSSetCallBack( pcHostName,
                                                         pvSearchID,
                                                         pCallbackFunction,
                                                         uxTimeout,
                                                         ( TickType_t ) uxIdentifier );
                                    }
                                #endif /* ( ipconfigUSE_IPv6 != 0 ) */
                            }
                        }
                        else if( ppxAddressInfo != NULL )
                        {
                            /* The IP address is known, do the call-back now. */
                            pCallbackFunction( pcHostName, pvSearchID, *( ppxAddressInfo ) );
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

    #if ( ipconfigUSE_IPv6 != 0 )

/**
 * @brief Increment the field 'ucDNSIndex', which is an index in the array
 *        of DNS addresses.
 * @param[in] pxEndPoint: The end-point of which the DNS index should be
 *                        incremented.
 */
        static void prvIncreaseDNS6Index( NetworkEndPoint_t * pxEndPoint )
        {
            uint8_t ucIndex = pxEndPoint->ipv6_settings.ucDNSIndex;

            ucIndex++;

            if( ucIndex >= ( uint8_t ) ipconfigENDPOINT_DNS_ADDRESS_COUNT )
            {
                ucIndex = 0U;
            }

            pxEndPoint->ipv6_settings.ucDNSIndex = ucIndex;
        }
    #endif /* ( ipconfigUSE_IPv6 != 0 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Increment the field 'ucDNSIndex', which is an index in the array
 *        of DNS addresses.
 * @param[in] pxEndPoint: The end-point of which the DNS index should be
 *                        incremented.
 */
    static void prvIncreaseDNS4Index( NetworkEndPoint_t * pxEndPoint )
    {
        uint8_t ucIndex = pxEndPoint->ipv4_settings.ucDNSIndex;

        ucIndex++;

        if( ucIndex >= ( uint8_t ) ipconfigENDPOINT_DNS_ADDRESS_COUNT )
        {
            ucIndex = 0U;
        }

        pxEndPoint->ipv4_settings.ucDNSIndex = ucIndex;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Get an IP address ( IPv4 or IPv6 ) of a DNS server.
 * @param[out] pxAddress: Variable to store the address found.
 * @param[in] pcHostName: use to check if it contains a dot ( DNS ), or not ( LLMNR ).
 * @return The end-point that holds the DNS address.
 */

    static NetworkEndPoint_t * prvGetDNSAddress( struct freertos_sockaddr * pxAddress,
                                                 const char * pcHostName )
    {
        NetworkEndPoint_t * pxEndPoint = NULL;
        BaseType_t xNeed_Endpoint = pdFALSE;

        /* Make sure all fields of the 'sockaddr' are cleared. */
        ( void ) memset( ( void * ) pxAddress, 0, sizeof( *pxAddress ) );

        /* And set the address type to IPv4.
         * It may change to IPv6 in case an IPv6 DNS server will be used. */
        pxAddress->sin_family = FREERTOS_AF_INET;

        /* 'sin_len' doesn't really matter, 'sockaddr' and 'sockaddr6'
         * have the same size. */
        pxAddress->sin_len = ( uint8_t ) sizeof( struct freertos_sockaddr );
        /* Use the DNS port by default, this may be changed later. */
        pxAddress->sin_port = dnsDNS_PORT;

        /* If LLMNR is being used then determine if the host name includes a '.' -
         * if not then LLMNR can be used as the lookup method. */
        /* For local resolution, mDNS uses names ending with the string ".local" */
        BaseType_t bHasDot = pdFALSE;
        BaseType_t bHasLocal = pdFALSE;
        char * pcDot = strchr( pcHostName, '.' );

        if( pcDot != NULL )
        {
            bHasDot = pdTRUE;

            if( strcmp( pcDot, ".local" ) == 0 )
            {
                bHasLocal = pdTRUE;
            }
            else
            {
                /* a DNS look-up of a public URL with at least one dot. */
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
                        pxAddress->sin_addr = ipMDNS_IP_ADDRESS; /* Is in network byte order. */
                        pxAddress->sin_port = ipMDNS_PORT;
                        pxAddress->sin_port = FreeRTOS_ntohs( pxAddress->sin_port );
                        xNeed_Endpoint = pdTRUE;
                        #if ( ipconfigUSE_IPv6 != 0 )
                            if( xDNS_IP_Preference == xPreferenceIPv6 )
                            {
                                sockaddr6_t * pxAddressV6 = ( ( sockaddr6_t * ) pxAddress );
                                memcpy( pxAddressV6->sin_addrv6.ucBytes,
                                        ipMDNS_IP_ADDR_IPv6.ucBytes,
                                        ipSIZE_OF_IPv6_ADDRESS );
                                pxAddress->sin_family = FREERTOS_AF_INET6;
                            }
                        #endif
                    }
                }
            #endif /* if ( ipconfigUSE_MDNS == 1 ) */
            #if ( ipconfigUSE_LLMNR == 1 )
                {
                    /* The hostname doesn't have a dot. */
                    if( bHasDot == pdFALSE )
                    {
                        /* Use LLMNR addressing. */
                        pxAddress->sin_addr = ipLLMNR_IP_ADDR; /* Is in network byte order. */
                        pxAddress->sin_port = ipLLMNR_PORT;
                        pxAddress->sin_port = FreeRTOS_ntohs( pxAddress->sin_port );
                        xNeed_Endpoint = pdTRUE;
                        #if ( ipconfigUSE_IPv6 != 0 )
                            sockaddr6_t * pxAddressV6 = ( ( sockaddr6_t * ) pxAddress );

                            if( xDNS_IP_Preference == xPreferenceIPv6 )
                            {
                                memcpy( pxAddressV6->sin_addrv6.ucBytes,
                                        ipLLMNR_IP_ADDR_IPv6.ucBytes,
                                        ipSIZE_OF_IPv6_ADDRESS );
                                pxAddress->sin_family = FREERTOS_AF_INET6;
                            }
                        #endif
                    }
                }
            #endif /* if ( ipconfigUSE_LLMNR == 1 ) */

            if( xNeed_Endpoint == pdTRUE )
            {
                for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
                     pxEndPoint != NULL;
                     pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
                {
                    #if ( ipconfigUSE_IPv6 != 0 )
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
                    #else /* if ( ipconfigUSE_IPv6 != 0 ) */
                        /* IPv6 is not included, so all end-points are IPv4. */
                        break;
                    #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
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
                #if ( ipconfigUSE_IPv6 != 0 )
                    if( ENDPOINT_IS_IPv6( pxEndPoint ) )
                    {
                        uint8_t ucIndex = pxEndPoint->ipv6_settings.ucDNSIndex;
                        uint8_t * ucBytes = pxEndPoint->ipv6_settings.xDNSServerAddresses[ ucIndex ].ucBytes;

                        /* Test if the DNS entry is in used. */
                        if( ( ucBytes[ 0 ] != 0U ) && ( ucBytes[ 1 ] != 0U ) )
                        {
                            struct freertos_sockaddr6 * pxAddress6 = ( struct freertos_sockaddr6 * ) pxAddress;

                            pxAddress->sin_family = FREERTOS_AF_INET6;
                            pxAddress->sin_len = ( uint8_t ) sizeof( struct freertos_sockaddr6 );
                            ( void ) memcpy( pxAddress6->sin_addrv6.ucBytes,
                                             pxEndPoint->ipv6_settings.xDNSServerAddresses[ ucIndex ].ucBytes,
                                             ipSIZE_OF_IPv6_ADDRESS );
                            break;
                        }
                    }
                    else
                #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
                {
                    uint8_t ucIndex = pxEndPoint->ipv4_settings.ucDNSIndex;
                    uint32_t ulIPAddress = pxEndPoint->ipv4_settings.ulDNSServerAddresses[ ucIndex ];

                    if( ( ulIPAddress != 0U ) && ( ulIPAddress != ipBROADCAST_IP_ADDRESS ) )
                    {
                        pxAddress->sin_addr = ulIPAddress;
                        break;
                    }
                }
            }
        }

        return pxEndPoint;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Prepare and send a message to a DNS server.  'uxReadTimeOut_ticks' will be passed as
 * zero, in case the user has supplied a call-back function.
 * @param[in] pcHostName: The hostname for which an IP address is required.
 * @param[in] uxIdentifier: Identifier to send in the DNS message.
 * @param[in] uxReadTimeOut_ticks: The timeout in ticks for waiting. In case the user has supplied
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
        struct freertos_sockaddr xAddress;
        Socket_t xDNSSocket;
        uint32_t ulIPAddress = 0U;
        BaseType_t xAttempt;
        int32_t lBytes;
        size_t uxPayloadLength;

        /* Two is added at the end for the count of characters in the first
         * subdomain part and the string end byte.
         * The two shorts are described in 'DNSTail_t'. */
        size_t uxExpectedPayloadLength = sizeof( DNSMessage_t ) + strlen( pcHostName ) + sizeof( uint16_t ) + sizeof( uint16_t ) + 2U;
        TickType_t uxWriteTimeOut_ticks = ipconfigDNS_SEND_BLOCK_TIME_TICKS;
        UBaseType_t uxHostType;

        #if ( ipconfigUSE_IPv6 != 0 )
            if( xFamily == FREERTOS_AF_INET6 )
            {
                /* Note that 'dnsTYPE_ANY_HOST' could be used here as well,
                 * but for testing, we want an IPv6 address. */
                uxHostType = dnsTYPE_AAAA_HOST;
                uxExpectedPayloadLength += ipSIZE_OF_IPv6_ADDRESS;
            }
            else
        #endif /* ( ipconfigUSE_IPv6 != 0 ) */
        {
            ( void ) xFamily;
            uxHostType = dnsTYPE_A_HOST;
        }

        xDNSSocket = DNS_CreateSocket( uxReadTimeOut_ticks );

        if( xDNSSocket != NULL )
        {
            for( xAttempt = 0; xAttempt < ipconfigDNS_REQUEST_ATTEMPTS; xAttempt++ )
            {
                size_t uxHeaderBytes;
                NetworkBufferDescriptor_t * pxNetworkBuffer;
                uint8_t * pucUDPPayloadBuffer = NULL, * pucReceiveBuffer;
                NetworkEndPoint_t * pxEndPoint;

                pxEndPoint = prvGetDNSAddress( &( xAddress ), pcHostName );

                if( pxEndPoint == NULL )
                {
                    FreeRTOS_printf( ( "Can not find a DNS address, along with an end-point.\n" ) );
                    /* No endpoint was found that defines a DNS address. */
                    break;
                }

                if( xAttempt == 0 )
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
                }

                /* Calculate the size of the headers. */
                #if ( ipconfigUSE_IPv6 != 0 )
                    if( xAddress.sin_family == FREERTOS_AF_INET6 )
                    {
                        uxHeaderBytes = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_UDP_HEADER;
                    }
                    else
                #endif
                {
                    uxHeaderBytes = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER;
                }

                {
                    char pcBuffer[ 41 ];
                    #if ( ipconfigUSE_IPv6 != 0 )
                        if( xAddress.sin_family == FREERTOS_AF_INET6 )
                        {
                            struct freertos_sockaddr6 * pxSockaddr6 = ( struct freertos_sockaddr6 * ) &( xAddress );
                            FreeRTOS_inet_ntop6( pxSockaddr6->sin_addrv6.ucBytes,
                                                 pcBuffer,
                                                 sizeof( pcBuffer ) );
                        }
                        else
                    #endif
                    {
                        FreeRTOS_inet_ntop4( ( void * ) &( xAddress.sin_addr ),
                                             pcBuffer,
                                             sizeof( pcBuffer ) );
                    }

                    FreeRTOS_printf( ( "DNS-%c lookup: \"%s\" DNS at %s\n",
                                       ( xFamily == FREERTOS_AF_INET4 ) ? '4' : '6',
                                       pcHostName,
                                       pcBuffer ) );
                }

                pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxHeaderBytes + uxExpectedPayloadLength, 0U );

                if( pxNetworkBuffer == NULL )
                {
                    FreeRTOS_printf( ( "prvGetHostByName: No network buffer\n" ) );
                    break;
                }

                /* A two-step conversion to conform to MISRA. */
                size_t uxIndex = ipUDP_PAYLOAD_IP_TYPE_OFFSET;
                BaseType_t xIndex = ( BaseType_t ) uxIndex;
                pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ uxHeaderBytes ] );

                /* Later when translating form UDP payload to a Network Buffer,
                 * it is important to know whether this is an IPv4 packet. */
                #if ( ipconfigUSE_IPv6 != 0 )
                    if( xAddress.sin_family == FREERTOS_AF_INET6 )
                    {
                        pucUDPPayloadBuffer[ -xIndex ] = ( uint8_t ) ipTYPE_IPv6;
                    }
                    else
                #endif
                {
                    pucUDPPayloadBuffer[ -xIndex ] = ( uint8_t ) ipTYPE_IPv4;
                }

                /* Create the message in the obtained buffer. */
                uxPayloadLength = prvCreateDNSMessage( pucUDPPayloadBuffer, pcHostName, uxIdentifier, uxHostType );

                iptraceSENDING_DNS_REQUEST();

                /* ipLLMNR_IP_ADDR is in network byte order. */
                if( ( xAddress.sin_addr == ipLLMNR_IP_ADDR ) || ( xAddress.sin_addr == ipMDNS_IP_ADDRESS ) )
                {
                    /* Use LLMNR addressing. */
                    ( ( ( DNSMessage_t * ) pucUDPPayloadBuffer ) )->usFlags = 0;
                }

                ulIPAddress = 0U;
                BaseType_t xSendResult = DNS_SendRequest( xDNSSocket,
                                                          &xAddress,
                                                          pucUDPPayloadBuffer,
                                                          uxPayloadLength );

                if( xSendResult <= 0 )
                {
                    /* The message was not sent so the stack will not be
                     * releasing the zero copy - it must be released here. */
                    vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
                    break;
                }

                struct freertos_sockaddr xRecvAddress;
                /* Wait for the reply. */
                lBytes = DNS_ReadReply( xDNSSocket,
                                        &xAddress,
                                        &pucReceiveBuffer );

                if( ( lBytes == -pdFREERTOS_ERRNO_EWOULDBLOCK ) && ( pxEndPoint != NULL ) )
                {
                    /* This search timed out, next time try with a different DNS. */
                    #if ( ipconfigUSE_IPv6 != 0 )
                        if( xRecvAddress.sin_family == FREERTOS_AF_INET6 )
                        {
                            prvIncreaseDNS6Index( pxEndPoint );
                        }
                        else
                    #endif
                    {
                        prvIncreaseDNS4Index( pxEndPoint );
                    }
                }
                else if( lBytes > 0 )
                {
                    BaseType_t xExpected;
                    const DNSMessage_t * pxDNSMessageHeader = ( ( const DNSMessage_t * ) pucReceiveBuffer );

                    #if ( ipconfigUSE_MDNS == 1 )
                        if( FreeRTOS_ntohs( xRecvAddress.sin_port ) == ipMDNS_PORT ) /* mDNS port 5353. */
                        {
                            /* In mDNS, the query ID field is ignored. */
                            xExpected = pdTRUE;
                        }
                        else
                    #endif /* if ( ipconfigUSE_MDNS == 1 ) */
                    {
                        /* See if the identifiers match. */
                        xExpected = ( uxIdentifier == ( TickType_t ) pxDNSMessageHeader->usIdentifier ) ? pdTRUE : pdFALSE;
                    }

                    /* The reply was received.  Process it. */
                    #if ( ipconfigDNS_USE_CALLBACKS == 0 )

                        /* It is useless to analyse the unexpected reply
                         * unless asynchronous look-ups are enabled. */
                        if( xExpected != pdFALSE )
                    #endif /* ipconfigDNS_USE_CALLBACKS == 0 */
                    {
                        /* IPv4: 'ulIPAddress' will contain the IP-address of the host, or zero.
                         * IPv6: 'ulIPAddress' will be non-zero, to indicated that an IPv6
                         * address was found. */
                        ulIPAddress = DNS_ParseDNSReply( pucReceiveBuffer,
                                                         ( size_t ) lBytes,
                                                         ppxAddressInfo,
                                                         xExpected,
                                                         xAddress.sin_port );
                    }

                    /* Finished with the buffer.  The zero copy interface
                     * is being used, so the buffer must be freed by the
                     * task. */
                    FreeRTOS_ReleaseUDPPayloadBuffer( pucReceiveBuffer );

                    if( ulIPAddress != 0U )
                    {
                        /* All done. */
                        break;
                    }
                }
                else
                {
                    /* No data were received. */
                }

                if( lBytes <= 0 )
                {
                    break;
                }

                /* The first send may not succeed if an ARP request is sent.
                * Only the second will succeed. So send at least 2 times. */
                if( ( uxReadTimeOut_ticks == 0U ) && ( xAttempt > 0 ) )
                {
                    /* This DNS lookup is asynchronous, using a call-back:
                     * send the request only once. */
                    break;
                }
            }     /* for( xAttempt = 0; xAttempt < ipconfigDNS_REQUEST_ATTEMPTS; xAttempt++ ) */

            /* Finished with the socket. */
            ( void ) DNS_CloseSocket( xDNSSocket );
        }     /* if( xDNSSocket != NULL ) */

        return ulIPAddress;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Create the DNS message in the zero copy buffer passed in the first parameter.
 * @param[in,out] pucUDPPayloadBuffer: The zero copy buffer where the DNS message will be created.
 * @param[in] pcHostName: Hostname to be looked up.
 * @param[in] uxIdentifier: The identifier to be added to the DNS message.
 * @param[in] uxHostType: dnsTYPE_A_HOST ( IPv4 ) or dnsTYPE_AAA_HOST ( IPv6 ).
 * @return Total size of the generated message, which is the space from the last written byte
 *         to the beginning of the buffer.
 */
    static size_t prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                                       const char * pcHostName,
                                       TickType_t uxIdentifier,
                                       UBaseType_t uxHostType )
    {
        DNSMessage_t * pxDNSMessageHeader;
        size_t uxStart, uxIndex;
        uint8_t * pucTail;
        static const DNSMessage_t xDefaultPartDNSHeader =
        {
            0,                     /* The identifier will be overwritten. */
            dnsOUTGOING_FLAGS,     /* Flags set for standard query. */
            dnsONE_QUESTION,       /* One question is being asked. */
            0,                     /* No replies are included. */
            0,                     /* No authorities. */
            0                      /* No additional authorities. */
        };

/* memcpy() helper variables for MISRA Rule 21.15 compliance*/
        const void * pvCopySource;
        void * pvCopyDest;

        /* Although both pointers have been checked already, some extra
         * asserts are added to help the CBMC proofs.. */
        configASSERT( pucUDPPayloadBuffer != NULL );
        configASSERT( pcHostName != NULL );

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

        /* Read type and class from the record. */
        pucTail = &( pucUDPPayloadBuffer[ uxStart + 1U ] );

        vSetField16( pucTail, DNSTail_t, usType, ( uint16_t ) uxHostType );
        vSetField16( pucTail, DNSTail_t, usClass, dnsCLASS_IN );

        /* Return the total size of the generated message, which is the space from
         * the last written byte to the beginning of the buffer. */
        return uxIndex + sizeof( DNSTail_t ) + 1U;
    }
/*-----------------------------------------------------------*/

/**
 * @brief For testing purposes: print an address of DNS replies.
 * @param[in] pcFormat: Print format.
 * @param[in] pxAddress: The address to print.
 */
    void show_single_addressinfo( const char * pcFormat,
                                  const struct freertos_addrinfo * pxAddress )
    {
        char cBuffer[ 40 ];
        const uint8_t * pucAddress;

        #if ( ipconfigUSE_IPv6 != 0 )
            if( pxAddress->ai_family == FREERTOS_AF_INET6 )
            {
                struct freertos_sockaddr6 * sockaddr6 = ( ( sockaddr6_t * ) pxAddress->ai_addr );

                pucAddress = ( const uint8_t * ) &( sockaddr6->sin_addrv6 );
            }
            else
        #endif /* ( ipconfigUSE_IPv6 != 0 ) */
        {
            pucAddress = ( const uint8_t * ) &( pxAddress->ai_addr->sin_addr );
        }

        ( void ) FreeRTOS_inet_ntop( pxAddress->ai_family, ( const void * ) pucAddress, cBuffer, sizeof( cBuffer ) );

        if( pcFormat != NULL )
        {
            FreeRTOS_printf( ( pcFormat, cBuffer ) );
        }
        else
        {
            FreeRTOS_printf( ( "Address: %s\n", cBuffer ) );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief For testing purposes: print a list of DNS replies.
 * @param[in] pxAddress: The first reply received ( or NULL )
 */
    void show_addressinfo( const struct freertos_addrinfo * pxAddress )
    {
        const struct freertos_addrinfo * ptr = pxAddress;
        BaseType_t xIndex = 0;

        while( ptr != NULL )
        {
            show_single_addressinfo( "Found Address: %s", ptr );

            ptr = ptr->ai_next;
        }

        /* In case the function 'FreeRTOS_printf()` is not implemented. */
        ( void ) xIndex;
    }


/* The function below will only be called :
 * when ipconfigDNS_USE_CALLBACKS == 1
 * when ipconfigUSE_LLMNR == 1
 * for testing purposes, by the module iot_test_freertos_tcp.c
 */
    #if ( ipconfigUSE_DNS == 1 ) && ( ( ipconfigDNS_USE_CALLBACKS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) )

/**
 * @brief Perform some preliminary checks and then parse the DNS packet.
 * @param[in] pxNetworkBuffer: The network buffer to be parsed.
 * @return Always pdFAIL to indicate that the packet was not consumed and must
 *         be released by the caller.
 */
        uint32_t ulDNSHandlePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
        {
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
                    uint8_t * pucUDPPayload = &( pxNetworkBuffer->pucEthernetBuffer[ uxUDPPacketSize ] );

                    /* The parameter pdFALSE indicates that the reply was not expected. */
                    ( void ) DNS_ParseDNSReply( pucUDPPayload,
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

    #endif /* ( ipconfigUSE_DNS == 1 ) && ( ( ipconfigDNS_USE_CALLBACKS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) ) */
/*-----------------------------------------------------------*/

    #if ( ipconfigUSE_NBNS == 1 )

/**
 * @brief Handle an NBNS packet.
 * @param[in] pxNetworkBuffer: The network buffer holding the NBNS packet.
 * @return pdFAIL to show that the packet was not consumed.
 */
        uint32_t ulNBNSHandlePacket( NetworkBufferDescriptor_t * pxNetworkBuffer )
        {
            UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
            uint8_t * pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( *pxUDPPacket ) ] );

            DNS_TreatNBNS( pucUDPPayloadBuffer,
                           pxNetworkBuffer->xDataLength,
                           pxUDPPacket->xIPHeader.ulSourceIPAddress );

            /* The packet was not consumed. */
            return pdFAIL;
        }

    #endif /* ipconfigUSE_NBNS */
/*-----------------------------------------------------------*/

#endif /* ipconfigUSE_DNS != 0 */

/* Provide access to private members for testing. */
#ifdef FREERTOS_ENABLE_UNIT_TESTS
    #include "freertos_tcp_test_access_dns_define.h"
#endif
