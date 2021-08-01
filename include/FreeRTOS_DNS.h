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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

#ifndef FREERTOS_DNS_H
    #define FREERTOS_DNS_H

    #ifdef __cplusplus
        extern "C" {
    #endif

/* Application level configuration options. */
    #include "FreeRTOSIPConfig.h"
    #include "IPTraceMacroDefaults.h"


/* The Link-local Multicast Name Resolution (LLMNR)
 * is included.
 * Note that a special MAC address is required in addition to the NIC's actual
 * MAC address: 01:00:5E:00:00:FC
 *
 * The target IP address will be 224.0.0.252
 */
    #if ( ipconfigBYTE_ORDER == pdFREERTOS_BIG_ENDIAN )
        #define ipLLMNR_IP_ADDR    0xE00000FCUL
    #else
        #define ipLLMNR_IP_ADDR    0xFC0000E0UL
    #endif /* ipconfigBYTE_ORDER == pdFREERTOS_BIG_ENDIAN */

    #define ipLLMNR_PORT           5355 /* Standard LLMNR port. */
    #define ipDNS_PORT             53   /* Standard DNS port. */
    #define ipDHCP_CLIENT          67
    #define ipDHCP_SERVER          68
    #define ipNBNS_PORT            137 /* NetBIOS Name Service. */
    #define ipNBDGM_PORT           138 /* Datagram Service, not included. */

/* Even when a DNS server is contacted through its IPv4 address,
 * it can look-up IPv6 addresses. */

    #define dnsTYPE_A_HOST       0x0001U
    #define dnsTYPE_AAAA_HOST    0x001CU

/** @brief freertos_addrinfo is the equivalent of 'struct addrinfo'. */
    struct freertos_addrinfo
    {
        BaseType_t ai_flags;                /**< The field is included for completeness, but it is not used. */
        BaseType_t ai_family;               /**< The type of IP-address, either FREERTOS_AF_INET4 or FREERTOS_AF_INET6. */
        BaseType_t ai_socktype;             /**< n.a. */
        BaseType_t ai_protocol;             /**< n.a. */
        socklen_t ai_addrlen;               /**< The length of the address, either ipSIZE_OF_IPv4_ADDRESS or ipSIZE_OF_IPv6_ADDRESS. */
        struct freertos_sockaddr * ai_addr; /**< The IP-address. Can be mapped onto 'freertos_sockaddr6' in case of IPv6. */
        char * ai_canonname;                /**< The name of the host. */
        struct freertos_addrinfo * ai_next; /**< A pointer to the next find result, or NULL. */
        struct
        {
            /* In order to avoid allocations, reserve space here for *ai_addr and *ai_canonname. */
            #if ( ipconfigUSE_IPv6 != 0 )
                struct freertos_sockaddr6 sockaddr6;
            #else
                struct freertos_sockaddr sockaddr4;
            #endif

            #if ( ipconfigUSE_DNS_CACHE != 0 )
                char ucName[ ipconfigDNS_CACHE_NAME_LENGTH ];
            #endif
        }
        xPrivateStorage; /**< In order to avoid extra calls to malloc, the necessary space is reserved 'statically'. */
    };

/* Below #include just tells the compiler to pack the structure.
 * It is included in to make the code more readable */
    #include "pack_struct_start.h"
    struct xDNSMessage
    {
        uint16_t usIdentifier;    /**< Query identifier. Used to match up replies to outstanding queries. */
        uint16_t usFlags;         /**< Flags. */
        uint16_t usQuestions;     /**< Number of questions asked in this query. */
        uint16_t usAnswers;       /**< Number of answers being provided in this query. */
        uint16_t usAuthorityRRs;  /**< Authoritative name server resource records. */
        uint16_t usAdditionalRRs; /**< Additional resource records.*/
    }
    #include "pack_struct_end.h"
    typedef struct xDNSMessage DNSMessage_t;

/* @brief A struct with a set of variables that are shared among the helper functions
 *        for the function 'prvParseDNSReply()'. For internal use only.
 */
    typedef struct xParseSet
    {
        DNSMessage_t * pxDNSMessageHeader; /**< A pointer to the UDP payload buffer where the DNS message is stored. */
        uint16_t usQuestions;              /**< The number of DNS questions that were asked. */
        uint8_t * pucByte;                 /**< A pointer that is used while parsing. */
        size_t uxSourceBytesRemaining;     /**< As pucByte is incremented, 'uxSourceBytesRemaining' will be decremented. */
        uint16_t usType;                   /**< The type of address, recognised are dnsTYPE_A_HOST ( Ipv4 ) and
                                            *   dnsTYPE_AAAA_HOST ( IPv6 ). */
        uint32_t ulIPAddress;              /**< The IPv4 address found. In an IPv6 look-up, store a non-zero value when
                                            *   an IPv6 address was found. */
        size_t uxAddressLength;            /**< The size of the address, either ipSIZE_OF_IPv4_ADDRESS or
                                            *   ipSIZE_OF_IPv6_ADDRESS */
        uint16_t usNumARecordsStored;      /**< The number of A-records stored during a look-up. */
        #if ( ipconfigUSE_LLMNR == 1 )
            uint16_t usClass;              /**< Only the value 'dnsCLASS_IN' is recognised, which stands for "Internet". */
            char * pcRequestedName;        /**< A pointer to the full name of the host being looked up. */
        #endif
        #if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
            BaseType_t xDoStore;                          /**< Becomes true when a DNS reply was requested by this device,
                                                           *   i.e. it has a matching request ID. */
            char pcName[ ipconfigDNS_CACHE_NAME_LENGTH ]; /**< A copy of the name that is mentioned in the questions. */
        #endif
        struct freertos_addrinfo * pxLastAddress;
        struct freertos_addrinfo ** ppxLastAddress;
    } ParseSet_t;

    extern void show_single_addressinfo( const char * pcFormat,
                                         const struct freertos_addrinfo * pxAddress );
    extern void show_addressinfo( const struct freertos_addrinfo * pxAddress );

/*
 * The following function should be provided by the user and return true if it
 * matches the domain name.
 */
    /* Even though the function is defined in main.c, the rule is violated. */
    /* misra_c_2012_rule_8_6_violation */
    extern BaseType_t xApplicationDNSQueryHook( struct xNetworkEndPoint * pxEndPoint,
                                                const char * pcName );

/*
 * LLMNR is very similar to DNS, so is handled by the DNS routines.
 */
    #if ( ipconfigUSE_DNS == 1 ) && ( ( ipconfigDNS_USE_CALLBACKS == 1 ) || ( ipconfigUSE_LLMNR == 1 ) )
        uint32_t ulDNSHandlePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer );
    #endif

    #if ( ipconfigUSE_LLMNR == 1 )
        /* The LLMNR MAC address is 01:00:5e:00:00:fc */
        extern const MACAddress_t xLLMNR_MacAdress;
    #endif /* ipconfigUSE_LLMNR */

    #if ( ipconfigUSE_LLMNR == 1 ) && ( ipconfigUSE_IPv6 != 0 )

/* The LLMNR IPv6 address is ff02::1:3 */
        extern const IPv6_Address_t ipLLMNR_IP_ADDR_IPv6;

/* The LLMNR IPv6 MAC address is 33:33:00:01:00:03 */
        extern const MACAddress_t xLLMNR_MacAdressIPv6;
    #endif /* ipconfigUSE_LLMNR */

    #if ( ipconfigUSE_NBNS != 0 )

/*
 * Inspect a NetBIOS Names-Service message.  If the name matches with ours
 * (xApplicationDNSQueryHook returns true) an answer will be sent back.
 * Note that LLMNR is a better protocol for name services on a LAN as it is
 * less polluted
 */
        uint32_t ulNBNSHandlePacket( NetworkBufferDescriptor_t * pxNetworkBuffer );

    #endif /* ipconfigUSE_NBNS */

    #if ( ipconfigUSE_DNS_CACHE != 0 )

/* Look for the indicated host name in the DNS cache. Returns the IPv4
 * address if present, or 0x0 otherwise. */
        uint32_t FreeRTOS_dnslookup( const char * pcHostName );

        #if ( ipconfigUSE_IPv6 != 0 )
            /* FreeRTOS_dnslookup6() returns pdTRUE when a host has been found. */
            uint32_t FreeRTOS_dnslookup6( const char * pcHostName,
                                          IPv6_Address_t * pxAddress_IPv6 );
        #endif

/* Remove all entries from the DNS cache. */
        void FreeRTOS_dnsclear( void );

    #endif /* ipconfigUSE_DNS_CACHE != 0 */

    #if ( ipconfigDNS_USE_CALLBACKS != 0 )

/*
 * Users may define this type of function as a callback.
 * It will be called when a DNS reply is received or when a timeout has been reached.
 */
        #if ( ipconfigUSE_IPv6 != 0 )
            typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                            void * /* pvSearchID */,
                                            struct freertos_addrinfo * /* pxAddressInfo */ );
        #else
            typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                            void * /* pvSearchID */,
                                            uint32_t /* ulIPAddress */ );
        #endif

/*
 * Asynchronous version of gethostbyname()
 * xTimeout is in units of ms.
 */
        uint32_t FreeRTOS_gethostbyname_a( const char * pcHostName,
                                           FOnDNSEvent pCallback,
                                           void * pvSearchID,
                                           TickType_t uxTimeout );
        void FreeRTOS_gethostbyname_cancel( void * pvSearchID );

/* The asynchronous versions of FreeRTOS_getaddrinfo(). */
        BaseType_t FreeRTOS_getaddrinfo_a( const char * pcName,                      /* The name of the node or device */
                                           const char * pcService,                   /* Ignored for now. */
                                           const struct freertos_addrinfo * pxHints, /* If not NULL: preferences. */
                                           struct freertos_addrinfo ** ppxResult,    /* An allocated struct, containing the results. */
                                           FOnDNSEvent pCallback,
                                           void * pvSearchID,
                                           TickType_t uxTimeout );

    #endif /* if ( ipconfigDNS_USE_CALLBACKS != 0 ) */

/*
 * Lookup a IPv4 node in a blocking-way.
 * It returns a 32-bit IP-address, 0 when not found.
 * gethostbyname() is already deprecated.
 */
    uint32_t FreeRTOS_gethostbyname( const char * pcHostName );

/*
 * FreeRTOS_getaddrinfo() replaces FreeRTOS_gethostbyname().
 * When 'ipconfigUSE_IPv6' is defined, it can also retrieve IPv6 addresses,
 * in case pxHints->ai_family equals FREERTOS_AF_INET6.
 * Otherwise, or when pxHints is NULL, only IPv4 addresses will be returned.
 */
    BaseType_t FreeRTOS_getaddrinfo( const char * pcName,                      /* The name of the node or device */
                                     const char * pcService,                   /* Ignored for now. */
                                     const struct freertos_addrinfo * pxHints, /* If not NULL: preferences. */
                                     struct freertos_addrinfo ** ppxResult );  /* An allocated struct, containing the results. */

/* When FreeRTOS_getaddrinfo() is successful, ppxResult will point to an
 * allocated structure.  This pointer must be released by the user by calling
 * FreeRTOS_freeaddrinfo().
 */
    void FreeRTOS_freeaddrinfo( struct freertos_addrinfo * pxInfo );

    #if ( ipconfigDNS_USE_CALLBACKS != 0 )

/*
 * The function vDNSInitialise() initialises the DNS module.
 * It will be called "internally", by the IP-task.
 */
        void vDNSInitialise( void );
    #endif /* ( ipconfigDNS_USE_CALLBACKS != 0 ) */


    #ifdef __cplusplus
        } /* extern "C" */
    #endif

#endif /* FREERTOS_DNS_H */
