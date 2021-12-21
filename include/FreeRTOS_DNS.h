/*
 * FreeRTOS+TCP V2.4.0
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

#ifndef FREERTOS_DNS_H
    #define FREERTOS_DNS_H

    #ifdef __cplusplus
        extern "C" {
    #endif

/* Application level configuration options. */
    #include "FreeRTOSIPConfig.h"
    #include "FreeRTOSIPConfigDefaults.h"
    #include "IPTraceMacroDefaults.h"


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

/* Host types. */
    #define dnsTYPE_A_HOST            0x01U /**< DNS type A host. */
    #define dnsCLASS_IN               0x01U /**< DNS class IN (Internet). */

/* Maximum hostname length as defined in RFC 1035 section 3.1. */
    #define dnsMAX_HOSTNAME_LENGTH    0xFFU

    #ifndef _lint
        /* LLMNR constants. */
        #define dnsLLMNR_TTL_VALUE           300000UL /**< LLMNR time to live value. */
        #define dnsLLMNR_FLAGS_IS_REPONSE    0x8000U  /**< LLMNR flag value for response. */
    #endif /* _lint */

/* NBNS constants. */
    #if ( ipconfigUSE_NBNS != 0 )
        #define dnsNBNS_TTL_VALUE               3600UL  /**< NBNS TTL: 1 hour valid. */
        #define dnsNBNS_TYPE_NET_BIOS           0x0020U /**< NBNS Type: NetBIOS. */
        #define dnsNBNS_CLASS_IN                0x01U   /**< NBNS Class: IN (Internet). */
        #define dnsNBNS_NAME_FLAGS              0x6000U /**< NBNS name flags. */
        #define dnsNBNS_ENCODED_NAME_LENGTH     32      /**< NBNS encoded name length. */

/** @brief If the queried NBNS name matches with the device's name,
 * the query will be responded to with these flags: */
        #define dnsNBNS_QUERY_RESPONSE_FLAGS    ( 0x8500U )
    #endif /* ( ipconfigUSE_NBNS != 0 ) */

/** @brief Flag DNS parsing errors in situations where an IPv4 address is the return
 * type. */
    #define dnsPARSE_ERROR    0U

    #ifndef _lint
        #if ( ipconfigUSE_DNS_CACHE == 0 )
            #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY != 1 )
                #error When DNS caching is disabled, please make ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY equal to 1.
            #endif
        #endif
    #endif

/** @brief Define the ASCII value of '.' (Period/Full-stop). */
    #define ASCII_BASELINE_DOT    46U

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

/* DNS answer record header. */
    #include "pack_struct_start.h"
    struct xDNSAnswerRecord
    {
        uint16_t usType;       /**< Type of DNS answer record. */
        uint16_t usClass;      /**< Class of DNS answer record. */
        uint32_t ulTTL;        /**< Number of seconds the result can be cached. */
        uint16_t usDataLength; /**< Length of the data field. */
    }
    #include "pack_struct_end.h"
    typedef struct xDNSAnswerRecord DNSAnswerRecord_t;


    #if ( ipconfigUSE_DNS_CACHE == 1 )
        typedef struct xDNS_CACHE_TABLE_ROW
        {
            uint32_t ulIPAddresses[ ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY ]; /* The IP address(es) of an ARP cache entry. */
            char pcName[ ipconfigDNS_CACHE_NAME_LENGTH ];                    /* The name of the host */
            uint32_t ulTTL;                                                  /* Time-to-Live (in seconds) from the DNS server. */
            uint32_t ulTimeWhenAddedInSeconds;
            #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
                uint8_t ucNumIPAddresses;
                uint8_t ucCurrentIPAddress;
            #endif
        } DNSCacheRow_t;
    #endif /* if ( ipconfigUSE_DNS_CACHE == 1 ) */

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

    #if ( ipconfigUSE_LLMNR == 1 )

        #include "pack_struct_start.h"
        struct xLLMNRAnswer
        {
            uint8_t ucNameCode;    /**< Name type. */
            uint8_t ucNameOffset;  /**< The name is not repeated in the answer, only the offset is given with "0xc0 <offs>" */
            uint16_t usType;       /**< Type of the Resource record. */
            uint16_t usClass;      /**< Class of the Resource record. */
            uint32_t ulTTL;        /**< Seconds till this entry can be cached. */
            uint16_t usDataLength; /**< Length of the address in this record. */
            uint32_t ulIPAddress;  /**< The IP-address. */
        }
        #include "pack_struct_end.h"
        typedef struct xLLMNRAnswer LLMNRAnswer_t;
    #endif /* if ( ipconfigUSE_LLMNR == 1 ) */

    #if ( ipconfigUSE_NBNS == 1 )

        #include "pack_struct_start.h"
        struct xNBNSRequest
        {
            uint16_t usRequestId;                          /**< NBNS request ID. */
            uint16_t usFlags;                              /**< Flags of the DNS message. */
            uint16_t ulRequestCount;                       /**< The number of requests/questions in this query. */
            uint16_t usAnswerRSS;                          /**< The number of answers in this query. */
            uint16_t usAuthRSS;                            /**< Number of authoritative resource records. */
            uint16_t usAdditionalRSS;                      /**< Number of additional resource records. */
            uint8_t ucNameSpace;                           /**< Length of name. */
            uint8_t ucName[ dnsNBNS_ENCODED_NAME_LENGTH ]; /**< The domain name. */
            uint8_t ucNameZero;                            /**< Terminator of the name. */
            uint16_t usType;                               /**< Type of NBNS record. */
            uint16_t usClass;                              /**< Class of NBNS request. */
        }
        #include "pack_struct_end.h"
        typedef struct xNBNSRequest NBNSRequest_t;

        #include "pack_struct_start.h"
        struct xNBNSAnswer
        {
            uint16_t usType;       /**< Type of NBNS answer. */
            uint16_t usClass;      /**< Class of NBNS answer. */
            uint32_t ulTTL;        /**< Time in seconds for which the answer can be cached. */
            uint16_t usDataLength; /**< Data length. */
            uint16_t usNbFlags;    /**< NetBIOS flags 0x6000 : IP-address, big-endian. */
            uint32_t ulIPAddress;  /**< The IPv4 address. */
        }
        #include "pack_struct_end.h"
        typedef struct xNBNSAnswer NBNSAnswer_t;
    #endif /* if ( ipconfigUSE_NBNS == 1 ) */

    #if ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_NBNS == 1 )

/*
 * The following function should be provided by the user and return true if it
 * matches the domain name.
 */
        extern BaseType_t xApplicationDNSQueryHook( const char * pcName );
    #endif /* ( ipconfigUSE_LLMNR == 1 ) || ( ipconfigUSE_NBNS == 1 ) */

/*
 * LLMNR is very similar to DNS, so is handled by the DNS routines.
 */
    uint32_t ulDNSHandlePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer );

    #if ( ipconfigUSE_LLMNR == 1 )
        /* The LLMNR MAC address is 01:00:5e:00:00:fc */
        extern const MACAddress_t xLLMNR_MacAdress;
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

/* Remove all entries from the DNS cache. */
        void FreeRTOS_dnsclear( void );

    #endif /* ipconfigUSE_DNS_CACHE != 0 */

    #if ( ipconfigDNS_USE_CALLBACKS != 0 )

/*
 * Users may define this type of function as a callback.
 * It will be called when a DNS reply is received or when a timeout has been reached.
 */
        typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                        void * /* pvSearchID */,
                                        uint32_t /* ulIPAddress */ );

/*
 * Asynchronous version of gethostbyname()
 * xTimeout is in units of ms.
 */
        uint32_t FreeRTOS_gethostbyname_a( const char * pcHostName,
                                           FOnDNSEvent pCallback,
                                           void * pvSearchID,
                                           TickType_t uxTimeout );
        void FreeRTOS_gethostbyname_cancel( void * pvSearchID );

/** @brief The structure to hold information for a DNS callback. */
        typedef struct xDNS_Callback
        {
            TickType_t uxRemaningTime;     /**< Timeout in ms */
            FOnDNSEvent pCallbackFunction; /**< Function to be called when the address has been found or when a timeout has been reached */
            TimeOut_t uxTimeoutState;      /**< Timeout state. */
            void * pvSearchID;             /**< Search ID of the callback function. */
            struct xLIST_ITEM xListItem;   /**< List struct. */
            char pcName[ 1 ];              /**< 1 character name. */
        } DNSCallback_t;

    #endif /* if ( ipconfigDNS_USE_CALLBACKS != 0 ) */

/*
 * Lookup a IPv4 node in a blocking-way.
 * It returns a 32-bit IP-address, 0 when not found.
 * gethostbyname() is already deprecated.
 */
    uint32_t FreeRTOS_gethostbyname( const char * pcHostName );

    #if ( ipconfigDNS_USE_CALLBACKS == 1 )

/*
 * The function vDNSInitialise() initialises the DNS module.
 * It will be called "internally", by the IP-task.
 */
        void vDNSInitialise( void );
    #endif /* ( ipconfigDNS_USE_CALLBACKS == 1 ) */

    #if ( ipconfigDNS_USE_CALLBACKS == 1 )

/*
 * A function local to the library.
 */
        extern void vDNSCheckCallBack( void * pvSearchID );
    #endif


    #ifdef __cplusplus
        } /* extern "C" */
    #endif

#endif /* FREERTOS_DNS_H */
