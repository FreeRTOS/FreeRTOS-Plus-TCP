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
 * @file FreeRTOS_DNS_Cache.c
 * @brief File that handles the DNS caching option
 */

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "FreeRTOS_DNS_Cache.h"
#include "FreeRTOS_DNS_Globals.h"

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#if ( ( ipconfigUSE_DNS != 0 ) && ( ipconfigUSE_DNS_CACHE == 1 ) )

/**
 * @brief cache entry format structure
 */
    typedef struct xDNS_CACHE_TABLE_ROW
    {
        IPv46_Address_t xAddresses[ ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY ]; /*!< The IP address(es) of an ARP cache entry. */
        char pcName[ ipconfigDNS_CACHE_NAME_LENGTH ];                        /*!< The name of the host */
        uint32_t ulTTL;                                                      /*!< Time-to-Live (in seconds) from the DNS server. */
        uint32_t ulTimeWhenAddedInSeconds;                                   /*!< time at which the entry was added */
        #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
            uint8_t ucNumIPAddresses;                                        /*!< number of ip addresses for the same entry */
            uint8_t ucCurrentIPAddress;                                      /*!< current ip address index */
        #endif
    } DNSCacheRow_t;

/*!
 * @brief DNS cache structure instantiation
 */
    static DNSCacheRow_t xDNSCache[ ipconfigDNS_CACHE_ENTRIES ] = { 0x0 };

/*!
 * @brief indicates the index of a free entry in the cache structure
 *        \a  DNSCacheRow_t
 */
    static UBaseType_t uxFreeEntry = 0U;

/** returns the index of the hostname entry in the dns cache. */
    static BaseType_t prvFindEntryIndex( const char * pcName,
                                         IPv46_Address_t * pxIP );

/** get entry at \p index from the cache. */
    static BaseType_t prvGetCacheIPEntry( BaseType_t index,
                                          IPv46_Address_t * pxIP,
                                          uint32_t ulCurrentTimeSeconds,
                                          struct freertos_addrinfo ** ppxAddressInfo );

/** update entry at \p index in the cache. */
    static void prvUpdateCacheEntry( BaseType_t index,
                                     uint32_t ulTTL,
                                     IPv46_Address_t * pxIP,
                                     uint32_t ulCurrentTimeSeconds );

/** insert entry in the cache. */
    static void prvInsertCacheEntry( const char * pcName,
                                     uint32_t ulTTL,
                                     IPv46_Address_t * pxIP,
                                     uint32_t ulCurrentTimeSeconds );

    #if ( ipconfigUSE_DNS_CACHE == 1 )
        /** Copy DNS cache entries at xIndex to a linked struct addrinfo. */
        static void prvReadDNSCache( BaseType_t xIndex,
                                     struct freertos_addrinfo ** ppxAddressInfo );
    #endif

/*-----------------------------------------------------------*/

/**
 * @brief perform a dns lookup in the local cache
 * @param pcHostName the lookup name
 * @return ulIPAddress with the value from the cache else returns a zero if the
 *         cache is not enabled or the lookup is not successful
 * @post the global structure \a xDNSCache might be modified
 */
    uint32_t FreeRTOS_dnslookup( const char * pcHostName )
    {
        IPv46_Address_t xIPv46_Address;

/* Looking up an IPv4 address in the DNS cache. */
        ( void ) memset( &xIPv46_Address, 0, sizeof( xIPv46_Address ) );
        ( void ) FreeRTOS_ProcessDNSCache( pcHostName,
                                           &( xIPv46_Address ),
                                           0,
                                           pdTRUE,
                                           NULL );

        return xIPv46_Address.ulIPAddress;
    }
/*-----------------------------------------------------------*/

    #if ( ipconfigUSE_DNS_CACHE == 1 ) && ( ipconfigUSE_IPv6 != 0 )
        uint32_t FreeRTOS_dnslookup6( const char * pcHostName,
                                      IPv6_Address_t * pxAddress_IPv6 )
        {
            IPv46_Address_t xIPv46_Address;
            BaseType_t xResult;
            uint32_t ulReturn = 0U;

            /* Looking up an IPv6 address in the DNS cache. */
            ( void ) memset( &xIPv46_Address, 0, sizeof xIPv46_Address );
            /* Let FreeRTOS_ProcessDNSCache only return IPv6 addresses. */
            xIPv46_Address.xIs_IPv6 = pdTRUE;
            xResult = FreeRTOS_ProcessDNSCache( pcHostName, &xIPv46_Address, 0, pdTRUE, NULL );

            if( xResult != pdFALSE )
            {
                ( void ) memcpy( pxAddress_IPv6->ucBytes, xIPv46_Address.xAddress_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                ulReturn = 1U;
            }

            return ulReturn;
        }
    #endif /* ( ipconfigUSE_DNS_CACHE == 1 ) && ( ipconfigUSE_IPv6 != 0 ) */
/*-----------------------------------------------------------*/

/**
 * @brief perform a dns update in the local cache
 * @param pcName the lookup name
 * @param pulIP the ip value to insert/replace
 * @param ulTTL Time To live (in seconds)
 * @return this is a dummy return, we are actually ignoring the return value
 *         from this function
 * @post the global structure \a xDNSCache might be modified
 */
    BaseType_t FreeRTOS_dns_update( const char * pcName,
                                    IPv46_Address_t * pxIP,
                                    uBaseType_t xLookUp,
                                    struct freertos_addrinfo ** ppxAddressInfo)
    {
        ( void ) FreeRTOS_ProcessDNSCache( pcName,
                                           pxIP,
                                           xLookUp,
                                           ppxAddressInfo );
        return pdTRUE;
    }

/**
 * @brief perform a dns clear in the local cache
 * @post the global structure \a xDNSCache is modified
 */
    void FreeRTOS_dnsclear( void )
    {
        ( void ) memset( xDNSCache, 0x0, sizeof( xDNSCache ) );
        uxFreeEntry = 0U;
    }

/**
 * @brief process a DNS Cache request (get, update, or insert)
 *
 * @param[in] pcName: the name of the host
 * @param[in,out] pxIP: when doing a lookup, will be set, when doing an update,
 *                       will be read.
 * @param[in] ulTTL: Time To Live (in seconds)
 * @param[in] xLookUp: pdTRUE if a look-up is expected, pdFALSE, when the DNS cache must
 *                     be updated.
 * @param[in,out] ppxAddressInfo: A pointer to a pointer where the find results
 *                                will be stored.
 * @return whether the operation was successful
 * @post the global structure \a xDNSCache might be modified
 */
    BaseType_t FreeRTOS_ProcessDNSCache( const char * pcName,
                                         IPv46_Address_t * pxIP,
                                         uint32_t ulTTL,
                                         BaseType_t xLookUp,
                                         struct freertos_addrinfo ** ppxAddressInfo )
    {
        UBaseType_t uxIndex;
        BaseType_t xResult;
        /* Get the current time in clock-ticks. */
        TickType_t xCurrentTickCount = xTaskGetTickCount();
        /* In milliseconds. */
        uint32_t ulCurrentTimeSeconds;

        configASSERT( ( pcName != NULL ) );

        if( xLookUp != pdFALSE )
        {
            pxIP->ulIPAddress = 0U;
        }

        ulCurrentTimeSeconds = ( xCurrentTickCount / portTICK_PERIOD_MS ) / 1000U;
        xResult = prvFindEntryIndex( pcName, &uxIndex );

        if( xResult == pdTRUE )
        { /* Element found */
            /* Is this function called for a lookup or to add/update an IP address? */
            if( xLookUp == pdTRUE )
            {
                /* This statement can only be reached when xResult is true; which
                 * implies that the entry is present and a 'get' operation will result
                 * in success. Therefore, it is safe to ignore the return value of the
                 * below function. */
                ( void ) prvGetCacheIPEntry( uxIndex,
                                             pxIP,
                                             ulCurrentTimeSeconds,
                                             ppxAddressInfo );
            }
            else
            {
                prvUpdateCacheEntry( uxIndex,
                                     ulTTL,
                                     pxIP,
                                     ulCurrentTimeSeconds );
            }
        }
        else /* Element not Found xResult = pdFALSE */
        {
            if( xLookUp == pdTRUE )
            {
                pxIP->ulIPAddress = 0U;
            }
            else
            {
                prvInsertCacheEntry( pcName,
                                     ulTTL,
                                     pxIP,
                                     ulCurrentTimeSeconds );
            }
        }

        if( ( xLookUp == pdFALSE ) || ( *pxIP != 0U ) ) /*TODO check */
        {
            FreeRTOS_debug_printf( ( "FreeRTOS_ProcessDNSCache: %s: '%s' @ %xip (TTL %u)\n",
                                     ( xLookUp != 0 ) ? "look-up" : "add",
                                     pcName,
                                     ( unsigned ) FreeRTOS_ntohl( *pxlIP ),
                                     ( unsigned ) FreeRTOS_ntohl( ulTTL ) ) );
        }

        return xResult;
    }

/**
 * @brief returns the index of the hostname entry in the dns cache.
 * @param[in] pcName find it in the cache
 * @param[in] pxIP ip address
 * @param [out] xResult index number
 * @returns res pdTRUE if index in found else pdFALSE
 */
    static UBaseType_t prvFindEntryIndex( const char * pcName,
                                         IPv46_Address_t * pxIP,
                                         UBaseType_t * uxResult )
    {
        BaseType_t xReturn = pdFALSE;
        UBaseType_t uxIndex;

        /* For each entry in the DNS cache table. */
        for( uxIndex = 0; uxIndex < ipconfigDNS_CACHE_ENTRIES; uxIndex++ )
        {
            if( xDNSCache[ uxIndex ].pcName[ 0 ] == ( char ) 0 )
            { /* empty slot */
                continue;
            }

            if( strcmp( xDNSCache[ uxIndex ].pcName, pcName ) == 0 )
            { /* hostname found */
                #if ( ipconfigUSE_IPv6 != 0 )
                    /* IPv6 is enabled, See if the cache entry has the correct type. */
                    if( pxIP->xIs_IPv6 == xDNSCache[ x ].xAddresses[ 0 ].xIs_IPv6 )
                #endif /* ipconfigUSE_IPv6 != 0 */
                {
                    xReturn = pdTRUE;
                    *uxResult = uxIndex;
                    break;
                }
            }
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief get entry at \p index from the cache
 * @param[in]  uxIndex : index in the cache
 * @param[out] pxIP fill it with the result
 * @param[in]  ulCurrentTimeSeconds current time
 * @param[out] ppxAddressInfo Target to store the DNS entries.
 * @returns    \c pdTRUE if the value is valid \c pdFALSE otherwise
 * @post the global structure \a xDNSCache might be modified
 *
 */
    static BaseType_t prvGetCacheIPEntry( UBaseType_t uxIndex,
                                          IPv46_Address_t * pxIP,
                                          uint32_t ulCurrentTimeSeconds,
                                          struct freertos_addrinfo ** ppxAddressInfo )
    {
        BaseType_t isRead;
        uint32_t ulIPAddressIndex = 0;
        uint32_t ulAge = ulCurrentTimeSeconds - xDNSCache[ uxIndex ].ulTimeWhenAddedInSeconds;

        /* Confirm that the record is still fresh.
         * The field ulTTL was stored as network-endian. */
        if( ulAge < FreeRTOS_ntohl( xDNSCache[ uxIndex ].ulTTL ) )
        {
            #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
                uint8_t ucIndex;

                /* The ucCurrentIPAddress value increments without bound and will rollover, */
                /*  modulo it by the number of IP addresses to keep it in range.     */
                /*  Also perform a final modulo by the max number of IP addresses    */
                /*  per DNS cache entry to prevent out-of-bounds access in the event */
                /*  that ucNumIPAddresses has been corrupted.                        */

                ucIndex = xDNSCache[ uxIndex ].ucCurrentIPAddress % xDNSCache[ uxIndex ].ucNumIPAddresses;
                ucIndex = ucIndex % ( uint8_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
                ulIPAddressIndex = ucIndex;

                xDNSCache[ uxIndex ].ucCurrentIPAddress++;
            #endif /* if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 ) */

            ( void ) memcpy( pxIP, &( xDNSCache[ index ].xAddresses[ ulIPAddressIndex ] ), sizeof( *pxIP ) );
            isRead = pdTRUE;

            if( ppxAddressInfo != NULL )
            {
                /* Copy all entries from position 'index' to a linked struct addrinfo. */
                prvReadDNSCache( index, ppxAddressInfo );
            }
        }
        else
        {
            /* Age out the old cached record. */
            xDNSCache[ uxIndex ].pcName[ 0 ] = ( char ) 0;
            isRead = pdFALSE;
        }

        return isRead;
    }
/*-----------------------------------------------------------*/

/**
 * @brief update entry at \p index in the cache
 * @param[in] uxIndex : index in the cache
 * @param[in] ulTTL time to live (in seconds)
 * @param[in] pxIP ip to update the cache with
 * @param[in] ulCurrentTimeSeconds current time
 * @post the global structure \a xDNSCache is modified
 */
    static void prvUpdateCacheEntry( UBaseType_t uxIndex,
                                     uint32_t ulTTL,
                                     IPv46_Address_t * pxIP,
                                     uint32_t ulCurrentTimeSeconds )
    {
        uint32_t ulIPAddressIndex = 0;

        #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
            if( xDNSCache[ uxIndex ].ucNumIPAddresses <
                ( uint8_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY )
            {
                /* If more answers exist than there are IP address storage
                 * slots they will overwrite entry 0 */
                ulIPAddressIndex = xDNSCache[ uxIndex ].ucNumIPAddresses;
                xDNSCache[ uxIndex ].ucNumIPAddresses++;
            }
        #endif
        ( void ) memcpy( &( xDNSCache[ index ].xAddresses[ ulIPAddressIndex ] ), pxIP, sizeof( *pxIP ) );
        xDNSCache[ uxIndex ].ulTTL = ulTTL;
        xDNSCache[ uxIndex ].ulTimeWhenAddedInSeconds = ulCurrentTimeSeconds;
    }
/*-----------------------------------------------------------*/

/**
 * @brief insert entry in the cache
 * @param[in] pcName cache entry key
 * @param[in] ulTTL time to live (in seconds)
 * @param[in] pxIP ip address
 * @param[in] ulCurrentTimeSeconds current time
 * @post the global structure \a xDNSCache is modified
 */
    static void prvInsertCacheEntry( const char * pcName,
                                     uint32_t ulTTL,
                                     IPv46_Address_t * pxIP,
                                     uint32_t ulCurrentTimeSeconds )
    {
        /* Add or update the item. */
        if( strlen( pcName ) < ( size_t ) ipconfigDNS_CACHE_NAME_LENGTH )
        {
            ( void ) strcpy( xDNSCache[ uxFreeEntry ].pcName, pcName );
            ( void ) memcpy( &( xDNSCache[ uxFreeEntry ].xAddresses[ 0 ] ), pxIP, sizeof( *pxIP ) );


            xDNSCache[ uxFreeEntry ].ulTTL = ulTTL;
            xDNSCache[ uxFreeEntry ].ulTimeWhenAddedInSeconds = ulCurrentTimeSeconds;
            #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
                xDNSCache[ uxFreeEntry ].ucNumIPAddresses = 1;
                xDNSCache[ uxFreeEntry ].ucCurrentIPAddress = 0;

                /* Initialize all remaining IP addresses in this entry to 0 */
                ( void ) memset( &xDNSCache[ uxFreeEntry ].xAddresses[ 1 ],
                                 0,
                                 sizeof( xDNSCache[ uxFreeEntry ].xAddresses[ 1 ] ) *
                                 ( ( uint32_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY - 1U ) );
            #endif
            uxFreeEntry++;

            if( uxFreeEntry == ipconfigDNS_CACHE_ENTRIES )
            {
                uxFreeEntry = 0;
            }
        }
    }
/*-----------------------------------------------------------*/

    #if ( ipconfigUSE_DNS_CACHE == 1 )

/**
 * @brief Copy DNS cache entries at xIndex to a linked struct addrinfo.
 * @param[in] xIndex: The index from where entries must be copied.
 * @param[out] ppxAddressInfo: Target to store the DNS entries.
 */
        static void prvReadDNSCache( BaseType_t xIndex,
                                     struct freertos_addrinfo ** ppxAddressInfo )
        {
            size_t uxIPAddressIndex;
            size_t uxNumIPAddresses = 1U;
            IPv46_Address_t * pxAddresses;
            struct freertos_addrinfo * pxNewAddress;
            struct freertos_addrinfo * pxLastAddress;
            struct freertos_addrinfo ** ppxLastAddress = &( pxLastAddress );

            #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
                uxNumIPAddresses = ( size_t ) xDNSCache[ xIndex ].ucNumIPAddresses;

                if( uxNumIPAddresses > ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY )
                {
                    /* Make this a configASSERT()? */
                    uxNumIPAddresses = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
                }
            #endif /* ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 ) */

            for( uxIPAddressIndex = 0; uxIPAddressIndex < uxNumIPAddresses; uxIPAddressIndex++ )
            {
                pxAddresses = &( xDNSCache[ xIndex ].xAddresses[ uxIPAddressIndex ] );

                #if ( ipconfigUSE_IPv6 != 0 )
                    if( pxAddresses->xIs_IPv6 != pdFALSE )
                    {
                        pxNewAddress = pxNew_AddrInfo( xDNSCache[ xIndex ].pcName, FREERTOS_AF_INET6, pxAddresses->xAddress_IPv6.ucBytes );
                    }
                    else
                #endif /* ( ipconfigUSE_IPv6 != 0 ) */
                {
                    uint8_t * ucBytes = ( uint8_t * ) &( pxAddresses->ulIPAddress );

                    pxNewAddress = pxNew_AddrInfo( xDNSCache[ xIndex ].pcName, FREERTOS_AF_INET4, ucBytes );
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
                        *( ppxLastAddress ) = pxNewAddress;
                    }

                    ppxLastAddress = &( pxNewAddress->ai_next );
                }
            }
        }
    #endif /* #if( ipconfigUSE_DNS_CACHE == 1 ) */
/*-----------------------------------------------------------*/

    #if ( ipconfigUSE_DNS_CACHE == 1 )
        uint32_t Prepare_CacheLookup( const char * pcHostName,
                                      BaseType_t xFamily,
                                      struct freertos_addrinfo ** ppxAddressInfo )
        {
            uint32_t ulIPAddress = 0U;

            if( xFamily == FREERTOS_AF_INET6 )
            {
                IPv46_Address_t xIPv46_Address;
                BaseType_t xFound;

                xIPv46_Address.xIs_IPv6 = pdTRUE;
                xFound = FreeRTOS_ProcessDNSCache( pcHostName, &( xIPv46_Address ), 0, pdTRUE, ppxAddressInfo );

                if( xFound != 0 )
                {
                    if( ( ppxAddressInfo != NULL ) && ( *( ppxAddressInfo ) != NULL ) )
                    {
                        struct freertos_sockaddr6 * sockaddr6 = ( ( sockaddr6_t * ) ( *( ppxAddressInfo ) )->ai_addr );

                        ( void ) sockaddr6;

                        /* This function returns either a valid IPv4 address, or
                         * in case of an IPv6 lookup, it will return a non-zero */
                        ulIPAddress = 1U;
                    }
                }
                else
                {
                    /* prvGetHostByName will be called to start a DNS lookup. */
                }
            }
            else
            {
                IPv46_Address_t xIPv46_Address;
                BaseType_t xFound;

                #if ( ipconfigUSE_IPv6 != 0 )
                    xIPv46_Address.xIs_IPv6 = pdFALSE;
                #endif /* ( ipconfigUSE_IPv6 != 0 ) */
                xFound = FreeRTOS_ProcessDNSCache( pcHostName, &( xIPv46_Address ), 0, pdTRUE, ppxAddressInfo );

                if( xFound != 0 )
                {
                    if( ( ppxAddressInfo != NULL ) && ( *( ppxAddressInfo ) != NULL ) )
                    {
                        struct freertos_sockaddr * sockaddr = ( *( ppxAddressInfo ) )->ai_addr;

                        ulIPAddress = sockaddr->sin_addr;
                    }
                }
                else
                {
                    /* prvGetHostByName will be called to start a DNS lookup. */
                }
            }

            return ulIPAddress;
        }
    #endif /* ( ipconfigUSE_DNS_CACHE == 1 ) */
/*-----------------------------------------------------------*/


#endif /* if ( ( ipconfigUSE_DNS != 0 ) && ( ipconfigUSE_DNS_CACHE == 1 ) ) */
