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
        uint32_t ulIPAddresses[ ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY ]; /*!< The IP address(es) of an ARP cache entry. */
        char pcName[ ipconfigDNS_CACHE_NAME_LENGTH ];                    /*!< The name of the host */
        uint32_t ulTTL;                                                  /*!< Time-to-Live (in seconds) from the DNS server. */
        uint32_t ulTimeWhenAddedInSeconds;                               /*!< time at which the entry was added */
        #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
            uint8_t ucNumIPAddresses;                                    /*!< number of ip addresses for the same entry */
            uint8_t ucCurrentIPAddress;                                  /*!< current ip address index */
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



    static BaseType_t prvFindEntryIndex( const char * pcName,
                                         UBaseType_t * uxResult );

    static BaseType_t prvGetCacheIPEntry( UBaseType_t uxIndex,
                                          uint32_t * pulIP,
                                          uint32_t ulCurrentTimeSeconds );

    static void prvUpdateCacheEntry( UBaseType_t uxIndex,
                                     uint32_t ulTTL,
                                     const uint32_t * pulIP,
                                     uint32_t ulCurrentTimeSeconds );

    static void prvInsertCacheEntry( const char * pcName,
                                     uint32_t ulTTL,
                                     const uint32_t * pulIP,
                                     uint32_t ulCurrentTimeSeconds );

/**
 * @brief perform a dns lookup in the local cache
 * @param pcHostName the lookup name
 * @return ulIPAddress with the value from the cache else returns a zero if the
 *         cache is not enabled or the lookup is not successful
 * @post the global structure \a xDNSCache might be modified
 */
    uint32_t FreeRTOS_dnslookup( const char * pcHostName )
    {
        uint32_t ulIPAddress = 0U;

        ( void ) FreeRTOS_ProcessDNSCache( pcHostName,
                                           &ulIPAddress,
                                           0,
                                           pdTRUE );

        return ulIPAddress;
    }

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
                                    uint32_t * pulIP,
                                    uint32_t ulTTL )
    {
        ( void ) FreeRTOS_ProcessDNSCache( pcName,
                                           pulIP,
                                           ulTTL,
                                           pdFALSE );
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
 * @param[in,out] pulIP: when doing a lookup, will be set, when doing an update,
 *                       will be read.
 * @param[in] ulTTL: Time To Live (in seconds)
 * @param[in] xLookUp: pdTRUE if a look-up is expected, pdFALSE, when the DNS cache must
 *                     be updated.
 * @return whether the operation was successful
 * @post the global structure \a xDNSCache might be modified
 */
    BaseType_t FreeRTOS_ProcessDNSCache( const char * pcName,
                                         uint32_t * pulIP,
                                         uint32_t ulTTL,
                                         BaseType_t xLookUp )
    {
        UBaseType_t uxIndex;
        BaseType_t xResult;
        TickType_t xCurrentTickCount = xTaskGetTickCount();
        uint32_t ulCurrentTimeSeconds;

        configASSERT( ( pcName != NULL ) );

        ulCurrentTimeSeconds = ( xCurrentTickCount / portTICK_PERIOD_MS ) / 1000U;
        xResult = prvFindEntryIndex( pcName, &uxIndex );

        if( xResult == pdTRUE )
        { /* Element found */
            if( xLookUp == pdTRUE )
            {
                /* This statement can only be reached when xResult is true; which
                 * implies that the entry is present and a 'get' operation will result
                 * in success. Therefore, it is safe to ignore the return value of the
                 * below function. */
                ( void ) prvGetCacheIPEntry( uxIndex,
                                             pulIP,
                                             ulCurrentTimeSeconds );
            }
            else
            {
                prvUpdateCacheEntry( uxIndex,
                                     ulTTL,
                                     pulIP,
                                     ulCurrentTimeSeconds );
            }
        }
        else /* Element not Found xResult = pdFALSE */
        {
            if( xLookUp == pdTRUE )
            {
                *pulIP = 0U;
            }
            else
            {
                prvInsertCacheEntry( pcName,
                                     ulTTL,
                                     pulIP,
                                     ulCurrentTimeSeconds );
            }
        }

        if( ( xLookUp == pdFALSE ) || ( *pulIP != 0U ) )
        {
            FreeRTOS_debug_printf( ( "FreeRTOS_ProcessDNSCache: %s: '%s' @ %xip (TTL %u)\n",
                                     ( xLookUp != 0 ) ? "look-up" : "add",
                                     pcName,
                                     ( unsigned ) FreeRTOS_ntohl( *pulIP ),
                                     ( unsigned ) FreeRTOS_ntohl( ulTTL ) ) );
        }

        return xResult;
    }

/**
 * @brief returns the index of the hostname entry in the dns cache.
 * @param[in] pcName find it in the cache
 * @param [out] xResult index number
 * @returns res pdTRUE if index in found else pdFALSE
 */
    static BaseType_t prvFindEntryIndex( const char * pcName,
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
                xReturn = pdTRUE;
                *uxResult = uxIndex;
                break;
            }
        }

        return xReturn;
    }

/**
 * @brief get entry at \p index from the cache
 * @param[in]  uxIndex : index in the cache
 * @param[out] pulIP fill it with the result
 * @param[in]  ulCurrentTimeSeconds current time
 * @returns    \c pdTRUE if the value is valid \c pdFALSE otherwise
 * @post the global structure \a xDNSCache might be modified
 *
 */
    static BaseType_t prvGetCacheIPEntry( UBaseType_t uxIndex,
                                          uint32_t * pulIP,
                                          uint32_t ulCurrentTimeSeconds )
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

            *pulIP = xDNSCache[ uxIndex ].ulIPAddresses[ ulIPAddressIndex ];
            isRead = pdTRUE;
        }
        else
        {
            /* Age out the old cached record. */
            xDNSCache[ uxIndex ].pcName[ 0 ] = ( char ) 0;
            isRead = pdFALSE;
        }

        return isRead;
    }

/**
 * @brief update entry at \p index in the cache
 * @param[in] uxIndex : index in the cache
 * @param[in] ulTTL time to live (in seconds)
 * @param[in] pulIP ip to update the cache with
 * @param[in] ulCurrentTimeSeconds current time
 * @post the global structure \a xDNSCache is modified
 *
 */
    static void prvUpdateCacheEntry( UBaseType_t uxIndex,
                                     uint32_t ulTTL,
                                     const uint32_t * pulIP,
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
        xDNSCache[ uxIndex ].ulIPAddresses[ ulIPAddressIndex ] = *pulIP;
        xDNSCache[ uxIndex ].ulTTL = ulTTL;
        xDNSCache[ uxIndex ].ulTimeWhenAddedInSeconds = ulCurrentTimeSeconds;
    }

/**
 * @brief insert entry in the cache
 * @param[in] pcName cache entry key
 * @param[in] ulTTL time to live (in seconds)
 * @param[in] pulIP ip address
 * @param[in] ulCurrentTimeSeconds current time
 * @post the global structure \a xDNSCache is modified
 */
    static void prvInsertCacheEntry( const char * pcName,
                                     uint32_t ulTTL,
                                     const uint32_t * pulIP,
                                     uint32_t ulCurrentTimeSeconds )
    {
        /* Add or update the item. */
        if( strlen( pcName ) < ( size_t ) ipconfigDNS_CACHE_NAME_LENGTH )
        {
            ( void ) strcpy( xDNSCache[ uxFreeEntry ].pcName, pcName );

            xDNSCache[ uxFreeEntry ].ulIPAddresses[ 0 ] = *pulIP;
            xDNSCache[ uxFreeEntry ].ulTTL = ulTTL;
            xDNSCache[ uxFreeEntry ].ulTimeWhenAddedInSeconds = ulCurrentTimeSeconds;
            #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
                xDNSCache[ uxFreeEntry ].ucNumIPAddresses = 1;
                xDNSCache[ uxFreeEntry ].ucCurrentIPAddress = 0;

                /* Initialize all remaining IP addresses in this entry to 0 */
                ( void ) memset( &xDNSCache[ uxFreeEntry ].ulIPAddresses[ 1 ],
                                 0,
                                 sizeof( xDNSCache[ uxFreeEntry ].ulIPAddresses[ 1 ] ) *
                                 ( ( uint32_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY - 1U ) );
            #endif
            uxFreeEntry++;

            if( uxFreeEntry == ipconfigDNS_CACHE_ENTRIES )
            {
                uxFreeEntry = 0;
            }
        }
    }

#endif /* if ( ( ipconfigUSE_DNS != 0 ) && ( ipconfigUSE_DNS_CACHE == 1 ) ) */
