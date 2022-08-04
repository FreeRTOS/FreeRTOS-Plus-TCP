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
 * @file FreeRTOS_DNS_Cache.c
 * @brief File that handles the DNS caching option
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "FreeRTOS_DNS_Cache.h"
#include "FreeRTOS_DNS_Globals.h"

#if ( ipconfigUSE_DNS != 0 )

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
    static BaseType_t uxFreeDNSEntry = 0;

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
        #if ( ipconfigUSE_DNS_CACHE == 1 )
            /* Also the fields 'xIs_IPv6' and 'ulIPAddress' have been cleared. */
            ( void ) FreeRTOS_ProcessDNSCache( pcHostName, &( xIPv46_Address ), 0, pdTRUE, NULL );
        #endif /* ipconfigUSE_DNS_CACHE == 1 */

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
 * @brief perform a dns clear in the local cache
 * @post the global structure \a xDNSCache is modified
 */
    void FreeRTOS_dnsclear( void )
    {
        ( void ) memset( xDNSCache, 0x0, sizeof( xDNSCache ) );
        uxFreeDNSEntry = 0;
    }
/*-----------------------------------------------------------*/

    #if ( ipconfigUSE_DNS_CACHE == 1 )

/**
 * @brief Send a DNS message to be used in NBNS or LLMNR
 *
 * @param[in] pcName: the name of the host
 * @param[in,out] pxIP: when doing a lookup, will be set, when doing an update,
 *                      will be read.
 * @param[in] ulTTL: Time To Live
 * @param[in] xLookUp: pdTRUE if a look-up is expected, pdFALSE, when the DNS cache must
 *                     be updated.
 * @param[in,out] ppxAddressInfo: A pointer to a pointer where the find results
 *                                will be stored.
 *
 * @return
 */
        BaseType_t FreeRTOS_ProcessDNSCache( const char * pcName,
                                             IPv46_Address_t * pxIP,
                                             uint32_t ulTTL,
                                             BaseType_t xLookUp,
                                             struct freertos_addrinfo ** ppxAddressInfo )
        {
            BaseType_t x;
            uint32_t ulCurrentTimeSeconds;
            uint32_t ulIPAddressIndex = 0;

            /* Get the current time in clock-ticks. */
            ulCurrentTimeSeconds = ( uint32_t ) xTaskGetTickCount();
            /* In milliseconds. */
            ulCurrentTimeSeconds /= portTICK_PERIOD_MS;
            /* In seconds. */
            ulCurrentTimeSeconds /= 1000U;

            configASSERT( ( pcName != NULL ) );

            if( xLookUp != pdFALSE )
            {
                pxIP->ulIPAddress = 0U;
            }

            x = prvFindEntryIndex( pcName, pxIP );

            if( x != -1 )
            { /* Element found */
                /* Is this function called for a lookup or to add/update an IP address? */
                if( xLookUp == pdTRUE )
                {
                    ( void ) prvGetCacheIPEntry( x,
                                                 pxIP,
                                                 ulCurrentTimeSeconds,
                                                 ppxAddressInfo );
                }
                else
                {
                    prvUpdateCacheEntry( x,
                                         ulTTL,
                                         pxIP,
                                         ulCurrentTimeSeconds );
                }
            } /* if( xFound != pdTRUE ) */
            else
            { /* Element not Found */
                prvInsertCacheEntry( pcName,
                                     ulTTL,
                                     pxIP,
                                     ulCurrentTimeSeconds );
            }

            if( x == -1 )
            {
                x = 0;
            }
            else
            {
                x = 1;
            }

            return x;
        }

    #endif /* ipconfigUSE_DNS_CACHE */

/*-----------------------------------------------------------*/

/**
 * @brief returns the index of the hostname entry in the dns cache.
 * @param[in] pcName find it in the cache
 * @param[in] pxIP ip address
 * @returns index number or -1 if not found
 */
    static BaseType_t prvFindEntryIndex( const char * pcName,
                                         IPv46_Address_t * pxIP )
    {
        BaseType_t index = -1;
        BaseType_t x;

        ( void ) pxIP;

        /* Look for a matching entry: same name and same IP-type. */
        for( x = 0; x < ( BaseType_t ) ipconfigDNS_CACHE_ENTRIES; x++ )
        {
            if( ( xDNSCache[ x ].pcName[ 0 ] != ( char ) 0 ) &&
                #if ( ipconfigUSE_IPv6 != 0 )
                    /* IPv6 is enabled, See if the cache entry has the correct type. */
                    ( pxIP->xIs_IPv6 == xDNSCache[ x ].xAddresses[ 0 ].xIs_IPv6 ) &&
                #endif /* ipconfigUSE_IPv6 != 0 */
                ( strcmp( xDNSCache[ x ].pcName, pcName ) == 0 ) )
            {
                index = x;
                break;
            }
        } /* for( x = 0; x < ( BaseType_t ) ipconfigDNS_CACHE_ENTRIES; x++ ) */

        return index;
    }
/*-----------------------------------------------------------*/

/**
 * @brief get entry at \p index from the cache
 * @param[in]  index in the cache
 * @param[out] pxIP fill it with the result
 * @param[in]  ulCurrentTimeSeconds current time
 * @param[out] ppxAddressInfo Target to store the DNS entries.
 * @returns    \c pdTRUE if the value is valid \c pdFALSE otherwise
 * @post the global structure \a xDNSCache might be modified
 *
 */
    static BaseType_t prvGetCacheIPEntry( BaseType_t index,
                                          IPv46_Address_t * pxIP,
                                          uint32_t ulCurrentTimeSeconds,
                                          struct freertos_addrinfo ** ppxAddressInfo )
    {
        BaseType_t isRead = pdFALSE;
        uint32_t ulIPAddressIndex = 0;
        uint32_t ulAge = ulCurrentTimeSeconds - xDNSCache[ index ].ulTimeWhenAddedInSeconds;

        /* Confirm that the record is still fresh.
         * The field ulTTL was stored as network-endian. */
        if( ulAge < FreeRTOS_ntohl( xDNSCache[ index ].ulTTL ) )
        {
            #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
                uint8_t ucIndex;

                /* The ucCurrentIPAddress value increments without bound and will rollover, */
                /*  modulo it by the number of IP addresses to keep it in range.     */
                /*  Also perform a final modulo by the max number of IP addresses    */
                /*  per DNS cache entry to prevent out-of-bounds access in the event */
                /*  that ucNumIPAddresses has been corrupted.                        */

                ucIndex = xDNSCache[ index ].ucCurrentIPAddress % xDNSCache[ index ].ucNumIPAddresses;
                ucIndex = ucIndex % ( uint8_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
                ulIPAddressIndex = ucIndex;

                xDNSCache[ index ].ucCurrentIPAddress++;
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
            xDNSCache[ index ].pcName[ 0 ] = ( char ) 0;
        }

        return isRead;
    }
/*-----------------------------------------------------------*/

/**
 * @brief update entry at \p index in the cache
 * @param[in]  index index in the cache
 * @param[in]  ulTTL time to live
 * @param[in]  pxIP ip to update the cache with
 * @param[in]  ulCurrentTimeSeconds current time
 * @post the global structure \a xDNSCache is modified
 */
    static void prvUpdateCacheEntry( BaseType_t index,
                                     uint32_t ulTTL,
                                     IPv46_Address_t * pxIP,
                                     uint32_t ulCurrentTimeSeconds )
    {
        uint32_t ulIPAddressIndex = 0;

        #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
            if( xDNSCache[ index ].ucNumIPAddresses <
                ( uint8_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY )
            {
                /* If more answers exist than there are IP address storage
                 * slots they will overwrite entry 0 */
                ulIPAddressIndex = xDNSCache[ index ].ucNumIPAddresses;
                xDNSCache[ index ].ucNumIPAddresses++;
            }
        #endif
        ( void ) memcpy( &( xDNSCache[ index ].xAddresses[ ulIPAddressIndex ] ), pxIP, sizeof( *pxIP ) );
        xDNSCache[ index ].ulTTL = ulTTL;
        xDNSCache[ index ].ulTimeWhenAddedInSeconds = ulCurrentTimeSeconds;
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
            ( void ) strcpy( xDNSCache[ uxFreeDNSEntry ].pcName, pcName );
            ( void ) memcpy( &( xDNSCache[ uxFreeDNSEntry ].xAddresses[ 0 ] ), pxIP, sizeof( *pxIP ) );

            xDNSCache[ uxFreeDNSEntry ].ulTTL = ulTTL;
            xDNSCache[ uxFreeDNSEntry ].ulTimeWhenAddedInSeconds = ulCurrentTimeSeconds;
            #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
                xDNSCache[ uxFreeDNSEntry ].ucNumIPAddresses = 1;
                xDNSCache[ uxFreeDNSEntry ].ucCurrentIPAddress = 0;

                /* Initialize all remaining IP addresses in this entry to 0 */
                ( void ) memset( &xDNSCache[ uxFreeDNSEntry ].xAddresses[ 1 ],
                                 0,
                                 sizeof( xDNSCache[ uxFreeDNSEntry ].xAddresses[ 1 ] ) *
                                 ( ( uint32_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY - 1U ) );
            #endif
            uxFreeDNSEntry++;

            if( uxFreeDNSEntry >= ipconfigDNS_CACHE_ENTRIES )
            {
                uxFreeDNSEntry = 0;
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

/**
 * @brief Store an IP-address in the DNS cache, and issue some logging.
 * @param[in] pxSet: a set of variables that are shared among the helper functions.
 * @param[out] pxIP_Address: The address found will be copied to 'pxIP_Address'.
 * @param[in] ulTTL: The Time To Live value, used for cleaning the cache.
 */
        void ParseDNS_StoreToCache( ParseSet_t * pxSet,
                                    IPv46_Address_t * pxIP_Address,
                                    uint32_t ulTTL )
        {
            /* The reply will only be stored in the DNS cache when the
             * request was issued by this device. */
            if( pxSet->xDoStore != pdFALSE )
            {
                ( void ) FreeRTOS_ProcessDNSCache( pxSet->pcName, pxIP_Address, ulTTL, pdFALSE, NULL );
                pxSet->usNumARecordsStored++; /* Track # of A records stored */
            }

            #if ( ipconfigUSE_IPv6 != 0 )
                if( pxSet->usType == ( uint16_t ) dnsTYPE_AAAA_HOST )
                {
                    char cBuffer[ 40 ];

                    ( void ) FreeRTOS_inet_ntop( FREERTOS_AF_INET6, ( const void * ) pxIP_Address->xAddress_IPv6.ucBytes, cBuffer, sizeof( cBuffer ) );
                    FreeRTOS_printf( ( "DNS[0x%04X]: The answer to '%s' (%s) will%s been stored\n",
                                       ( unsigned ) pxSet->pxDNSMessageHeader->usIdentifier,
                                       pxSet->pcName,
                                       cBuffer,
                                       ( pxSet->xDoStore != 0 ) ? "" : " NOT" ) );
                }
                else
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */
            {
                char cBuffer[ 16 ];

                ( void ) FreeRTOS_inet_ntop( FREERTOS_AF_INET, ( const void * ) &( pxSet->ulIPAddress ), cBuffer, sizeof( cBuffer ) );
                /* Show what has happened. */
                FreeRTOS_printf( ( "DNS[0x%04X]: The answer to '%s' (%s) will%s be stored\n",
                                   pxSet->pxDNSMessageHeader->usIdentifier,
                                   pxSet->pcName,
                                   cBuffer,
                                   ( pxSet->xDoStore != 0 ) ? "" : " NOT" ) );
            }
        }
    #endif /* ( ipconfigUSE_DNS_CACHE == 1 ) */
/*-----------------------------------------------------------*/

    #if ( ipconfigUSE_DNS_CACHE == 1 )
        uint32_t Prepare_CacheLookup( const char * pcHostName,
                                      BaseType_t xFamily,
                                      struct freertos_addrinfo ** ppxAddressInfo )
        {
            uint32_t ulIPAddress = 0U;

            #if ( ipconfigUSE_IPv6 != 0 )
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
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */
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

#endif /* if ( ipconfigUSE_DNS != 0 ) */
