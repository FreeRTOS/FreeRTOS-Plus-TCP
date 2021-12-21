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

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "DNS/DNS_Cache.h"
#include "DNS/DNS_Globals.h"

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#if ( ipconfigUSE_DNS != 0 )


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

    #define dnsNAME_IS_OFFSET    ( ( uint8_t ) 0xc0 )

    static DNSCacheRow_t xDNSCache[ ipconfigDNS_CACHE_ENTRIES ] = { 0x0 };
    static BaseType_t xFreeEntry = 0;



    static BaseType_t prvFindEntryIndex( const char * pcName );

    static BaseType_t prvGetCacheIPEntry( BaseType_t index,
                                          uint32_t * pulIP,
                                          uint32_t ulCurrentTimeSeconds );

    static void prvUpdateCacheEntry( int index,
                                     int ulTTL,
                                     int32_t * pulIP,
                                     uint32_t ulCurrentTimeSeconds );

    static void prvInsertCacheEntry( const char * pcName,
                                     int32_t ulTTL,
                                     int32_t * pulIP,
                                     uint32_t ulCurrentTimeSeconds );


    uint32_t FreeRTOS_dnslookup( const char * pcHostName )
    {
        uint32_t ulIPAddress = 0UL;

        #if ( ipconfigUSE_DNS_CACHE == 1 )
            ( void ) FreeRTOS_ProcessDNSCache( pcHostName,
                                               &ulIPAddress,
                                               0,
                                               pdTRUE );
        #endif
        return ulIPAddress;
    }

    BaseType_t FreeRTOS_dns_update( const char * pcName,
                                    uint32_t * pulIP,
                                    uint32_t ulTTL )
    {
        ( void ) FreeRTOS_ProcessDNSCache( pcName,
                                           pulIP,
                                           0,
                                           pdFALSE );
    }

    void FreeRTOS_dnsclear( void )
    {
        ( void ) memset( xDNSCache, 0x0, sizeof( xDNSCache ) );
        xFreeEntry = 0;
    }

/**
 * @brief Send a DNS message to be used in NBNS or LLMNR
 *
 * @param[in] pcName: the name of the host
 * @param[in,out] pulIP: when doing a lookup, will be set, when doing an update,
 *                       will be read.
 * @param[in] ulTTL: Time To Live
 * @param[in] xLookUp: pdTRUE if a look-up is expected, pdFALSE, when the DNS cache must
 *                     be updated.
 *
 * @return
 */
    BaseType_t FreeRTOS_ProcessDNSCache( const char * pcName,
                                         uint32_t * pulIP,
                                         uint32_t ulTTL,
                                         BaseType_t xLookUp )
    {
        BaseType_t x;
        BaseType_t xFound = pdFALSE;
        TickType_t xCurrentTickCount = xTaskGetTickCount();
        uint32_t ulCurrentTimeSeconds;
        uint32_t ulIPAddressIndex = 0;

        configASSERT( ( pcName != NULL ) );

        ulCurrentTimeSeconds = ( xCurrentTickCount / portTICK_PERIOD_MS ) / 1000UL;
        x = prvFindEntryIndex( pcName );

        if( x != -1 )
        {   /* Element found */
            if( xLookUp == pdTRUE )
            {
                prvGetCacheIPEntry( x,
                                    pulIP,
                                    ulCurrentTimeSeconds );
            }
            else
            {
                prvUpdateCacheEntry( x,
                                     ulTTL,
                                     pulIP,
                                     ulCurrentTimeSeconds );
            }
        }
        else /* Element not Found */
        {
            if( xLookUp == pdTRUE )
            {
                *pulIP = 0UL;
            }
            else
            {
                prvInsertCacheEntry( pcName,
                                     ulTTL,
                                     pulIP,
                                     ulCurrentTimeSeconds );
            }
        }

        if( ( xLookUp == pdFALSE ) || ( *pulIP != 0UL ) )
        {
            FreeRTOS_debug_printf( ( "prvProcessDNSCache: %s: '%s' @ %lxip\n", ( xLookUp != 0 ) ? "look-up" : "add", pcName, FreeRTOS_ntohl( *pulIP ) ) );
        }
        return !!( x + 1 );
    }

/**
 * @brief returns the index of the hostname entry in the dns cache.
 * @returns index number or -1 if not found
 */
    static BaseType_t prvFindEntryIndex( const char * pcName )
    {
        int index = -1;
        int x;

        /* For each entry in the DNS cache table. */
        for( x = 0; x < ipconfigDNS_CACHE_ENTRIES; x++ )
        {
            if( xDNSCache[ x ].pcName[ 0 ] == ( char ) 0 )
            { /* empty slot */
                continue;
            }

            if( strcmp( xDNSCache[ x ].pcName, pcName ) == 0 )
            { /* hostname found */
                index = x;
                break;
            }
        }

        return index;
    }

    static BaseType_t prvGetCacheIPEntry( BaseType_t index,
                                          uint32_t * pulIP,
                                          uint32_t ulCurrentTimeSeconds )
    {
        BaseType_t isRead;
        uint32_t ulIPAddressIndex = 0;

        /* Confirm that the record is still fresh. */
        if( ulCurrentTimeSeconds < ( xDNSCache[ index ].ulTimeWhenAddedInSeconds +
                                     FreeRTOS_ntohl( xDNSCache[ index ].ulTTL ) ) )
        {
            #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
                uint8_t ucIndex;

                /* The ucCurrentIPAddress value increments without bound and will rollover, */
                /*  modulo it by the number of IP addresses to keep it in range.     */
                /*  Also perform a final modulo by the max number of IP addresses    */
                /*  per DNS cache entry to prevent out-of-bounds access in the event */
                /*  that ucNumIPAddresses has been corrupted.                        */
                /*if( xDNSCache[ x ].ucNumIPAddresses == 0 ) */
                /* { */

                /* Trying lookup before cache is updated with the number of IP
                 * addressed? Maybe an accident. Break out of the loop. */
/*                                break; */
/*          } */

                ucIndex = xDNSCache[ index ].ucCurrentIPAddress % xDNSCache[ index ].ucNumIPAddresses;
                ucIndex = ucIndex % ( uint8_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
                ulIPAddressIndex = ucIndex;

                xDNSCache[ index ].ucCurrentIPAddress++;
            #endif /* if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 ) */

            *pulIP = xDNSCache[ index ].ulIPAddresses[ ulIPAddressIndex ];
            isRead = pdTRUE;
        }
        else
        {
            /* Age out the old cached record. */
            xDNSCache[ index ].pcName[ 0 ] = ( char ) 0;
            isRead = pdFALSE;
        }

        return isRead;
    }

    static void prvUpdateCacheEntry( int index,
                                     int ulTTL,
                                     int32_t * pulIP,
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
        xDNSCache[ index ].ulIPAddresses[ ulIPAddressIndex ] = *pulIP;
        xDNSCache[ index ].ulTTL = ulTTL;
        xDNSCache[ index ].ulTimeWhenAddedInSeconds = ulCurrentTimeSeconds;
    }

    static void prvInsertCacheEntry( const char * pcName,
                                     int32_t ulTTL,
                                     int32_t * pulIP,
                                     uint32_t ulCurrentTimeSeconds )
    {
        int ulIPAddressIndex = 0;

        /* Add or update the item. */
        if( strlen( pcName ) < ( size_t ) ipconfigDNS_CACHE_NAME_LENGTH )
        {
            ( void ) strcpy( xDNSCache[ xFreeEntry ].pcName, pcName );

            xDNSCache[ xFreeEntry ].ulIPAddresses[ 0 ] = *pulIP;
            xDNSCache[ xFreeEntry ].ulTTL = ulTTL;
            xDNSCache[ xFreeEntry ].ulTimeWhenAddedInSeconds = ulCurrentTimeSeconds;
            #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
                xDNSCache[ xFreeEntry ].ucNumIPAddresses = 1;
                xDNSCache[ xFreeEntry ].ucCurrentIPAddress = 0;

                /* Initialize all remaining IP addresses in this entry to 0 */
                ( void ) memset( &xDNSCache[ xFreeEntry ].ulIPAddresses[ 1 ],
                                 0,
                                 sizeof( xDNSCache[ xFreeEntry ].ulIPAddresses[ 1 ] ) *
                                 ( ( uint32_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY - 1U ) );
            #endif
            xFreeEntry++;

            if( xFreeEntry == ipconfigDNS_CACHE_ENTRIES )
            {
                xFreeEntry = 0;
            }
        }
    }
#endif /* if ( ipconfigUSE_DNS != 0 ) */
