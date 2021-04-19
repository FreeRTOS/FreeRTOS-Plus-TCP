#include "private/FreeRTOS_DNS_Cache.h"

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

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

static DNSCacheRow_t xDNSCache[ ipconfigDNS_CACHE_ENTRIES ];

uint32_t FreeRTOS_dnslookup( const char * pcHostName )
{
    uint32_t ulIPAddress = 0UL;
#if ( ipconfigUSE_DNS_CACHE == 1 )
    ( void ) FreeRTOS_ProcessDNSCache( pcHostName, &ulIPAddress, 0, pdTRUE );
#endif
    return ulIPAddress;
}

BaseType_t FreeRTOS_dns_update( const char * pcName,
                                uint32_t * pulIP,
                                uint32_t ulTTL)
{
    ( void ) FreeRTOS_ProcessDNSCache( pcName, pulIP, 0, pdFALSE );
}

void FreeRTOS_dnsclear( void )
{
    ( void ) memset( xDNSCache, 0x0, sizeof( xDNSCache ) );
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
    static BaseType_t xFreeEntry = 0;

    configASSERT( ( pcName != NULL ) );

    ulCurrentTimeSeconds = ( xCurrentTickCount / portTICK_PERIOD_MS ) / 1000UL;

    /* For each entry in the DNS cache table. */
    for( x = 0; x < ipconfigDNS_CACHE_ENTRIES; x++ )
    {
        if( xDNSCache[ x ].pcName[ 0 ] == ( char ) 0 )
        {
            continue;
        }

        if( strcmp( xDNSCache[ x ].pcName, pcName ) == 0 )
        {
            /* Is this function called for a lookup or to add/update an IP address? */
            if( xLookUp != pdFALSE )
            {
                /* Confirm that the record is still fresh. */
                if( ulCurrentTimeSeconds < ( xDNSCache[ x ].ulTimeWhenAddedInSeconds + FreeRTOS_ntohl( xDNSCache[ x ].ulTTL ) ) )
                {
                    #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
                        uint8_t ucIndex;

                        /* The ucCurrentIPAddress value increments without bound and will rollover, */
                        /*  modulo it by the number of IP addresses to keep it in range.     */
                        /*  Also perform a final modulo by the max number of IP addresses    */
                        /*  per DNS cache entry to prevent out-of-bounds access in the event */
                        /*  that ucNumIPAddresses has been corrupted.                        */
                        if( xDNSCache[ x ].ucNumIPAddresses == 0 )
                        {
                            /* Trying lookup before cache is updated with the number of IP
                                * addressed? Maybe an accident. Break out of the loop. */
                            break;
                        }

                        ucIndex = xDNSCache[ x ].ucCurrentIPAddress % xDNSCache[ x ].ucNumIPAddresses;
                        ucIndex = ucIndex % ( uint8_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
                        ulIPAddressIndex = ucIndex;

                        xDNSCache[ x ].ucCurrentIPAddress++;
                    #endif /* if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 ) */

                    *pulIP = xDNSCache[ x ].ulIPAddresses[ ulIPAddressIndex ];
                }
                else
                {
                    /* Age out the old cached record. */
                    xDNSCache[ x ].pcName[ 0 ] = ( char ) 0;
                }
            }
            else
            {
                #if ( ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY > 1 )
                    if( xDNSCache[ x ].ucNumIPAddresses < ( uint8_t ) ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY )
                    {
                        /* If more answers exist than there are IP address storage slots */
                        /* they will overwrite entry 0 */

                        ulIPAddressIndex = xDNSCache[ x ].ucNumIPAddresses;
                        xDNSCache[ x ].ucNumIPAddresses++;
                    }
                #endif
                xDNSCache[ x ].ulIPAddresses[ ulIPAddressIndex ] = *pulIP;
                xDNSCache[ x ].ulTTL = ulTTL;
                xDNSCache[ x ].ulTimeWhenAddedInSeconds = ulCurrentTimeSeconds;
            }

            xFound = pdTRUE;
            break;
        }
    }

    if( xFound == pdFALSE )
    {
        if( xLookUp != pdFALSE )
        {
            *pulIP = 0UL;
        }
        else
        {
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
    }

    if( ( xLookUp == 0 ) || ( *pulIP != 0UL ) )
    {
        FreeRTOS_debug_printf( ( "prvProcessDNSCache: %s: '%s' @ %lxip\n", ( xLookUp != 0 ) ? "look-up" : "add", pcName, FreeRTOS_ntohl( *pulIP ) ) );
    }

    return xFound;
}

/**
 * @brief Read the Name field out of a DNS response packet.
 *
 * @param[in] pucByte: Pointer to the DNS response.
 * @param[in] uxRemainingBytes: Length of the DNS response.
 * @param[out] pcName: The pointer in which the name in the DNS response will be returned.
 * @param[in] uxDestLen: Size of the pcName array.
 *
 * @return If a fully formed name was found, then return the number of bytes processed in pucByte.
 */
size_t prvReadNameField( const uint8_t * pucByte,
                                         size_t uxRemainingBytes,
                                         char * pcName,
                                         size_t uxDestLen )
        {
            size_t uxNameLen = 0U;
            size_t uxIndex = 0U;
            size_t uxSourceLen = uxRemainingBytes;

            /* uxCount gets the values from pucByte and counts down to 0.
             * No need to have a different type than that of pucByte */
            size_t uxCount;

            if( uxSourceLen == ( size_t ) 0U )
            {
                /* Return 0 value in case of error. */
                uxIndex = 0U;
            }

            /* Determine if the name is the fully coded name, or an offset to the name
             * elsewhere in the message. */
            else if( ( pucByte[ uxIndex ] & dnsNAME_IS_OFFSET ) == dnsNAME_IS_OFFSET )
            {
                /* Jump over the two byte offset. */
                if( uxSourceLen > sizeof( uint16_t ) )
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
                /* 'uxIndex' points to the full name. Walk over the string. */
                while( ( uxIndex < uxSourceLen ) && ( pucByte[ uxIndex ] != ( uint8_t ) 0x00U ) )
                {
                    /* If this is not the first time through the loop, then add a
                     * separator in the output. */
                    if( ( uxNameLen > 0U ) )
                    {
                        if( uxNameLen >= uxDestLen )
                        {
                            uxIndex = 0U;
                            /* coverity[break_stmt] : Break statement terminating the loop */
                            break;
                        }

                        pcName[ uxNameLen ] = '.';
                        uxNameLen++;
                    }

                    /* Process the first/next sub-string. */
                    uxCount = ( size_t ) pucByte[ uxIndex ];
                    uxIndex++;

                    if( ( uxIndex + uxCount ) > uxSourceLen )
                    {
                        uxIndex = 0U;
                        break;
                    }

                    while( uxCount-- != 0U )
                    {
                        if( uxNameLen >= uxDestLen )
                        {
                            uxIndex = 0U;
                            break;

                            /* break out of inner loop here
                             * break out of outer loop at the test uxNameLen >= uxDestLen. */
                        }

                        pcName[ uxNameLen ] = ( char ) pucByte[ uxIndex ];
                        uxNameLen++;
                        uxIndex++;
                    }
                }

                /* Confirm that a fully formed name was found. */
                if( uxIndex > 0U )
                {
                    /* Here, there is no need to check for pucByte[ uxindex ] == 0 because:
                     * When we break out of the above while loop, uxIndex is made 0 thereby
                     * failing above check. Whenever we exit the loop otherwise, either
                     * pucByte[ uxIndex ] == 0 (which makes the check here unnecessary) or
                     * uxIndex >= uxSourceLen (which makes sure that we do not go in the 'if'
                     * case).
                     */
                    if( ( uxNameLen < uxDestLen ) && ( uxIndex < uxSourceLen ) )
                    {
                        pcName[ uxNameLen ] = '\0';
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
