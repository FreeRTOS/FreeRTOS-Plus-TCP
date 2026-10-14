/*
 * FreeRTOS+TCP
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

/**
 * @file FreeRTOS_ND.c
 * @brief Implements a few functions that handle Neighbour Discovery and other ICMPv6 messages.
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
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Routing.h"
#include "FreeRTOS_ND.h"
#include "FreeRTOS_IP_Timers.h"

#if ( ipconfigUSE_LLMNR == 1 )
    #include "FreeRTOS_DNS.h"
#endif /* ipconfigUSE_LLMNR */
#include "NetworkBufferManagement.h"


/* The entire module FreeRTOS_ND.c is skipped when IPv6 is not used. */
#if ( ipconfigUSE_IPv6 != 0 )

/* RFC Flags */
/** @brief Type of Neighbour Advertisement packets - ROUTER. */
    #define ndICMPv6_FLAG_ROUTER                 0x80000000U
/** @brief Type of Neighbour Advertisement packets - SOLICIT. */
    #define ndICMPv6_FLAG_SOLICITED              0x40000000U
/** @brief Type of Neighbour Advertisement packets - OVERRIDE. */
    #define ndICMPv6_FLAG_OVERRIDE               0x20000000U

/** @brief DELAY state duration, in vNDAgeCache() periods, not seconds. */
    #define ndDELAY_FIRST_PROBE_TIME_SECONDS     ( 5U )

/** @brief INCOMPLETE retry interval, in vNDAgeCache() periods. */
    #define ndINCOMPLETE_TIMEOUT                 ( 3U )

/** @brief Maximum number of ND re-lookup attempts before giving up. */
    #define ipconfigMAX_ND_RE_LOOKUP_ATTEMPTS    ( 3U )

/** @brief ucFlags bit indicating the neighbour is a router. */
    #define ndpFLAG_IS_ROUTER                    ( 0x01U )

/** @brief The hop limit an ND packet is sent and must be received with. */
    #define ndHOP_LIMIT                          ( 255U )

/** @brief Default lifetime (in age ticks) assigned to a fresh ND cache entry. */
    #ifndef ipconfigMAX_ND_AGE
        #define ipconfigMAX_ND_AGE    ( 150U )
    #endif

/** @brief A block time of 0 simply means "don't block". */
    #define ndDONT_BLOCK                                  ( ( TickType_t ) 0 )

/** @brief The character used to fill ICMP echo requests, and therefore also the
 *         character expected to fill ICMP echo replies.
 */
    #define ndECHO_DATA_FILL_BYTE                         'x'

/** @brief When ucAge becomes 3 or less, it is time for a new
 * neighbour solicitation.
 */
    #define ndMAX_CACHE_AGE_BEFORE_NEW_ND_SOLICITATION    ( 3U )

/** @brief All nodes on the local network segment: IP address. */
    const uint8_t pcLOCAL_ALL_NODES_MULTICAST_IP[ ipSIZE_OF_IPv6_ADDRESS ] = { 0xffU, 0x02U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x01U }; /* ff02::1 */
/** @brief All nodes on the local network segment: MAC address. */
    const uint8_t pcLOCAL_ALL_NODES_MULTICAST_MAC[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x33U, 0x33U, 0x00U, 0x00U, 0x00U, 0x01U };

/** @brief See if the MAC-address can be resolved because it is a multi-cast address. */
    static eResolutionLookupResult_t prvMACResolve( const IPv6_Address_t * pxAddressToLookup,
                                                    MACAddress_t * const pxMACAddress,
                                                    NetworkEndPoint_t ** ppxEndPoint );

/** @brief Lookup an MAC address in the ND cache from the IP address. */
    static eResolutionLookupResult_t prvNDCacheLookup( const IPv6_Address_t * pxAddressToLookup,
                                                       MACAddress_t * const pxMACAddress,
                                                       NetworkEndPoint_t ** ppxEndPoint );

    #if ( ipconfigHAS_PRINTF == 1 )
        static const char * pcMessageType( BaseType_t xType );
    #endif

/** @brief Find the first end-point of type IPv6. */
    static NetworkEndPoint_t * pxFindLocalEndpoint( void );

/* Two functions to facilitate debugging. */

    const char * pcNDStateName( eNDState_t eState );
    const char * pcNDActionName( eNaAction_t eState );

    static BaseType_t prvIsValidNa( const NaPacket_t * pxNa );

/** @brief See if an IPv6 address is one of the addresses of this device. */
    static BaseType_t prvIsOwnIPAddress( const IPv6_Address_t * pxIPAddress );

/** @brief See if an IPv6 address sits on a network this device is attached to. */
    static BaseType_t prvIsAddressOnLink( const IPv6_Address_t * pxIPAddress );

/** @brief Remember that a Neighbour Solicitation was sent for an address. */
    static void prvNDCacheRecordSolicitation( const IPv6_Address_t * pxIPAddress,
                                              NetworkEndPoint_t * pxEndPoint );

/** @brief Find a free slot in the NDP cache, or evacuate an old one. */
    static NDCacheRow_t * prvGetFreeNDPCacheEntry( void );

/**
 * @brief Update an existing NDP cache entry with a new MAC address and state.
 */
    static void vNDPCacheUpdate( IPv6_Address_t * pxTargetIP,
                                 MACAddress_t * pxTargetMAC,
                                 eNDState_t eState,
                                 BaseType_t xRouter,
                                 NetworkEndPoint_t * pxEndPoint );

/**
 * @brief Insert a brand-new entry into the NDP cache.
 */
    static void vNDPCacheInsert( IPv6_Address_t * pxTargetIP,
                                 MACAddress_t * pxTargetMAC,
                                 eNDState_t eState,
                                 NetworkEndPoint_t * pxEndPoint );

/**
 * @brief Update only the state of an entry, keeping its MAC-address.
 */
    static void vNDPCacheSetState( IPv6_Address_t * pxTargetIP,
                                   eNDState_t eState );

/* Search the NDP cache for an IP address. Documented at the definition. */
    NDCacheRow_t * pxNDPCacheLookup( const IPv6_Address_t * pxIPAddress );

/* Process an incoming packet of the type ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6. */

    static eNaAction_t prvProcessNA( const NetworkBufferDescriptor_t * pxDescriptor,
                                     NetworkEndPoint_t * pxEndPoint );

/**
 * @brief Logic core: Determines what to do with the cache based on RFC 4861.
 * It is called from prvProcessNA().
 */
    static eNaAction_t prvDetermineAction( const NaPacket_t * pxNa,
                                           const NDCacheRow_t * pxEntry );

/** @brief The ND cache.
**/
    static NDCacheRow_t xNDCache[ ipconfigND_CACHE_ENTRIES ];


/*-----------------------------------------------------------*/

/*
 *  ff02::1: All IPv6 devices
 *  ff02::2: All IPv6 routers
 *  ff02::5: All OSPFv3 routers
 *  ff02::a: All EIGRP (IPv6) routers
 */

/**
 * @brief Find the first end-point of type IPv6.
 *
 * @return The first IPv6 end-point found.
 */
    static NetworkEndPoint_t * pxFindLocalEndpoint( void )
    {
        NetworkEndPoint_t * pxEndPoint;

        for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
             pxEndPoint != NULL;
             pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
        {
            if( pxEndPoint->bits.bIPv6 == pdTRUE_UNSIGNED )
            {
                IPv6_Type_t eType = xIPv6_GetIPType( &( pxEndPoint->ipv6_settings.xIPAddress ) );

                if( eType == eIPv6_LinkLocal )
                {
                    break;
                }
            }
        }

        return pxEndPoint;
    }
/*-----------------------------------------------------------*/

/**
 * @brief See if the MAC-address can be resolved because it is a multi-cast address.
 *
 * @param[in] pxAddressToLookup The IP-address to look-up.
 * @param[out] pxMACAddress The resulting MAC-address is stored here.
 * @param[out] ppxEndPoint A pointer to an end-point pointer where the end-point will be stored.
 *
 * @return An enum, either eResolutionCacheHit or eResolutionCacheMiss.
 */
    static eResolutionLookupResult_t prvMACResolve( const IPv6_Address_t * pxAddressToLookup,
                                                    MACAddress_t * const pxMACAddress,
                                                    NetworkEndPoint_t ** ppxEndPoint )
    {
        eResolutionLookupResult_t eReturn = eResolutionCacheMiss;

        /* Mostly used multi-cast address is ff02::. */
        if( xIsIPv6AllowedMulticast( pxAddressToLookup ) != pdFALSE )
        {
            vSetMultiCastIPv6MacAddress( pxAddressToLookup, pxMACAddress );

            if( ppxEndPoint != NULL )
            {
                *ppxEndPoint = pxFindLocalEndpoint();

                if( *ppxEndPoint != NULL )
                {
                    eReturn = eResolutionCacheHit;
                }
                else
                {
                    /* No link-local endpoint configured, eResolutionCacheMiss */
                }
            }
        }
        else
        {
            /* Not a multicast IP address, eResolutionCacheMiss */
        }

        return eReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find the MAC-address of an IPv6 address.  It will first determine if is a multicast
 *        address, if not, it will check the ND cache.
 *
 * @param[in] pxIPAddress The IPv6 address to be looked up.
 * @param[out] pxMACAddress The MAC-address found.
 * @param[out] ppxEndPoint A pointer to a pointer to an end-point, where the end-point will be stored.
 *
 * @return An enum which says whether the address was found: eResolutionCacheHit or eResolutionCacheMiss.
 */
    eResolutionLookupResult_t eNDGetCacheEntry( IPv6_Address_t * pxIPAddress,
                                                MACAddress_t * const pxMACAddress,
                                                struct xNetworkEndPoint ** ppxEndPoint )
    {
        eResolutionLookupResult_t eReturn;
        NetworkEndPoint_t * pxEndPoint;

        /* Multi-cast addresses can be resolved immediately. */
        eReturn = prvMACResolve( pxIPAddress, pxMACAddress, ppxEndPoint );

        if( eReturn == eResolutionCacheMiss )
        {
            /* See if the IP-address has an entry in the cache. */
            eReturn = prvNDCacheLookup( pxIPAddress, pxMACAddress, ppxEndPoint );
        }

        if( eReturn == eResolutionCacheMiss )
        {
            FreeRTOS_printf( ( "eNDGetCacheEntry: lookup %pip miss\n", ( void * ) pxIPAddress->ucBytes ) );
        }

        if( eReturn == eResolutionCacheMiss )
        {
            IPv6_Type_t eIPType = xIPv6_GetIPType( pxIPAddress );

            pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( pxIPAddress );

            if( pxEndPoint != NULL )
            {
                if( ppxEndPoint != NULL )
                {
                    *( ppxEndPoint ) = pxEndPoint;
                }

                FreeRTOS_printf( ( "eNDGetCacheEntry: FindEndPointOnIP failed for %pip (endpoint %pip)\n",
                                   ( void * ) pxIPAddress->ucBytes,
                                   ( void * ) pxEndPoint->ipv6_settings.xIPAddress.ucBytes ) );
            }
            else
            {
                if( eIPType == eIPv6_LinkLocal )
                {
                    for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
                         pxEndPoint != NULL;
                         pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
                    {
                        IPv6_Type_t eMyType = xIPv6_GetIPType( &( pxEndPoint->ipv6_settings.xIPAddress ) );

                        if( eMyType == eIPType )
                        {
                            eReturn = prvNDCacheLookup( pxIPAddress, pxMACAddress, ppxEndPoint );
                            break;
                        }
                    }

                    FreeRTOS_printf( ( "eNDGetCacheEntry: LinkLocal %pip \"%s\"\n", ( void * ) pxIPAddress->ucBytes,
                                       ( eReturn == eResolutionCacheHit ) ? "hit" : "miss" ) );
                }
                else
                {
                    pxEndPoint = FreeRTOS_FindGateWay( ( BaseType_t ) ipTYPE_IPv6 );

                    if( pxEndPoint != NULL )
                    {
                        ( void ) memcpy( pxIPAddress->ucBytes, pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                        FreeRTOS_printf( ( "eNDGetCacheEntry: Using gw %pip\n", ( void * ) pxIPAddress->ucBytes ) );
                        FreeRTOS_printf( ( "eNDGetCacheEntry: From addr %pip\n", ( void * ) pxEndPoint->ipv6_settings.xIPAddress.ucBytes ) );

                        /* See if the gateway has an entry in the cache. */
                        eReturn = prvNDCacheLookup( pxIPAddress, pxMACAddress, ppxEndPoint );

                        if( ( ppxEndPoint != NULL ) && ( *ppxEndPoint != NULL ) )
                        {
                            FreeRTOS_printf( ( "eNDGetCacheEntry: found end-point %pip\n", ( void * ) ( *ppxEndPoint )->ipv6_settings.xIPAddress.ucBytes ) );
                        }

                        if( ppxEndPoint != NULL )
                        {
                            *( ppxEndPoint ) = pxEndPoint;
                        }
                    }
                }
            }
        }

        return eReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Age the NDP cache and handle state transitions/probes; every countdown
 *        here is in 'ipND_TIMER_PERIOD_MS' units, not seconds.
 */
    void vNDAgeCache( void )
    {
        BaseType_t x;

        for( x = 0; x < ( BaseType_t ) ipconfigND_CACHE_ENTRIES; x++ )
        {
            /* Only process entries that are currently in use. */
            if( xNDCache[ x ].ucState != ( uint8_t ) eND_FREE )
            {
                /* 1. Decrement the age counter. */
                if( xNDCache[ x ].ucAge > ( uint8_t ) 0U )
                {
                    xNDCache[ x ].ucAge--;
                }

                /* 2. Handle Logic based on the current state of the entry. */
                switch( xNDCache[ x ].ucState )
                {
                    case ( uint8_t ) eND_INCOMPLETE:

                        /* We are waiting for a resolution (NS sent, no NA received yet). */
                        if( xNDCache[ x ].ucAge == 0U )
                        {
                            if( xNDCache[ x ].ucNumProbes < ( uint8_t ) ipconfigMAX_ND_RE_LOOKUP_ATTEMPTS )
                            {
                                uint8_t ucAttempt = xNDCache[ x ].ucNumProbes + 1U;
                                size_t uxNeededSize;
                                NetworkBufferDescriptor_t * pxNetworkBuffer;

                                FreeRTOS_debug_printf( ( "NDP: vNDAgeCache: solicitation retry %u for %pip\n",
                                                         ucAttempt,
                                                         xNDCache[ x ].xIPAddress.ucBytes ) );

                                uxNeededSize = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t );
                                pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxNeededSize, 0U );

                                if( pxNetworkBuffer != NULL )
                                {
                                    pxNetworkBuffer->pxEndPoint = xNDCache[ x ].pxEndPoint;
                                    vNDSendNeighbourSolicitation( pxNetworkBuffer, &( xNDCache[ x ].xIPAddress ) );
                                }

                                /* Count the attempt even without a buffer, and set ucAge
                                 * after sending because sending resets it. */
                                xNDCache[ x ].ucNumProbes = ucAttempt;
                                xNDCache[ x ].ucAge = ( uint8_t ) 1U;
                            }
                            else
                            {
                                if( pxNDWaitingNetworkBuffer != NULL )
                                {
                                    const ICMPPacket_IPv6_t * pxIPPacket = ( const ICMPPacket_IPv6_t * ) pxNDWaitingNetworkBuffer->pucEthernetBuffer;

                                    /* A packet is parked on its SOURCE address, so compare
                                     * against that field. */
                                    if( memcmp( pxIPPacket->xIPHeader.xSourceAddress.ucBytes, xNDCache[ x ].xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) == 0 )
                                    {
                                        FreeRTOS_debug_printf( ( "NDP: vNDAgeCache: Resolution timeout. Dropping parked packet.\n" ) );
                                        vReleaseNetworkBufferAndDescriptor( pxNDWaitingNetworkBuffer );
                                        pxNDWaitingNetworkBuffer = NULL;

                                        /* Nothing is parked any more, so the resolution
                                         * timer has nothing left to expire. */
                                        vIPSetNDResolutionTimerEnableState( pdFALSE );
                                    }
                                }

                                /* Clear the entry. */
                                xNDCache[ x ].ucState = ( uint8_t ) eND_FREE;
                            }
                        }

                        break;

                    case ( uint8_t ) eND_REACHABLE:

                        /* The neighbor is known and reachability was recently confirmed. */
                        if( xNDCache[ x ].ucAge <= ( uint8_t ) ndMAX_CACHE_AGE_BEFORE_NEW_ND_SOLICITATION )
                        {
                            /* Reachability 'timer' has expired. Move to STALE.
                             * Traffic can still be sent, but NUD will be triggered on next use. */
                            iptraceND_TABLE_ENTRY_WILL_EXPIRE( xNDCache[ x ].xIPAddress );
                            xNDCache[ x ].ucState = ( uint8_t ) eND_STALE;

                            /* Give STALE its own lifetime; keeping the spent REACHABLE
                             * countdown would free the entry before NUD could run. */
                            xNDCache[ x ].ucAge = ( uint8_t ) ipconfigMAX_ND_AGE;
                        }

                        break;

                    case ( uint8_t ) eND_DELAY:

                        /* Traffic was sent to a STALE neighbor. We are waiting a short while
                         * for an upper-layer confirmation (like a TCP ACK). */
                        if( xNDCache[ x ].ucAge == 0U )
                        {
                            /* No confirmation received. Move to PROBE state to send Unicast NS. */
                            xNDCache[ x ].ucState = ( uint8_t ) eND_PROBE;
                            xNDCache[ x ].ucNumProbes = 0;
                            /* Probe on the next call of this function. */
                            xNDCache[ x ].ucAge = ( uint8_t ) 1U;
                        }

                        break;

                    case ( uint8_t ) eND_PROBE:

                        /* We are actively probing the neighbor with Unicast Neighbor Solicitations. */
                        if( xNDCache[ x ].ucAge == 0U )
                        {
                            if( xNDCache[ x ].ucNumProbes < ( uint8_t ) ipconfigMAX_ND_RE_LOOKUP_ATTEMPTS )
                            {
                                size_t uxNeededSize;
                                NetworkBufferDescriptor_t * pxNetworkBuffer;
                                FreeRTOS_debug_printf( ( "NDP: vNDAgeCache: NUD probe %u for %pip\n",
                                                         xNDCache[ x ].ucNumProbes + 1,
                                                         xNDCache[ x ].xIPAddress.ucBytes ) );

                                uxNeededSize = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t );
                                pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxNeededSize, 0U );

                                if( pxNetworkBuffer != NULL )
                                {
                                    pxNetworkBuffer->pxEndPoint = xNDCache[ x ].pxEndPoint;
                                    vNDSendNeighbourSolicitation( pxNetworkBuffer, &( xNDCache[ x ].xIPAddress ) );
                                }

                                xNDCache[ x ].ucNumProbes++;
                                /* Send the next probe on the next call of this function. */
                                xNDCache[ x ].ucAge = ( uint8_t ) 1U;
                            }
                            else
                            {
                                /* Max probes reached with no response. Neighbor is gone. */
                                xNDCache[ x ].ucState = ( uint8_t ) eND_FREE;
                            }
                        }

                        break;

                    case ( uint8_t ) eND_STALE:
                    default:

                        /* In STALE, the entry just sits there until the age hits 0.
                         * If no traffic triggers a move to DELAY, we eventually free it. */
                        if( xNDCache[ x ].ucAge == 0U )
                        {
                            xNDCache[ x ].ucState = ( uint8_t ) eND_FREE;
                        }

                        break;
                }

                /* 3. Final Cleanup: If the state was moved to FREE, wipe the IP. */
                if( xNDCache[ x ].ucState == ( uint8_t ) eND_FREE )
                {
                    iptraceND_TABLE_ENTRY_EXPIRED( xNDCache[ x ].xIPAddress );
                    ( void ) memset( xNDCache[ x ].xIPAddress.ucBytes, 0, ipSIZE_OF_IPv6_ADDRESS );
                }
            }
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find a free slot in the NDP cache, or evacuate an old one.
 *
 * @return Pointer to an available NDCacheRow_t, or NULL if none can be freed.
 */
    static NDCacheRow_t * prvGetFreeNDPCacheEntry( void )
    {
        BaseType_t x;
        NDCacheRow_t * pxReturn = NULL;

        /* First pass: Look for an empty slot. */
        for( x = 0; x < ( BaseType_t ) ipconfigND_CACHE_ENTRIES; x++ )
        {
            if( xNDCache[ x ].ucState == ( uint8_t ) eND_FREE )
            {
                pxReturn = &( xNDCache[ x ] );
                break;
            }
        }

        /* Second pass: evict by rank - STALE, then other bound states, then
         * INCOMPLETE, then a router, each only as a last resort. */
        if( pxReturn == NULL )
        {
            /* Rank 0 is most attractive; -1 means nothing chosen yet. */
            BaseType_t xBestRank = -1;
            uint16_t usBestAge = 0U;

            for( x = 0; x < ( BaseType_t ) ipconfigND_CACHE_ENTRIES; x++ )
            {
                BaseType_t xRank;
                uint16_t usAge = ( uint16_t ) xNDCache[ x ].ucAge;

                if( ( xNDCache[ x ].ucFlags & ndpFLAG_IS_ROUTER ) != 0U )
                {
                    xRank = 3;
                }
                else if( xNDCache[ x ].ucState == ( uint8_t ) eND_STALE )
                {
                    xRank = 0;
                }
                else if( xNDCache[ x ].ucState == ( uint8_t ) eND_INCOMPLETE )
                {
                    xRank = 2;
                }
                else
                {
                    xRank = 1;
                }

                if( ( xBestRank < 0 ) ||
                    ( xRank < xBestRank ) ||
                    ( ( xRank == xBestRank ) && ( usAge < usBestAge ) ) )
                {
                    xBestRank = xRank;
                    usBestAge = usAge;
                    pxReturn = &( xNDCache[ x ] );
                }
            }
        }

        /* Clean up the entry before returning it. */
        if( pxReturn != NULL ) /* LCOV_EXCL_BR_LINE - defensive, a full cache always yields a victim */
        {
            ( void ) memset( pxReturn, 0, sizeof( NDCacheRow_t ) );
            pxReturn->ucState = ( uint8_t ) eND_FREE;
        }

        return pxReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Update an existing NDP cache entry with a new MAC address and state.
 */
    static void vNDPCacheUpdate( IPv6_Address_t * pxTargetIP,
                                 MACAddress_t * pxTargetMAC,
                                 eNDState_t eState,
                                 BaseType_t xRouter,
                                 NetworkEndPoint_t * pxEndPoint )
    {
        NDCacheRow_t * pxEntry = pxNDPCacheLookup( pxTargetIP );

        if( pxEntry != NULL ) /* LCOV_EXCL_BR_LINE - defensive NULL check, entry always present here */
        {
            /* Update the L2 mapping. */
            ( void ) memcpy( pxEntry->xMACAddress.ucBytes, pxTargetMAC->ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );

            /* Update state and reset the life-cycle counters. */
            pxEntry->ucState = ( uint8_t ) eState;
            pxEntry->ucAge = ( uint8_t ) ipconfigMAX_ND_AGE;
            pxEntry->ucNumProbes = 0;

            if( pxEndPoint != NULL ) /* LCOV_EXCL_BR_LINE - defensive NULL check */
            {
                pxEntry->pxEndPoint = pxEndPoint;
            }

            /* Track if this neighbor is a router. */
            if( xRouter != pdFALSE )
            {
                pxEntry->ucFlags |= ndpFLAG_IS_ROUTER;
            }
            else
            {
                pxEntry->ucFlags &= ( uint8_t ) ~ndpFLAG_IS_ROUTER;
            }

            #if ipconfigIS_ENABLED( ipconfigHAS_DEBUG_PRINTF )
            {
                char pxMacBuffer[ 24 ];
                FreeRTOS_EUI48_ntop( pxTargetMAC->ucBytes, pxMacBuffer, 'a', '-' );
                FreeRTOS_debug_printf( ( "NDP: NDP Update: %pip at %s %s(%u)\n",
                                         pxTargetIP->ucBytes,
                                         pxMacBuffer,
                                         pcNDStateName( eState ),
                                         ( unsigned ) eState ) );
            }
            #endif
        }
        else
        {
            FreeRTOS_printf( ( "NDP: vNDPCacheUpdate: Entry %pip not found\n",
                               pxTargetIP->ucBytes ) );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Insert a brand-new entry into the NDP cache; only self-originated
 *        bindings come this way, so no router flag is taken.
 */
    static void vNDPCacheInsert( IPv6_Address_t * pxTargetIP,
                                 MACAddress_t * pxTargetMAC,
                                 eNDState_t eState,
                                 NetworkEndPoint_t * pxEndPoint )
    {
        /* prvGetFreeNDPCacheEntry handles the 'eviction' of old STALE entries if full. */
        NDCacheRow_t * pxEntry = prvGetFreeNDPCacheEntry();

        if( pxEntry != NULL ) /* LCOV_EXCL_BR_LINE - defensive, a full cache always yields a victim */
        {
            ( void ) memcpy( pxEntry->xIPAddress.ucBytes, pxTargetIP->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
            ( void ) memcpy( pxEntry->xMACAddress.ucBytes, pxTargetMAC->ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );

            pxEntry->ucState = ( uint8_t ) eState;
            pxEntry->ucAge = ( uint8_t ) ipconfigMAX_ND_AGE;
            pxEntry->ucNumProbes = 0;
            pxEntry->pxEndPoint = pxEndPoint;
            pxEntry->ucFlags = 0;

            #if ipconfigIS_ENABLED( ipconfigHAS_DEBUG_PRINTF )
            {
                char pcBuffer[ 24 ];
                FreeRTOS_EUI48_ntop( pxTargetMAC->ucBytes, pcBuffer, 'a', '-' );
                FreeRTOS_debug_printf( ( "NDP Insert: %pip added (MAC: %s)\n",
                                         pxTargetIP->ucBytes,
                                         pcBuffer ) );
            }
            #endif /* ipconfigIS_ENABLED( ipconfigHAS_DEBUG_PRINTF ) */
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Update only the state of an entry, leaving its MAC-address untouched.
 */
    static void vNDPCacheSetState( IPv6_Address_t * pxTargetIP,
                                   eNDState_t eState )
    {
        NDCacheRow_t * pxEntry = pxNDPCacheLookup( pxTargetIP );

        if( pxEntry != NULL ) /* LCOV_EXCL_BR_LINE - defensive NULL check, entry always present here */
        {
            const uint8_t ucWasVerifying = ( ( pxEntry->ucState == ( uint8_t ) eND_DELAY ) || ( pxEntry->ucState == ( uint8_t ) eND_PROBE ) ) ? 1U : 0U;

            pxEntry->ucState = ( uint8_t ) eState;

            switch( eState )
            {
                case eND_REACHABLE:
                    pxEntry->ucAge = ( uint8_t ) ipconfigMAX_ND_AGE;
                    pxEntry->ucNumProbes = 0;
                    break;

                case eND_PROBE:

                    /* Restarting a verification already under way would stop the
                     * probes ever running out, so the entry could never be freed. */
                    if( ucWasVerifying == 0U )
                    {
                        pxEntry->ucAge = ( uint8_t ) 1U;
                        pxEntry->ucNumProbes = 0;
                    }

                    break;

                case eND_STALE:
                default:

                    /* Restart the lifetime, so one advertisement cannot expire an
                     * entry that was about to be probed. */
                    pxEntry->ucAge = ( uint8_t ) ipconfigMAX_ND_AGE;
                    break;
            }

            FreeRTOS_debug_printf( ( "NDP: NDP State: %pip set to %s(%u)\n",
                                     pxTargetIP->ucBytes,
                                     pcNDStateName( eState ),
                                     ( unsigned ) eState ) );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief See if an IPv6 address is one of the addresses of this device.
 *
 * @param[in] pxIPAddress The address to look for.
 *
 * @return pdTRUE when an end-point owns this exact address.
 */
    static BaseType_t prvIsOwnIPAddress( const IPv6_Address_t * pxIPAddress )
    {
        /* Not const: FreeRTOS_NextEndPoint() takes a writable end-point. */
        NetworkEndPoint_t * pxEndPoint;
        BaseType_t xReturn = pdFALSE;

        for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
             pxEndPoint != NULL;
             pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
        {
            if( ( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED ) &&
                ( memcmp( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS ) == 0 ) )
            {
                xReturn = pdTRUE;
                break;
            }
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief See if an IPv6 address sits on a network this device is attached to.
 *
 * @param[in] pxIPAddress The address to test.
 *
 * @return pdTRUE when the address falls inside the prefix of an end-point.
 *
 * @note Prefixes are compared directly, and a zero-length one skipped, because
 *       both FreeRTOS_FindEndPointOnNetMask_IPv6() and a zero prefix match all.
 */
    static BaseType_t prvIsAddressOnLink( const IPv6_Address_t * pxIPAddress )
    {
        /* Not const: FreeRTOS_NextEndPoint() takes a writable end-point. */
        NetworkEndPoint_t * pxEndPoint;
        BaseType_t xReturn = pdFALSE;

        for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
             pxEndPoint != NULL;
             pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
        {
            if( ( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED ) &&
                ( pxEndPoint->ipv6_settings.uxPrefixLength > 0U ) &&
                ( xCompareIPv6_Address( &( pxEndPoint->ipv6_settings.xPrefix ),
                                        pxIPAddress,
                                        pxEndPoint->ipv6_settings.uxPrefixLength ) == 0 ) )
            {
                xReturn = pdTRUE;
                break;
            }
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Apply the RFC 4861 section 7.1.2 validity checks to a received NA.
 *
 * @param[in] pxNa The fields that were extracted from the packet.
 *
 * @return pdTRUE when the advertisement may be processed further.
 */
    static BaseType_t prvIsValidNa( const NaPacket_t * pxNa )
    {
        BaseType_t xReturn = pdFALSE;

        do
        {
            if( pxNa->ucCode != 0U )
            {
                break;
            }

            if( pxNa->xTargetIP.ucBytes[ 0 ] == 0xFFU )
            {
                break;
            }

            /* A multicast advertisement answers no solicitation of ours, so it may
             * not claim to be solicited and reach REACHABLE. */
            if( ( pxNa->xDestinationIsMulticast != pdFALSE ) && ( pxNa->xSolicited != pdFALSE ) )
            {
                break;
            }

            /* Our own address means a duplicate, which vReceiveNA() handles; it must
             * never become a cache entry. */
            if( prvIsOwnIPAddress( &( pxNa->xTargetIP ) ) != pdFALSE )
            {
                break;
            }

            /* If the Target Link-Layer Address (TLLA) is present, validate it. */
            if( pxNa->xHasTargetLLA != pdFALSE )
            {
                static const uint8_t ucZeroMac[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0, 0, 0, 0, 0, 0 };

                /* For Ethernet the option holds exactly one 8-byte unit. */
                if( pxNa->ucTargetLLALength != 1U )
                {
                    break;
                }

                /* MAC cannot be multicast (the I/G bit). */
                if( ( pxNa->xTargetMAC.ucBytes[ 0 ] & 0x01U ) != 0U )
                {
                    break;
                }

                /* MAC cannot be all zeros. */
                if( memcmp( pxNa->xTargetMAC.ucBytes, ucZeroMac, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
                {
                    break;
                }
            }

            xReturn = pdTRUE;
        } while( 0 );

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Record a sent Neighbour Solicitation as an INCOMPLETE entry, the only
 *        state prvDetermineAction() will learn an address into.
 *
 * @param[in] pxIPAddress The address that was solicited.
 * @param[in] pxEndPoint The end-point the solicitation was sent from.
 */
    static void prvNDCacheRecordSolicitation( const IPv6_Address_t * pxIPAddress,
                                              NetworkEndPoint_t * pxEndPoint )
    {
        NDCacheRow_t * pxEntry = pxNDPCacheLookup( pxIPAddress );

        if( pxEntry == NULL )
        {
            pxEntry = prvGetFreeNDPCacheEntry();

            if( pxEntry != NULL ) /* LCOV_EXCL_BR_LINE - defensive, a full cache always yields a victim */
            {
                ( void ) memcpy( pxEntry->xIPAddress.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                pxEntry->ucState = ( uint8_t ) eND_INCOMPLETE;
                pxEntry->ucAge = ( uint8_t ) ndINCOMPLETE_TIMEOUT;
                pxEntry->pxEndPoint = pxEndPoint;

                FreeRTOS_debug_printf( ( "NDP: Solicited %pip, awaiting an advertisement\n",
                                         pxIPAddress->ucBytes ) );
            }
        }
        else if( pxEntry->ucState == ( uint8_t ) eND_INCOMPLETE )
        {
            pxEntry->ucAge = ( uint8_t ) ndINCOMPLETE_TIMEOUT;
        }
        else
        {
            /* A NUD probe for a bound entry, whose state must not be disturbed. */
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Search the NDP cache for an IP address.
 *
 * @param[in] pxIPAddress: The IPv6 address to look up.
 *
 * @return Pointer to the cache row if found and valid; NULL otherwise.
 *
 * @note Side-effect free, so safe on the receive path; prvNDCacheLookup() makes
 *       the transition that RFC 4861 ties to sending.
 */
    NDCacheRow_t * pxNDPCacheLookup( const IPv6_Address_t * pxIPAddress )
    {
        BaseType_t x;
        NDCacheRow_t * pxReturn = NULL;

        for( x = 0; x < ( BaseType_t ) ipconfigND_CACHE_ENTRIES; x++ )
        {
            /* Match if the entry is not free and the IP address matches. */
            if( ( xNDCache[ x ].ucState != ( uint8_t ) eND_FREE ) &&
                ( memcmp( xNDCache[ x ].xIPAddress.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS ) == 0 ) )
            {
                pxReturn = &( xNDCache[ x ] );
                break;
            }
        }

        return pxReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Main function to process incoming Neighbor Advertisement.
 *
 * @param[in] pxDescriptor The buffer holding the advertisement.
 * @param[in] pxEndPoint The end-point the advertisement arrived on.
 *
 * @return The action that was carried out on the cache.
 *
 * @pre ETH + IPv6 header + usPayloadLength is at most xDataLength, which
 *      xCheckIPv6SizeFields() and the checksum path enforce before this call.
 */
    static eNaAction_t prvProcessNA( const NetworkBufferDescriptor_t * pxDescriptor,
                                     NetworkEndPoint_t * pxEndPoint )
    {
        NaPacket_t xNaPacket;
        const ICMPPacket_IPv6_t * pxICMPPacket;
        const ICMPHeader_IPv6_t * pxICMPHeader_IPv6;
        uint32_t ulReserved;
        NDCacheRow_t * pxExistingEntry = NULL;
        eNaAction_t xAction = eNA_DROP;
        BaseType_t xFoundError = pdFALSE;
        const uint8_t * pucOptions;
        uint16_t usICMPSize;
        size_t uxICMPSize;
        size_t uxRemaining;

        do
        {
            if( ( pxDescriptor == NULL ) || ( pxDescriptor->pucEthernetBuffer == NULL ) ) /* LCOV_EXCL_BR_LINE - caller guarantees non-NULL */
            {
                break;
            }

            /* Map pointers to the packet buffer */
            pxICMPPacket = ( ICMPPacket_IPv6_t * ) pxDescriptor->pucEthernetBuffer;
            pxICMPHeader_IPv6 = &( pxICMPPacket->xICMPHeaderIPv6 );
            /* Three important bits are store in "Reserved". */
            ulReserved = FreeRTOS_ntohl( pxICMPHeader_IPv6->ulReserved );

            /* Extract Packet Data */
            memset( &xNaPacket, 0, sizeof( xNaPacket ) );
            xNaPacket.xRouter = ( ( ulReserved & ndICMPv6_FLAG_ROUTER ) != 0 ) ? pdTRUE : pdFALSE;
            xNaPacket.xSolicited = ( ( ulReserved & ndICMPv6_FLAG_SOLICITED ) != 0 ) ? pdTRUE : pdFALSE;
            xNaPacket.xOverride = ( ( ulReserved & ndICMPv6_FLAG_OVERRIDE ) != 0 ) ? pdTRUE : pdFALSE;

            /* This struct member is the ICMPv6 Code field under its old name. */
            xNaPacket.ucCode = pxICMPHeader_IPv6->ucTypeOfService;
            xNaPacket.xDestinationIsMulticast =
                ( pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes[ 0 ] == 0xFFU ) ? pdTRUE : pdFALSE;

            FreeRTOS_debug_printf( ( "NDP: Received S=%d, O=%d, R=%d\n",
                                     ( int ) xNaPacket.xSolicited,
                                     ( int ) xNaPacket.xOverride,
                                     ( int ) xNaPacket.xRouter ) );
            memcpy( xNaPacket.xTargetIP.ucBytes, pxICMPHeader_IPv6->xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

            /* Iterate through NDP Options, looking for Link-Layer target address. */
            /* ICMPv6 options start after the 16-byte Target Address in the NA packet. */
            pucOptions = &( pxICMPHeader_IPv6->ucOptionType );

            usICMPSize = FreeRTOS_ntohs( pxICMPPacket->xIPHeader.usPayloadLength );
            uxICMPSize = ( size_t ) usICMPSize;

            configASSERT( ( ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize ) <= pxDescriptor->xDataLength );

            if( uxICMPSize < ipSIZE_OF_ICMPv6_HEADER )
            {
                /* Not even enough bytes for an IPv6 ICMP header. */
                break;
            }

            uxRemaining = uxICMPSize - ipSIZE_OF_ICMPv6_HEADER;

            while( uxRemaining >= 8U ) /* Each option is at least 8 bytes */
            {
                uint8_t ucType = pucOptions[ 0 ];
                uint8_t ucLen = pucOptions[ 1 ]; /* Length in units of 8 bytes */

                if( ( ucLen == 0U ) || ( ( ( size_t ) ucLen * 8U ) > uxRemaining ) )
                {
                    /* Malformed option: length is 0 or exceeds packet size. */
                    xFoundError = pdTRUE;
                    break;
                }

                if( ucType == ndICMP_TARGET_LINK_LAYER_ADDRESS ) /* Target Link-Layer Address */
                {
                    xNaPacket.xHasTargetLLA = pdTRUE;
                    xNaPacket.ucTargetLLALength = ucLen;
                    ( void ) memcpy( xNaPacket.xTargetMAC.ucBytes, &pucOptions[ 2 ], ipMAC_ADDRESS_LENGTH_BYTES );
                }

                /* Move to the next option; the check above already bounds it. */
                pucOptions = &pucOptions[ ucLen * 8U ];
                uxRemaining -= ( ( size_t ) ucLen * 8U );
            }

            if( xFoundError == pdTRUE )
            {
                break;
            }

            /* Validation (RFC 4861 rules) */
            if( prvIsValidNa( &xNaPacket ) == pdTRUE )
            {
                /* Cache Lookup */
                /* This assumes a function that returns a pointer to the cache row if found. */
                pxExistingEntry = pxNDPCacheLookup( &( xNaPacket.xTargetIP ) );

                /* Determine the Action based on Flags and Cache State */
                xAction = prvDetermineAction( &xNaPacket, pxExistingEntry );

                /* Execute the Action on the actual stack cache */
                switch( xAction )
                {
                    case eNA_UPDATE_REACHABLE:
                        vNDPCacheUpdate( &xNaPacket.xTargetIP, &xNaPacket.xTargetMAC, eND_REACHABLE, xNaPacket.xRouter, pxEndPoint );
                        break;

                    case eNA_CONFIRM_REACHABLE:
                        vNDPCacheSetState( &xNaPacket.xTargetIP, eND_REACHABLE );
                        break;

                    case eNA_UPDATE_STALE:
                        vNDPCacheUpdate( &xNaPacket.xTargetIP, &xNaPacket.xTargetMAC, eND_STALE, xNaPacket.xRouter, pxEndPoint );
                        break;

                    case eNA_REJECT_MAC_SET_STALE:
                        vNDPCacheSetState( &xNaPacket.xTargetIP, eND_STALE );
                        break;

                    case eNA_REJECT_MAC_PROBE:
                        vNDPCacheSetState( &xNaPacket.xTargetIP, eND_PROBE );
                        break;

                    case eNA_MAINTAIN:
                    case eNA_DROP:
                    default:
                        /* Do nothing. */
                        break;
                }

                /* Only a resolve or confirm may release the parked packet; doing it
                 * for every advertisement would let a device re-inject it at will. */
                if( ( xAction == eNA_UPDATE_REACHABLE ) ||
                    ( xAction == eNA_UPDATE_STALE ) ||
                    ( xAction == eNA_CONFIRM_REACHABLE ) )
                {
                    vNDCheckWaitingPacket( &( xNaPacket.xTargetIP ) );
                }

                FreeRTOS_printf( ( "NDP: Received NA for %pip: %s\n", ( void * ) xNaPacket.xTargetIP.ucBytes, pcNDActionName( xAction ) ) );
            }
        } while( 0 );

        return xAction;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Process a packet parked in pxNDWaitingNetworkBuffer once the target
 *        address has been resolved, sending it if it matches or releasing it.
 *
 * @param[in] pxTargetIP The IPv6 address that has just been resolved.
 */
    void vNDCheckWaitingPacket( const IPv6_Address_t * pxTargetIP )
    {
        /*
         * pxNDWaitingNetworkBuffer holds at most one received packet that could not
         * be processed until the address it came from had been resolved.
         */
        if( ( pxNDWaitingNetworkBuffer != NULL ) &&
            ( uxIPHeaderSizePacket( pxNDWaitingNetworkBuffer ) == ipSIZE_OF_IPv6_HEADER ) )
        {
            const ICMPPacket_IPv6_t * pxIPPacket = ( const ICMPPacket_IPv6_t * ) pxNDWaitingNetworkBuffer->pucEthernetBuffer;

            /* The packet was parked because its SOURCE address was unresolved. */
            if( memcmp( pxIPPacket->xIPHeader.xSourceAddress.ucBytes, pxTargetIP->ucBytes, ipSIZE_OF_IPv6_ADDRESS ) == 0 )
            {
                NetworkBufferDescriptor_t * pxBuffer = pxNDWaitingNetworkBuffer;
                IPStackEvent_t xEventMessage;

                FreeRTOS_debug_printf( ( "NDP: vNDCheckWaitingPacket: %pip resolved, sending the parked packet.\n",
                                         pxTargetIP->ucBytes ) );

                /* Clear the global first: the buffer is now owned by the queued
                 * event, or by the release below when queueing fails. */
                pxNDWaitingNetworkBuffer = NULL;

                /* Send the buffer. This function is internal to the IP-task. */
                xEventMessage.eEventType = eNetworkRxEvent;
                xEventMessage.pvData = ( void * ) pxBuffer;

                if( xSendEventStructToIPTask( &xEventMessage, ndDONT_BLOCK ) != pdTRUE )
                {
                    vReleaseNetworkBufferAndDescriptor( pxBuffer );
                }

                /* Disable the ND resolution timer. */
                vIPSetNDResolutionTimerEnableState( pdFALSE );

                iptrace_DELAYED_ND_REQUEST_REPLIED();
            }
            else
            {
                /* A different address: the packet stays parked for its own. */
                FreeRTOS_debug_printf( ( "NDP: vNDCheckWaitingPacket: parked packet %pip is not waiting for %pip\n",
                                         pxIPPacket->xIPHeader.xSourceAddress.ucBytes,
                                         pxTargetIP->ucBytes ) );
            }
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Logic core: Determines what to do with the cache based on RFC 4861.
 * It is called from prvProcessNA().
 *
 * @param[in] pxNa The fields that were extracted from the advertisement.
 * @param[in] pxEntry The cache entry for the advertised target, or NULL when the
 *                    target is not in the cache.
 *
 * @return The action that prvProcessNA() should carry out.
 */
    static eNaAction_t prvDetermineAction( const NaPacket_t * pxNa,
                                           const NDCacheRow_t * pxEntry )
    {
        eNaAction_t eNaAction;

        if( pxEntry == NULL )
        {
            /* RFC 4861 section 7.2.5: discard, else an attacker could claim the
             * gateway before it is resolved. */
            eNaAction = eNA_DROP;
        }
        else if( pxEntry->ucState == ( uint8_t ) eND_INCOMPLETE )
        {
            if( pxNa->xHasTargetLLA == pdFALSE )
            {
                eNaAction = eNA_DROP;
            }
            else
            {
                eNaAction = ( pxNa->xSolicited != pdFALSE ) ? eNA_UPDATE_REACHABLE : eNA_UPDATE_STALE;
            }
        }
        else if( pxNa->xHasTargetLLA == pdFALSE )
        {
            eNaAction = ( pxNa->xSolicited != pdFALSE ) ? eNA_CONFIRM_REACHABLE : eNA_MAINTAIN;
        }
        else if( memcmp( pxNa->xTargetMAC.ucBytes, pxEntry->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
        {
            eNaAction = ( pxNa->xSolicited != pdFALSE ) ? eNA_CONFIRM_REACHABLE : eNA_MAINTAIN;
        }
        else if( pxNa->xOverride == pdFALSE )
        {
            /* RFC 4861 section 7.2.5: with O=0 only a REACHABLE entry is demoted,
             * else an attacker could cut short a verification in flight. */
            if( ( pxNa->xSolicited != pdFALSE ) && ( pxEntry->ucState == ( uint8_t ) eND_REACHABLE ) )
            {
                eNaAction = eNA_REJECT_MAC_SET_STALE;
            }
            else
            {
                eNaAction = eNA_MAINTAIN;
            }
        }
        else
        {
            /* Keep the cached binding and let NUD settle it, whatever the
             * sender-chosen S bit says ( RFC 3756 section 4.1.1 ). */
            eNaAction = eNA_REJECT_MAC_PROBE;
        }

        return eNaAction;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Provide a hint to the NDP cache that the neighbor is reachable.
 *        Called by TCP or UDP when forward progress is confirmed.
 *
 * @param[in] pxMACAddress The Ethernet source address of the packet that arrived.
 * @param[in] pxIPAddress The IPv6 source address of that packet.
 *
 * @note Only accepted from the bound MAC-address, since a spoofed IPv6 source
 *       could otherwise keep a poisoned entry alive for ever.
 */
    void vNDRefreshCacheEntryAge( const MACAddress_t * pxMACAddress,
                                  const IPv6_Address_t * pxIPAddress )
    {
        NDCacheRow_t * pxEntry = pxNDPCacheLookup( pxIPAddress );

        if( pxEntry == NULL )
        {
            /* Unknown neighbour: a received packet never creates an entry. */
        }
        else if( pxEntry->ucState == ( uint8_t ) eND_INCOMPLETE )
        {
        }
        else if( memcmp( pxEntry->xMACAddress.ucBytes, pxMACAddress->ucBytes, ipMAC_ADDRESS_LENGTH_BYTES ) != 0 )
        {
            FreeRTOS_debug_printf( ( "NDP: Upper-layer hint for %pip ignored: MAC-address does not match\n",
                                     pxEntry->xIPAddress.ucBytes ) );
        }
        else
        {
            if( pxEntry->ucState != ( uint8_t ) eND_REACHABLE )
            {
                FreeRTOS_debug_printf( ( "NDP: Upper-layer hint: %pip moved to REACHABLE\n",
                                         pxEntry->xIPAddress.ucBytes ) );
            }

            pxEntry->ucState = ( uint8_t ) eND_REACHABLE;
            pxEntry->ucAge = ( uint8_t ) ipconfigMAX_ND_AGE;
            pxEntry->ucNumProbes = 0;
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Insert or refresh a fully-trusted ND cache binding as REACHABLE.
 *
 * This is used for self-originated bindings that are not derived from received
 * network traffic (e.g. the loopback interface mapping the endpoint's own MAC
 * to its own loopback IPv6 address).  Because the binding is trusted, it may
 * create a new entry - unlike vNDRefreshCacheEntryAge(), which never inserts.
 * Do NOT call this from the receive path for peer neighbours; that path must go
 * through prvProcessNA()/prvDetermineAction().
 */
    void vNDRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                               const IPv6_Address_t * pxIPAddress,
                               NetworkEndPoint_t * pxEndPoint )
    {
        IPv6_Address_t xTargetIP;
        MACAddress_t xTargetMAC;

        ( void ) memcpy( xTargetIP.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
        ( void ) memcpy( xTargetMAC.ucBytes, pxMACAddress->ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );

        if( pxNDPCacheLookup( pxIPAddress ) != NULL )
        {
            /* Entry already exists: refresh its L2 mapping and mark REACHABLE. */
            vNDPCacheUpdate( &xTargetIP, &xTargetMAC, eND_REACHABLE, pdFALSE, pxEndPoint );
        }
        else
        {
            /* No entry yet: create a new trusted binding as REACHABLE. */
            vNDPCacheInsert( &xTargetIP, &xTargetMAC, eND_REACHABLE, pxEndPoint );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief A call to this function will clear the ND cache.
 * @param[in] pxEndPoint only clean entries with this end-point, or when NULL,
 *                        clear the entire ND cache.
 */
    void FreeRTOS_ClearND( const struct xNetworkEndPoint * pxEndPoint )
    {
        if( pxEndPoint != NULL )
        {
            BaseType_t x;

            for( x = 0; x < ipconfigND_CACHE_ENTRIES; x++ )
            {
                if( xNDCache[ x ].pxEndPoint == pxEndPoint )
                {
                    ( void ) memset( &( xNDCache[ x ] ), 0, sizeof( NDCacheRow_t ) );
                }
            }
        }
        else
        {
            ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Look-up an IPv6 address in the cache.
 *
 * @param[in] pxAddressToLookup The IPv6 address to look-up.Ethernet packet.
 * @param[out] pxMACAddress The resulting MAC-address will be stored here.
 * @param[out] ppxEndPoint A pointer to a pointer to an end-point, where the end-point will be stored.
 *
 * @return An enum: either eResolutionCacheHit or eResolutionCacheMiss.
 *
 * @note This runs for a packet about to be sent, so it makes the transition
 *       RFC 4861 section 7.3.3 ties to sending.
 */
    static eResolutionLookupResult_t prvNDCacheLookup( const IPv6_Address_t * pxAddressToLookup,
                                                       MACAddress_t * const pxMACAddress,
                                                       NetworkEndPoint_t ** ppxEndPoint )
    {
        NDCacheRow_t * pxRow;
        eResolutionLookupResult_t eReturn = eResolutionCacheMiss;
        size_t x;

        pxRow = pxNDPCacheLookup( pxAddressToLookup );

        /* INCOMPLETE holds no MAC-address yet, so it is not a hit. */
        if( ( pxRow != NULL ) && ( pxRow->ucState == ( uint8_t ) eND_INCOMPLETE ) )
        {
            pxRow = NULL;
        }

        if( pxRow != NULL )
        {
            char pcMAC[ 18 ];

            if( pxRow->ucState == ( uint8_t ) eND_STALE )
            {
                pxRow->ucState = ( uint8_t ) eND_DELAY;
                pxRow->ucAge = ( uint8_t ) ndDELAY_FIRST_PROBE_TIME_SECONDS;
            }

            eReturn = eResolutionCacheHit;
            x = ( size_t ) ( pxRow - xNDCache );
            ( void ) x; /* May be unused when FreeRTOS_debug_printf() is compiled out. */
            ( void ) memcpy( pxMACAddress->ucBytes, pxRow->xMACAddress.ucBytes, sizeof( MACAddress_t ) );
            FreeRTOS_EUI48_ntop( pxMACAddress->ucBytes, pcMAC, 'a', '-' );
            FreeRTOS_debug_printf( ( "prvCacheLookup6[ %d ] %pip with %s\n",
                                     ( int ) x,
                                     ( void * ) pxAddressToLookup->ucBytes,
                                     pcMAC ) );

            if( ppxEndPoint != NULL )
            {
                *ppxEndPoint = pxRow->pxEndPoint;
            }
        }
        else
        {
            FreeRTOS_printf( ( "prvNDCacheLookup %pip Miss\n", ( void * ) pxAddressToLookup->ucBytes ) );

            if( ppxEndPoint != NULL )
            {
                *ppxEndPoint = NULL;
            }
        }

        return eReturn;
    }
/*-----------------------------------------------------------*/

    #if ( ( ipconfigHAS_PRINTF != 0 ) || ( ipconfigHAS_DEBUG_PRINTF != 0 ) )

/**
 * @brief Print the contents of the ND cache, for debugging only.
 * An example of the logging:
 *
 * 0 | fe80::7001 | 00-01-02-03-04-05 | Reachable | 149 | Router
 */
        void FreeRTOS_PrintNDCache( void )
        {
            BaseType_t x, xCount = 0;
            char pcBuffer_EUI48[ 18 ];

            /* Loop through each entry in the ND cache. */
            for( x = 0; x < ipconfigND_CACHE_ENTRIES; x++ )
            {
                if( xNDCache[ x ].ucState != ( uint8_t ) eND_FREE )
                {
                    const char * pcHostType = ( xNDCache[ x ].ucFlags & ndpFLAG_IS_ROUTER ) ? "Router" : "Host"; /* LCOV_EXCL_BR_LINE - debug-only (ipconfigHAS_DEBUG_PRINTF) */

                    /* See if the MAC-address also matches, and we're all happy */
                    FreeRTOS_EUI48_ntop( xNDCache[ x ].xMACAddress.ucBytes, pcBuffer_EUI48, 'a', '-' );

                    FreeRTOS_printf( ( " %u | %pip | %s | %s | %u | %s \n",
                                       ( int ) x,
                                       ( void * ) xNDCache[ x ].xIPAddress.ucBytes,
                                       pcBuffer_EUI48,
                                       pcNDStateName( ( eNDState_t ) xNDCache[ x ].ucState ),
                                       xNDCache[ x ].ucAge,
                                       pcHostType ) );
                    xCount++;
                }
            }

            FreeRTOS_printf( ( "ND has %ld entries\n", xCount ) );
        }

    #endif /* ( ipconfigHAS_PRINTF != 0 ) || ( ipconfigHAS_DEBUG_PRINTF != 0 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Return an ICMPv6 packet to the peer.
 *
 * @param[in] pxNetworkBuffer The Ethernet packet.
 * @param[in] uxICMPSize The number of bytes to be sent.
 */
    static void prvReturnICMP_IPv6( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    size_t uxICMPSize )
    {
        const NetworkEndPoint_t * pxEndPoint = pxNetworkBuffer->pxEndPoint;

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        ICMPPacket_IPv6_t * pxICMPPacket = ( ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );

        ( void ) memcpy( pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes, pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
        ( void ) memcpy( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
        pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( uxICMPSize );

        /* Important: tell NIC driver how many bytes must be sent */
        pxNetworkBuffer->xDataLength = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );

        #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
        {
            /* calculate the ICMPv6 checksum for outgoing package */
            ( void ) usGenerateProtocolChecksum( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE );
        }
        #else
        {
            /* Many EMAC peripherals will only calculate the ICMP checksum
             * correctly if the field is nulled beforehand. */
            pxICMPPacket->xICMPHeaderIPv6.usChecksum = 0;
        }
        #endif

        /* This function will fill in the Ethernet addresses and send the packet */
        vReturnEthernetFrame( pxNetworkBuffer, pdFALSE );
    }
/*-----------------------------------------------------------*/

/**
 * @brief Send out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 *        add an entry into the ND table that indicates that an ND reply is outstanding
 *        so re-transmissions can be generated.
 *
 * @param[in] pxNetworkBuffer The network buffer in which the message shall be stored.
 * @param[in] pxIPAddress The IPv6 address that is asked to send a Neighbour Advertisement.
 *
 * @note Send out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 * add an entry into the ND table that indicates that an ND reply is
 * outstanding so re-transmissions can be generated.
 */

    void vNDSendNeighbourSolicitation( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                       const IPv6_Address_t * pxIPAddress )
    {
        ICMPPacket_IPv6_t * pxICMPPacket;
        ICMPHeader_IPv6_t * pxICMPHeader_IPv6;
        NetworkEndPoint_t * pxEndPoint = pxNetworkBuffer->pxEndPoint;
        size_t uxNeededSize;
        IPv6_Address_t xTargetIPAddress;
        MACAddress_t xMultiCastMacAddress;
        NetworkBufferDescriptor_t * pxDescriptor = pxNetworkBuffer;
        NetworkBufferDescriptor_t * pxNewDescriptor = NULL;
        BaseType_t xReleased = pdFALSE;

        if( ( pxEndPoint != NULL ) && ( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED ) )
        {
            uxNeededSize = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t );

            if( pxDescriptor->xDataLength < uxNeededSize )
            {
                pxNewDescriptor = pxDuplicateNetworkBufferWithDescriptor( pxDescriptor, uxNeededSize );
                vReleaseNetworkBufferAndDescriptor( pxDescriptor );
                pxDescriptor = pxNewDescriptor;
            }

            if( pxDescriptor != NULL )
            {
                const uint32_t ulPayloadLength = 32U;

                /* MISRA Ref 11.3.1 [Misaligned access] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                /* coverity[misra_c_2012_rule_11_3_violation] */
                pxICMPPacket = ( ( ICMPPacket_IPv6_t * ) pxDescriptor->pucEthernetBuffer );
                pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( pxICMPPacket->xICMPHeaderIPv6 ) );

                pxDescriptor->xDataLength = uxNeededSize;

                /* Set the multi-cast MAC-address. */
                xMultiCastMacAddress.ucBytes[ 0 ] = 0x33U;
                xMultiCastMacAddress.ucBytes[ 1 ] = 0x33U;
                xMultiCastMacAddress.ucBytes[ 2 ] = 0xffU;
                xMultiCastMacAddress.ucBytes[ 3 ] = pxIPAddress->ucBytes[ 13 ];
                xMultiCastMacAddress.ucBytes[ 4 ] = pxIPAddress->ucBytes[ 14 ];
                xMultiCastMacAddress.ucBytes[ 5 ] = pxIPAddress->ucBytes[ 15 ];

                /* Set Ethernet header. Source and Destination will be swapped. */
                ( void ) memcpy( pxICMPPacket->xEthernetHeader.xSourceAddress.ucBytes, xMultiCastMacAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
                ( void ) memcpy( pxICMPPacket->xEthernetHeader.xDestinationAddress.ucBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
                pxICMPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

                /* Set IP-header. */
                pxICMPPacket->xIPHeader.ucVersionTrafficClass = 0x60U;
                pxICMPPacket->xIPHeader.ucTrafficClassFlow = 0U;
                pxICMPPacket->xIPHeader.usFlowLabel = 0U;
                pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( ulPayloadLength );
                pxICMPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
                pxICMPPacket->xIPHeader.ucHopLimit = ndHOP_LIMIT;

                /* Source address */
                ( void ) memcpy( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

                /*ff02::1:ff5a:afe7 */
                ( void ) memset( xTargetIPAddress.ucBytes, 0, sizeof( xTargetIPAddress.ucBytes ) );
                xTargetIPAddress.ucBytes[ 0 ] = 0xff;
                xTargetIPAddress.ucBytes[ 1 ] = 0x02;
                xTargetIPAddress.ucBytes[ 11 ] = 0x01;
                xTargetIPAddress.ucBytes[ 12 ] = 0xff;
                xTargetIPAddress.ucBytes[ 13 ] = pxIPAddress->ucBytes[ 13 ];
                xTargetIPAddress.ucBytes[ 14 ] = pxIPAddress->ucBytes[ 14 ];
                xTargetIPAddress.ucBytes[ 15 ] = pxIPAddress->ucBytes[ 15 ];
                ( void ) memcpy( pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes, xTargetIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

                /* Set ICMP header. */
                ( void ) memset( pxICMPHeader_IPv6, 0, sizeof( *pxICMPHeader_IPv6 ) );
                pxICMPHeader_IPv6->ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
                ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                pxICMPHeader_IPv6->ucOptionType = ndICMP_SOURCE_LINK_LAYER_ADDRESS;
                pxICMPHeader_IPv6->ucOptionLength = 1U; /* times 8 bytes. */
                ( void ) memcpy( pxICMPHeader_IPv6->ucOptionBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );

                /* Checksums. */
                #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
                {
                    /* calculate the ICMPv6 checksum for outgoing package */
                    ( void ) usGenerateProtocolChecksum( pxDescriptor->pucEthernetBuffer, pxDescriptor->xDataLength, pdTRUE );
                }
                #else
                {
                    /* Many EMAC peripherals will only calculate the ICMP checksum
                     * correctly if the field is nulled beforehand. */
                    pxICMPHeader_IPv6->usChecksum = 0U;
                }
                #endif

                /* Record before sending, because some callers pass an address inside
                 * the descriptor that vReturnEthernetFrame() releases. */
                prvNDCacheRecordSolicitation( pxIPAddress, pxEndPoint );

                /* This function will fill in the eth addresses and send the packet */
                vReturnEthernetFrame( pxDescriptor, pdTRUE );
                xReleased = pdTRUE;
            }
        }

        if( ( pxDescriptor != NULL ) && ( xReleased == pdFALSE ) )
        {
            vReleaseNetworkBufferAndDescriptor( pxDescriptor );
        }
    }
/*-----------------------------------------------------------*/

    #if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

/**
 * @brief Send a PING request using an ICMPv6 format.
 *
 * @param[in] pxIPAddress Send an IPv6 PING request.
 * @param[in] uxNumberOfBytesToSend The number of bytes to be sent.
 * @param[in] uxBlockTimeTicks The maximum number of clock-ticks to wait while
 *            putting the message on the queue for the IP-task.
 *
 * @return When failed: pdFAIL, otherwise the PING sequence number.
 */
        BaseType_t FreeRTOS_SendPingRequestIPv6( const IPv6_Address_t * pxIPAddress,
                                                 size_t uxNumberOfBytesToSend,
                                                 TickType_t uxBlockTimeTicks )
        {
            NetworkBufferDescriptor_t * pxNetworkBuffer = NULL;
            EthernetHeader_t * pxEthernetHeader;
            ICMPPacket_IPv6_t * pxICMPPacket;
            ICMPEcho_IPv6_t * pxICMPHeader;
            BaseType_t xReturn = pdFAIL;
            static uint16_t usSequenceNumber = 0;
            uint8_t * pucChar;
            IPStackEvent_t xStackTxEvent = { eStackTxEvent, NULL };
            NetworkEndPoint_t * pxEndPoint = NULL;
            size_t uxPacketLength = 0U;
            BaseType_t xEnoughSpace;

            pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( pxIPAddress );

            /* MISRA Ref 14.3.1 [Configuration dependent invariant] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-143 */
            /* coverity[misra_c_2012_rule_14_3_violation] */
            /* coverity[notnull] */
            if( pxEndPoint == NULL )
            {
                BaseType_t xWanted = ( xIPv6_GetIPType( pxIPAddress ) == eIPv6_Global ) ? 1 : 0;

                for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
                     pxEndPoint != NULL;
                     pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
                {
                    if( pxEndPoint->bits.bIPv6 != 0U )
                    {
                        BaseType_t xGot = ( xIPv6_GetIPType( &( pxEndPoint->ipv6_settings.xIPAddress ) ) == eIPv6_Global ) ? 1 : 0;

                        if( xWanted == xGot )
                        {
                            break;
                        }
                    }
                }
            }

            if( uxNumberOfBytesToSend < ( ( ipconfigNETWORK_MTU - sizeof( IPHeader_IPv6_t ) ) - sizeof( ICMPEcho_IPv6_t ) ) )
            {
                xEnoughSpace = pdTRUE;
            }
            else
            {
                xEnoughSpace = pdFALSE;
            }

            if( pxEndPoint == NULL )
            {
                /* No endpoint found for the target IP-address. */
                FreeRTOS_printf( ( "SendPingRequestIPv6: no end-point found for %pip\n",
                                   ( void * ) pxIPAddress->ucBytes ) );
            }
            else if( ( uxGetNumberOfFreeNetworkBuffers() >= 3U ) && ( uxNumberOfBytesToSend >= 1U ) && ( xEnoughSpace != pdFALSE ) )
            {
                uxPacketLength = sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) + sizeof( ICMPEcho_IPv6_t ) + uxNumberOfBytesToSend;

                /* MISRA Ref 11.3.1 [Misaligned access] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                /* coverity[misra_c_2012_rule_11_3_violation] */
                pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxPacketLength, uxBlockTimeTicks );

                if( pxNetworkBuffer != NULL )
                {
                    /* Probably not necessary to clear the buffer. */
                    ( void ) memset( pxNetworkBuffer->pucEthernetBuffer, 0, pxNetworkBuffer->xDataLength );

                    pxNetworkBuffer->pxEndPoint = pxEndPoint;
                    pxNetworkBuffer->pxInterface = pxEndPoint->pxNetworkInterface;

                    /* MISRA Ref 11.3.1 [Misaligned access] */
                    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                    /* coverity[misra_c_2012_rule_11_3_violation] */
                    pxICMPPacket = ( ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );

                    pxICMPHeader = ( ( ICMPEcho_IPv6_t * ) &( pxICMPPacket->xICMPHeaderIPv6 ) );
                    usSequenceNumber++;

                    pxICMPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

                    pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( sizeof( ICMPEcho_IPv6_t ) + uxNumberOfBytesToSend );
                    ( void ) memcpy( pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                    ( void ) memcpy( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                    FreeRTOS_printf( ( "ICMP send from %pip\n", ( void * ) pxICMPPacket->xIPHeader.xSourceAddress.ucBytes ) );

                    /* Fill in the basic header information. */
                    pxICMPHeader->ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
                    pxICMPHeader->ucTypeOfService = 0;
                    pxICMPHeader->usIdentifier = FreeRTOS_htons( usSequenceNumber );
                    pxICMPHeader->usSequenceNumber = FreeRTOS_htons( usSequenceNumber );

                    /* Find the start of the data. */
                    pucChar = ( uint8_t * ) pxICMPHeader;
                    pucChar = &( pucChar[ sizeof( ICMPEcho_IPv6_t ) ] );

                    /* Just memset the data to a fixed value. */
                    ( void ) memset( pucChar, ( int32_t ) ndECHO_DATA_FILL_BYTE, uxNumberOfBytesToSend );

                    /* The message is complete, IP and checksum's are handled by
                     * vProcessGeneratedUDPPacket */
                    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] = FREERTOS_SO_UDPCKSUM_OUT;
                    ( void ) memset( pxNetworkBuffer->xIPAddress.xIP_IPv6.ucBytes, 0, ipSIZE_OF_IPv6_ADDRESS );
                    ( void ) memcpy( pxNetworkBuffer->xIPAddress.xIP_IPv6.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                    /* Let vProcessGeneratedUDPPacket() know that this is an ICMP packet. */
                    pxNetworkBuffer->usPort = ipPACKET_CONTAINS_ICMP_DATA;
                    /* 'uxPacketLength' is initialised due to the flow of the program. */
                    pxNetworkBuffer->xDataLength = uxPacketLength;

                    /* MISRA Ref 11.3.1 [Misaligned access] */
                    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                    /* coverity[misra_c_2012_rule_11_3_violation] */
                    pxEthernetHeader = ( ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );
                    pxEthernetHeader->usFrameType = ipIPv6_FRAME_TYPE;

                    /* Send to the stack. */
                    xStackTxEvent.pvData = pxNetworkBuffer;

                    if( xSendEventStructToIPTask( &xStackTxEvent, uxBlockTimeTicks ) != pdPASS )
                    {
                        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
                        iptraceSTACK_TX_EVENT_LOST( ipSTACK_TX_EVENT );
                    }
                    else
                    {
                        xReturn = ( BaseType_t ) usSequenceNumber;
                    }
                }
            }
            else
            {
                /* Either no proper end-pint found, or allocating the network buffer failed. */
            }

            return xReturn;
        }

    #endif /* ipconfigSUPPORT_OUTGOING_PINGS == 1 */
/*-----------------------------------------------------------*/


    #if ( ipconfigHAS_PRINTF == 1 )

/**
 * @brief Returns a printable string for the major ICMPv6 message types.  Used for
 *        debugging only.
 *
 * @param[in] xType The type of message.
 *
 * @return A null-terminated string that represents the type the kind of message.
 */
        static const char * pcMessageType( BaseType_t xType )
        {
            const char * pcReturn;

            switch( ( uint8_t ) xType )
            {
                case ipICMP_DEST_UNREACHABLE_IPv6:
                    pcReturn = "DEST_UNREACHABLE";
                    break;

                case ipICMP_PACKET_TOO_BIG_IPv6:
                    pcReturn = "PACKET_TOO_BIG";
                    break;

                case ipICMP_TIME_EXCEEDED_IPv6:
                    pcReturn = "TIME_EXCEEDED";
                    break;

                case ipICMP_PARAMETER_PROBLEM_IPv6:
                    pcReturn = "PARAMETER_PROBLEM";
                    break;

                case ipICMP_PING_REQUEST_IPv6:
                    pcReturn = "PING_REQUEST";
                    break;

                case ipICMP_PING_REPLY_IPv6:
                    pcReturn = "PING_REPLY";
                    break;

                case ipICMP_ROUTER_SOLICITATION_IPv6:
                    pcReturn = "ROUTER_SOL";
                    break;

                case ipICMP_ROUTER_ADVERTISEMENT_IPv6:
                    pcReturn = "ROUTER_ADV";
                    break;

                case ipICMP_NEIGHBOR_SOLICITATION_IPv6:
                    pcReturn = "NEIGHBOR_SOL";
                    break;

                case ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6:
                    pcReturn = "NEIGHBOR_ADV";
                    break;

                case ipICMP_MULTICAST_LISTENER_REPORT_V1:
                    pcReturn = "MCAST_LISTENER_REPORT_V1";
                    break;

                case ipICMP_MULTICAST_LISTENER_REPORT_V2:
                    pcReturn = "MCAST_LISTENER_REPORT_V2";
                    break;

                default:
                    pcReturn = "UNKNOWN ICMP";
                    break;
            }

            return pcReturn;
        }
    #endif /* ( ipconfigHAS_PRINTF == 1 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Process an ICMPv6 packet and send replies when applicable.
 *
 * @param[in] pxNetworkBuffer The Ethernet packet which contains an IPv6 message.
 *
 * @return A const value 'eReleaseBuffer' which means that the network must still be released.
 */
    eFrameProcessingResult_t prvProcessICMPMessage_IPv6( NetworkBufferDescriptor_t * const pxNetworkBuffer )
    {
        /*
         *  ICMPv6 messages have the following general format:
         *
         *  0                   1                   2                   3
         *  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
         +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
         |     Type      |     Code      |          Checksum             |
         +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
         |                                                               |
         +                         Message Body                          +
         |                                                               |
         |
         |  The packet should contain atleast 4 bytes of general fields
         |
         */
        if( pxNetworkBuffer->xDataLength >= ( ( size_t ) ipSIZE_OF_ETH_HEADER + ( size_t ) ipSIZE_OF_IPv6_HEADER + ( size_t ) ipICMPv6_GENERAL_FIELD_SIZE ) )
        {
            /* MISRA Ref 11.3.1 [Misaligned access] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            ICMPPacket_IPv6_t * pxICMPPacket = ( ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
            /* coverity[misra_c_2012_rule_11_3_violation] */
            ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( pxICMPPacket->xICMPHeaderIPv6 ) );
            /* Note: pxNetworkBuffer->pxEndPoint is already verified to be non-NULL in prvProcessEthernetPacket() */
            NetworkEndPoint_t * pxEndPoint = pxNetworkBuffer->pxEndPoint;
            size_t uxNeededSize;

            #if ( ipconfigHAS_PRINTF == 1 )
            {
                if( ( pxICMPHeader_IPv6->ucTypeOfMessage != ipICMP_PING_REQUEST_IPv6 ) && /* LCOV_EXCL_BR_LINE - debug-only (ipconfigHAS_PRINTF) */
                    ( pxICMPHeader_IPv6->ucTypeOfMessage != ipICMP_ROUTER_ADVERTISEMENT_IPv6 ) &&
                    ( pxICMPHeader_IPv6->ucTypeOfMessage != ipICMP_NEIGHBOR_SOLICITATION_IPv6 ) )
                {
                    char pcAddress[ 40 ];
                    FreeRTOS_printf( ( "ICMPv6_recv %d (%s) from %pip to %pip end-point = %s\n",
                                       pxICMPHeader_IPv6->ucTypeOfMessage,
                                       pcMessageType( ( BaseType_t ) pxICMPHeader_IPv6->ucTypeOfMessage ),
                                       ( void * ) pxICMPPacket->xIPHeader.xSourceAddress.ucBytes,
                                       ( void * ) pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes,
                                       pcEndpointName( pxEndPoint, pcAddress, sizeof( pcAddress ) ) ) );
                }
            }
            #endif /* ( ipconfigHAS_PRINTF == 1 ) */

            if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
            {
                switch( pxICMPHeader_IPv6->ucTypeOfMessage )
                {
                    case ipICMP_DEST_UNREACHABLE_IPv6:
                    case ipICMP_PACKET_TOO_BIG_IPv6:
                    case ipICMP_TIME_EXCEEDED_IPv6:
                    case ipICMP_PARAMETER_PROBLEM_IPv6:
                        /* These message types are not implemented. They are logged here above. */
                        break;

                    case ipICMP_PING_REQUEST_IPv6:
                       {
                           size_t uxICMPSize;
                           uint16_t usICMPSize;

                           /* Lint would complain about casting '()' immediately. */
                           usICMPSize = FreeRTOS_ntohs( pxICMPPacket->xIPHeader.usPayloadLength );
                           uxICMPSize = ( size_t ) usICMPSize;
                           uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );

                           if( uxNeededSize > pxNetworkBuffer->xDataLength )
                           {
                               FreeRTOS_printf( ( "Too small\n" ) );
                               break;
                           }

                           pxICMPHeader_IPv6->ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;

                           /* MISRA Ref 4.14.1 [The validity of values received from external sources]. */
                           /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#directive-414. */
                           /* coverity[misra_c_2012_directive_4_14_violation] */
                           prvReturnICMP_IPv6( pxNetworkBuffer, uxICMPSize );
                       }
                       break;

                        #if ( ipconfigSUPPORT_OUTGOING_PINGS != 0 )
                            case ipICMP_PING_REPLY_IPv6:
                               {
                                   ePingReplyStatus_t eStatus = eSuccess;
                                   /* MISRA Ref 11.3.1 [Misaligned access] */
                                   /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                                   /* coverity[misra_c_2012_rule_11_3_violation] */
                                   const ICMPEcho_IPv6_t * pxICMPEchoHeader = ( ( const ICMPEcho_IPv6_t * ) pxICMPHeader_IPv6 );
                                   size_t uxDataLength, uxCount;
                                   const uint8_t * pucByte;

                                   /* Find the total length of the IP packet. */
                                   uxDataLength = ipNUMERIC_CAST( size_t, FreeRTOS_ntohs( pxICMPPacket->xIPHeader.usPayloadLength ) );

                                   uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxDataLength );

                                   if( uxNeededSize > pxNetworkBuffer->xDataLength )
                                   {
                                       FreeRTOS_printf( ( "Too small\n" ) );
                                       break;
                                   }

                                   if( uxDataLength < sizeof( *pxICMPEchoHeader ) )
                                   {
                                       break;
                                   }

                                   uxDataLength = uxDataLength - sizeof( *pxICMPEchoHeader );

                                   /* Find the first byte of the data within the ICMP packet. */
                                   pucByte = ( const uint8_t * ) pxICMPEchoHeader;
                                   pucByte = &( pucByte[ sizeof( *pxICMPEchoHeader ) ] );

                                   /* Check each byte. */
                                   for( uxCount = 0; uxCount < uxDataLength; uxCount++ )
                                   {
                                       if( *pucByte != ( uint8_t ) ipECHO_DATA_FILL_BYTE )
                                       {
                                           eStatus = eInvalidData;
                                           break;
                                       }

                                       pucByte++;
                                   }

                                   /* Call back into the application to pass it the result. */
                                   vApplicationPingReplyHook( eStatus, pxICMPEchoHeader->usIdentifier );
                               }
                               break;
                        #endif /* ( ipconfigSUPPORT_OUTGOING_PINGS != 0 ) */
                    case ipICMP_NEIGHBOR_SOLICITATION_IPv6:
                       {
                           size_t uxICMPSize;
                           BaseType_t xCompare;
                           const NetworkEndPoint_t * pxTargetedEndPoint = pxEndPoint;
                           const NetworkEndPoint_t * pxEndPointInSameSubnet;

                           uxICMPSize = sizeof( ICMPHeader_IPv6_t );
                           uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );

                           if( uxNeededSize > pxNetworkBuffer->xDataLength )
                           {
                               FreeRTOS_printf( ( "Too small\n" ) );
                               break;
                           }

                           pxEndPointInSameSubnet = FreeRTOS_InterfaceEPInSameSubnet_IPv6( pxNetworkBuffer->pxInterface, &( pxICMPHeader_IPv6->xIPv6Address ) );

                           if( pxEndPointInSameSubnet != NULL )
                           {
                               pxTargetedEndPoint = pxEndPointInSameSubnet;
                           }
                           else
                           {
                               FreeRTOS_debug_printf( ( "prvProcessICMPMessage_IPv6: No match for %pip\n",
                                                        pxICMPHeader_IPv6->xIPv6Address.ucBytes ) );
                           }

                           xCompare = memcmp( pxICMPHeader_IPv6->xIPv6Address.ucBytes, pxTargetedEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

                           if( xCompare == 0 )
                           {
                               FreeRTOS_printf( ( "ND NS for %pip endpoint %pip %s\n",
                                                  ( void * ) pxICMPHeader_IPv6->xIPv6Address.ucBytes,
                                                  ( void * ) pxNetworkBuffer->pxEndPoint->ipv6_settings.xIPAddress.ucBytes,
                                                  ( xCompare == 0 ) ? "Reply" : "Ignore" ) );
                           }

                           if( xCompare == 0 )
                           {
                               pxICMPHeader_IPv6->ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
                               pxICMPHeader_IPv6->ucTypeOfService = 0U;
                               pxICMPHeader_IPv6->ulReserved = ndICMPv6_FLAG_SOLICITED | ndICMPv6_FLAG_OVERRIDE;
                               pxICMPHeader_IPv6->ulReserved = FreeRTOS_htonl( pxICMPHeader_IPv6->ulReserved );

                               /* Type of option. */
                               pxICMPHeader_IPv6->ucOptionType = ndICMP_TARGET_LINK_LAYER_ADDRESS;
                               /* Length of option in units of 8 bytes. */
                               pxICMPHeader_IPv6->ucOptionLength = 1U;
                               ( void ) memcpy( pxICMPHeader_IPv6->ucOptionBytes, pxTargetedEndPoint->xMACAddress.ucBytes, sizeof( MACAddress_t ) );
                               pxICMPPacket->xIPHeader.ucHopLimit = ndHOP_LIMIT;
                               ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, pxTargetedEndPoint->ipv6_settings.xIPAddress.ucBytes, sizeof( pxICMPHeader_IPv6->xIPv6Address.ucBytes ) );
                               prvReturnICMP_IPv6( pxNetworkBuffer, uxICMPSize );
                           }
                       }
                       break;

                    case ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6:
                       {
                           size_t uxICMPSize;
                           eNaAction_t eResult;
                           uxICMPSize = sizeof( ICMPHeader_IPv6_t );
                           uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );

                           if( uxNeededSize > pxNetworkBuffer->xDataLength )
                           {
                               FreeRTOS_printf( ( "prvProcessICMPMessage_IPv6: Too small to reuse buffer: %u < %u.\n",
                                                  ( unsigned ) pxNetworkBuffer->xDataLength,
                                                  ( unsigned ) uxNeededSize ) );
                               break;
                           }

                           if( pxICMPPacket->xIPHeader.ucHopLimit != ndHOP_LIMIT )
                           {
                               FreeRTOS_debug_printf( ( "prvProcessICMPMessage_IPv6: ucHopLimit %u\n",
                                                        ( unsigned ) pxICMPPacket->xIPHeader.ucHopLimit ) );
                               break;
                           }

                           eResult = prvProcessNA( pxNetworkBuffer, pxEndPoint );
                           ( void ) eResult; /* May be unused when FreeRTOS_printf() is compiled out. */
                           FreeRTOS_printf( ( "NDP: Received Neighbour Advertisement: %s(%d)\n",
                                              pcNDActionName( eResult ),
                                              eResult ) );

                           #if ( ipconfigUSE_RA != 0 )

                               /* Receive a NA ( Neighbour Advertisement ) message to see if a chosen IP-address is already in use.
                                * This is important during SLAAC. */
                               vReceiveNA( pxNetworkBuffer );
                           #endif

                           /* prvProcessNA() releases any parked packet itself, and
                            * only for an accepted advertisement. */
                       }
                       break;

                    case ipICMP_ROUTER_SOLICITATION_IPv6:
                        break;

                        #if ( ipconfigUSE_RA != 0 )
                            case ipICMP_ROUTER_ADVERTISEMENT_IPv6:
                                /* Size check is done inside vReceiveRA */
                                vReceiveRA( pxNetworkBuffer );
                                break;
                        #endif /* ( ipconfigUSE_RA != 0 ) */

                    default:
                        /* All possible values are included here above. */
                        break;
                } /* switch( pxICMPHeader_IPv6->ucTypeOfMessage ) */
            }     /* if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED ) */
        }
        else
        {
            /* Malformed ICMPv6 packet, release the network buffer (performed
             * in prvProcessEthernetPacket)*/
        }

        return eReleaseBuffer;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Send out a Neighbour Advertisement message.
 *
 * @param[in] pxEndPoint The end-point to use.
 */
/* MISRA Ref 8.9.1 [File scoped variables] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-89 */
/* coverity[misra_c_2012_rule_8_9_violation] */
/* coverity[single_use] */
    void FreeRTOS_OutputAdvertiseIPv6( NetworkEndPoint_t * pxEndPoint )
    {
        NetworkBufferDescriptor_t * pxNetworkBuffer;
        ICMPPacket_IPv6_t * pxICMPPacket;
        NetworkInterface_t * pxInterface;
        ICMPHeader_IPv6_t * pxICMPHeader_IPv6;
        size_t uxICMPSize;
        size_t uxPacketSize;

        uxPacketSize = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t );

        /* This is called from the context of the IP event task, so a block time
         * must not be used. */
        pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxPacketSize, ndDONT_BLOCK );

        if( pxNetworkBuffer != NULL )
        {
            ( void ) memset( pxNetworkBuffer->xIPAddress.xIP_IPv6.ucBytes, 0, ipSIZE_OF_IPv6_ADDRESS );
            pxNetworkBuffer->pxEndPoint = pxEndPoint;

            pxInterface = pxEndPoint->pxNetworkInterface;

            configASSERT( pxInterface != NULL );

            /* MISRA Ref 11.3.1 [Misaligned access] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            pxICMPPacket = ( ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
            pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( pxICMPPacket->xICMPHeaderIPv6 ) );

            ( void ) memcpy( pxICMPPacket->xEthernetHeader.xDestinationAddress.ucBytes, pcLOCAL_ALL_NODES_MULTICAST_MAC, ipMAC_ADDRESS_LENGTH_BYTES );
            ( void ) memcpy( pxICMPPacket->xEthernetHeader.xSourceAddress.ucBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
            pxICMPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE; /* 12 + 2 = 14 */

            pxICMPPacket->xIPHeader.ucVersionTrafficClass = 0x60;
            pxICMPPacket->xIPHeader.ucTrafficClassFlow = 0;
            pxICMPPacket->xIPHeader.usFlowLabel = 0;

            pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( sizeof( ICMPHeader_IPv6_t ) );
            pxICMPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
            pxICMPPacket->xIPHeader.ucHopLimit = ndHOP_LIMIT;
            ( void ) memcpy( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
            ( void ) memcpy( pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes, pcLOCAL_ALL_NODES_MULTICAST_IP, ipSIZE_OF_IPv6_ADDRESS );

            uxICMPSize = sizeof( ICMPHeader_IPv6_t );
            pxICMPHeader_IPv6->ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
            pxICMPHeader_IPv6->ucTypeOfService = 0;
            /* RFC 4861 section 7.2.6: an unsolicited advertisement must have S=0. */
            pxICMPHeader_IPv6->ulReserved = ndICMPv6_FLAG_OVERRIDE;
            pxICMPHeader_IPv6->ulReserved = FreeRTOS_htonl( pxICMPHeader_IPv6->ulReserved );

            /* Type of option. */
            pxICMPHeader_IPv6->ucOptionType = ndICMP_TARGET_LINK_LAYER_ADDRESS;
            /* Length of option in units of 8 bytes. */
            pxICMPHeader_IPv6->ucOptionLength = 1;
            ( void ) memcpy( pxICMPHeader_IPv6->ucOptionBytes, pxEndPoint->xMACAddress.ucBytes, sizeof( MACAddress_t ) );
            pxICMPPacket->xIPHeader.ucHopLimit = ndHOP_LIMIT;
            ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, sizeof( pxICMPHeader_IPv6->xIPv6Address.ucBytes ) );

            /* Important: tell NIC driver how many bytes must be sent */
            pxNetworkBuffer->xDataLength = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );

            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
            {
                /* calculate the ICMPv6 checksum for outgoing package */
                ( void ) usGenerateProtocolChecksum( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE );
            }
            #else
            {
                /* Many EMAC peripherals will only calculate the ICMP checksum
                 * correctly if the field is nulled beforehand. */
                pxICMPHeader_IPv6->usChecksum = 0;
            }
            #endif

            /* Set the parameter 'bReleaseAfterSend'. */
            ( void ) pxInterface->pfOutput( pxInterface, pxNetworkBuffer, pdTRUE );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Create an IPv16 address, based on a prefix.
 *
 * @param[out] pxIPAddress The location where the new IPv6 address will be stored.
 * @param[in] pxPrefix The prefix to be used.
 * @param[in] uxPrefixLength The length of the prefix.
 * @param[in] xDoRandom A non-zero value if the bits after the prefix should have a random value.
 *
 * @return pdPASS if the operation was successful. Or pdFAIL in case xApplicationGetRandomNumber()
 *         returned an error.
 */
    BaseType_t FreeRTOS_CreateIPv6Address( IPv6_Address_t * pxIPAddress,
                                           const IPv6_Address_t * pxPrefix,
                                           size_t uxPrefixLength,
                                           BaseType_t xDoRandom )
    {
        uint32_t pulRandom[ 4 ];
        uint8_t * pucSource;
        BaseType_t xIndex, xResult = pdPASS;

        if( xDoRandom != pdFALSE )
        {
            /* Create an IP-address, based on a net prefix and a
             * random host address.
             * ARRAY_SIZE_X() returns the size of an array as a
             * signed value ( BaseType_t ).
             */
            for( xIndex = 0; xIndex < ARRAY_SIZE_X( pulRandom ); xIndex++ )
            {
                if( xApplicationGetRandomNumber( &( pulRandom[ xIndex ] ) ) == pdFAIL )
                {
                    xResult = pdFAIL;
                    break;
                }
            }
        }
        else
        {
            ( void ) memset( pulRandom, 0, sizeof( pulRandom ) );
        }

        if( xResult == pdPASS )
        {
            size_t uxIndex;
            /* A loopback IP-address has a prefix of 128. */
            configASSERT( ( uxPrefixLength > 0U ) && ( uxPrefixLength <= ( 8U * ipSIZE_OF_IPv6_ADDRESS ) ) );

            if( ( uxPrefixLength == 0U ) || ( uxPrefixLength > ( 8U * ipSIZE_OF_IPv6_ADDRESS ) ) ) /* LCOV_EXCL_BR_LINE - preceding configASSERT aborts first */
            {
                FreeRTOS_printf( ( "Invalid prefix length %u\n",
                                   ( unsigned ) uxPrefixLength ) );
                xResult = pdFAIL;
            }
            else if( uxPrefixLength >= 8U )
            {
                ( void ) memcpy( pxIPAddress->ucBytes, pxPrefix->ucBytes, ( uxPrefixLength + 7U ) / 8U );
            }
            else
            {
                /* No bytes to copy for prefix lengths less than 8. */
                FreeRTOS_printf( ( "Prefix length %u < 8, no full bytes to copy\n",
                                   ( unsigned ) uxPrefixLength ) );
            }

            if( xResult == pdPASS ) /* LCOV_EXCL_BR_LINE - false side only via configASSERT-guarded pdFAIL above */
            {
                pucSource = ( uint8_t * ) pulRandom;
                uxIndex = uxPrefixLength / 8U;

                /*
                 * When uxPrefixLength is 128, uxIndex is calculated as 128 / 8 = 16,
                 * which is past the end of the 16-byte ucBytes array (valid indices 0-15).
                 * Add bounds check before writing to ucBytes[uxIndex] in the partial-byte
                 * prefix block.
                 */
                if( ( ( uxPrefixLength % 8U ) != 0U ) && ( uxIndex < ipSIZE_OF_IPv6_ADDRESS ) ) /* LCOV_EXCL_BR_LINE - uxIndex>=16 requires prefix>=128, which forces %8==0 */
                {
                    /* uxHostLen is between 1 and 7 bits long. */
                    size_t uxHostLen = 8U - ( uxPrefixLength % 8U );
                    uint32_t uxHostMask = ( ( ( uint32_t ) 1U ) << uxHostLen ) - 1U;
                    uint8_t ucNetMask = ( uint8_t ) ~( uxHostMask );

                    pxIPAddress->ucBytes[ uxIndex ] &= ucNetMask;
                    pxIPAddress->ucBytes[ uxIndex ] |= ( pucSource[ 0 ] & ( ( uint8_t ) uxHostMask ) );
                    pucSource = &( pucSource[ 1 ] );
                    uxIndex++;
                }

                if( uxIndex < ipSIZE_OF_IPv6_ADDRESS )
                {
                    ( void ) memcpy( &( pxIPAddress->ucBytes[ uxIndex ] ), pucSource, ipSIZE_OF_IPv6_ADDRESS - uxIndex );
                }
            }
        }

        return xResult;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Check whether a packet needs ND resolution if it is on local subnet. If required send an ND Solicitation.
 *
 * @param[in] pxNetworkBuffer The network buffer with the packet to be checked.
 *
 * @return pdTRUE if the packet needs ND resolution, pdFALSE otherwise.
 */
    BaseType_t xCheckRequiresNDResolution( const NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        BaseType_t xNeedsNDResolution = pdFALSE;

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        IPPacket_IPv6_t * pxIPPacket = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
        IPHeader_IPv6_t * pxIPHeader = &( pxIPPacket->xIPHeader );
        IPv6_Address_t * pxIPAddress = &( pxIPHeader->xSourceAddress );
        uint8_t ucNextHeader = pxIPHeader->ucNextHeader;

        configASSERT( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE );

        if( ( ucNextHeader == ipPROTOCOL_TCP ) ||
            ( ucNextHeader == ipPROTOCOL_UDP ) )
        {
            IPv6_Type_t eType = xIPv6_GetIPType( ( const IPv6_Address_t * ) pxIPAddress );
            FreeRTOS_debug_printf( ( "xCheckRequiresNDResolution: %pip type %s\n",
                                     ( void * ) pxIPAddress->ucBytes,
                                     ( eType == eIPv6_Global ) ? "Global" :
                                     ( eType == eIPv6_LinkLocal ) ? "LinkLocal" :
                                     ( eType == eIPv6_Loopback ) ? "Loopback" :
                                     "other" ) );

            /* Only an on-link neighbour can be resolved, and a global one must be
             * covered since nothing else now learns its MAC-address. */
            if( ( eType == eIPv6_LinkLocal ) ||
                ( ( eType == eIPv6_Global ) && ( prvIsAddressOnLink( pxIPAddress ) != pdFALSE ) ) )
            {
                MACAddress_t xMACAddress;
                NetworkEndPoint_t * pxEndPoint;
                eResolutionLookupResult_t eResult;
                char pcName[ 80 ];

                ( void ) memset( &( pcName ), 0, sizeof( pcName ) );
                eResult = eNDGetCacheEntry( pxIPAddress, &xMACAddress, &pxEndPoint );
                FreeRTOS_printf( ( "xCheckRequiresNDResolution: eResult %s with EP %s\n",
                                   ( eResult == eResolutionCacheMiss ) ? "Miss" :
                                   ( eResult == eResolutionCacheHit ) ? "Hit" : "Error",
                                   pcEndpointName( pxEndPoint, pcName, sizeof pcName ) ) );

                if( eResult == eResolutionCacheMiss )
                {
                    NetworkBufferDescriptor_t * pxTempBuffer;
                    size_t uxNeededSize;

                    uxNeededSize = sizeof( ICMPPacket_IPv6_t );
                    pxTempBuffer = pxGetNetworkBufferWithDescriptor( uxNeededSize, 0U );

                    if( pxTempBuffer != NULL )
                    {
                        pxTempBuffer->pxEndPoint = pxNetworkBuffer->pxEndPoint;
                        pxTempBuffer->pxInterface = pxNetworkBuffer->pxInterface;
                        vNDSendNeighbourSolicitation( pxTempBuffer, pxIPAddress );
                    }
                    else
                    {
                        FreeRTOS_printf( ( "xCheckRequiresNDResolution: Buffer creation failed\n" ) );
                    }

                    xNeedsNDResolution = pdTRUE;
                }
            }
        }

        return xNeedsNDResolution;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Return a human-readable name for an ND cache entry state.
 *
 * @param[in] eState The ND state to describe.
 *
 * @return A pointer to a constant string describing the state.
 */
    const char * pcNDStateName( eNDState_t eState )
    {
        static char pcSpace[ 24 ];
        const char * pcReturn;

        switch( eState )
        {
            case eND_FREE:
                pcReturn = "Free";
                break; /* Entry is not used */

            case eND_INCOMPLETE:
                pcReturn = "Incomplete";
                break; /* Address resolution in progress (NS sent, no NA yet) */

            case eND_REACHABLE:
                pcReturn = "Reachable";
                break; /* Positive confirmation received (NA with S=1) */

            case eND_STALE:
                pcReturn = "Stale";
                break; /* MAC is known, but reachability is unknown */

            case eND_DELAY:
                pcReturn = "Delay";
                break; /* Packet sent to STALE neighbor; waiting for reachability confirmation */

            case eND_PROBE:
                pcReturn = "Probe";
                break; /* Unicast NS is being sent to confirm reachability */

            default:
                pcReturn = pcSpace;
                snprintf( pcSpace, sizeof pcSpace, "State %u", ( unsigned ) eState );
        }

        return pcReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Return a human-readable name for a Neighbour Advertisement action.
 *
 * @param[in] eState The action to describe.
 *
 * @return A pointer to a constant string describing the action.
 */
    const char * pcNDActionName( eNaAction_t eState )
    {
        static char pcSpace[ 24 ];
        const char * pcReturn;

        switch( eState )
        {
            case eNA_DROP:
                pcReturn = "Drop";
                break; /* Invalid packet or error. */

            case eNA_UPDATE_REACHABLE:
                pcReturn = "Update_Reachable";
                break; /* Update MAC and set state to REACHABLE. */

            case eNA_UPDATE_STALE:
                pcReturn = "Update_Stale";
                break; /* Update MAC and set state to STALE. */

            case eNA_CONFIRM_REACHABLE:
                pcReturn = "Confirm_Reachable";
                break; /* Do not change MAC, but set state to REACHABLE. */

            case eNA_REJECT_MAC_SET_STALE:
                pcReturn = "Reject_Mac_Set_Stale";
                break; /* Keep the cached MAC, demote the entry to STALE. */

            case eNA_REJECT_MAC_PROBE:
                pcReturn = "Reject_Mac_Probe";
                break; /* Keep the cached MAC and verify it with NUD. */

            case eNA_MAINTAIN:
                pcReturn = "Maintain";
                break; /* Entry remains in its current state (likely STALE). */

            default:
                pcReturn = pcSpace;
                snprintf( pcSpace, sizeof pcSpace, "State %u", ( unsigned ) eState );
        }

        return pcReturn;
    }
/*-----------------------------------------------------------*/

#endif /* ipconfigUSE_IPv6 != 0 ) */
