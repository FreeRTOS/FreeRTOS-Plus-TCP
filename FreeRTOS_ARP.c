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

/**
 * @file FreeRTOS_ARP.c
 * @brief Implements the Address Resolution Protocol for the FreeRTOS+TCP network stack.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#if ( ipconfigUSE_LLMNR == 1 )
    #include "FreeRTOS_DNS.h"
#endif /* ipconfigUSE_LLMNR */
#include "NetworkBufferManagement.h"
#include "FreeRTOS_Routing.h"
#if ( ipconfigUSE_IPv6 != 0 )
    #include "FreeRTOS_ND.h"
#endif

/** @brief When the age of an entry in the ARP table reaches this value (it counts down
 * to zero, so this is an old entry) an ARP request will be sent to see if the
 * entry is still valid and can therefore be refreshed. */
#define arpMAX_ARP_AGE_BEFORE_NEW_ARP_REQUEST    ( 3 )

/** @brief The time between gratuitous ARPs. */
#ifndef arpGRATUITOUS_ARP_PERIOD
    #define arpGRATUITOUS_ARP_PERIOD    ( pdMS_TO_TICKS( 20000U ) )
#endif

/*-----------------------------------------------------------*/

/*
 * Lookup an MAC address in the ARP cache from the IP address.
 */
static eARPLookupResult_t prvCacheLookup( uint32_t ulAddressToLookup,
                                          MACAddress_t * const pxMACAddress,
                                          NetworkEndPoint_t ** ppxEndPoint );

/*-----------------------------------------------------------*/

/** @brief The ARP cache. */
_static ARPCacheRow_t xARPCache[ ipconfigARP_CACHE_ENTRIES ];

/** @brief  The time at which the last gratuitous ARP was sent.  Gratuitous ARPs are used
 * to ensure ARP tables are up to date and to detect IP address conflicts. */
static TickType_t xLastGratuitousARPTime = ( TickType_t ) 0;

/*
 * IP-clash detection is currently only used internally. When DHCP doesn't respond, the
 * driver can try out a random LinkLayer IP address (169.254.x.x).  It will send out a
 * gratuitous ARP message and, after a period of time, check the variables here below:
 */
#if ( ipconfigARP_USE_CLASH_DETECTION != 0 )
    /* Becomes non-zero if another device responded to a gratuitous ARP message. */
    BaseType_t xARPHadIPClash;
    /* MAC-address of the other device containing the same IP-address. */
    MACAddress_t xARPClashMacAddress;
#endif /* ipconfigARP_USE_CLASH_DETECTION */

/*-----------------------------------------------------------*/

/**
 * @brief Process the ARP packets.
 *
 * @param[in] pxNetworkBuffer: The Ethernet packet.
 *
 * @return An enum which says whether to return the frame or to release it.
 */
eFrameProcessingResult_t eARPProcessPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    ARPPacket_t * const pxARPFrame = ipPOINTER_CAST( ARPPacket_t * const, pxNetworkBuffer->pucEthernetBuffer );
    eFrameProcessingResult_t eReturn = eReleaseBuffer;
    ARPHeader_t * pxARPHeader = &( pxARPFrame->xARPHeader );
    uint32_t ulTargetProtocolAddress, ulSenderProtocolAddress;
/* memcpy() helper variables for MISRA Rule 21.15 compliance*/
    const void * pvCopySource;
    void * pvCopyDest;
    NetworkEndPoint_t * pxTargetEndPoint = pxNetworkBuffer->pxEndPoint;

    #if ( ipconfigARP_USE_CLASH_DETECTION != 0 )
        NetworkEndPoint_t * pxSourceEndPoint;
    #endif

    /* The field ulSenderProtocolAddress is badly aligned, copy byte-by-byte. */

    /*
     * Use helper variables for memcpy() to remain
     * compliant with MISRA Rule 21.15.  These should be
     * optimized away.
     */
    pvCopySource = pxARPHeader->ucSenderProtocolAddress;
    pvCopyDest = &ulSenderProtocolAddress;
    ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( ulSenderProtocolAddress ) );
    /* The field ulTargetProtocolAddress is well-aligned, a 32-bits copy. */
    ulTargetProtocolAddress = pxARPHeader->ulTargetProtocolAddress;

    #if ( ipconfigARP_USE_CLASH_DETECTION != 0 )
        {
            pxSourceEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( ulSenderProtocolAddress, 2 ); /* Clash detection. */
        }
    #endif

    traceARP_PACKET_RECEIVED();

    /* Some extra logging while still testing. */
    if( pxARPHeader->usOperation == ( uint16_t ) ipARP_REQUEST )
    {
        /*if( ulSenderProtocolAddress != ulTargetProtocolAddress ) */
        {
            if( pxTargetEndPoint != NULL )
            {
                FreeRTOS_debug_printf( ( "ipARP_REQUEST from %lxip to %lxip end-point %lxip\n",
                                         FreeRTOS_ntohl( ulSenderProtocolAddress ),
                                         FreeRTOS_ntohl( ulTargetProtocolAddress ),
                                         FreeRTOS_ntohl( ( pxTargetEndPoint != NULL ) ? pxTargetEndPoint->ipv4_settings.ulIPAddress : 0UL ) ) );
            }
        }
    }
    else if( pxARPHeader->usOperation == ( uint16_t ) ipARP_REPLY )
    {
        FreeRTOS_printf( ( "ipARP_REPLY from %lxip to %lxip end-point %lxip\n",
                           FreeRTOS_ntohl( ulSenderProtocolAddress ),
                           FreeRTOS_ntohl( ulTargetProtocolAddress ),
                           FreeRTOS_ntohl( ( pxTargetEndPoint != NULL ) ? pxTargetEndPoint->ipv4_settings.ulIPAddress : 0UL ) ) );
    }
    else
    {
        /* Unexpected ARP type. */
    }

    if( ( pxTargetEndPoint != NULL ) && ( pxTargetEndPoint->bits.bEndPointUp != pdFALSE_UNSIGNED ) )
    {
        switch( pxARPHeader->usOperation )
        {
            case ipARP_REQUEST:

                /* The packet contained an ARP request.  Was it for the IP
                 * address of one of the end-points? */
                if( pxTargetEndPoint != NULL )
                {
                    iptraceSENDING_ARP_REPLY( ulSenderProtocolAddress );

                    /* The request is for the address of this node.  Add the
                     * entry into the ARP cache, or refresh the entry if it
                     * already exists. */
                    vARPRefreshCacheEntry( &( pxARPHeader->xSenderHardwareAddress ), ulSenderProtocolAddress, pxTargetEndPoint );

                    /* Generate a reply payload in the same buffer. */
                    pxARPHeader->usOperation = ( uint16_t ) ipARP_REPLY;

                    if( ulTargetProtocolAddress == ulSenderProtocolAddress )
                    {
                        /* A double IP address is detected! */
                        /* Give the sources MAC address the value of the broadcast address, will be swapped later */

                        /*
                         * Use helper variables for memcpy() to remain
                         * compliant with MISRA Rule 21.15.  These should be
                         * optimized away.
                         */
                        pvCopySource = xBroadcastMACAddress.ucBytes;
                        pvCopyDest = pxARPFrame->xEthernetHeader.xSourceAddress.ucBytes;
                        ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( xBroadcastMACAddress ) );

                        ( void ) memset( pxARPHeader->xTargetHardwareAddress.ucBytes, 0, sizeof( MACAddress_t ) );
                        pxARPHeader->ulTargetProtocolAddress = 0UL;
                    }
                    else
                    {
                        /*
                         * Use helper variables for memcpy() to remain
                         * compliant with MISRA Rule 21.15.  These should be
                         * optimized away.
                         */
                        pvCopySource = pxARPHeader->xSenderHardwareAddress.ucBytes;
                        pvCopyDest = pxARPHeader->xTargetHardwareAddress.ucBytes;
                        ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( MACAddress_t ) );
                        pxARPHeader->ulTargetProtocolAddress = ulSenderProtocolAddress;
                    }

                    /*
                     * Use helper variables for memcpy() to remain
                     * compliant with MISRA Rule 21.15.  These should be
                     * optimized away.
                     */
                    pvCopySource = pxTargetEndPoint->xMACAddress.ucBytes;
                    pvCopyDest = pxARPHeader->xSenderHardwareAddress.ucBytes;
                    ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( MACAddress_t ) );
                    pvCopySource = &( pxTargetEndPoint->ipv4_settings.ulIPAddress );
                    pvCopyDest = pxARPHeader->ucSenderProtocolAddress;
                    ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( pxARPHeader->ucSenderProtocolAddress ) );

                    eReturn = eReturnEthernetFrame;
                }

                break;

            case ipARP_REPLY:
                iptracePROCESSING_RECEIVED_ARP_REPLY( ulTargetProtocolAddress );
                vARPRefreshCacheEntry( &( pxARPHeader->xSenderHardwareAddress ), ulSenderProtocolAddress, pxTargetEndPoint );
                /* Process received ARP frame to see if there is a clash. */
                #if ( ipconfigARP_USE_CLASH_DETECTION != 0 )
                    {
                        if( pxSourceEndPoint != NULL )
                        {
                            xARPHadIPClash = pdTRUE;
                            /* Remember the MAC-address of the other device which has the same IP-address. */
                            ( void ) memcpy( xARPClashMacAddress.ucBytes, pxARPHeader->xSenderHardwareAddress.ucBytes, sizeof( xARPClashMacAddress.ucBytes ) );
                        }
                    }
                #endif /* ipconfigARP_USE_CLASH_DETECTION */
                break;

            default:
                /* Invalid. */
                break;
        }
    }

    return eReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_ARP_REMOVE_ENTRY != 0 )

/**
 * @brief Remove an ARP cache entry that matches with .pxMACAddress.
 *
 * @param[in] pxMACAddress: Pointer to the MAC address whose entry shall
 *                          be removed..
 * @return When the entry was found and remove: the IP-address, otherwise zero.
 */
    uint32_t ulARPRemoveCacheEntryByMac( const MACAddress_t * pxMACAddress )
    {
        BaseType_t x;
        uint32_t lResult = 0;

        configASSERT( pxMACAddress != NULL );

        /* For each entry in the ARP cache table. */
        for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
        {
            if( ( memcmp( xARPCache[ x ].xMACAddress.ucBytes, pxMACAddress->ucBytes, sizeof( pxMACAddress->ucBytes ) ) == 0 ) )
            {
                lResult = xARPCache[ x ].ulIPAddress;
                ( void ) memset( &xARPCache[ x ], 0, sizeof( xARPCache[ x ] ) );
                break;
            }
        }

        return lResult;
    }

#endif /* ipconfigUSE_ARP_REMOVE_ENTRY != 0 */
/*-----------------------------------------------------------*/

/**
 * @brief Add/update the ARP cache entry MAC-address to IP-address mapping.
 *
 * @param[in] pxMACAddress: Pointer to the MAC address whose mapping is being
 *                          updated.
 * @param[in] ulIPAddress: 32-bit representation of the IP-address whose mapping
 *                         is being updated.
 * @param[in] pxEndPoint: The end-point stored in the table.
 */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                            const uint32_t ulIPAddress,
                            struct xNetworkEndPoint * pxEndPoint )
{
    BaseType_t x = 0;
    BaseType_t xIpEntry = -1;
    BaseType_t xMacEntry = -1;
    BaseType_t xUseEntry = 0;
    uint8_t ucMinAgeFound = 0U;

    #if ( ipconfigARP_STORES_REMOTE_ADDRESSES != 0 )
        BaseType_t xAddressIsLocal = ( BaseType_t ) -1;
    #endif

    #if ( ipconfigARP_STORES_REMOTE_ADDRESSES == 0 )

        /* Only process the IP address if it matches with one of the end-points,
         * or as long as not all end-points are up. */
        if( ( FreeRTOS_FindEndPointOnNetMask( ulIPAddress, 1 ) != NULL ) || /* Refresh ARP cache. */
            ( FreeRTOS_AllEndPointsUp( NULL ) == pdFALSE ) )                /*lint !e9007 side effects on right hand of logical operator, ''||'' [MISRA 2012 Rule 13.5, required]. */
    #else

        /* If ipconfigARP_STORES_REMOTE_ADDRESSES is non-zero, IP addresses with
         * a different netmask will also be stored.  After when replying to a UDP
         * message from a different netmask, the IP address can be looped up and a
         * reply sent.  This option is useful for systems with multiple gateways,
         * the reply will surely arrive.  If ipconfigARP_STORES_REMOTE_ADDRESSES is
         * zero the the gateway address is the only option. */

        /* 506: (Warning -- Constant value Boolean [MISRA 2012 Rule 2.1, required]) */
        /* 774: (Info -- Boolean within 'if' always evaluates to True [MISRA 2012 Rule 14.3, required]) */

        if( pdTRUE ) /*lint !e774 !e506*/
    #endif /* if ( ipconfigARP_STORES_REMOTE_ADDRESSES == 0 ) */
    {
        /* Start with the maximum possible number. */
        ucMinAgeFound--;

        /* For each entry in the ARP cache table. */
        for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
        {
            BaseType_t xMatchingMAC;

            if( pxMACAddress != NULL )
            {
                if( memcmp( xARPCache[ x ].xMACAddress.ucBytes, pxMACAddress->ucBytes, sizeof( pxMACAddress->ucBytes ) ) == 0 )
                {
                    xMatchingMAC = pdTRUE;
                }
                else
                {
                    xMatchingMAC = pdFALSE;
                }
            }
            else
            {
                xMatchingMAC = pdFALSE;
            }

            /* Does this line in the cache table hold an entry for the IP
             * address	being queried? */
            if( xARPCache[ x ].ulIPAddress == ulIPAddress )
            {
                if( pxMACAddress == NULL )
                {
                    /* In case the parameter pxMACAddress is NULL, an entry will be reserved to
                     * indicate that there is an outstanding ARP request, This entry will have
                     * "ucValid == pdFALSE". */
                    xIpEntry = x;
                    break;
                }

                /* See if the MAC-address also matches. */
                if( xMatchingMAC != pdFALSE )
                {
                    /* This function will be called for each received packet
                     * As this is by far the most common path the coding standard
                     * is relaxed in this case and a return is permitted as an
                     * optimisation. */
                    xARPCache[ x ].ucAge = ( uint8_t ) ipconfigMAX_ARP_AGE;
                    xARPCache[ x ].ucValid = ( uint8_t ) pdTRUE;
                    xARPCache[ x ].pxEndPoint = pxEndPoint;
                    return;
                }

                /* Found an entry containing ulIPAddress, but the MAC address
                 * doesn't match.  Might be an entry with ucValid=pdFALSE, waiting
                 * for an ARP reply.  Still want to see if there is match with the
                 * given MAC address.ucBytes.  If found, either of the two entries
                 * must be cleared. */
                xIpEntry = x;
            }
            else if( xMatchingMAC != pdFALSE )
            {
                /* Found an entry with the given MAC-address, but the IP-address
                 * is different.  Continue looping to find a possible match with
                 * ulIPAddress. */
                #if ( ipconfigARP_STORES_REMOTE_ADDRESSES != 0 )
                    {
                        /* If ARP stores the MAC address of IP addresses outside the
                         * network, than the MAC address of the gateway should not be
                         * overwritten. */
                        BaseType_t xOtherIsLocal = FreeRTOS_FindEndPointOnNetMask( xARPCache[ x ].ulIPAddress, 3 ) != NULL; /* ARP remote address. */

                        if( xAddressIsLocal < ( BaseType_t ) 0 )
                        {
                            /* Only look-up the address when needed. */
                            xAddressIsLocal = FreeRTOS_FindEndPointOnNetMask( ulIPAddress, 2 ) != NULL; /* ARP remote address. */
                        }

                        if( xAddressIsLocal == xOtherIsLocal )
                        {
                            xMacEntry = x;
                        }
                    }
                #else /* if ( ipconfigARP_STORES_REMOTE_ADDRESSES != 0 ) */
                    {
                        xMacEntry = x;
                    }
                #endif /* if ( ipconfigARP_STORES_REMOTE_ADDRESSES != 0 ) */
            }

            /* _HT_
             * Shouldn't we test for xARPCache[ x ].ucValid == pdFALSE here ? */
            else if( xARPCache[ x ].ucAge < ucMinAgeFound )
            {
                /* As the table is traversed, remember the table row that
                 * contains the oldest entry (the lowest age count, as ages are
                 * decremented to zero) so the row can be re-used if this function
                 * needs to add an entry that does not already exist. */
                ucMinAgeFound = xARPCache[ x ].ucAge;
                xUseEntry = x;
            }
            else
            {
                /* Nothing happens to this cache entry for now. */
            }
        }

        if( xMacEntry >= 0 )
        {
            xUseEntry = xMacEntry;

            if( xIpEntry >= 0 )
            {
                /* Both the MAC address as well as the IP address were found in
                 * different locations: clear the entry which matches the
                 * IP-address */
                ( void ) memset( &( xARPCache[ xIpEntry ] ), 0, sizeof( ARPCacheRow_t ) );
            }
        }
        else if( xIpEntry >= 0 )
        {
            /* An entry containing the IP-address was found, but it had a different MAC address */
            xUseEntry = xIpEntry;
        }
        else
        {
            /* No matching entry found. */
        }

        /* If the entry was not found, we use the oldest entry and set the IPaddress */
        xARPCache[ xUseEntry ].ulIPAddress = ulIPAddress;

        if( pxMACAddress != NULL )
        {
            ( void ) memcpy( xARPCache[ xUseEntry ].xMACAddress.ucBytes, pxMACAddress->ucBytes, sizeof( pxMACAddress->ucBytes ) );

            iptraceARP_TABLE_ENTRY_CREATED( ulIPAddress, ( *pxMACAddress ) );
            /* And this entry does not need immediate attention */
            xARPCache[ xUseEntry ].ucAge = ( uint8_t ) ipconfigMAX_ARP_AGE;
            xARPCache[ xUseEntry ].ucValid = ( uint8_t ) pdTRUE;
            xARPCache[ xUseEntry ].pxEndPoint = pxEndPoint;
        }
        else if( xIpEntry < 0 )
        {
            xARPCache[ xUseEntry ].ucAge = ( uint8_t ) ipconfigMAX_ARP_RETRANSMISSIONS;
            xARPCache[ xUseEntry ].ucValid = ( uint8_t ) pdFALSE;
        }
        else
        {
            /* Nothing will be stored. */
        }
    }
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_ARP_REVERSED_LOOKUP == 1 )

/**
 * @brief Retrieve an entry from the cache table
 *
 * @param[in] pxMACAddress: The MAC-address of the entry of interest.
 * @param[out] pulIPAddress: set to the IP-address found, or unchanged when not found.
 *
 * @return Either eARPCacheMiss or eARPCacheHit.
 */
    eARPLookupResult_t eARPGetCacheEntryByMac( MACAddress_t * const pxMACAddress,
                                               uint32_t * pulIPAddress )
    {
        BaseType_t x;
        eARPLookupResult_t eReturn = eARPCacheMiss;

        configASSERT( pxMACAddress != NULL );
        configASSERT( pulIPAddress != NULL );

        /* Loop through each entry in the ARP cache. */
        for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
        {
            /* Does this row in the ARP cache table hold an entry for the MAC
             * address being searched? */
            if( memcmp( pxMACAddress->ucBytes, xARPCache[ x ].xMACAddress.ucBytes, sizeof( MACAddress_t ) ) == 0 )
            {
                *pulIPAddress = xARPCache[ x ].ulIPAddress;
                eReturn = eARPCacheHit;
                break;
            }
        }

        return eReturn;
    }
#endif /* ipconfigUSE_ARP_REVERSED_LOOKUP */

/*-----------------------------------------------------------*/

/**
 * @brief Look for ulIPAddress in the ARP cache.
 *
 * @param[in,out] pulIPAddress: Pointer to the IP-address to be queried to the ARP cache.
 * @param[in,out] pxMACAddress: Pointer to a MACAddress_t variable where the MAC address
 *                          will be stored, if found.
 * @param[in,out] ppxEndPoint: a pointer to a pointer where the end-point will be stored.
 *
 * @return If the IP address exists, copy the associated MAC address into pxMACAddress,
 *         refresh the ARP cache entry's age, and return eARPCacheHit. If the IP
 *         address does not exist in the ARP cache return eARPCacheMiss. If the packet
 *         cannot be sent for any reason (maybe DHCP is still in process, or the
 *         addressing needs a gateway but there isn't a gateway defined) then return
 *         eCantSendPacket.
 */
eARPLookupResult_t eARPGetCacheEntry( uint32_t * pulIPAddress,
                                      MACAddress_t * const pxMACAddress,
                                      struct xNetworkEndPoint ** ppxEndPoint )
{
    eARPLookupResult_t eReturn;
    uint32_t ulAddressToLookup;
    NetworkEndPoint_t * pxEndPoint = NULL;

    configASSERT( ppxEndPoint != NULL );
    configASSERT( pulIPAddress != NULL );

    *( ppxEndPoint ) = NULL;
    ulAddressToLookup = *pulIPAddress;

    if( ( *pulIPAddress == 0x70040120U ) || ( *pulIPAddress == 0x80feU ) )
    {
        FreeRTOS_printf( ( "eARPGetCacheEntry %lxip\n", FreeRTOS_ntohl( *pulIPAddress ) ) );
    }

    #if ( ipconfigUSE_LLMNR == 1 )
        if( ulAddressToLookup == ipLLMNR_IP_ADDR ) /* Is in network byte order. */
        {
            /* The LLMNR IP-address has a fixed virtual MAC address. */
            ( void ) memcpy( pxMACAddress->ucBytes, xLLMNR_MacAdress.ucBytes, sizeof( MACAddress_t ) );
            eReturn = eARPCacheHit;
        }
        else
    #endif

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( ulAddressToLookup, 0 );

    if( pxEndPoint != NULL ) /* ARP lookup loop-back? */
    {
        /* Targeted at this device? Make sure that xNetworkInterfaceOutput()
         * in NetworkInterface.c calls xCheckLoopback(). */
        *( ppxEndPoint ) = pxEndPoint;
        ( void ) memcpy( pxMACAddress->ucBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
        eReturn = eARPCacheHit;
    }
    else
    if( ( FreeRTOS_ntohl( ulAddressToLookup ) & 0xffuL ) == 0xffuL )
    {
        /* This is a broadcast so it uses the broadcast MAC address. */
        ( void ) memcpy( pxMACAddress->ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );
        pxEndPoint = FreeRTOS_FindEndPointOnNetMask( ulAddressToLookup, 4 );

        if( pxEndPoint != NULL )
        {
            *( ppxEndPoint ) = pxEndPoint;
        }

        eReturn = eARPCacheHit;
    }
    else
    {
        /* It is assumed that devices with the same netmask are on the same
         * LAN and don't need a gateway. */
        pxEndPoint = FreeRTOS_FindEndPointOnNetMask( ulAddressToLookup, 4 );
        eReturn = eARPCacheMiss;

        if( pxEndPoint == NULL ) /*lint !e774 Boolean within 'if' always evaluates to True [MISRA 2012 Rule 14.3, required]. */
        {
            /* No matching end-point is found, look for a gateway. */
            #if ( ipconfigARP_STORES_REMOTE_ADDRESSES == 1 )
                eReturn = prvCacheLookup( ulAddressToLookup, pxMACAddress, ppxEndPoint );

                if( eReturn == eARPCacheHit )
                {
                    /* The stack is configured to store 'remote IP addresses', i.e. addresses
                     * belonging to a different the netmask.  prvCacheLookup() returned a hit, so
                     * the MAC address is known. */
                }
                else
            #endif
            {
                /* The IP address is off the local network, so look up the
                 * hardware address of the router, if any. */
                *( ppxEndPoint ) = FreeRTOS_FindGateWay( ( BaseType_t ) ipTYPE_IPv4 );

                if( *( ppxEndPoint ) != NULL )
                {
                    /* 'ipv4_settings' can be accessed safely, because 'ipTYPE_IPv4' was provided. */
                    ulAddressToLookup = ( *ppxEndPoint )->ipv4_settings.ulGatewayAddress;
                }
                else
                {
                    ulAddressToLookup = *pulIPAddress;
                }

                FreeRTOS_printf( ( "Using gateway %lxip\n", FreeRTOS_ntohl( ulAddressToLookup ) ) );
            }
        }
        else
        {
            /* The IP address is on the local network, so lookup the requested
             * IP address directly. */
            ulAddressToLookup = *pulIPAddress;
        }

        #if ( ipconfigARP_STORES_REMOTE_ADDRESSES == 1 )
            if( eReturn == eARPCacheMiss )
        #endif
        {
            if( ulAddressToLookup == 0UL )
            {
                /* The address is not on the local network, and there is not a
                 * router. */
                eReturn = eCantSendPacket;
            }
            else
            {
                eReturn = prvCacheLookup( ulAddressToLookup, pxMACAddress, ppxEndPoint );

                FreeRTOS_printf( ( "ARP %s using %lxip\n", ( eReturn == eARPCacheHit ) ? "hit" : "miss", FreeRTOS_ntohl( ulAddressToLookup ) ) );
                /* It might be that the ARP has to go to the gateway. */
                *pulIPAddress = ulAddressToLookup;
            }
        }
    }

    return eReturn;
}

/*-----------------------------------------------------------*/

/**
 * @brief Lookup an IP address in the ARP cache.
 *
 * @param[in] ulAddressToLookup: The 32-bit representation of an IP address to
 *                               lookup.
 * @param[out] pxMACAddress: A pointer to MACAddress_t variable where, if there
 *                          is an ARP cache hit, the MAC address corresponding to
 *                          the IP address will be stored.
 * @param[in,out] ppxEndPoint: a pointer to the end-point will be stored.
 *
 * @return When the IP-address is found: eARPCacheHit, when not found: eARPCacheMiss,
 *         and when waiting for a ARP reply: eCantSendPacket.
 */
static eARPLookupResult_t prvCacheLookup( uint32_t ulAddressToLookup,
                                          MACAddress_t * const pxMACAddress,
                                          NetworkEndPoint_t ** ppxEndPoint )
{
    BaseType_t x;
    eARPLookupResult_t eReturn = eARPCacheMiss;

    /* Loop through each entry in the ARP cache. */
    for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        /* Does this row in the ARP cache table hold an entry for the IP address
         * being queried? */
        if( xARPCache[ x ].ulIPAddress == ulAddressToLookup )
        {
            /* A matching valid entry was found. */
            if( xARPCache[ x ].ucValid == ( uint8_t ) pdFALSE )
            {
                /* This entry is waiting an ARP reply, so is not valid. */
                eReturn = eCantSendPacket;
            }
            else
            {
                /* A valid entry was found. */
                ( void ) memcpy( pxMACAddress->ucBytes, xARPCache[ x ].xMACAddress.ucBytes, sizeof( MACAddress_t ) );
                /* ppxEndPoint != NULL was tested in the only caller eARPGetCacheEntry(). */
                *( ppxEndPoint ) = xARPCache[ x ].pxEndPoint;
                eReturn = eARPCacheHit;
            }

            break;
        }
    }

    return eReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief A call to this function will update (or 'Age') the ARP cache entries.
 *        The function will also try to prevent a removal of entry by sending
 *        an ARP query. It will also check whether we are waiting on an ARP
 *        reply - if we are, then an ARP request will be re-sent.
 *        In case an ARP entry has 'Aged' to 0, it will be removed from the ARP
 *        cache.
 */
void vARPAgeCache( void )
{
    BaseType_t x;
    TickType_t xTimeNow;

    /* Loop through each entry in the ARP cache. */
    for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
    {
        /* If the entry is valid (its age is greater than zero). */
        if( xARPCache[ x ].ucAge > 0U )
        {
            /* Decrement the age value of the entry in this ARP cache table row.
             * When the age reaches zero it is no longer considered valid. */
            ( xARPCache[ x ].ucAge )--;

            /* If the entry is not yet valid, then it is waiting an ARP
             * reply, and the ARP request should be retransmitted. */
            if( xARPCache[ x ].ucValid == ( uint8_t ) pdFALSE )
            {
                FreeRTOS_OutputARPRequest( xARPCache[ x ].ulIPAddress );
            }
            else if( xARPCache[ x ].ucAge <= ( uint8_t ) arpMAX_ARP_AGE_BEFORE_NEW_ARP_REQUEST )
            {
                /* This entry will get removed soon.  See if the MAC address is
                 * still valid to prevent this happening. */
                iptraceARP_TABLE_ENTRY_WILL_EXPIRE( xARPCache[ x ].ulIPAddress );
                FreeRTOS_OutputARPRequest( xARPCache[ x ].ulIPAddress );
            }
            else
            {
                /* The age has just ticked down, with nothing to do. */
            }

            if( xARPCache[ x ].ucAge == 0U )
            {
                /* The entry is no longer valid.  Wipe it out. */
                iptraceARP_TABLE_ENTRY_EXPIRED( xARPCache[ x ].ulIPAddress );
                xARPCache[ x ].ulIPAddress = 0UL;
            }
        }
    }

    xTimeNow = xTaskGetTickCount();

    if( ( xLastGratuitousARPTime == ( TickType_t ) 0 ) || ( ( xTimeNow - xLastGratuitousARPTime ) > ( TickType_t ) arpGRATUITOUS_ARP_PERIOD ) )
    {
        NetworkEndPoint_t * pxEndPoint = pxNetworkEndPoints;

        while( pxEndPoint != NULL )
        {
            if( ( pxEndPoint->bits.bEndPointUp != pdFALSE_UNSIGNED ) && ( pxEndPoint->ipv4_settings.ulIPAddress != 0UL ) )
            {
                #if ( ipconfigUSE_IPv6 != 0 )
                    if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
                    {
                        FreeRTOS_OutputAdvertiseIPv6( pxEndPoint );
                    }
                #endif

                if( pxEndPoint->ipv4_settings.ulIPAddress != 0UL )
                {
                    FreeRTOS_OutputARPRequest( pxEndPoint->ipv4_settings.ulIPAddress );
                }
            }

            pxEndPoint = pxEndPoint->pxNext;
        }

        xLastGratuitousARPTime = xTimeNow;
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Send a Gratuitous ARP packet to allow this node to announce the IP-MAC
 *        mapping to the entire network.
 */
void vARPSendGratuitous( void )
{
    /* Setting xLastGratuitousARPTime to 0 will force a gratuitous ARP the next
     * time vARPAgeCache() is called. */
    xLastGratuitousARPTime = ( TickType_t ) 0;

    /* Let the IP-task call vARPAgeCache(). */
    ( void ) xSendEventToIPTask( eARPTimerEvent );
}

/*-----------------------------------------------------------*/

/**
 * @brief Create and send an ARP request packet.
 *
 * @param[in] ulIPAddress: A 32-bit representation of the IP-address whose
 *                         physical (MAC) address is required.
 */
void FreeRTOS_OutputARPRequest( uint32_t ulIPAddress )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    NetworkInterface_t * pxInterface;

    for( pxInterface = FreeRTOS_FirstNetworkInterface();
         pxInterface != NULL;
         pxInterface = FreeRTOS_NextNetworkInterface( pxInterface ) )
    {
        pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( ulIPAddress, 25 );

        if( pxEndPoint == NULL )
        {
            pxEndPoint = FreeRTOS_InterfaceEndPointOnNetMask( pxInterface, ulIPAddress, 26 );
        }

/*
 *      {
 *          FreeRTOS_printf( ( "OutputARPRequest: remote IP = %lxip end-point = %lxip\n",
 *              FreeRTOS_ntohl( ulIPAddress ),
 *              FreeRTOS_ntohl( pxEndPoint != 0 ? pxEndPoint->ipv4_settings.ulIPAddress : 0x0UL ) ) );
 *      }
 */
        if( pxEndPoint != NULL )
        {
            /* This is called from the context of the IP event task, so a block time
             * must not be used. */
            pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( sizeof( ARPPacket_t ), ( TickType_t ) 0U );

            if( pxNetworkBuffer != NULL )
            {
                pxNetworkBuffer->ulIPAddress = ulIPAddress;
                pxNetworkBuffer->pxEndPoint = pxEndPoint;

                vARPGenerateRequestPacket( pxNetworkBuffer );

                #if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES )
                    {
                        if( pxNetworkBuffer->xDataLength < ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES )
                        {
                            BaseType_t xIndex;

                            /*					FreeRTOS_printf( ( "OutputARPRequest: length %lu -> %lu\n", */
                            /*						pxNetworkBuffer->xDataLength, ipconfigETHERNET_MINIMUM_PACKET_BYTES ) ); */
                            for( xIndex = ( BaseType_t ) pxNetworkBuffer->xDataLength; xIndex < ( BaseType_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES; xIndex++ )
                            {
                                pxNetworkBuffer->pucEthernetBuffer[ xIndex ] = 0U;
                            }

                            pxNetworkBuffer->xDataLength = ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES;
                        }
                    }
                #endif /* if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES ) */

                if( xIsCallingFromIPTask() != 0 )
                {
                    iptraceNETWORK_INTERFACE_OUTPUT( pxNetworkBuffer->xDataLength, pxNetworkBuffer->pucEthernetBuffer );
                    /* Only the IP-task is allowed to call this function directly. */
                    ( void ) pxInterface->pfOutput( pxInterface, pxNetworkBuffer, pdTRUE );
                }
                else
                {
                    IPStackEvent_t xSendEvent;

                    /* Send a message to the IP-task to send this ARP packet. */
                    xSendEvent.eEventType = eNetworkTxEvent;
                    xSendEvent.pvData = pxNetworkBuffer;

                    if( xSendEventStructToIPTask( &xSendEvent, ( TickType_t ) portMAX_DELAY ) == pdFAIL )
                    {
                        /* Failed to send the message, so release the network buffer. */
                        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
                    }
                }
            }
        }
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief  Wait for address resolution: look-up the IP-address in the ARP-cache, and if
 *         needed send an ARP request, and wait for a reply.  This function is useful when
 *         called before FreeRTOS_sendto().
 *
 * @param[in] ulIPAddress: The IP-address to look-up.
 * @param[in] uxTicksToWait: The maximum number of clock ticks to wait for a reply.
 *
 * @return Zero when successful.
 */
BaseType_t xARPWaitResolution( uint32_t ulIPAddress,
                               TickType_t uxTicksToWait )
{
    BaseType_t xResult = -pdFREERTOS_ERRNO_EADDRNOTAVAIL;
    TimeOut_t xTimeOut;
    MACAddress_t xMACAddress;
    eARPLookupResult_t xLookupResult;
    NetworkEndPoint_t * pxEndPoint;

    xLookupResult = eARPGetCacheEntry( &( ulIPAddress ), &( xMACAddress ), &( pxEndPoint ) );

    if( xLookupResult == eARPCacheMiss )
    {
        const TickType_t uxSleepTime = pdMS_TO_TICKS( 10U );

        /* We might use ipconfigMAX_ARP_RETRANSMISSIONS here. */
        FreeRTOS_OutputARPRequest( ulIPAddress );
        vTaskSetTimeOutState( &xTimeOut );

        for( ; ; )
        {
            xLookupResult = eARPGetCacheEntry( &( ulIPAddress ), &( xMACAddress ), &( pxEndPoint ) );

            if( ( xTaskCheckForTimeOut( &( xTimeOut ), &( uxTicksToWait ) ) == pdTRUE ) ||
                ( xLookupResult != eARPCacheMiss ) )
            {
                break;
            }

            vTaskDelay( uxSleepTime );
        }
    }

    if( xLookupResult == eARPCacheHit )
    {
        xResult = 0;
    }

    return xResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Generate an ARP request packet by copying various constant details to
 *        the buffer.
 *
 * @param[in,out] pxNetworkBuffer: Pointer to the buffer which has to be filled with
 *                             the ARP request packet details.
 */
void vARPGenerateRequestPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
/* Part of the Ethernet and ARP headers are always constant when sending an IPv4
 * ARP packet.  This array defines the constant parts, allowing this part of the
 * packet to be filled in using a simple memcpy() instead of individual writes. */
    static const uint8_t xDefaultPartARPPacketHeader[] =
    {
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, /* Ethernet destination address. */
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, /* Ethernet source address. */
        0x08, 0x06,                         /* Ethernet frame type (ipARP_FRAME_TYPE). */
        0x00, 0x01,                         /* usHardwareType (ipARP_HARDWARE_TYPE_ETHERNET). */
        0x08, 0x00,                         /* usProtocolType. */
        ipMAC_ADDRESS_LENGTH_BYTES,         /* ucHardwareAddressLength. */
        ipIP_ADDRESS_LENGTH_BYTES,          /* ucProtocolAddressLength. */
        0x00, 0x01,                         /* usOperation (ipARP_REQUEST). */
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, /* xSenderHardwareAddress. */
        0x00, 0x00, 0x00, 0x00,             /* ulSenderProtocolAddress. */
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00  /* xTargetHardwareAddress. */
    };

    ARPPacket_t * pxARPPacket;

/* memcpy() helper variables for MISRA Rule 21.15 compliance*/
    const void * pvCopySource;
    void * pvCopyDest;

    /* Buffer allocation ensures that buffers always have space
     * for an ARP packet. See buffer allocation implementations 1
     * and 2 under portable/BufferManagement. */
    configASSERT( pxNetworkBuffer != NULL );
    configASSERT( pxNetworkBuffer->xDataLength >= sizeof( ARPPacket_t ) );

    pxARPPacket = ipCAST_PTR_TO_TYPE_PTR( ARPPacket_t, pxNetworkBuffer->pucEthernetBuffer );

    /* memcpy the const part of the header information into the correct
     * location in the packet.  This copies:
     * xEthernetHeader.ulDestinationAddress
     * xEthernetHeader.usFrameType;
     * xARPHeader.usHardwareType;
     * xARPHeader.usProtocolType;
     * xARPHeader.ucHardwareAddressLength;
     * xARPHeader.ucProtocolAddressLength;
     * xARPHeader.usOperation;
     * xARPHeader.xTargetHardwareAddress;
     */
    configASSERT( pxNetworkBuffer->pxEndPoint != NULL );

    /*
     * Use helper variables for memcpy() to remain
     * compliant with MISRA Rule 21.15.  These should be
     * optimized away.
     */
    pvCopySource = xDefaultPartARPPacketHeader;
    pvCopyDest = pxNetworkBuffer->pucEthernetBuffer;
    ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( xDefaultPartARPPacketHeader ) );

    pvCopySource = pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes;
    pvCopyDest = pxARPPacket->xEthernetHeader.xSourceAddress.ucBytes;
    ( void ) memcpy( pvCopyDest, pvCopySource, ipMAC_ADDRESS_LENGTH_BYTES );

    pvCopySource = pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes;
    pvCopyDest = pxARPPacket->xARPHeader.xSenderHardwareAddress.ucBytes;
    ( void ) memcpy( pvCopyDest, pvCopySource, ipMAC_ADDRESS_LENGTH_BYTES );

    pvCopySource = &( pxNetworkBuffer->pxEndPoint->ipv4_settings.ulIPAddress );
    pvCopyDest = pxARPPacket->xARPHeader.ucSenderProtocolAddress;
    ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( pxARPPacket->xARPHeader.ucSenderProtocolAddress ) );
    pxARPPacket->xARPHeader.ulTargetProtocolAddress = pxNetworkBuffer->ulIPAddress;

    pxNetworkBuffer->xDataLength = sizeof( ARPPacket_t );

    iptraceCREATING_ARP_REQUEST( pxNetworkBuffer->ulIPAddress );
}
/*-----------------------------------------------------------*/

/**
 * @brief A call to this function will clear the ARP cache.
 * @param[in] pxEndPoint: only clean entries with this end-point, or when NULL,
 *                        clear the entire ARP cache.
 */
void FreeRTOS_ClearARP( const struct xNetworkEndPoint * pxEndPoint )
{
    if( pxEndPoint != NULL )
    {
        BaseType_t x;

        for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
        {
            if( xARPCache[ x ].pxEndPoint == pxEndPoint )
            {
                ( void ) memset( &( xARPCache[ x ] ), 0, sizeof( ARPCacheRow_t ) );
            }
        }
    }
    else
    {
        ( void ) memset( xARPCache, 0, sizeof( xARPCache ) );
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief  This function will check if the target IP-address belongs to this device.
 *         If so, the packet will be passed to the IP-stack, who will answer it.
 *         The function is to be called within the function xNetworkInterfaceOutput().
 *
 * @param[in] pxDescriptor: The network buffer which is to be checked for loop-back.
 * @param[in] bReleaseAfterSend: pdTRUE: Driver is allowed to transfer ownership of descriptor.
 *                              pdFALSE: Driver is not allowed to take ownership of descriptor,
 *                                       make a copy of it.
 *
 * @return pdTRUE/pdFALSE: There is/isn't a loopback address in the packet.
 */
BaseType_t xCheckLoopback( NetworkBufferDescriptor_t * const pxDescriptor,
                           BaseType_t bReleaseAfterSend )
{
    BaseType_t xResult = pdFALSE;
    NetworkBufferDescriptor_t * pxUseDescriptor = pxDescriptor;
    const IPPacket_t * pxIPPacket = ipCAST_PTR_TO_TYPE_PTR( IPPacket_t, pxUseDescriptor->pucEthernetBuffer );

    /* This function will check if the target IP-address belongs to this device.
     * If so, the packet will be passed to the IP-stack, who will answer it.
     * The function is to be called within the function xNetworkInterfaceOutput().
     */

    if( pxIPPacket->xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE )
    {
        NetworkEndPoint_t * pxEndPoint;

        pxEndPoint = FreeRTOS_FindEndPointOnMAC( &( pxIPPacket->xEthernetHeader.xDestinationAddress ), NULL );

        if( pxEndPoint != NULL )
        {
            xResult = pdTRUE;

            if( bReleaseAfterSend == pdFALSE )
            {
                /* Driver is not allowed to transfer the ownership
                 * of descriptor,  so make a copy of it */
                NetworkBufferDescriptor_t * pxNewDescriptor =
                    pxDuplicateNetworkBufferWithDescriptor( pxUseDescriptor, pxUseDescriptor->xDataLength );
                *( ( NetworkBufferDescriptor_t ** ) &pxUseDescriptor ) = pxNewDescriptor;
            }

            if( pxUseDescriptor != NULL )
            {
                IPStackEvent_t xRxEvent;

                pxUseDescriptor->pxInterface = pxEndPoint->pxNetworkInterface;
                pxUseDescriptor->pxEndPoint = pxEndPoint;

                xRxEvent.eEventType = eNetworkRxEvent;
                xRxEvent.pvData = pxUseDescriptor;

                if( xSendEventStructToIPTask( &xRxEvent, 0U ) != pdTRUE )
                {
                    vReleaseNetworkBufferAndDescriptor( pxUseDescriptor );
                    iptraceETHERNET_RX_EVENT_LOST();
                    FreeRTOS_printf( ( "prvEMACRxPoll: Can not queue return packet!\n" ) );
                }
            }
        }
    }

    return xResult;
}
/*-----------------------------------------------------------*/

#if ( ipconfigHAS_PRINTF != 0 ) || ( ipconfigHAS_DEBUG_PRINTF != 0 )

    void FreeRTOS_PrintARPCache( void )
    {
        BaseType_t x, xCount = 0;

        /* Loop through each entry in the ARP cache. */
        for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
        {
            if( ( xARPCache[ x ].ulIPAddress != 0UL ) && ( xARPCache[ x ].ucAge > ( uint8_t ) 0U ) )
            {
                /* See if the MAC-address also matches, and we're all happy */
                FreeRTOS_printf( ( "Arp %2ld: %3u - %16lxip : %02x:%02x:%02x : %02x:%02x:%02x\n",
                                   x,
                                   xARPCache[ x ].ucAge,
                                   xARPCache[ x ].ulIPAddress,
                                   xARPCache[ x ].xMACAddress.ucBytes[ 0 ],
                                   xARPCache[ x ].xMACAddress.ucBytes[ 1 ],
                                   xARPCache[ x ].xMACAddress.ucBytes[ 2 ],
                                   xARPCache[ x ].xMACAddress.ucBytes[ 3 ],
                                   xARPCache[ x ].xMACAddress.ucBytes[ 4 ],
                                   xARPCache[ x ].xMACAddress.ucBytes[ 5 ] ) );
                xCount++;
            }
        }

        FreeRTOS_printf( ( "Arp has %ld entries\n", xCount ) );
    }

#endif /* ( ipconfigHAS_PRINTF != 0 ) || ( ipconfigHAS_DEBUG_PRINTF != 0 ) */
