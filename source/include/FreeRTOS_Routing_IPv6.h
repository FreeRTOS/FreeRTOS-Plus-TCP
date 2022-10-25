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

#ifndef FREERTOS_ROUTING_H
#define FREERTOS_ROUTING_H

#ifdef __cplusplus
    extern "C" {
#endif

#define ipconfigUSE_IPv6 1

#if ( ipconfigUSE_IPv6 != 0 )
    #include "FreeRTOS_DHCPv6.h"


/** @brief The network settings for IPv6. */

    typedef struct xIPV6Parameters
        {
            IPv6_Address_t xIPAddress;      /* The actual IPv4 address. Will be 0 as long as end-point is still down. */
            size_t uxPrefixLength;          /* Number of valid bytes in the network prefix. */
            IPv6_Address_t xPrefix;         /* The network prefix, e.g. fe80::/10 */
            IPv6_Address_t xGatewayAddress; /* Gateway to the web. */
            IPv6_Address_t xDNSServerAddresses[ ipconfigENDPOINT_DNS_ADDRESS_COUNT ];
            uint8_t ucDNSIndex;             /**< The index of the next DNS address to be used. */
        } IPV6Parameters_t;

    #if ( ipconfigUSE_RA != 0 )
/* Router Advertisement (RA). End-points can obtain their IP-address by asking for a RA. */
        typedef enum xRAState
        {
            eRAStateApply,    /* Send a Router Solicitation. */
            eRAStateWait,     /* Wait for a Router Advertisement. */
            eRAStateIPTest,   /* Take a random IP address, test if another device is using it already. */
            eRAStateIPWait,   /* Wait for a reply, if any */
            eRAStatePreLease, /* The device is ready to go to the 'eRAStateLease' state. */
            eRAStateLease,    /* The device is up, repeat the RA-process when timer expires. */
            eRAStateFailed,
        } eRAState_t;

        struct xRA_DATA
        {
            struct
            {
                uint32_t
                    bRouterReplied : 1,
                    bIPAddressInUse : 1;
            }
            bits;
            TickType_t ulPreferredLifeTime;
            UBaseType_t uxRetryCount;
            /* Maintains the RA state machine state. */
            eRAState_t eRAState;
        };

        typedef struct xRA_DATA RAData_t;
    #endif /* ( ipconfigUSE_RA != 0 ) */

/** @brief The description of an end-point. */
    typedef struct xNetworkEndPoint_IPv6
    {
        struct
        {
            IPV6Parameters_t ipv6_settings; /**< Actual IPv6 settings used by the end-point. */
            IPV6Parameters_t ipv6_defaults; /**< Use values form "ipv6_defaults" in case DHCP has failed. */
        };
            
        MACAddress_t xMACAddress; /**< The MAC-address assigned to this end-point. */
        struct
        {
            uint32_t
                bIsDefault : 1, /**< This bit will be removed. */
            #if ( ipconfigUSE_DHCPv6 != 0 )
                bWantDHCP : 1,  /**< This end-point wants to use DHCPv4 to obtain an IP-address. */
            #endif /* ipconfigUSE_DHCP */
            #if ( ipconfigUSE_RA != 0 )
                bWantRA : 1, /**< This end-point wants to use RA/SLAAC to obtain an IP-address. */
            #endif /* ipconfigUSE_RA */
                bIPv6 : 1, /**< This end-point has an IP-address of type IPv6. */
            #if ( ipconfigUSE_NETWORK_EVENT_HOOK != 0 )
                bCallDownHook : 1, /**< The network down hook-must be called for this end-point. */
            #endif /* ipconfigUSE_NETWORK_EVENT_HOOK */
            bEndPointUp : 1;       /**< The end-point is up. */
        } bits;                    /**< A collection of boolean properties. */
            uint8_t usDNSType;     /**< A LLMNR/mDNS lookup is being done for an IPv6 address.
                                    * This field is only valid while xApplicationDNSQueryHook() is called. */
        #if ( ipconfigUSE_RA != 0 )
            IPTimer_t xDHCP_RATimer; /**<  The timer used to call the DHCP/DHCPv6/RA state machine. */
            RAData_t xRAData;                    /**< A description of the Router Advertisement ( RA ) client state machine. */
        #endif /* ( ipconfigUSE_DHCP != 0 ) || ( ipconfigUSE_RA != 0 ) */
        #if ( ipconfigUSE_DHCPv6 != 0 )
            DHCPData_t xDHCPData; /**< A description of the DHCP client state machine. */
        #endif /* ( ipconfigUSE_DHCP != 0 ) || ( ipconfigUSE_DHCPv6 != 0 ) */
            DHCPMessage_IPv6_t * pxDHCPMessage; /**< A description of the DHCPv6 client state machine. */
        
        NetworkInterface_t * pxNetworkInterface; /**< The network interface that owns this end-point. */
        struct xNetworkEndPoint_IPv6 * pxNext;        /**< The next end-point in the chain. */
    } NetworkEndPoint_IPv6_t;


        #define END_POINT_USES_DHCP( pxEndPoint )    ( ( ( pxEndPoint ) != NULL ) && ( ( pxEndPoint )->bits.bWantDHCP != pdFALSE_UNSIGNED ) )
        #define END_POINT_USES_RA( pxEndPoint )      ( ( ( pxEndPoint ) != NULL ) && ( ( pxEndPoint )->bits.bIPv6 != pdFALSE_UNSIGNED ) && ( ( pxEndPoint )->bits.bWantRA != pdFALSE_UNSIGNED ) )

        #define ENDPOINT_IS_IPv4( pxEndPoint )       ( ( ( pxEndPoint ) != NULL ) && ( ( pxEndPoint )->bits.bIPv6 == 0U ) )
        #define ENDPOINT_IS_IPv6( pxEndPoint )       ( ( ( pxEndPoint ) != NULL ) && ( ( pxEndPoint )->bits.bIPv6 != 0U ) )


/*
 * Get the first end-point belonging to a given interface.  When pxInterface is
 * NULL, the very first end-point will be returned.
 */
    NetworkEndPoint_IPv6_t * FreeRTOS_FirstEndPoint_IPv6( NetworkInterface_t * pxInterface );

/*
 * Get the next end-point.  When pxInterface is null, all end-points can be
 * iterated.
 */
    NetworkEndPoint_IPv6_t * FreeRTOS_NextEndPoint_IPv6( NetworkInterface_t * pxInterface,
                                               NetworkEndPoint_IPv6_t * pxEndPoint );

/*
 * Find the end-point with given IP-address.
 */
    NetworkEndPoint_IPv6_t * FreeRTOS_FindEndPointOnIP_IPv6( const IPv6_Address_t * pxIPAddress );

/*
 * Find the end-point with given MAC-address.
 * The search can be limited by supplying a particular interface.
 */
    NetworkEndPoint_IPv6_t * FreeRTOS_FindEndPointOnMAC_IPv6( const MACAddress_t * pxMACAddress,
                                                    NetworkInterface_t * pxInterface );

/*
 * Find the best fitting end-point to reach a given IP-address.
 */
    NetworkEndPoint_t * FreeRTOS_FindEndPointOnNetMask_IPv6( const IPv6_Address_t * pxIPv6Address );
    

/* A ethernet packet has come in on a certain network interface.
 * Find the best matching end-point. */
    NetworkEndPoint_IPv6_t * FreeRTOS_MatchingEndPoint_IPv6( NetworkInterface_t * pxNetworkInterface,
                                                   uint8_t * pucEthernetBuffer );

/* Find an end-point that has a defined gateway.
 * xIPType should equal ipTYPE_IPv4 or ipTYPE_IPv6. */
    NetworkEndPoint_IPv6_t * FreeRTOS_FindGateWay_IPv6( BaseType_t xIPType );

/* Fill-in the end-point structure. */
    void FreeRTOS_FillEndPoint_IPv6( NetworkInterface_t * pxNetworkInterface,
                                         NetworkEndPoint_t * pxEndPoint,
                                         IPv6_Address_t * pxIPAddress,
                                         IPv6_Address_t * pxNetPrefix,
                                         size_t uxPrefixLength,
                                         IPv6_Address_t * pxGatewayAddress,
                                         IPv6_Address_t * pxDNSServerAddress, /* Not used yet. */
                                         const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] );

    #if ( ipconfigHAS_ROUTING_STATISTICS == 1 )
/** @brief Some simple network statistics. */
        typedef struct xRoutingStats_IPv6
        {
            UBaseType_t ulOnIp;             /**< The number of times 'FreeRTOS_FindEndPointOnIP_IPv4()' has been called. */
            UBaseType_t ulOnMAC;            /**< The number of times 'FreeRTOS_FindEndPointOnMAC()' has been called. */
            UBaseType_t ulOnNetMask;        /**< The number of times 'FreeRTOS_InterfaceEndPointOnNetMask()' has been called. */
            UBaseType_t ulMatching;         /**< The number of times 'FreeRTOS_MatchingEndpoint()' has been called. */
            UBaseType_t ulLocations[ 14 ];  /**< The number of times 'FreeRTOS_InterfaceEndPointOnNetMask()' has been called from a particular location. */
            UBaseType_t ulLocationsIP[ 8 ]; /**< The number of times 'FreeRTOS_FindEndPointOnIP_IPv4()' has been called from a particular location. */
        } RoutingStats_IPv6_t;

        extern RoutingStats_t xRoutingStatistics;
    #endif /* ( ipconfigHAS_ROUTING_STATISTICS == 1 ) */

    NetworkEndPoint_IPv6_t * pxGetSocketEndPoint_IPv6( Socket_t xSocket );
    void vSetSocketEndPoint_IPv6( Socket_t xSocket,
                             NetworkEndPoint_IPv6_t * pxEndPoint );

#endif /* ( ipconfigUSE_IPv6 != 0 )*/

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* FREERTOS_ROUTING_H */
