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

#ifndef FREERTOS_ROUTING_IPV4_H
    #define FREERTOS_ROUTING_IPV4_H

    #ifdef __cplusplus
        extern "C" {
    #endif

    #if ( ipconfigUSE_DHCP != 0 )
        #include "FreeRTOS_DHCP.h"
    #endif

struct xNetworkInterface;

/** @brief The network settings for IPv4. */
    typedef struct xIPV4Parameters
    {
        uint32_t ulIPAddress;                                                /**< The actual IPv4 address. Will be 0 as long as end-point is still down. */
        uint32_t ulNetMask;                                                  /**< The netmask. */
        uint32_t ulGatewayAddress;                                           /**< The IP-address of the gateway. */
        uint32_t ulDNSServerAddresses[ ipconfigENDPOINT_DNS_ADDRESS_COUNT ]; /**< IP-addresses of DNS servers. */
        uint32_t ulBroadcastAddress;                                         /**< The local broadcast address, e.g. '192.168.1.255'. */
        uint8_t ucDNSIndex;                                                  /**< The index of the next DNS address to be used. */
    } IPV4Parameters_t;

/** @brief The description of an end-point. */
    typedef struct xNetworkEndPoint_IPv4
    {
        
        struct
        {
            IPV4Parameters_t ipv4_settings; /**< Actual IPv4 settings used by the end-point. */
            IPV4Parameters_t ipv4_defaults; /**< Use values form "ipv4_defaults" in case DHCP has failed. */
        };
        struct
        {
            uint32_t
                bIsDefault : 1, /**< This bit will be removed. */
            #if ( ipconfigUSE_DHCP != 0 )
                bWantDHCP : 1,  /**< This end-point wants to use DHCPv4 to obtain an IP-address. */
            #endif /* ipconfigUSE_DHCP */
            #if ( ipconfigUSE_NETWORK_EVENT_HOOK != 0 )
                bCallDownHook : 1, /**< The network down hook-must be called for this end-point. */
            #endif /* ipconfigUSE_NETWORK_EVENT_HOOK */
            bEndPointUp : 1;       /**< The end-point is up. */
        } bits;                    /**< A collection of boolean properties. */
        #if ( ipconfigUSE_DHCP != 0 )
            IPTimer_t xDHCP_RATimer; /**<  The timer used to call the DHCP/DHCPv6/RA state machine. */
            DHCPData_t xDHCPData; /**< A description of the DHCP client state machine. */
        #endif /* ( ipconfigUSE_DHCP != 0 )  */
        struct xNetworkInterface * pxNetworkInterface; /**< The network interface that owns this end-point. */
        struct xNetworkEndPoint_IPv4 * pxNext;        /**< The next end-point in the chain. */
    } NetworkEndPoint_IPv4_t;

    /** @brief A list of all network end-points.  Each element has a next pointer. */
    extern struct xNetworkEndPoint_IPv4* pxNetworkEndPoints_IPv4;
/*
 * Get the first end-point belonging to a given interface.  When pxInterface is
 * NULL, the very first end-point will be returned.
 */
    NetworkEndPoint_IPv4_t* FreeRTOS_FirstEndPoint_IPv4( NetworkInterface_t * pxInterface);

/*
 * Get the next end-point.  When pxInterface is null, all end-points can be
 * iterated.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_NextEndPoint_IPv4(NetworkInterface_t* pxInterface, NetworkEndPoint_IPv4_t * pxEndPoint );

/*
 * Find the end-point with given IP-address.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_FindEndPointOnIP_IPv4( uint32_t ulIPAddress,
                                                        uint32_t ulWhere );

/*
 * Find the end-point with given MAC-address.
 * The search can be limited by supplying a particular interface.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_FindEndPointOnMAC_IPv4( const MACAddress_t * pxMACAddress );

/*
 * Find the best fitting end-point to reach a given IP-address.
 * Find an end-point whose IP-address is in the same network as the IP-address provided.
 * 'ulWhere' is temporary and or debugging only.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_FindEndPointOnNetMask_IPv4( uint32_t ulIPAddress,
                                                        uint32_t ulWhere );

/*
 * Find the best fitting end-point to reach a given IP-address on a given interface
 * 'ulWhere' is temporary and or debugging only.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_InterfaceEndPointOnNetMask_IPv4( uint32_t ulIPAddress,
                                                             uint32_t ulWhere );

 
/* Find an end-point that has a defined gateway.
 * xIPType should equal ipTYPE_IPv4 or ipTYPE_IPv6. */
    NetworkEndPoint_IPv4_t * FreeRTOS_FindGateWay_IPv4( BaseType_t xIPType );

/* Fill-in the end-point structure. */
    void FreeRTOS_FillEndPoint_IPv4( struct NetworkInterface_t * pxNetworkInterface,
                                NetworkEndPoint_IPv4_t * pxEndPoint,
                                const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                                const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ],
                                const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                                const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                                const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] );

    
    #if ( ipconfigHAS_ROUTING_STATISTICS == 1 )
/** @brief Some simple network statistics. */
        typedef struct xRoutingStats_IPv4
        {
            UBaseType_t ulOnIp;             /**< The number of times 'FreeRTOS_FindEndPointOnIP_IPv4()' has been called. */
            UBaseType_t ulOnMAC;            /**< The number of times 'FreeRTOS_FindEndPointOnMAC()' has been called. */
            UBaseType_t ulOnNetMask;        /**< The number of times 'FreeRTOS_InterfaceEndPointOnNetMask()' has been called. */
            UBaseType_t ulMatching;         /**< The number of times 'FreeRTOS_MatchingEndpoint()' has been called. */
            UBaseType_t ulLocations[ 14 ];  /**< The number of times 'FreeRTOS_InterfaceEndPointOnNetMask()' has been called from a particular location. */
            UBaseType_t ulLocationsIP[ 8 ]; /**< The number of times 'FreeRTOS_FindEndPointOnIP_IPv4()' has been called from a particular location. */
        } RoutingStats_IPv4_t;

        extern RoutingStats_IPv4_t xRoutingStatistics;
    #endif /* ( ipconfigHAS_ROUTING_STATISTICS == 1 ) */

    NetworkEndPoint_IPv4_t * pxGetSocketEndPoint_IPv4( Socket_t xSocket );
    void vSetSocketEndPoint_IPv4( Socket_t xSocket,
                             NetworkEndPoint_IPv4_t * pxEndPoint );

    #ifdef __cplusplus
        } /* extern "C" */
    #endif

#endif /* FREERTOS_ROUTING_H */
