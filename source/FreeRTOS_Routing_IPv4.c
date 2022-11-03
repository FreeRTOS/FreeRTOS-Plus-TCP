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
#include "NetworkBufferManagement.h"
#if ( ipconfigUSE_LLMNR == 1 )
    #include "FreeRTOS_DNS.h"
#endif /* ipconfigUSE_LLMNR */
#include "FreeRTOS_Routing.h"

struct xNetworkEndPoint_IPv4* pxNetworkEndPoints_IPv4 = NULL;

/*
 * Add a new IP-address to a Network Interface.  The object pointed to by
 * 'pxEndPoint' and the interface must continue to exist.
 */
static NetworkEndPoint_IPv4_t * FreeRTOS_AddEndPoint_IPv4( NetworkEndPoint_IPv4_t * pxEndPoint );

/*-----------------------------------------------------------*/

/**
 * @brief Configure and install a new IPv4 end-point.
 *
 * @param[in] pxNetworkInterface: The interface to which it belongs.
 * @param[in] pxEndPoint: Space for the new end-point. This memory is dedicated for the
 *                        end-point and should not be freed or get any other purpose.
 * @param[in] pxIPAddress: The IP-address.
 * @param[in] pxNetPrefix: The prefix which shall be used for this end-point.
 * @param[in] uxPrefixLength: The length of the above end-point.
 * @param[in] pxGatewayAddress: The IP-address of a device on the LAN which can serve as
 *                              as a gateway to the Internet.
 * @param[in] pxDNSServerAddress: The IP-address of a DNS server.
 * @param[in] ucMACAddress: The MAC address of the end-point.
 */
void FreeRTOS_FillEndPoint_IPv4( NetworkInterface_t * pxNetworkInterface,
                            NetworkEndPoint_IPv4_t * pxEndPoint,
                            const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                            const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ],
                            const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                            const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                            const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] )
{
    uint32_t ulIPAddress;

    /* Fill in and add an end-point to a network interface.
     * The user must make sure that the object pointed to by 'pxEndPoint'
     * will remain to exist. */
    ( void ) memset( pxEndPoint, 0, sizeof( *pxEndPoint ) );

    /* All is cleared, also the IPv6 flag. */
    /* pxEndPoint->bits.bIPv6 = pdFALSE; */

    ulIPAddress = FreeRTOS_inet_addr_quick( ucIPAddress[ 0 ], ucIPAddress[ 1 ], ucIPAddress[ 2 ], ucIPAddress[ 3 ] );
    pxEndPoint->ipv4_settings.ulNetMask = FreeRTOS_inet_addr_quick( ucNetMask[ 0 ], ucNetMask[ 1 ], ucNetMask[ 2 ], ucNetMask[ 3 ] );
    pxEndPoint->ipv4_settings.ulGatewayAddress = FreeRTOS_inet_addr_quick( ucGatewayAddress[ 0 ], ucGatewayAddress[ 1 ], ucGatewayAddress[ 2 ], ucGatewayAddress[ 3 ] );
    pxEndPoint->ipv4_settings.ulDNSServerAddresses[ 0 ] = FreeRTOS_inet_addr_quick( ucDNSServerAddress[ 0 ], ucDNSServerAddress[ 1 ], ucDNSServerAddress[ 2 ], ucDNSServerAddress[ 3 ] );
    pxEndPoint->ipv4_settings.ulBroadcastAddress = ulIPAddress | ~( pxEndPoint->ipv4_settings.ulNetMask );

    /* Copy the current values to the default values. */
    ( void ) memcpy( &( pxEndPoint->ipv4_defaults ), &( pxEndPoint->ipv4_settings ), sizeof( pxEndPoint->ipv4_defaults ) );

    /* The default IP-address will be used in case DHCP is not used, or also if DHCP has failed, or
     * when the user chooses to use the default IP-address. */
    pxEndPoint->ipv4_defaults.ulIPAddress = ulIPAddress;

    /* The hardware interface the Endpoint is associated with */
    pxEndPoint->pxNetworkInterface = pxNetworkInterface;

    /* The field 'ipv4_settings.ulIPAddress' will be set later on. */

    ( void ) memcpy( pxEndPoint->pxNetworkInterface->xMACAddress.ucBytes, 
                    ucMACAddress, 
                    sizeof( pxEndPoint->pxNetworkInterface->xMACAddress ) );
    ( void ) FreeRTOS_AddEndPoint_IPv4( pxEndPoint );
}
/*-----------------------------------------------------------*/

#if ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 )

    #if ( ipconfigHAS_ROUTING_STATISTICS == 1 )
        RoutingStats_IPv4_t xRoutingStatistics;
    #endif

/*-----------------------------------------------------------*/

/**
 * @brief Add an end-point to a given interface.
 *
 * @param[in] pxInterface: The interface that gets a new end-point.
 * @param[in] pxEndPoint: The end-point to be added.
 *
 * @return The value of the parameter 'pxEndPoint'.
 */
    static NetworkEndPoint_IPv4_t * FreeRTOS_AddEndPoint_IPv4( NetworkEndPoint_IPv4_t * pxEndPoint )
    {
        NetworkEndPoint_IPv4_t * pxIterator = NULL;

        /* This end point will go to the end of the list, so there is no pxNext
         * yet. */
        pxEndPoint->pxNext = NULL;

        if( pxNetworkEndPoints_IPv4 == NULL )
        {
            /* No other end points are defined yet - so this is the first in the
             * list. */
            pxNetworkEndPoints_IPv4 = pxEndPoint;
        }
        else
        {
            /* Other end points are already defined so iterate to the end of the
             * list. */
            pxIterator = pxNetworkEndPoints_IPv4;

            for( ; ; )
            {
                if( pxIterator == pxEndPoint )
                {
                    /* This end-point has already been added to the list. */
                    break;
                }

                if( pxIterator->pxNext == NULL )
                {
                    pxIterator->pxNext = pxEndPoint;
                    break;
                }

                pxIterator = pxIterator->pxNext;
            }
        }

        FreeRTOS_printf( ( "FreeRTOS_AddEndPoint: MAC: %02x-%02x IPv4: %lxip\n",
                               pxEndPoint->pxNetworkInterface->xMACAddress.ucBytes[ 4 ],
                               pxEndPoint->pxNetworkInterface->xMACAddress.ucBytes[ 5 ],
                               FreeRTOS_ntohl( pxEndPoint->ipv4_defaults.ulIPAddress ) ) );

        return pxEndPoint;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find the first end-point bound to a given interface.
 *
 * @param[in] pxInterface: The interface whose first end-point will be returned.
 *
 * @return The first end-point that is found to the interface, or NULL when the
 *         interface doesn't have any end-point yet.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_FirstEndPoint_IPv4( NetworkInterface_t * pxInterface )
    {
        NetworkEndPoint_IPv4_t * pxEndPoint = pxNetworkEndPoints_IPv4;

        /* Find and return the NetworkEndPoint_t structure that is associated with
         * the pxInterface NetworkInterface_t. *//*_RB_ Could this be made a two way link, so the NetworkEndPoint_t can just be read from the NetworkInterface_t structure?  Looks like there is a pointer in the struct already. */
        while( pxEndPoint != NULL )
        {
            if( ( pxInterface == NULL ) || ( pxEndPoint->pxNetworkInterface == pxInterface ) )
            {
                break;
            }

            pxEndPoint = pxEndPoint->pxNext;
        }

        return pxEndPoint;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Get the next end-point.  The parameter 'pxInterface' may be NULL, which means:
 *        don't care which interface the end-point is bound to.
 *
 * @param[in] pxInterface: An interface of interest, or NULL when iterating through all
 *                         end-points.
 * @param[in] pxEndPoint: This is the current end-point.
 *
 * @return The end-point that is found, or NULL when there are no more end-points in the list.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_NextEndPoint_IPv4( NetworkInterface_t * pxInterface, NetworkEndPoint_IPv4_t * pxEndPoint )
    {
        NetworkEndPoint_IPv4_t * pxResult = pxEndPoint;

        if( pxResult != NULL )
        {
            pxResult = pxResult->pxNext;
            while( pxResult != NULL )
            {
                if( ( pxInterface == NULL ) || ( pxResult->pxNetworkInterface == pxInterface ) )
                {
                    break;
                }

                pxResult = pxResult->pxNext;
            }

        }

        return pxResult;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find the end-point which has a given IPv4 address.
 *
 * @param[in] ulIPAddress: The IP-address of interest, or 0 if any IPv4 end-point may be returned.
 *
 * @return The end-point found or NULL.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_FindEndPointOnIP_IPv4( uint32_t ulIPAddress,
                                                        uint32_t ulWhere )
    {
        NetworkEndPoint_IPv4_t * pxEndPoint = pxNetworkEndPoints_IPv4;

        #if ( ipconfigHAS_ROUTING_STATISTICS == 1 )
            uint32_t ulLocationCount = ( uint32_t ) ( sizeof( xRouteingStatistics.ulLocationsIP ) / sizeof( xRoutingStatistics.ulLocationsIP )[ 0 ] );

            xRouteingStatistics.ulOnIp++;

            if( ulWhere < ulLocationCount )
            {
                xRouteingStatistics.ulLocationsIP[ ulWhere ]++;
            }
        #endif /* ( ipconfigHAS_ROUTING_STATISTICS == 1 ) */

        while( pxEndPoint != NULL )
        {
            if( ( ulIPAddress == 0U ) || ( pxEndPoint->ipv4_settings.ulIPAddress == ulIPAddress ) )
                {
                    break;
                }
            pxEndPoint = pxEndPoint->pxNext;
        }
    
        return pxEndPoint;
    }

/*-----------------------------------------------------------*/

/**
 * @brief Find the end-point that has a certain MAC-address.
 *
 * @param[in] pxMACAddress: The Ethernet packet.
 * @param[in] pxInterface: The interface on which the packet was received, or NULL when unknown.
 *
 * @return The end-point that has the given MAC-address.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_FindEndPointOnMAC_IPv4( const MACAddress_t * pxMACAddress)
    {
        NetworkEndPoint_IPv4_t * pxEndPoint = pxNetworkEndPoints_IPv4;

        #if ( ipconfigHAS_ROUTING_STATISTICS == 1 )
            {
                xRouteingStatistics.ulOnMAC++;
            }
        #endif

        /*_RB_ Question - would it be more efficient to store the mac addresses in
         * uin64_t variables for direct comparison instead of using memcmp()?  [don't
         * know if there is a quick way of creating a 64-bit number from the 48-byte
         * MAC address without getting junk in the top 2 bytes]. */

        /* Find the end-point with given MAC-address. */
        while( pxEndPoint != NULL )
        {
            if( memcmp( pxEndPoint->pxNetworkInterface->xMACAddress.ucBytes, pxMACAddress->ucBytes, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
                {
                    break;
                }

            pxEndPoint = pxEndPoint->pxNext;
        }

        return pxEndPoint;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find an end-point that handles a given IPv4-address.
 *
 * @param[in] ulIPAddress: The IP-address for which an end-point is looked-up.
 *
 * @return An end-point that has the same network mask as the given IP-address.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_FindEndPointOnNetMask_IPv4( uint32_t ulIPAddress,
                                                        uint32_t ulWhere )
    {
        /* The 'ulWhere' parameter is only for debugging purposes. */
        return FreeRTOS_InterfaceEndPointOnNetMask_IPv4( NULL, ulIPAddress, ulWhere );
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find an end-point that handles a given IPv4-address.
 *
 * @param[in] pxInterface: Only end-points that have this interface are returned, unless
 *                         pxInterface is NULL.
 * @param[in] ulIPAddress: The IP-address for which an end-point is looked-up.
 *
 * @return An end-point that has the same network mask as the given IP-address.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_InterfaceEndPointOnNetMask_IPv4( NetworkInterface_t * pxInterface,
                                                             uint32_t ulIPAddress,
                                                             uint32_t ulWhere )
    {
        NetworkEndPoint_IPv4_t * pxEndPoint = pxNetworkEndPoints_IPv4;

        #if ( ipconfigHAS_ROUTING_STATISTICS == 1 )
            uint32_t ulLocationCount = ( uint32_t ) ( sizeof( xRouteingStatistics.ulLocations ) / sizeof( xRoutingStatistics.ulLocations )[ 0 ] );

            xRouteingStatistics.ulOnNetMask++;

            if( ulWhere < ulLocationCount )
            {
                xRouteingStatistics.ulLocations[ ulWhere ]++;
            }
        #endif /* ( ipconfigHAS_ROUTING_STATISTICS == 1 ) */

        /* Find the best fitting end-point to reach a given IP-address. */

        /*_RB_ Presumably then a broadcast reply could go out on a different end point to that on
         * which the broadcast was received - although that should not be an issue if the nodes are
         * on the same LAN it could be an issue if the nodes are on separate LAN's. */

        while( pxEndPoint != NULL )
        {
            if( ( ulIPAddress & pxEndPoint->ipv4_settings.ulNetMask ) == ( pxEndPoint->ipv4_settings.ulIPAddress & pxEndPoint->ipv4_settings.ulNetMask ) )
                    {
                        /* Found a match. */
                        break;
                    }
        
            pxEndPoint = pxEndPoint->pxNext;
        }

        /* This was only for debugging. */
        if( ( pxEndPoint == NULL ) && ( ulWhere != 1U ) && ( ulWhere != 2U ) )
        {
            FreeRTOS_printf( ( "FreeRTOS_FindEndPointOnNetMask[%ld]: No match for %lxip\n",
                               ulWhere, FreeRTOS_ntohl( ulIPAddress ) ) );
        }

        return pxEndPoint;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find an end-point that defines a gateway of a certain type ( IPv4 or IPv6 ).
 *
 * @param[in] xIPType: The type of Gateway to look for ( ipTYPE_IPv4 or ipTYPE_IPv6 ).
 *
 * @return The end-point that will lead to the gateway, or NULL when no gateway was found.
 */
    NetworkEndPoint_IPv4_t * FreeRTOS_FindGateWay_IPv4( )
    {
        NetworkEndPoint_IPv4_t * pxEndPoint = pxNetworkEndPoints_IPv4;

        while( pxEndPoint != NULL )
        {
            if( pxEndPoint->ipv4_settings.ulGatewayAddress != 0U ) /* access to ipv4_settings is checked. */
                {
                    break;
                }
            
            pxEndPoint = pxEndPoint->pxNext;
        }

        return pxEndPoint;
    }
/*-----------------------------------------------------------*/

 /**
 * @brief Get the end-point that is bound to a socket.
 *
 * @param[in] xSocket: The socket of interest.
 *
 * @return An end-point or NULL in case the socket is not bound to an end-point.
 */
    NetworkEndPoint_IPv4_t * pxGetSocketEndpoint_IPv4( Socket_t xSocket )
    {
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
        NetworkEndPoint_IPv4_t * pxResult;

        if( pxSocket != NULL )
        {
            pxResult = pxSocket->pxEndPoint;
        }
        else
        {
            pxResult = NULL;
        }

        return pxResult;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Assign an end-point to a socket.
 *
 * @param[in] xSocket: The socket to which an end-point will be assigned.
 * @param[in] pxEndPoint: The end-point to be assigned.
 */
    void vSetSocketEndpoint_IPv4( Socket_t xSocket,
                             NetworkEndPoint_IPv4_t * pxEndPoint )
    {
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;

        pxSocket->pxEndPoint = pxEndPoint;
    }
/*-----------------------------------------------------------*/

#endif ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 )