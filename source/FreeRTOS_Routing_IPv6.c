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

/* The entire module FreeRTOS_ND.c is skipped when IPv6 is not used. */



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

#if ( ipconfigUSE_IPv6 != 0 )
#include "FreeRTOS_Routing.h"

struct xNetworkEndPoint_IPv6 * pxNetworkEndPoints_IPv6 = NULL;

/*
 * Add a new IP-address to a Network Interface.  The object pointed to by
 * 'pxEndPoint' and the interface must continue to exist.
 */
static NetworkEndPoint_IPv6_t * FreeRTOS_AddEndPoint_IPv6( NetworkInterface_t * pxInterface,
                                                 NetworkEndPoint_IPv6_t * pxEndPoint );

/*-----------------------------------------------------------*/


#if ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 )

    static NetworkEndPoint_IPv6_t * prvFindFirstAddress_IPv6( void );


/*-----------------------------------------------------------*/

/**
 * @brief Add an end-point to a given interface.
 *
 * @param[in] pxInterface: The interface that gets a new end-point.
 * @param[in] pxEndPoint: The end-point to be added.
 *
 * @return The value of the parameter 'pxEndPoint'.
 */
    static NetworkEndPoint_IPv6_t * FreeRTOS_AddEndPoint_IPv6( NetworkInterface_t * pxInterface,
                                                     NetworkEndPoint_IPv6_t * pxEndPoint )
    {
        NetworkEndPoint_IPv6_t * pxIterator = NULL;

        /* This end point will go to the end of the list, so there is no pxNext
         * yet. */
        pxEndPoint->pxNext = NULL;

        /* Double link between the NetworkInterface_t that is using the addressing
         * defined by this NetworkEndPoint_t structure. */
        pxEndPoint->pxNetworkInterface = pxInterface;

        if( pxNetworkEndPoints_IPv6 == NULL )
        {
            /* No other end points are defined yet - so this is the first in the
             * list. */
            pxNetworkEndPoints_IPv6 = pxEndPoint;
        }
        else
        {
            /* Other end points are already defined so iterate to the end of the
             * list. */
            pxIterator = pxNetworkEndPoints_IPv6;

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

        FreeRTOS_printf( ( "FreeRTOS_AddEndPoint: MAC: %02x-%02x IPv6: %pip\n",
                                   pxEndPoint->xMACAddress.ucBytes[ 4 ],
                                   pxEndPoint->xMACAddress.ucBytes[ 5 ],
                                   pxEndPoint->ipv6_defaults.xIPAddress.ucBytes ) );

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
    NetworkEndPoint_IPv6_t * FreeRTOS_NextEndPoint_IPv6( NetworkInterface_t * pxInterface,
                                               NetworkEndPoint_IPv6_t * pxEndPoint )
    {
        NetworkEndPoint_IPv6_t * pxResult = pxEndPoint;

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
 * @brief Find the end-point which handles a given IPv6 address.
 *
 * @param[in] pxIPAddress: The IP-address of interest.
 *
 * @return The end-point found or NULL.
 */
        NetworkEndPoint_IPv6_t * FreeRTOS_FindEndPointOnIP_IPv6( const IPv6_Address_t * pxIPAddress )
        {
            NetworkEndPoint_IPv6_t * pxEndPoint = pxNetworkEndPoints_IPv6;

            while( pxEndPoint != NULL )
            {
                if( xCompareIPv6_Address( &( pxEndPoint->ipv6_settings.xIPAddress ), pxIPAddress, pxEndPoint->ipv6_settings.uxPrefixLength ) == 0 )
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
    NetworkEndPoint_IPv6_t * FreeRTOS_FindEndPointOnMAC_IPv6( const MACAddress_t * pxMACAddress )
    {
        NetworkEndPoint_IPv6_t * pxEndPoint = pxNetworkEndPoints_IPv6;

        #if ( ipconfigHAS_ROUTING_STATISTICS == 1 )
            {
                xRoutingStatistics_IPv6.ulOnMAC++;
            }
        #endif

        /*_RB_ Question - would it be more efficient to store the mac addresses in
         * uin64_t variables for direct comparison instead of using memcmp()?  [don't
         * know if there is a quick way of creating a 64-bit number from the 48-byte
         * MAC address without getting junk in the top 2 bytes]. */

        /* Find the end-point with given MAC-address. */
        while( pxEndPoint != NULL )
        {
            if( memcmp( pxEndPoint->xMACAddress.ucBytes, pxMACAddress->ucBytes, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
                {
                    break;
                }
            

            pxEndPoint = pxEndPoint->pxNext;
        }

        return pxEndPoint;
    }

/*-----------------------------------------------------------*/


/**
 * @brief Configure and install a new IPv6 end-point.
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
        void FreeRTOS_FillEndPoint_IPv6( NetworkInterface_t * pxNetworkInterface,
                                         NetworkEndPoint_IPv6_t * pxEndPoint,
                                         IPv6_Address_t * pxIPAddress,
                                         IPv6_Address_t * pxNetPrefix,
                                         size_t uxPrefixLength,
                                         IPv6_Address_t * pxGatewayAddress,
                                         IPv6_Address_t * pxDNSServerAddress,
                                         const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] )
        {
            configASSERT( pxIPAddress != NULL );
            configASSERT( ucMACAddress != NULL );
            configASSERT( pxEndPoint != NULL );

            ( void ) memset( pxEndPoint, 0, sizeof( *pxEndPoint ) );

            pxEndPoint->bits.bIPv6 = pdTRUE_UNSIGNED;

            pxEndPoint->ipv6_settings.uxPrefixLength = uxPrefixLength;

            if( pxGatewayAddress != NULL )
            {
                ( void ) memcpy( pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, pxGatewayAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
            }

            if( pxDNSServerAddress != NULL )
            {
                ( void ) memcpy( pxEndPoint->ipv6_settings.xDNSServerAddresses[ 0 ].ucBytes, pxDNSServerAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
            }

            if( pxNetPrefix != NULL )
            {
                ( void ) memcpy( pxEndPoint->ipv6_settings.xPrefix.ucBytes, pxNetPrefix->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
            }

            /* Copy the current values to the default values. */
            ( void ) memcpy( &( pxEndPoint->ipv6_defaults ), &( pxEndPoint->ipv6_settings ), sizeof( pxEndPoint->ipv6_defaults ) );

            ( void ) memcpy( pxEndPoint->ipv6_defaults.xIPAddress.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );

            ( void ) memcpy( pxEndPoint->xMACAddress.ucBytes, ucMACAddress, ipMAC_ADDRESS_LENGTH_BYTES );
            ( void ) FreeRTOS_AddEndPoint_IPv6( pxNetworkInterface, pxEndPoint );
        }
/*-----------------------------------------------------------*/

/**
 * @brief Find the first end-point of the type IPv6.
 *
 * @return The first IPv6 end-point found, or NULL when there are no IPv6 end-points.
 */

        static NetworkEndPoint_IPv6_t * prvFindFirstAddress_IPv6( void )
        {
            NetworkEndPoint_IPv6_t * pxEndPoint = pxNetworkEndPoints_IPv6;

            return pxEndPoint;
        }

/*-----------------------------------------------------------*/

/**
 * @brief Find an end-point that handles a given IPv6-address.
 *
 * @param[in] pxIPv6Address: The IP-address for which an end-point is looked-up.
 *
 * @return An end-point that has the same network mask as the given IP-address.
 */
        NetworkEndPoint_IPv6_t * FreeRTOS_FindEndPointOnNetMask_IPv6( const IPv6_Address_t * pxIPv6Address )
        {
            ( void ) pxIPv6Address;

            /* _HT_ to be worked out later. __TODO__*/
            return prvFindFirstAddress_IPv6();
        }

/*-----------------------------------------------------------*/

/**
 * @brief Find an end-point that defines a gateway of a certain type ( IPv4 or IPv6 ).
 *
 * @param[in] xIPType: The type of Gateway to look for ( ipTYPE_IPv4 or ipTYPE_IPv6 ).
 *
 * @return The end-point that will lead to the gateway, or NULL when no gateway was found.
 */
    NetworkEndPoint_IPv6_t * FreeRTOS_FindGateWay_IPv6( void )
    {
        NetworkEndPoint_IPv6_t * pxEndPoint = pxNetworkEndPoints_IPv6;

        while( pxEndPoint != NULL )
        {
            {
                /* Check if the IP-address is non-zero. */
                if( memcmp( in6addr_any.ucBytes, pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) != 0 ) /* access to ipv6_settings is checked. */
                {
                    break;
                }
            }

            pxEndPoint = pxEndPoint->pxNext;
        }

        return pxEndPoint;
    }
/*-----------------------------------------------------------*/


/* Get the first end-point belonging to a given interface.
 * When pxInterface is NULL, the very first end-point will be returned. */

/**
 * @brief Find the first IPv6 end-point.
 *
 * @param[in] pxInterface: Either NULL ( don't care ), or a specific interface.
 *
 * @return The end-point found, or NULL when there are no end-points at all.
 */
        NetworkEndPoint_IPv6_t * FreeRTOS_FirstEndPoint_IPv6( NetworkInterface_t * pxInterface )
        {
            NetworkEndPoint_IPv6_t * pxEndPoint = pxNetworkEndPoints_IPv6;

            while( pxEndPoint != NULL )
            {
                if( ( ( pxInterface == NULL ) || ( pxEndPoint->pxNetworkInterface == pxInterface ) ) && ( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED ) )
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
    NetworkEndPoint_IPv6_t * pxGetSocketEndpoint_IPv6( Socket_t xSocket )
    {
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
        NetworkEndPoint_IPv6_t * pxResult;

        if( pxSocket != NULL )
        {
            pxResult = pxSocket->pxEndPointIPv6;
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
    void vSetSocketEndpoint_IPv6( Socket_t xSocket,
                             NetworkEndPoint_IPv6_t * pxEndPoint )
    {
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;

        pxSocket->pxEndPointIPv6 = pxEndPoint;
    }
/*-----------------------------------------------------------*/


#endif ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 )

#endif /* ipconfigUSE_IPv6 */
