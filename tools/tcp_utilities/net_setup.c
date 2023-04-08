/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
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
 * @file net_setup.c
 * @brief Some helping functions to make it configure the IP-stack.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

#include "net_setup.h"

BaseType_t xSetupEndpoint_v4( NetworkInterface_t * pxInterface, NetworkEndPoint_t * pxEndpoint, SetupV4_t * pxSetup )
{
    BaseType_t xResult = pdPASS;
    NetworkEndPoint_t * pxUseEndpoint = pxEndpoint;
    if( pxUseEndpoint == NULL )
    {
        pxUseEndpoint = ( NetworkEndPoint_t * ) pvPortMalloc( sizeof( * pxUseEndpoint ) );
    }
    if( pxUseEndpoint != NULL )
    {
        BaseType_t xIndex;
        BaseType_t xTarget = 0;
        uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ];
        uint8_t ucMask[ ipIP_ADDRESS_LENGTH_BYTES ];
        uint8_t ucGateway[ ipIP_ADDRESS_LENGTH_BYTES ];
        uint8_t ucDNS[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0, 0, 0, 0 };
        MACAddress_t xMACAddress;

        memset( pxUseEndpoint, 0, sizeof( *pxUseEndpoint ) );

        FreeRTOS_inet_pton( FREERTOS_AF_INET4, pxSetup->pcIPAddress, ( void * ) ucIPAddress );
        FreeRTOS_inet_pton( FREERTOS_AF_INET4, pxSetup->pcMask,      ( void * ) ucMask );
        FreeRTOS_inet_pton( FREERTOS_AF_INET4, pxSetup->pcGateway,   ( void * ) ucGateway );
        FreeRTOS_EUI48_pton( pxSetup->pcMACAddress, xMACAddress.ucBytes );

        FreeRTOS_FillEndPoint( pxInterface,
                            pxUseEndpoint,
                            ucIPAddress,
                            ucMask,
                            ucGateway,
                            ucDNS,
                            xMACAddress.ucBytes );

        for( xIndex = 0; xIndex < ipconfigENDPOINT_DNS_ADDRESS_COUNT; xIndex++ )
        {
            uint32_t ulDNSAddress;
            FreeRTOS_inet_pton( FREERTOS_AF_INET4, pxSetup->pcDNS[ xIndex ], ( void * ) &ulDNSAddress );
            if( ulDNSAddress )
            {
                pxUseEndpoint->ipv4_settings.ulDNSServerAddresses[ xTarget ] = ulDNSAddress;
                pxUseEndpoint->ipv4_defaults.ulDNSServerAddresses[ xTarget ] = ulDNSAddress;
                xTarget++;
            }
        }
        #if ( ipconfigUSE_DHCP != 0 )
            if( pxSetup->eType == eDHCP )
            {
                pxUseEndpoint->bits.bWantDHCP = 1;
            }
        #endif
    }
    return xResult;
}

BaseType_t xSetupEndpoint_v6( NetworkInterface_t * pxInterface, NetworkEndPoint_t * pxEndpoint, SetupV6_t * pxSetup  )
{
    BaseType_t xResult = pdPASS;
    NetworkEndPoint_t * pxUseEndpoint = pxEndpoint;
    if( pxUseEndpoint == NULL )
    {
        pxUseEndpoint = ( NetworkEndPoint_t * ) pvPortMalloc( sizeof( * pxUseEndpoint ) );
    }
    if( pxUseEndpoint != NULL )
    {
        BaseType_t xIndex;
        BaseType_t xTarget = 0;
        IPv6_Address_t xIPAddress;
        IPv6_Address_t xPrefix;
        IPv6_Address_t xGateway;
        MACAddress_t xMACAddress;

        memset( pxUseEndpoint, 0, sizeof( *pxUseEndpoint ) );
        ( void ) memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
        ( void ) memset( &xPrefix, 0, sizeof( IPv6_Address_t ) );
        ( void ) memset( &xGateway, 0, sizeof( IPv6_Address_t ) );

        FreeRTOS_EUI48_pton( pxSetup->pcMACAddress, xMACAddress.ucBytes );
        FreeRTOS_inet_pton( FREERTOS_AF_INET6, pxSetup->pcIPAddress, ( void * ) xIPAddress.ucBytes );
        if( pxSetup->pcPrefix != NULL )
        {
            FreeRTOS_inet_pton( FREERTOS_AF_INET6, pxSetup->pcPrefix, ( void * ) xPrefix.ucBytes );
        }
        if( pxSetup->pcGateway != NULL )
        {
            FreeRTOS_inet_pton( FREERTOS_AF_INET6, pxSetup->pcGateway, ( void * ) xGateway.ucBytes );
        }

        FreeRTOS_FillEndPoint_IPv6( pxInterface,
                                    pxUseEndpoint,
                                    &xIPAddress,
                                    &xPrefix,
                                    pxSetup->uxPrefixLength,
                                    &xGateway,
                                    NULL, /* DNS addresses will be added manually. */
                                    xMACAddress.ucBytes );

        pxUseEndpoint->ipv6_settings.uxPrefixLength =                pxSetup->uxPrefixLength;

        for( xIndex = 0; xIndex < ipconfigENDPOINT_DNS_ADDRESS_COUNT; xIndex++ )
        {
            IPv6_Address_t xDNSAddress;
            if(pxSetup->pcDNS[ xIndex ] != NULL)
            {
                FreeRTOS_inet_pton( FREERTOS_AF_INET6, pxSetup->pcDNS[xIndex], ( void* )xDNSAddress.ucBytes );
                if( ( xDNSAddress.ucBytes[ 0 ] != 0U) && ( xDNSAddress.ucBytes[ 1 ] != 0U ) )
                {
                    ( void )memcpy( pxUseEndpoint->ipv6_settings.xDNSServerAddresses[ xTarget ].ucBytes,
                        xDNSAddress.ucBytes,
                        ipSIZE_OF_IPv6_ADDRESS );
                    ( void )memcpy( pxUseEndpoint->ipv6_defaults.xDNSServerAddresses[ xTarget ].ucBytes,
                        xDNSAddress.ucBytes,
                        ipSIZE_OF_IPv6_ADDRESS );
                    xTarget++;
                }
            }
        }

        #if ( ipconfigUSE_DHCP != 0 )
            if( pxSetup->eType == eDHCP )
            {
                pxUseEndpoint->bits.bWantDHCP = 1;
            }
        #endif
        #if ( ipconfigUSE_RA != 0 )
            if( pxSetup->eType == eRA )
            {
                pxUseEndpoint->bits.bWantRA = 1;
            }
        #endif
    }
    return xResult;
}
