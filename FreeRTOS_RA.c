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
 * @file FreeRTOS_RA.c
 * @brief A client implementation of Router advertisement protocol.
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
#include "FreeRTOS_Routing.h"
#include "FreeRTOS_ND.h"
#if ( ipconfigUSE_LLMNR == 1 )
    #include "FreeRTOS_DNS.h"
#endif /* ipconfigUSE_LLMNR */
#include "NetworkBufferManagement.h"

/* This define may exclude the entire source file. */
#if ( ipconfigUSE_IPv6 != 0 ) && ( ipconfigUSE_RA != 0 )

/*-----------------------------------------------------------*/

/* A block time of 0 simply means "don't block". */
    #define raDONT_BLOCK    ( ( TickType_t ) 0 )

/*-----------------------------------------------------------*/

/* Initialise the Router Advertisement process for a given end-point. */
    static void vRAProcessInit( NetworkEndPoint_t * pxEndPoint );

/*-----------------------------------------------------------*/

/**
 * @brief Sned an ICMPv6 message of the type: Router Solicitation.
 *
 * @param[in] pxNetworkBuffer: The network buffer which can be used for this.
 * @param[in] pxIPAddress: The target address, normally ff02::2
 *
 * @return An enum which says whether to return the frame or to release it
 */
    void vNDSendRouterSolicitation( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    IPv6_Address_t * pxIPAddress )
    {
        ICMPPacket_IPv6_t * pxICMPPacket;
        ICMPRouterSolicitation_IPv6_t * xRASolicitationRequest;
        NetworkEndPoint_t * pxEndPoint = pxNetworkBuffer->pxEndPoint;
        size_t uxNeededSize;
        MACAddress_t xMultiCastMacAddress;
        NetworkBufferDescriptor_t * pxDescriptor = pxNetworkBuffer;

        configASSERT( pxEndPoint != NULL );
        uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) );

        if( pxDescriptor->xDataLength < uxNeededSize )
        {
            pxDescriptor = pxDuplicateNetworkBufferWithDescriptor( pxDescriptor, uxNeededSize );

            if( pxDescriptor == NULL )
            {
                return; /*lint !e904 Return statement before end of function [MISRA 2012 Rule 15.5, advisory]. */
            }
        }

        pxICMPPacket = ipPOINTER_CAST( ICMPPacket_IPv6_t *, pxDescriptor->pucEthernetBuffer );
        xRASolicitationRequest = ipPOINTER_CAST( ICMPRouterSolicitation_IPv6_t *, &( pxICMPPacket->xICMPHeader_IPv6 ) );

        pxDescriptor->xDataLength = uxNeededSize;

        eNDGetCacheEntry( pxIPAddress, &( xMultiCastMacAddress ), NULL );

        /* Set Ethernet header. Will be swapped. */
        ( void ) memcpy( pxICMPPacket->xEthernetHeader.xSourceAddress.ucBytes, xMultiCastMacAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
        ( void ) memcpy( pxICMPPacket->xEthernetHeader.xDestinationAddress.ucBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
        pxICMPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

        /* Set IP-header. */
        pxICMPPacket->xIPHeader.ucVersionTrafficClass = 0x60;
        pxICMPPacket->xIPHeader.ucTrafficClassFlow = 0;
        pxICMPPacket->xIPHeader.usFlowLabel = 0;
        pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( sizeof( ICMPRouterSolicitation_IPv6_t ) ); /*lint !e845: (Info -- The right argument to operator '|' is certain to be 0. */
        pxICMPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
        pxICMPPacket->xIPHeader.ucHopLimit = 255;

        configASSERT( pxEndPoint != NULL );
        configASSERT( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED );

        ( void ) memcpy( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, 16 );

        ( void ) memcpy( pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes, pxIPAddress->ucBytes, 16 );

        /* Set ICMP header. */
        ( void ) memset( xRASolicitationRequest, 0, sizeof( *xRASolicitationRequest ) );
        xRASolicitationRequest->ucTypeOfMessage = ipICMP_ROUTER_SOLICITATION_IPv6;

/*
 *  xRASolicitationRequest->ucOptionType = ndICMP_SOURCE_LINK_LAYER_ADDRESS;
 *  xRASolicitationRequest->ucOptionLength = 1;
 *  ( void ) memcpy( xRASolicitationRequest->ucOptionBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
 */
        /* Checksums. */
        xRASolicitationRequest->usChecksum = 0;
        /* calculate the UDP checksum for outgoing package */
        ( void ) usGenerateProtocolChecksum( pxDescriptor->pucEthernetBuffer, pxDescriptor->xDataLength, pdTRUE );

        /* This function will fill in the eth addresses and send the packet */
        vReturnEthernetFrame( pxDescriptor, pdTRUE );
    }
/*-----------------------------------------------------------*/

/**
 * @brief Receive a NA ( Neighbourhood Advertisement ) message to see if a chosen IP-address is already in use.
 *
 * @param[in] pxNetworkBuffer: The buffer that contains the message.
 */
    void vReceiveNA( NetworkBufferDescriptor_t * const pxNetworkBuffer )
    {
        NetworkInterface_t * pxInterface = pxNetworkBuffer->pxInterface;
        NetworkEndPoint_t * pxPoint;
        ICMPPacket_IPv6_t * pxICMPPacket = ipPOINTER_CAST( ICMPPacket_IPv6_t *, pxNetworkBuffer->pucEthernetBuffer );
        ICMPHeader_IPv6_t * xICMPHeader_IPv6 = ipPOINTER_CAST( ICMPHeader_IPv6_t *, &( pxICMPPacket->xICMPHeader_IPv6 ) );

        for( pxPoint = FreeRTOS_FirstEndPoint( pxInterface );
             pxPoint != NULL;
             pxPoint = FreeRTOS_NextEndPoint( pxInterface, pxPoint ) )
        {
            if( ( pxPoint->bits.bWantRA != pdFALSE_UNSIGNED ) && ( pxPoint->xRAData.eRAState == eRAStateIPWait ) )
            {
                if( memcmp( pxPoint->ipv6_settings.xIPAddress.ucBytes, &( xICMPHeader_IPv6->xIPv6_Address ), ipSIZE_OF_IPv6_ADDRESS ) == 0 )
                {
                    pxPoint->xRAData.bits.bIPAddressInUse = pdTRUE_UNSIGNED;
                    vIPReloadDHCP_RATimer( pxPoint, 100UL );
                }
            }
        }
    }

/**
 * @brief Receive and analyse a RA ( Router Advertisement ) message.
 *        If the reply is satisfactory, the end-point will do SLAAC: choose an IP-address using the
 *        prefix offered, and completed with random bits.  It will start testing if another device
 *        already exists that uses the same IP-address.
 *
 * @param[in] pxNetworkBuffer: The buffer that contains the message.
 */
    void vReceiveRA( NetworkBufferDescriptor_t * const pxNetworkBuffer )
    {
        ICMPPacket_IPv6_t * pxICMPPacket = ipPOINTER_CAST( ICMPPacket_IPv6_t *, pxNetworkBuffer->pucEthernetBuffer );
        ICMPRouterAdvertisement_IPv6_t * pxAdvertisement = ipPOINTER_CAST( ICMPRouterAdvertisement_IPv6_t *, &( pxICMPPacket->xICMPHeader_IPv6 ) );
        ICMPPrefixOption_IPv6_t * pxPrefixOption = NULL;
        size_t uxIndex;
        size_t uxLast;
        size_t uxICMPSize;
        size_t uxNeededSize;
        uint8_t * pucBytes;

        /* A Router Advertisement was received, handle it here. */
        uxICMPSize = sizeof( ICMPRouterAdvertisement_IPv6_t );
        uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );

        if( uxNeededSize > pxNetworkBuffer->xDataLength )
        {
            FreeRTOS_printf( ( "Too small\n" ) );
            return; /*lint !e904 Return statement before end of function [MISRA 2012 Rule 15.5, advisory]. */
        }

        FreeRTOS_printf( ( "RA: Type %02x Srv %02x Checksum %04x Hops %d Flags %02x Life %d\n",
                           pxAdvertisement->ucTypeOfMessage,
                           pxAdvertisement->ucTypeOfService,
                           FreeRTOS_ntohs( pxAdvertisement->usChecksum ),
                           pxAdvertisement->ucHopLimit,
                           pxAdvertisement->ucFlags,
                           FreeRTOS_ntohs( pxAdvertisement->usLifetime ) ) );
        uxIndex = 0;
        /* uxLast points to the first byte after the buffer. */
        uxLast = pxNetworkBuffer->xDataLength - uxNeededSize;
        pucBytes = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );

        while( ( uxIndex + 1U ) < uxLast )
        {
            uint8_t ucType = pucBytes[ uxIndex ];
            size_t uxLength = ( size_t ) pucBytes[ uxIndex + 1U ] * 8U;

            if( uxLast < ( uxIndex + uxLength ) )
            {
                FreeRTOS_printf( ( "RA: Not enough bytes ( %u > %u )\n", ( unsigned ) uxIndex + uxLength, ( unsigned ) uxLast ) );
                break;
            }

            switch( ucType )
            {
                case ndICMP_SOURCE_LINK_LAYER_ADDRESS: /* 1 */
                    FreeRTOS_printf( ( "RA: Source = %02x-%02x-%02x-%02x-%02x-%02x\n",
                                       pucBytes[ uxIndex + 2U ],
                                       pucBytes[ uxIndex + 3U ],
                                       pucBytes[ uxIndex + 4U ],
                                       pucBytes[ uxIndex + 5U ],
                                       pucBytes[ uxIndex + 6U ],
                                       pucBytes[ uxIndex + 7U ] ) );
                    break;

                case ndICMP_TARGET_LINK_LAYER_ADDRESS: /* 2 */
                    break;

                case ndICMP_PREFIX_INFORMATION: /* 3 */
                    pxPrefixOption = ipPOINTER_CAST( ICMPPrefixOption_IPv6_t *, &( pucBytes[ uxIndex ] ) );

                    FreeRTOS_printf( ( "RA: Prefix len %d Life %lu, %lu (%pip)\n",
                                       pxPrefixOption->ucPrefixLength,
                                       FreeRTOS_ntohl( pxPrefixOption->ulValidLifeTime ),
                                       FreeRTOS_ntohl( pxPrefixOption->ulPreferredLifeTime ),
                                       pxPrefixOption->ucPrefix ) );
                    break;

                case ndICMP_REDIRECTED_HEADER: /* 4 */
                    break;

                case ndICMP_MTU_OPTION: /* 5 */
                   {
                       uint32_t ulMTU;

                       /* ulChar2u32 returns host-endian numbers. */
                       ulMTU = ulChar2u32( &( pucBytes[ uxIndex + 4 ] ) ); /*lint !e9029 Mismatched essential type categories for binary operator [MISRA 2012 Rule 10.4, required]. */
                       FreeRTOS_printf( ( "RA: MTU = %lu\n", ulMTU ) );
                   }
                   break;

                default:
                    FreeRTOS_printf( ( "RA: Type %02x not implemented\n", ucType ) );
                    break;
            }

            uxIndex = uxIndex + uxLength;
        } /* while( ( uxIndex + 1 ) < uxLast ) */

        configASSERT( pxNetworkBuffer->pxInterface != NULL );

        if( pxPrefixOption != NULL )
        {
            NetworkEndPoint_t * pxEndPoint;

            for( pxEndPoint = FreeRTOS_FirstEndPoint( pxNetworkBuffer->pxInterface );
                 pxEndPoint != NULL;
                 pxEndPoint = FreeRTOS_NextEndPoint( pxNetworkBuffer->pxInterface, pxEndPoint ) )
            {
                if( ( pxEndPoint->bits.bWantRA != pdFALSE_UNSIGNED ) && ( pxEndPoint->xRAData.eRAState == eRAStateWait ) )
                {
                    pxEndPoint->ipv6_settings.uxPrefixLength = pxPrefixOption->ucPrefixLength;
                    ( void ) memcpy( pxEndPoint->ipv6_settings.xPrefix.ucBytes, pxPrefixOption->ucPrefix, ipSIZE_OF_IPv6_ADDRESS );
                    ( void ) memcpy( pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

                    pxEndPoint->xRAData.bits.bRouterReplied = pdTRUE_UNSIGNED;
                    pxEndPoint->xRAData.uxRetryCount = 0UL;
                    pxEndPoint->xRAData.ulPreferredLifeTime = FreeRTOS_ntohl( pxPrefixOption->ulPreferredLifeTime );
                    /* Force taking a new random IP-address. */
                    pxEndPoint->xRAData.bits.bIPAddressInUse = pdTRUE_UNSIGNED;
                    pxEndPoint->xRAData.eRAState = eRAStateIPTest;
                    vRAProcess( pdFALSE, pxEndPoint );
                }
            }
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief This is an option to test SLAAC. This device will take the IP-address of a
 *        known device in the LAN, just to simulate a IP-address clash.
 *
 * @param[in] xIndex: the index to be used in the list of IP-addresses.
 * @param[out] pxIPAddress: Here the IP-address will be written.
 *
 * @return pdPASS if an existing IP-address has been found and written to pxIPAddress.
 */
    static BaseType_t prvGetTestAddress( BaseType_t xIndex,
                                         IPv6_Address_t * pxIPAddress )
    {
        ( void ) xIndex;
        ( void ) pxIPAddress;
        return 0;

        #if 0
            BaseType_t xResult;

            /* For testing only: return an IPv6 address that is already taken in the LAN. */
            const char * ip_address[] =
            {
                "fe80::6816:5e9b:80a0:9edb", /* laptop _HT_ */
                "fe80::9355:69c7:585a:afe7", /* raspberry */
            };

            if( xIndex < ARRAY_SIZE( ip_address ) )
            {
                ( void ) FreeRTOS_inet_pton6( ip_address[ xIndex ], pxIPAddress->ucBytes );
                xResult = pdPASS;
            }
            else
            {
                xResult = pdFAIL;
            }
            return xResult;
        #endif /* 0 */
    }
/*-----------------------------------------------------------*/

/**
 * @brief Initialise the RA state machine.
 *
 * @param[in] pxEndPoint: The end-point for which Router Advertisement is required.
 */
    static void vRAProcessInit( NetworkEndPoint_t * pxEndPoint )
    {
        pxEndPoint->xRAData.uxRetryCount = 0;
        pxEndPoint->xRAData.eRAState = eRAStateApply;
    }

/**
 * @brief Do a single cycle of the RA state machine.
 *
 * @param[in] xDoReset: pdTRUE if the state machine must be reset.
 * @param[in] pxEndPoint: The end-point for which a RA assignment is required.
 */
    void vRAProcess( BaseType_t xDoReset,
                     NetworkEndPoint_t * pxEndPoint )
    {
        eRAState_t eRAState = pxEndPoint->xRAData.eRAState;
        TickType_t uxReloadTime = pdMS_TO_TICKS( 5000UL );
        BaseType_t xSkipLease = pdFALSE;

        configASSERT( pxEndPoint != NULL );

        if( xDoReset != pdFALSE )
        {
            vRAProcessInit( pxEndPoint );
        }

        switch( pxEndPoint->xRAData.eRAState )
        {
            case eRAStateWait:

                /* A Router Solicitation has been sent, waited for a reply, but no came.
                 * All replies will be handled in the function vReceiveRA(). */
                pxEndPoint->xRAData.uxRetryCount++;

                if( pxEndPoint->xRAData.uxRetryCount < ( UBaseType_t ) ipconfigRA_SEARCH_COUNT )
                {
                    pxEndPoint->xRAData.eRAState = eRAStateApply;
                }
                else
                {
                    FreeRTOS_printf( ( "RA: Giving up waiting for a Router.\n" ) );
                    ( void ) memcpy( &( pxEndPoint->ipv6_settings ), &( pxEndPoint->ipv6_defaults ), sizeof( pxEndPoint->ipv6_settings ) );

                    pxEndPoint->xRAData.bits.bRouterReplied = pdFALSE_UNSIGNED;
                    pxEndPoint->xRAData.uxRetryCount = 0UL;
                    /* Force taking a new random IP-address. */
                    pxEndPoint->xRAData.bits.bIPAddressInUse = pdTRUE_UNSIGNED;
                    pxEndPoint->xRAData.eRAState = eRAStateIPTest;
                }

                break;

            case eRAStateIPWait:

                /* A Neighbour Solicitation has been sent, waited for a reply.
                 * Repeat this 'ipconfigRA_IP_TEST_COUNT' times to be sure. */
                if( pxEndPoint->xRAData.bits.bIPAddressInUse != pdFALSE_UNSIGNED )
                {
                    /* Another device has responded with the same IPv4 address. */
                    pxEndPoint->xRAData.uxRetryCount = 0UL;
                    pxEndPoint->xRAData.eRAState = eRAStateIPTest;
                    uxReloadTime = pdMS_TO_TICKS( ipconfigRA_IP_TEST_TIME_OUT_MSEC );
                }
                else if( pxEndPoint->xRAData.uxRetryCount < ( UBaseType_t ) ipconfigRA_IP_TEST_COUNT )
                {
                    /* Try again. */
                    pxEndPoint->xRAData.uxRetryCount++;
                    pxEndPoint->xRAData.eRAState = eRAStateIPTest;
                    uxReloadTime = pdMS_TO_TICKS( ipconfigRA_IP_TEST_TIME_OUT_MSEC );
                }
                else
                {
                    /* Now it is assumed that there is no other device using the same IP-address. */
                    if( pxEndPoint->xRAData.bits.bRouterReplied != pdFALSE_UNSIGNED )
                    {
                        /* Obtained configuration from a router. */
                        uxReloadTime = pdMS_TO_TICKS( 1000UL * pxEndPoint->xRAData.ulPreferredLifeTime );
                        pxEndPoint->xRAData.eRAState = eRAStateLease;
                        xSkipLease = pdTRUE;
                        iptraceRA_SUCCEDEED( &( pxEndPoint->ipv6_settings.xIPAddress ) );
                        FreeRTOS_printf( ( "RA: succeeded, using IP address %pip\n", pxEndPoint->ipv6_settings.xIPAddress.ucBytes ) );
                    }
                    else
                    {
                        /* Using the default network parameters. */
                        pxEndPoint->xRAData.eRAState = eRAStateFailed;

                        iptraceRA_REQUESTS_FAILED_USING_DEFAULT_IP_ADDRESS( &( pxEndPoint->ipv6_settings.xIPAddress ) );

                        FreeRTOS_printf( ( "RA: failed, using default parameters and IP address %pip\n", pxEndPoint->ipv6_settings.xIPAddress.ucBytes ) );
                        /* Disable the timer. */
                        uxReloadTime = 0UL;
                    }

                    /* Now call vIPNetworkUpCalls() to send the network-up event and
                     * start the ARP timer. */
                    vIPNetworkUpCalls( pxEndPoint );
                }

                break;

            case eRAStateApply:
            case eRAStateIPTest:
            case eRAStateLease:
            case eRAStateFailed:
            default:
                /* Other states are handled here below. */
                break;
        }

        switch( pxEndPoint->xRAData.eRAState )
        {
            case eRAStateApply:
               {
                   IPv6_Address_t xIPAddress;
                   size_t uxNeededSize;
                   NetworkBufferDescriptor_t * pxNetworkBuffer;

                   /* Send a Router Solicitation to ff02::2 */
                   ( void ) memset( xIPAddress.ucBytes, 0, sizeof xIPAddress.ucBytes );
                   xIPAddress.ucBytes[ 0 ] = 0xff;
                   xIPAddress.ucBytes[ 1 ] = 0x02;
                   xIPAddress.ucBytes[ 15 ] = 0x02;
                   uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) );
                   pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxNeededSize, raDONT_BLOCK );

                   if( pxNetworkBuffer != NULL )
                   {
                       pxNetworkBuffer->pxEndPoint = pxEndPoint;
                       vNDSendRouterSolicitation( pxNetworkBuffer, &( xIPAddress ) );
                   }

                   FreeRTOS_printf( ( "vRAProcess: Router Solicitation, attempt %lu/%u\n",
                                      pxEndPoint->xRAData.uxRetryCount + 1U,
                                      ipconfigRA_SEARCH_COUNT ) );
                   /* Wait a configurable time for a router advertisement. */
                   uxReloadTime = pdMS_TO_TICKS( ipconfigRA_SEARCH_TIME_OUT_MSEC );
                   pxEndPoint->xRAData.eRAState = eRAStateWait;
               }
               break;

            case eRAStateWait:
                /* Waiting for a router advertisement. */
                /* Handled here above. */
                break;

            case eRAStateIPTest: /* Assuming an IP address, test if another device is using it already. */
               {
                   size_t uxNeededSize;
                   NetworkBufferDescriptor_t * pxNetworkBuffer;

                   /* Get an IP-address, using the network prefix and a random host address. */
                   if( pxEndPoint->xRAData.bits.bIPAddressInUse != 0U )
                   {
                       static BaseType_t xUseIndex = 0;

                       pxEndPoint->xRAData.bits.bIPAddressInUse = pdFALSE_UNSIGNED;

                       if( prvGetTestAddress( xUseIndex, &( pxEndPoint->ipv6_settings.xIPAddress ) ) == pdPASS )
                       {
                           /* TESTING ONLY */
                           xUseIndex++;
                       }
                       else
                       {
                           ( void ) FreeRTOS_CreateIPv6Address( &pxEndPoint->ipv6_settings.xIPAddress, &pxEndPoint->ipv6_settings.xPrefix, pxEndPoint->ipv6_settings.uxPrefixLength, pdTRUE );
                       }

                       FreeRTOS_printf( ( "RA: Creating a random IP-address\n" ) );
                   }

                   FreeRTOS_printf( ( "RA: Neighbour solicitation for %pip\n", pxEndPoint->ipv6_settings.xIPAddress.ucBytes ) );

                   uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t ) );
                   pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxNeededSize, raDONT_BLOCK );

                   if( pxNetworkBuffer != NULL )
                   {
                       pxNetworkBuffer->pxEndPoint = pxEndPoint;
                       vNDSendNeighbourSolicitation( pxNetworkBuffer, &( pxEndPoint->ipv6_settings.xIPAddress ) );
                   }

                   uxReloadTime = pdMS_TO_TICKS( 1000UL );
                   pxEndPoint->xRAData.eRAState = eRAStateIPWait;
               }
               break;

            case eRAStateIPWait:
                /* Assuming an IP address, test if another device is using it already. */
                /* Handled here above. */
                break;

            case eRAStateLease:

                if( xSkipLease == pdFALSE )
                {
                    vRAProcessInit( pxEndPoint );
                    uxReloadTime = pdMS_TO_TICKS( 1000UL );
                }

                break;

            case eRAStateFailed:
                break;

            default:
                /* All states were handled. */
                break;
        }

        FreeRTOS_printf( ( "vRAProcess( %ld, %pip) bRouterReplied=%d bIPAddressInUse=%d state %d -> %d\n",
                           xDoReset,
                           pxEndPoint->ipv6_defaults.xIPAddress.ucBytes,
                           pxEndPoint->xRAData.bits.bRouterReplied,
                           pxEndPoint->xRAData.bits.bIPAddressInUse,
                           eRAState,
                           pxEndPoint->xRAData.eRAState ) );

        if( uxReloadTime != 0UL )
        {
            vIPReloadDHCP_RATimer( pxEndPoint, uxReloadTime );
        }
        else
        {
            /* Disable the timer, this function vRAProcess() won't be called anymore for this end-point. */
            FreeRTOS_printf( ( "RA: Disabled timer.\n" ) );
            vIPSetDHCP_RATimerEnableState( pxEndPoint, pdFALSE );
        }
    }
/*-----------------------------------------------------------*/

#endif /* ( ipconfigUSE_IPv6 != 0 ) && ( ipconfigUSE_RA != 0 ) */
