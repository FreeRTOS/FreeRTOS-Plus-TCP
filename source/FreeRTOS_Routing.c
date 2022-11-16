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

#if ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 )
/** @brief A list of all network interfaces: */
    struct xNetworkInterface * pxNetworkInterfaces = NULL;

/*-----------------------------------------------------------*/

/**
 * @brief Add a network interface to the list of interfaces.  Check if the interface was
 *        already added in an earlier call.
 *
 * @param[in] pxInterface: The address of the new interface.
 *
 * @return The value of the parameter 'pxInterface'.
 */
    NetworkInterface_t * FreeRTOS_AddNetworkInterface( NetworkInterface_t * pxInterface )
    {
        NetworkInterface_t * pxIterator = NULL;

        /* This interface will be added to the end of the list of interfaces, so
         * there is no pxNext yet. */
        pxInterface->pxNext = NULL;

        if( pxNetworkInterfaces == NULL )
        {
            /* No other interfaces are set yet, so this is the first in the list. */
            pxNetworkInterfaces = pxInterface;
        }
        else
        {
            /* Other interfaces are already defined, so iterate to the end of the
             * list. */

            /*_RB_ Question - if ipconfigMULTI_INTERFACE is used to define the
             * maximum number of interfaces, would it be more efficient to have an
             * array of interfaces rather than a linked list of interfaces? */
            pxIterator = pxNetworkInterfaces;

            for( ; ; )
            {
                if( pxIterator == pxInterface )
                {
                    /* This interface was already added. */
                    break;
                }

                if( pxIterator->pxNext == NULL )
                {
                    pxIterator->pxNext = pxInterface;
                    break;
                }

                pxIterator = pxIterator->pxNext;
            }
        }

        return pxInterface;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Get the first Network Interface, or NULL if none has been added.
 *
 * @return The first interface, or NULL if none has been added
 */
    NetworkInterface_t * FreeRTOS_FirstNetworkInterface( void )
    {
        return pxNetworkInterfaces;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Get the next interface.
 *
 * @return The interface that comes after 'pxInterface'. NULL when either 'pxInterface'
 *         is NULL, or when 'pxInterface' is the last interface.
 */
    NetworkInterface_t * FreeRTOS_NextNetworkInterface( const NetworkInterface_t * pxInterface )
    {
        NetworkInterface_t * pxReturn;

        if( pxInterface != NULL )
        {
            pxReturn = pxInterface->pxNext;
        }
        else
        {
            pxReturn = NULL;
        }

        return pxReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find out the best matching end-point given an incoming Ethernet packet.
 *
 * @param[in] pxNetworkInterface: The interface on which the packet was received.
 * @param[in] pucEthernetBuffer: The Ethernet packet that was just received.
 *
 * @return The end-point that should handle the incoming Ethernet packet.
 */
    void FreeRTOS_MatchingEndpoint( const NetworkInterface_t * pxNetworkInterface,
                                    NetworkBufferDescriptor_t * pucEthernetBuffer )
    {
        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        const ProtocolPacket_t * pxPacket = ( ( const ProtocolPacket_t * ) pucEthernetBuffer->pucEthernetBuffer );
        /*#pragma warning 'name' for logging only, take this away */
        const char * name = "";

        configASSERT( pucEthernetBuffer->pucEthernetBuffer != NULL );

        /* Check if 'pucEthernetBuffer()' has the expected alignment,
         * which is 32-bits + 2. */
        #ifndef _lint
            {
                /* MISRA Ref 11.4.3 [Casting pointer to int for verification] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
                /* coverity[misra_c_2012_rule_11_4_violation] */
                uintptr_t uxAddress = ( uintptr_t ) pucEthernetBuffer->pucEthernetBuffer;
                uxAddress += 2U;
                configASSERT( ( uxAddress % 4U ) == 0U );
                /* And in case configASSERT is not defined. */
                ( void ) uxAddress;
            }
        #endif /* ifndef _lint */

        /* An Ethernet packet has been received. Inspect the contents to see which
         * defined end-point has the best match.
         */

        #if ( ipconfigHAS_ROUTING_STATISTICS == 1 )
            {
                /* Some stats while developing. */
                xRoutingStatistics.ulMatching++;
            }
        #endif

        /* Probably an ARP packet or a broadcast. */
        switch( pxPacket->xUDPPacket.xEthernetHeader.usFrameType )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                case ipIPv6_FRAME_TYPE:
                   {
                       /* MISRA Ref 11.3.1 [Misaligned access] */
                       /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                       /* coverity[misra_c_2012_rule_11_3_violation] */
                       const IPPacket_IPv6_t * pxIPPacket_IPv6 = ( ( IPPacket_IPv6_t * ) pucEthernetBuffer->pucEthernetBuffer );
                       NetworkEndPoint_IPv6_t * pxEndPoint = NULL;

                       pxEndPoint = pxNetworkEndPoints_IPv6;

                       while( pxEndPoint != NULL )
                       {
                           if( pxEndPoint->pxNetworkInterface == pxNetworkInterface )
                           {
                               /* This is a IPv6 end-point on the same interface,
                                * and with a matching IP-address. */
                               if( xCompareIPv6_Address( &( pxEndPoint->ipv6_settings.xIPAddress ), &( pxIPPacket_IPv6->xIPHeader.xDestinationAddress ), pxEndPoint->ipv6_settings.uxPrefixLength ) == 0 )
                               {
                                   break;
                               }
                           }

                           pxEndPoint = pxEndPoint->pxNext;
                       }

                       #if ( ipconfigUSE_LLMNR != 0 )
                           {
                               if( pxEndPoint == NULL )
                               {
                                   if( xCompareIPv6_Address( &( ipLLMNR_IP_ADDR_IPv6 ), &( pxIPPacket_IPv6->xIPHeader.xDestinationAddress ), ( size_t ) 8U * ipSIZE_OF_IPv6_ADDRESS ) == 0 )
                                   {
                                       pxEndPoint = FreeRTOS_FirstEndPoint_IPv6( pxNetworkInterface );
                                   }
                               }
                           }
                       #endif

                       if( pxEndPoint != NULL )
                       {
                           pucEthernetBuffer->pxEndPointIPv6 = pxEndPoint;
                           pucEthernetBuffer->bits.bIPv6 = pdTRUE_UNSIGNED;
                       }
                   }
                   break;
            #endif /* ipconfigUSE_IPv6 */

            case ipARP_FRAME_TYPE:
               {
                   NetworkEndPoint_IPv4_t * pxEndPoint = NULL;
                   pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( pxPacket->xARPPacket.xARPHeader.ulTargetProtocolAddress, 3U );
                   name = "ARP";
                   pucEthernetBuffer->pxEndPoint = pxEndPoint;

                   break;
               }

            case ipIPv4_FRAME_TYPE:
               {
                   /* An IPv4 UDP or TCP packet. */
                   uint32_t ulIPSourceAddress = pxPacket->xUDPPacket.xIPHeader.ulSourceIPAddress;
                   uint32_t ulIPTargetAddress = pxPacket->xUDPPacket.xIPHeader.ulDestinationIPAddress;
                   uint32_t ulMatchAddress;
                   BaseType_t xIPBroadcast;
                   BaseType_t xDone = pdFALSE;
                   NetworkEndPoint_IPv4_t * pxEndPoint = NULL;

                   if( ( FreeRTOS_ntohl( ulIPTargetAddress ) & 0xffuL ) == 0xffuL )
                   {
                       xIPBroadcast = pdTRUE;
                   }
                   else
                   {
                       xIPBroadcast = pdFALSE;
                   }

                   if( pxPacket->xUDPPacket.xIPHeader.ucProtocol == ( uint8_t ) ipPROTOCOL_UDP )
                   {
                       name = "UDP";
                   }
                   else
                   {
                       name = "TCP";
                   }

                   if( ulIPTargetAddress == ~0U )
                   {
                       ulMatchAddress = ulIPSourceAddress;
                   }
                   else
                   {
                       ulMatchAddress = ulIPTargetAddress;
                   }

                   for( pxEndPoint = FreeRTOS_FirstEndPoint_IPv4( pxNetworkInterface );
                        pxEndPoint != NULL;
                        pxEndPoint = FreeRTOS_NextEndPoint_IPv4( pxNetworkInterface, pxEndPoint ) )
                   {
                       ( void ) name;

                       if( pxEndPoint->ipv4_settings.ulIPAddress == ulIPTargetAddress )
                       {
                           /* The perfect match. */
                           xDone = pdTRUE;
                       }
                       else
                       if( ( xIPBroadcast != pdFALSE ) &&
                           ( ( ( pxEndPoint->ipv4_settings.ulIPAddress ^ ulMatchAddress ) & pxEndPoint->ipv4_settings.ulNetMask ) == 0U ) )
                       {
                           xDone = pdTRUE;
                       }
                       else
                       if( xIsIPv4Multicast( ulIPTargetAddress ) != pdFALSE )
                       {
                           /* Target is a multicast address. */
                           xDone = pdTRUE;
                       }
                       else
                       {
                           /* This end-point doesn't match with the packet. */
                       }

                       if( xDone != pdFALSE )
                       {
                           break;
                       }
                   }

                   if( ( xIPBroadcast != 0 ) && ( pxEndPoint == NULL ) )
                   {
                       pxEndPoint = FreeRTOS_FirstEndPoint_IPv4( pxNetworkInterface );
                   }

                   pucEthernetBuffer->pxEndPoint = pxEndPoint;
               }
               break;

            default:
                /* Frame type not supported. */
                FreeRTOS_printf( ( "Frametpye %04x not supported.\n", FreeRTOS_ntohs( pxPacket->xUDPPacket.xEthernetHeader.usFrameType ) ) );
                break;
        } /* switch usFrameType */

        ( void ) name;
    }
/*-----------------------------------------------------------*/

#else /* ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 ) */

/* Here below the most important function of FreeRTOS_Routing.c in a short
 * version: it is assumed that only 1 interface and 1 end-point will be created.
 * The reason for this is downward compatibility with the earlier release of
 * FreeRTOS+TCP, which had a single network interface only. */

/**
 * @brief Add a network interface to the list of interfaces.  Check if this will be
 *        first and only interface ( ipconfigCOMPATIBLE_WITH_SINGLE = 1 ).
 *
 * @param[in] pxInterface: The address of the new interface.
 *
 * @return The value of the parameter 'pxInterface'.
 */
    NetworkInterface_t * FreeRTOS_AddNetworkInterface( NetworkInterface_t * pxInterface )
    {
        configASSERT( pxNetworkInterfaces == NULL );
        pxNetworkInterfaces = pxInterface;
        return pxInterface;
    }
/*-----------------------------------------------------------*/

/**
 * @brief And an end-point to an interface.  Note that when ipconfigCOMPATIBLE_WITH_SINGLE
 *        is defined, only one interface is allowed, which will have one end-point only.
 *
 * @param[in] pxInterface: The interface to which the end-point is assigned.
 * @param[in] pxEndPoint: The end-point to be assigned to the above interface.
 *
 * @return The value of the parameter 'pxEndPoint'.
 */
    static NetworkEndPoint_t * FreeRTOS_AddEndPoint( NetworkInterface_t * pxInterface,
                                                     NetworkEndPoint_t * pxEndPoint )
    {
        /* This code is in backward-compatibility mode.
         * Only one end-point is allowed, make sure that
         * no end-point has been defined yet. */
        configASSERT( pxNetworkEndPoints == NULL );

        /* This end point will go to the end of the list, so there is no pxNext
         * yet. */
        pxEndPoint->pxNext = NULL;

        /* Double link between the NetworkInterface_t that is using the addressing
         * defined by this NetworkEndPoint_t structure. */
        pxEndPoint->pxNetworkInterface = pxInterface;

        pxInterface->pxEndPoint = pxEndPoint;

        /* No other end points are defined yet - so this is the first in the
         * list. */
        pxNetworkEndPoints = pxEndPoint;

        return pxEndPoint;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find the end-point which has a given IPv4 address.
 *
 * @param[in] ulIPAddress: The IP-address of interest, or 0 if any IPv4 end-point may be returned.
 *
 * @return The end-point found or NULL.
 */
    NetworkEndPoint_t * FreeRTOS_FindEndPointOnIP_IPv4( uint32_t ulIPAddress,
                                                        uint32_t ulWhere )
    {
        NetworkEndPoint_t * pxResult = NULL;

        ( void ) ulIPAddress;
        ( void ) ulWhere;

        if( ( ulIPAddress == 0U ) || ( pxNetworkEndPoints->ipv4_settings.ulIPAddress == ulIPAddress ) )
        {
            pxResult = pxNetworkEndPoints;
        }

        return pxResult;
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
    NetworkEndPoint_t * FreeRTOS_FindEndPointOnMAC( const MACAddress_t * pxMACAddress,
                                                    NetworkInterface_t * pxInterface )
    {
        NetworkEndPoint_t * pxResult = NULL;

        ( void ) pxMACAddress;
        ( void ) pxInterface;

        if( memcmp( pxNetworkEndPoints->xMACAddress.ucBytes, pxMACAddress->ucBytes, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
        {
            pxResult = pxNetworkEndPoints;
        }

        return pxResult;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find an end-point that handles a given IPv4-address.
 *
 * @param[in] ulIPAddress: The IP-address for which an end-point is looked-up.
 *
 * @return An end-point that has the same network mask as the given IP-address.
 */
    NetworkEndPoint_t * FreeRTOS_FindEndPointOnNetMask( uint32_t ulIPAddress,
                                                        uint32_t ulWhere )
    {
        return FreeRTOS_InterfaceEndPointOnNetMask( NULL, ulIPAddress, ulWhere );
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find an end-point that defines a gateway of a certain type ( IPv4 or IPv6 ).
 *
 * @param[in] xIPType: The type of Gateway to look for ( ipTYPE_IPv4 or ipTYPE_IPv6 ).
 *
 * @return The end-point that will lead to the gateway, or NULL when no gateway was found.
 */
    NetworkEndPoint_t * FreeRTOS_FindGateWay( void )
    {
        NetworkEndPoint_t * pxReturn = NULL;

        if( pxNetworkEndPoints != NULL )
        {
            if( pxNetworkEndPoints->ipv4_settings.ulGatewayAddress != 0U )
            {
                pxReturn = pxNetworkEndPoints;
            }
        }

        return pxReturn;
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
    NetworkEndPoint_t * FreeRTOS_FirstEndPoint( NetworkInterface_t * pxInterface )
    {
        ( void ) pxInterface;

        /* ipconfigCOMPATIBLE_WITH_SINGLE is defined and this is the simplified version:
         * only one interface and one end-point is defined. */
        return pxNetworkEndPoints;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Get the first Network Interface, or NULL if none has been added.
 *
 * @return The first interface, or NULL if none has been added
 */
    NetworkInterface_t * FreeRTOS_FirstNetworkInterface( void )
    {
        /* ipconfigCOMPATIBLE_WITH_SINGLE is defined: only one interface and
         * one end-point is defined. */
        return pxNetworkInterfaces;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find an end-point that handles a given IPv4-address.
 *
 * @param[in] pxInterface: Ignored in this simplified version.
 * @param[in] ulIPAddress: The IP-address for which an end-point is looked-up.
 *
 * @return An end-point that has the same network mask as the given IP-address.
 */
    NetworkEndPoint_t * FreeRTOS_InterfaceEndPointOnNetMask( NetworkInterface_t * pxInterface,
                                                             uint32_t ulIPAddress,
                                                             uint32_t ulWhere )
    {
        NetworkEndPoint_t * pxResult = NULL;

        ( void ) pxInterface;
        ( void ) ulWhere;

        if( ( ( ulIPAddress ^ pxNetworkEndPoints->ipv4_settings.ulIPAddress ) & pxNetworkEndPoints->ipv4_settings.ulNetMask ) == 0U )
        {
            pxResult = pxNetworkEndPoints;
        }

        return pxResult;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Find out the best matching end-point given an incoming Ethernet packet.
 *
 * @param[in] pxNetworkInterface: The interface on which the packet was received.
 * @param[in] pucEthernetBuffer: The Ethernet packet that was just received.
 *
 * @return The end-point that should handle the incoming Ethernet packet.
 */
    NetworkEndPoint_t * FreeRTOS_MatchingEndpoint( NetworkInterface_t * pxNetworkInterface,
                                                   uint8_t * pucEthernetBuffer )
    {
        ( void ) pxNetworkInterface;
        ( void ) pucEthernetBuffer;

        /* ipconfigCOMPATIBLE_WITH_SINGLE is defined: only one interface and
         * one end-point is defined. */
        return pxNetworkEndPoints;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Get the next end-point.  As this is the simplified version, it will always
 *        return NULL.
 *
 * @param[in] pxInterface: An interface of interest, or NULL when iterating through all
 *                         end-points.
 * @param[in] pxEndPoint: This is the current end-point.
 *
 * @return NULL because ipconfigCOMPATIBLE_WITH_SINGLE is defined.
 */
    NetworkEndPoint_t * FreeRTOS_NextEndPoint( NetworkInterface_t * pxInterface,
                                               NetworkEndPoint_t * pxEndPoint )
    {
        ( void ) pxInterface;
        ( void ) pxEndPoint;

        return NULL;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Get the next interface.
 *
 * @return NULL because ipconfigCOMPATIBLE_WITH_SINGLE is defined.
 */
    NetworkInterface_t * FreeRTOS_NextNetworkInterface( NetworkInterface_t * pxInterface )
    {
        ( void ) pxInterface;

        return NULL;
    }
/*-----------------------------------------------------------*/

#endif /* ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 ) */
