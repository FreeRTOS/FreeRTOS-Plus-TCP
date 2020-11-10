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
 * @file FreeRTOS_DHCPv6.c
 * @brief A DHCPv6 client.
 */

/* Standard includes. */
#include <stdio.h>
#include <time.h>
#include <ctype.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "timers.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"

#if ( ipconfigUSE_IPv6 != 0 ) && ( ipconfigUSE_DHCPv6 != 0 )

    #include "FreeRTOS_Sockets.h"
    #include "FreeRTOS_DHCPv6.h"
    #include "FreeRTOS_DNS.h"
    #include "NetworkBufferManagement.h"
    #include "FreeRTOS_ARP.h"
    #include "FreeRTOS_Sockets.h"
    #include "FreeRTOS_IP_Private.h"

    #include "FreeRTOS_BitConfig.h"

    #include "FreeRTOS_Routing.h"

    #include "FreeRTOS_ND.h"

    #include "eventLogging.h"
    #include "UDPLoggingPrintf.h"

    #define DHCPv6_CLIENT_PORT    546U
    #define DHCPv6_SERVER_PORT    547U

/* Timer parameters */
    #ifndef dhcpINITIAL_DHCP_TX_PERIOD
        #define dhcpINITIAL_TIMER_PERIOD      ( pdMS_TO_TICKS( 250U ) )
        #define dhcpINITIAL_DHCP_TX_PERIOD    ( pdMS_TO_TICKS( 5000U ) )
    #endif

/* IPv6 optoin numbers. */

    #define DHCPv6_message_Type_Solicit                                 1U
    #define DHCPv6_message_Type_Advertise                               2U
    #define DHCPv6_message_Type_Request                                 3U
    #define DHCPv6_message_Type_Confirm                                 4U
    #define DHCPv6_message_Type_Renew                                   5U
    #define DHCPv6_message_Type_Reply                                   7U
    #define DHCPv6_message_Type_Release                                 8U
    #define DHCPv6_message_Type_Decline                                 9U

    #define DHCPv6_Option_Client_Identifier                             1U
    #define DHCPv6_Option_Server_Identifier                             2U
    #define DHCPv6_Option_NonTemporaryAddress                           3U
    #define DHCPv6_Option_IA_Address                                    5U
    #define DHCPv6_Option_Option_List                                   6U
    #define DHCPv6_Option_Preference                                    7U
    #define DHCPv6_Option_Elapsed_Time                                  8U
    #define DHCPv6_Option_Status_Code                                   13U
    #define DHCPv6_Option_DNS_recursive_name_server                     23U
    #define DHCPv6_Option_Domain_Search_List                            24U
    #define DHCPv6_Option_Identity_Association_for_Prefix_Delegation    25U
    #define DHCPv6_Option_IA_Prefix                                     26U

/** @brief The following codes are used in combination with 'DHCPv6_Option_Option_List' */
    #define DHCP6_OPTION_REQUEST_DNS                                    0x0017
    #define DHCP6_OPTION_REQUEST_DOMAIN_SEARCH_LIST                     0x0018

/** @brief The following define is temporary and serves to make the /single source
 * code more similar to the /multi version. */

    #define EP_DHCPData                 pxEndPoint->xDHCPData
    #define EP_IPv6_SETTINGS            pxEndPoint->ipv6_settings

/** @brief If a lease time is not received, use the default of two days.  48 hours in ticks.
 * Do not use the macro pdMS_TO_TICKS() here as integer overflow can occur. */
    #define dhcpDEFAULT_LEASE_TIME      ( ( 48UL * 60UL * 60UL ) * configTICK_RATE_HZ )

/** @brief Don't allow the lease time to be too short. */
    #define dhcpMINIMUM_LEASE_TIME      ( pdMS_TO_TICKS( 60000UL ) )            /* 60 seconds in ticks. */

/** @brief The function time() counts since 1-1-1970.  The DHCPv6 time-stamp however
 * uses a time stamp that had zero on 1-1-2000. */
    #define SECS_FROM_1970_TILL_2000    946684800U

/** @brief When a reply is received, some options are mandatory for this driver. */
    #define dhcpMANDATORY_OPTIONS                   \
    ( ( uint32_t )                                  \
      ( ( 1U << DHCPv6_Option_Client_Identifier ) | \
        ( 1U << DHCPv6_Option_Server_Identifier ) ) )

/** @brief The UDP socket which is shared by all end-points that need DHCPv6. */
    static Socket_t xDHCPSocket;

/** @brief A reference count makes sure that the UDP socket will be deleted when it
 * is not used anymore. */
    static BaseType_t xDHCPSocketUserCount;

    static BaseType_t prvDHCPv6Analyse( const uint8_t * pucAnswer,
                                        size_t uxLength,
                                        DHCPMessage_IPv6_t * pxDHCPMessage );

    static void vDHCPProcessEndPoint( BaseType_t xReset,
                                      NetworkEndPoint_t * pxEndPoint,
                                      DHCPMessage_IPv6_t * pxDHCPMessage );

    static void prvInitialiseDHCP( NetworkEndPoint_t * pxEndPoint );

    static void prvSendDHCPMessage( NetworkEndPoint_t * pxEndPoint );

/*
 * Create the DHCP socket, if it has not been created already.
 */
    static void prvCreateDHCPSocket( NetworkEndPoint_t * pxEndPoint );

/*
 * Close the DHCP socket, only when not in use anymore (i.e. xDHCPSocketUserCount = 0).
 */
    static void prvCloseDHCPSocket( NetworkEndPoint_t * pxEndPoint );

    static const char * prvStateName( eDHCPState_t eState );


    #warning Take this away
    void vUDPLoggingPost( void )
    {
        vUDPLoggingFlush( 2 );
    }

/*-----------------------------------------------------------*/

    static DHCPMessage_IPv6_t xDHCPMessage;

/**
 * @brief Check the DHCP socket and run one cycle of the DHCP state machine.
 *
 * @param[in] xReset: When pdTRUE, the state machine needs to be reset.  Tis may happen
 *            when the end-point has just become up.
 * @param[in] pxEndPoint: The end-point that wants a DHCPv6 address.
 */
    void vDHCPv6Process( BaseType_t xReset,
                         struct xNetworkEndPoint * pxEndPoint )
    {
        BaseType_t xDoProcess = pdTRUE;

        /* Is DHCP starting over? */
        if( xReset != pdFALSE )
        {
            EP_DHCPData.eDHCPState = eInitialWait;

            if( pxEndPoint->pxDHCPMessage == NULL )
            {
                pxEndPoint->pxDHCPMessage = pvPortMalloc( sizeof( *pxEndPoint->pxDHCPMessage ) );

                if( pxEndPoint->pxDHCPMessage != NULL )
                {
                    memset( pxEndPoint->pxDHCPMessage, 0, sizeof( *pxEndPoint->pxDHCPMessage ) );
                }
                else
                {
                    FreeRTOS_printf( ( "vDHCPv6Process: malloc failed %u byt4es\n", sizeof( *pxEndPoint->pxDHCPMessage ) ) );
                }
            }
        }

        /* If there is a socket, check for incoming messages first. */
        if( EP_DHCPData.xDHCPSocket != NULL )
        {
            uint8_t * pucUDPPayload;

            BaseType_t lBytes;
            size_t uxLength;

            for( ; ; )
            {
                NetworkEndPoint_t * pxIterator = NULL;
                BaseType_t xResult;

                /* Get the next UDP message. */
                lBytes = FreeRTOS_recvfrom( EP_DHCPData.xDHCPSocket, &( pucUDPPayload ), 0, ( UBaseType_t ) FREERTOS_ZERO_COPY, NULL, NULL );

                if( lBytes <= 0 )
                {
                    if( ( lBytes < 0 ) && ( lBytes != -pdFREERTOS_ERRNO_EAGAIN ) )
                    {
                        FreeRTOS_printf( ( "vDHCPProcess: FreeRTOS_recvfrom returns %d\n", ( int ) lBytes ) );
                    }

                    break;
                }

                uxLength = ( size_t ) lBytes;

                xResult = prvDHCPv6Analyse( pucUDPPayload, uxLength, &( xDHCPMessage ) );

                FreeRTOS_printf( ( "prvDHCPv6Analyse: %s\n", ( xResult == pdPASS ) ? "Pass" : "Fail" ) );
                eventLogAdd( "prvDHCPv6Analyse: %s", ( xResult == pdPASS ) ? "Pass" : "Fail" );

                if( xResult == pdPASS )
                {
                    pxIterator = pxNetworkEndPoints;

                    /* Find the end-point with given transaction ID. */
                    while( pxIterator != NULL )
                    {
                        if( ( pxIterator->bits.bIPv6 != pdFALSE_UNSIGNED ) && ( pxIterator->bits.bWantDHCP != pdFALSE_UNSIGNED ) )
                        {
                            FreeRTOS_printf( ( "vDHCPProcess: 0x%06lX == 0x%06lX ?\n",
                                               xDHCPMessage.ulTransactionID,
                                               pxIterator->xDHCPData.ulTransactionId ) );

                            if( xDHCPMessage.ulTransactionID == pxIterator->xDHCPData.ulTransactionId )
                            {
                                break;
                            }
                        }

                        pxIterator = pxIterator->pxNext;
                    }
                }

                if( ( pxIterator != NULL ) && ( pxIterator->xDHCPData.eDHCPState == eLeasedAddress ) )
                {
                    /* No DHCP messages are expected while in eLeasedAddress state. */
                    pxIterator = NULL;
                }

                if( ( pxIterator != NULL ) && ( pxIterator->pxDHCPMessage != NULL ) )
                {
                    if( pxIterator->pxDHCPMessage->xServerID.usDUIDType != 0U )
                    {
                        int rc1 = ( xDHCPMessage.xServerID.usDUIDType == pxIterator->pxDHCPMessage->xServerID.usDUIDType ) ? 1 : 0;
                        int rc2 = ( xDHCPMessage.xServerID.uxLength == pxIterator->pxDHCPMessage->xServerID.uxLength ) ? 1 : 0;
                        int rc3 = ( memcmp( xDHCPMessage.xServerID.pucID, pxIterator->pxDHCPMessage->xServerID.pucID, pxIterator->pxDHCPMessage->xServerID.uxLength ) == 0 ) ? 1 : 0;
                        int rc4 = rc1 && rc2 && rc3;
                        FreeRTOS_printf( ( "ServerID check: %d %d %d = %d\n", rc1, rc2, rc3, rc4 ) );
                    }

                    /* Assign a complete struct. */
                    *( pxIterator->pxDHCPMessage ) = xDHCPMessage;

                    /* The second parameter pdTRUE tells to check for a UDP message. */
                    vDHCPProcessEndPoint( pdFALSE, pxIterator, pxIterator->pxDHCPMessage );
                    pxIterator->pxDHCPMessage->ucHasUID = 0U;

                    if( pxEndPoint == pxIterator )
                    {
                        xDoProcess = pdFALSE;
                    }
                }
            }
        }

        if( ( pxEndPoint != NULL ) && ( xDoProcess != pdFALSE ) )
        {
            /* Process the end-point, but do not expect incoming packets. */
            vDHCPProcessEndPoint( xReset, pxEndPoint, pxEndPoint->pxDHCPMessage );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Run one cycle of the DHCP state machine.
 *
 * @param[in] xReset: pdTRUE is the state machine has to be reset.
 * @param[in] pxEndPoint: The end-point that needs DHCP.
 * @param[in] pxDHCPMessage: A DHCP message that has just been received, or NULL.
 */
    static void vDHCPProcessEndPoint( BaseType_t xReset,
                                      NetworkEndPoint_t * pxEndPoint,
                                      DHCPMessage_IPv6_t * pxDHCPMessage )
    {
        BaseType_t xGivingUp = pdFALSE;

        #if ( ipconfigUSE_DHCP_HOOK != 0 )
            eDHCPCallbackAnswer_t eAnswer;
        #endif /* ipconfigUSE_DHCP_HOOK */

        configASSERT( pxEndPoint != NULL );

        /* Is DHCP starting over? */
        if( xReset != pdFALSE )
        {
            EP_DHCPData.eDHCPState = eInitialWait;
        }

        if( ( EP_DHCPData.eDHCPState != EP_DHCPData.eExpectedState ) && ( xReset == pdFALSE ) )
        {
            /* When the DHCP event was generated, the DHCP client was
            * in a different state.  Therefore, ignore this event. */
            FreeRTOS_debug_printf( ( "vDHCPProcessEndPoint: wrong state: expect: %d got: %d : ignore\n",
                                     EP_DHCPData.eExpectedState, EP_DHCPData.eDHCPState ) );
        }
        else
        {
            {
                static eDHCPState_t lastState = eNotUsingLeasedAddress;

                if( lastState != EP_DHCPData.eDHCPState )
                {
                    lastState = EP_DHCPData.eDHCPState;
                    FreeRTOS_debug_printf( ( "vDHCPProcessEndPoint: enter %s (%d)\n", prvStateName( EP_DHCPData.eDHCPState ), EP_DHCPData.eDHCPState ) );
                }
            }

            switch( EP_DHCPData.eDHCPState )
            {
                case eInitialWait:

                    /* Initial state.  Create the DHCP socket, timer, etc. if they
                     * have not already been created. */

                    /* Initial state.  Create the DHCP socket, timer, etc. if they
                     * have not already been created. */
                    prvInitialiseDHCP( pxEndPoint );
                    EP_DHCPData.eDHCPState = eWaitingSendFirstDiscover;
                    /*EP_DHCPData.eExpectedState = eWaitingSendFirstDiscover; */
                    break;

                case eWaitingSendFirstDiscover:
                    /* Ask the user if a DHCP discovery is required. */
                    #if ( ipconfigUSE_DHCP_HOOK != 0 )
                        eAnswer = xApplicationDHCPHook( eDHCPPhasePreDiscover, pxEndPoint->ipv4_defaults.ulIPAddress );

                        if( eAnswer == eDHCPContinue )
                    #endif /* ipconfigUSE_DHCP_HOOK */
                    {
                        /* See if prvInitialiseDHCP() has created a socket. */
                        if( EP_DHCPData.xDHCPSocket == NULL )
                        {
                            FreeRTOS_debug_printf( ( "xGivingUp because socket is closed\n" ) );
                            xGivingUp = pdTRUE;
                        }
                        else
                        {
                            /* Send the first discover request. */
                            EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();
                            prvSendDHCPMessage( pxEndPoint );
                            EP_DHCPData.eDHCPState = eWaitingOffer;
                        }
                    }

                    #if ( ipconfigUSE_DHCP_HOOK != 0 )
                        else
                        {
                            if( eAnswer == eDHCPUseDefaults )
                            {
                                ( void ) memcpy( &( pxEndPoint->ipv4_settings ), &( pxEndPoint->ipv4_defaults ), sizeof( pxEndPoint->ipv4_settings ) );
                            }

                            /* The user indicates that the DHCP process does not continue. */
                            FreeRTOS_debug_printf( ( "xGivingUp because call-back\n" ) );
                            xGivingUp = pdTRUE;
                        }
                    #endif /* ipconfigUSE_DHCP_HOOK */
                    break;

                case eWaitingOffer:

                    xGivingUp = pdFALSE;

                    /* Look for offers coming in. */
                    if( pxDHCPMessage != NULL )
                    {
                        if( pxDHCPMessage->uxMessageType == DHCPv6_message_Type_Advertise )
                        {
                            #if ( ipconfigUSE_DHCP_HOOK != 0 )
                                /* Ask the user if a DHCP request is required. */
                                eAnswer = xApplicationDHCPHook( eDHCPPhasePreRequest, EP_DHCPData.ulOfferedIPAddress );

                                if( eAnswer == eDHCPContinue )
                            #endif /* ipconfigUSE_DHCP_HOOK */
                            {
                                /* An offer has been made, the user wants to continue,
                                 * generate the request. */
                                EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();
                                EP_DHCPData.xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;
                                /* Force creating a new transaction ID. */
                                pxDHCPMessage->ucHasUID = 0U;
                                prvSendDHCPMessage( pxEndPoint );
                                EP_DHCPData.eDHCPState = eWaitingAcknowledge;
                            }

                            #if ( ipconfigUSE_DHCP_HOOK != 0 )
                                else
                                {
                                    if( eAnswer == eDHCPUseDefaults )
                                    {
                                        ( void ) memcpy( &( pxEndPoint->ipv6_settings ), &( pxEndPoint->ipv6_defaults ), sizeof( pxEndPoint->ipv6_settings ) );
                                    }

                                    /* The user indicates that the DHCP process does not continue. */
                                    FreeRTOS_debug_printf( ( "xGivingUp because call-back 2\n" ) );
                                    xGivingUp = pdTRUE;
                                }
                            #endif /* ipconfigUSE_DHCP_HOOK */
                        }
                    }

                    /* Is it time to send another Discover? */
                    else if( ( xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod )
                    {
                        /* It is time to send another Discover.  Increase the time
                         * period, and if it has not got to the point of giving up - send
                         * another discovery. */
                        EP_DHCPData.xDHCPTxPeriod <<= 1;

                        if( EP_DHCPData.xDHCPTxPeriod <= ipconfigMAXIMUM_DISCOVER_TX_PERIOD )
                        {
                            EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();
                            prvSendDHCPMessage( pxEndPoint );
                            FreeRTOS_debug_printf( ( "vDHCPProcess: timeout %lu ticks\n", EP_DHCPData.xDHCPTxPeriod ) );
                        }
                        else
                        {
                            FreeRTOS_debug_printf( ( "vDHCPProcess: giving up %lu > %lu ticks\n", EP_DHCPData.xDHCPTxPeriod, ipconfigMAXIMUM_DISCOVER_TX_PERIOD ) );

                            #if ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 )
                                {
                                    /* Only use a fake Ack if the default IP address == 0x00
                                     * and the link local addressing is used.  Start searching
                                     * a free LinkLayer IP-address.  Next state will be
                                     * 'eGetLinkLayerAddress'. */
                                    prvPrepareLinkLayerIPLookUp( pxEndPoint );

                                    /* Setting an IP address manually so set to not using
                                     * leased address mode. */
                                    EP_DHCPData.eDHCPState = eGetLinkLayerAddress;
                                }
                            #else
                                {
                                    xGivingUp = pdTRUE;
                                }
                            #endif /* ipconfigDHCP_FALL_BACK_AUTO_IP */
                        }
                    }
                    else
                    {
                        /* There was no DHCP reply, there was no time-out, just keep on waiting. */
                    }

                    break;

                case eWaitingAcknowledge:
                   {
                       int a = ( pxDHCPMessage == NULL ) ? -1 : ( ( int ) pxDHCPMessage->uxMessageType );
                       int b = DHCPv6_message_Type_Reply;
                       FreeRTOS_printf( ( "vDHCPProcess: eWaitingAcknowledge with %d %c= %u\n", a, ( a == b ) ? '=' : '!', b ) );
                       eventLogAdd( "%d %c= %u\n", a, ( a == b ) ? '=' : '!', b );
                   }

                    if( pxDHCPMessage == NULL )
                    {
                        /* Is it time to send another Discover? */
                        if( ( xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod )
                        {
                            /* Increase the time period, and if it has not got to the
                             * point of giving up - send another request. */
                            EP_DHCPData.xDHCPTxPeriod <<= 1;

                            if( EP_DHCPData.xDHCPTxPeriod <= ipconfigMAXIMUM_DISCOVER_TX_PERIOD )
                            {
                                EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();
                                prvSendDHCPMessage( pxEndPoint );
                                FreeRTOS_printf( ( "vDHCPProcess: eWaitingAcknowledge: try again with %lu\n", EP_DHCPData.xDHCPTxPeriod ) );
                            }
                            else
                            {
                                /* Give up, start again. */
                                EP_DHCPData.eDHCPState = eInitialWait;
                            }
                        }
                    }
                    else if( pxDHCPMessage->uxMessageType == DHCPv6_message_Type_Reply )
                    {
                        FreeRTOS_printf( ( "vDHCPProcess: acked %lxip\n", FreeRTOS_ntohl( EP_DHCPData.ulOfferedIPAddress ) ) );
                        eventLogAdd( "acked %lxip\n", FreeRTOS_ntohl( EP_DHCPData.ulOfferedIPAddress ) );

                        /* DHCP completed.  The IP address can now be used, and the
                         * timer set to the lease timeout time. */
                        /*pxEndPoint->ipv6_settings.xIPAddress;		/ * The actual IPv4 address. Will be 0 as long as end-point is still down. * / */
                        pxEndPoint->ipv6_settings.uxPrefixLength = pxDHCPMessage->ucprefixLength;                                           /* Number of valid bytes in the network prefix. */
                        memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, pxDHCPMessage->xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                        memcpy( pxEndPoint->ipv6_settings.xPrefix.ucBytes, pxDHCPMessage->xPrefixAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS ); /* The network prefix, e.g. fe80::/10 */
                        /*pxEndPoint->xGatewayAddress;	/ * Gateway to the web. * / */
                        memcpy( pxEndPoint->ipv6_settings.xDNSServerAddresses[ 0 ].ucBytes, pxDHCPMessage->ucDNSServer.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

                        EP_DHCPData.eDHCPState = eLeasedAddress;

                        iptraceDHCP_SUCCEDEED( EP_DHCPData.ulOfferedIPAddress );

                        /* Close socket to ensure packets don't queue on it. */
                        prvCloseDHCPSocket( pxEndPoint );

                        if( EP_DHCPData.ulLeaseTime == 0UL )
                        {
                            EP_DHCPData.ulLeaseTime = dhcpDEFAULT_LEASE_TIME;
                        }
                        else if( EP_DHCPData.ulLeaseTime < dhcpMINIMUM_LEASE_TIME )
                        {
                            EP_DHCPData.ulLeaseTime = dhcpMINIMUM_LEASE_TIME;
                        }
                        else
                        {
                            /* The lease time is already valid. */
                        }

                        /* Check for clashes. */
/*					vARPSendGratuitous(); */
                        vIPReloadDHCP_RATimer( ( struct xNetworkEndPoint * ) pxEndPoint, EP_DHCPData.ulLeaseTime );

                        /* DHCP failed, the default configured IP-address will be used
                         * Now call vIPNetworkUpCalls() to send the network-up event and
                         * start the ARP timer. */
                        vIPNetworkUpCalls( pxEndPoint );
                    }
                    else
                    {
                        /* There are no replies yet. */
                    }

                    break;

                    #if ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 )
                        case eGetLinkLayerAddress:

                            if( ( xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod )
                            {
                                if( xARPHadIPClash == pdFALSE )
                                {
                                    /* ARP OK. proceed. */
                                    iptraceDHCP_SUCCEDEED( EP_DHCPData.ulOfferedIPAddress );

                                    EP_DHCPData.eDHCPState = eNotUsingLeasedAddress;

                                    /* Auto-IP succeeded, the default configured IP-address will
                                     * be used.  Now call vIPNetworkUpCalls() to send the
                                     * network-up event and start the ARP timer. */
                                    vIPNetworkUpCalls( pxEndPoint );
                                }
                                else
                                {
                                    /* ARP clashed - try another IP address. */
                                    prvPrepareLinkLayerIPLookUp( pxEndPoint );

                                    /* Setting an IP address manually so set to not using leased
                                     * address mode. */
                                    EP_DHCPData.eDHCPState = eGetLinkLayerAddress;
                                }
                            }
                            break;
                    #endif /* ipconfigDHCP_FALL_BACK_AUTO_IP */

                case eLeasedAddress:

                    /* Resend the request at the appropriate time to renew the lease. */
                    prvCreateDHCPSocket( pxEndPoint );

                    if( EP_DHCPData.xDHCPSocket != NULL )
                    {
                        EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();
                        EP_DHCPData.xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;
                        prvSendDHCPMessage( pxEndPoint );
                        EP_DHCPData.eDHCPState = eWaitingAcknowledge;

                        /* From now on, we should be called more often */
                        vIPReloadDHCP_RATimer( pxEndPoint, dhcpINITIAL_TIMER_PERIOD );
                    }

                    break;

                case eNotUsingLeasedAddress:

                    vIPSetDHCP_RATimerEnableState( pxEndPoint, pdFALSE );
                    break;

                default:
                    /* Lint: all options are included. */
                    break;
            }

/*{ */
/*	static eDHCPState_t lastState = eNotUsingLeasedAddress; */
/*	if( lastState != EP_DHCPData.eDHCPState ) */
/*	{ */
/*		lastState = EP_DHCPData.eDHCPState; */
/*		FreeRTOS_debug_printf( ( "vDHCPProcessEndPoint: exit %d\n", EP_DHCPData.eDHCPState ) ); */
/*	} */
/*} */

            if( xGivingUp != pdFALSE )
            {
                FreeRTOS_debug_printf( ( "vDHCPProcessEndPoint: Giving up\n" ) );

                /* xGivingUp became true either because of a time-out, or because
                 * xApplicationDHCPHook() returned another value than 'eDHCPContinue',
                 * meaning that the conversion is cancelled from here. */

                /* Revert to static IP address. */
                taskENTER_CRITICAL();
                {
                    memcpy( EP_IPv6_SETTINGS.xIPAddress.ucBytes, pxEndPoint->ipv6_defaults.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                    iptraceDHCP_REQUESTS_FAILED_USING_DEFAULT_IPv6_ADDRESS( EP_IPv6_SETTINGS.xIPAddress );
                }
                taskEXIT_CRITICAL();

                EP_DHCPData.eDHCPState = eNotUsingLeasedAddress;
                vIPSetDHCP_RATimerEnableState( pxEndPoint, pdFALSE );

                /* Close socket to ensure packets don't queue on it. */
                prvCloseDHCPSocket( pxEndPoint );

                /* DHCP failed, the default configured IP-address will be used. Now
                 * call vIPNetworkUpCalls() to send the network-up event and start the ARP
                 * timer. */
                vIPNetworkUpCalls( pxEndPoint );
            }
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Close the shared UDP/DHCP socket.  This results in lowering the reference count.
 *        The last user of the socket will close it.
 *
 * @param[in] pxEndPoint: The end-point that wants to close the socket.
 */
    static void prvCloseDHCPSocket( NetworkEndPoint_t * pxEndPoint )
    {
        if( ( EP_DHCPData.xDHCPSocket == NULL ) || ( EP_DHCPData.xDHCPSocket != xDHCPSocket ) )
        {
            /* the socket can not be closed. */
        }
        else if( xDHCPSocketUserCount > 0 )
        {
            xDHCPSocketUserCount--;

            if( xDHCPSocketUserCount == 0 )
            {
                /* This modules runs from the IP-task. Use the internal
                 * function 'vSocketClose()` to close the socket. */
                ( void ) vSocketClose( xDHCPSocket );
                xDHCPSocket = NULL;
            }

            EP_DHCPData.xDHCPSocket = NULL;
        }
        else
        {
            /* Strange: there is a socket, but there are no users. */
        }

        FreeRTOS_printf( ( "DHCP-socket[%02x-%02x]: closed, user count %d\n",
                           pxEndPoint->xMACAddress.ucBytes[ 4 ],
                           pxEndPoint->xMACAddress.ucBytes[ 5 ],
                           ( int ) xDHCPSocketUserCount ) );
    }

/**
 * @brief Return the UDP/DHCP socket, or create if it doesn't exist.
 *
 * @param[in] pxEndPoint: The end-point that needs the socket.
 */
    static void prvCreateDHCPSocket( NetworkEndPoint_t * pxEndPoint )
    {
        struct freertos_sockaddr xAddress;
        BaseType_t xReturn;
        TickType_t xTimeoutTime = ( TickType_t ) 0;

        if( ( xDHCPSocket != NULL ) && ( EP_DHCPData.xDHCPSocket == xDHCPSocket ) )
        {
            /* the socket is still valid. */
        }
        else if( xDHCPSocket == NULL ) /* Create the socket, if it has not already been created. */
        {
            xDHCPSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
            configASSERT( ( xDHCPSocket != FREERTOS_INVALID_SOCKET ) );

            /* Ensure the Rx and Tx timeouts are zero as the DHCP executes in the
             * context of the IP task. */
            ( void ) FreeRTOS_setsockopt( xDHCPSocket, 0, FREERTOS_SO_RCVTIMEO, &( xTimeoutTime ), sizeof( TickType_t ) );
            ( void ) FreeRTOS_setsockopt( xDHCPSocket, 0, FREERTOS_SO_SNDTIMEO, &( xTimeoutTime ), sizeof( TickType_t ) );

            /* Bind to the standard DHCP client port. */
            xAddress.sin_port = FreeRTOS_htons( DHCPv6_CLIENT_PORT );
            xReturn = vSocketBind( xDHCPSocket, &xAddress, sizeof( xAddress ), pdFALSE );
            configASSERT( xReturn == 0 );
            xDHCPSocketUserCount = 1;
            FreeRTOS_printf( ( "DHCP-socket[%02x-%02x]: DHCP Socket Create\n",
                               pxEndPoint->xMACAddress.ucBytes[ 4 ],
                               pxEndPoint->xMACAddress.ucBytes[ 5 ] ) );

            /* Remove compiler warnings if configASSERT() is not defined. */
            ( void ) xReturn;
        }
        else
        {
            xDHCPSocketUserCount++;
        }

        EP_DHCPData.xDHCPSocket = xDHCPSocket;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Initialise the DHCP state machine of a given end-point.
 *
 * @param[in] pxEndPoint: The end-point.
 */
    static void prvInitialiseDHCP( NetworkEndPoint_t * pxEndPoint )
    {
        /* Initialise the parameters that will be set by the DHCP process. Per
         * https://www.ietf.org/rfc/rfc2131.txt, Transaction ID should be a random
         * value chosen by the client. */

        /* Check for random number generator API failure. */
        EP_DHCPData.ulOfferedIPAddress = 0UL;
        EP_DHCPData.ulDHCPServerAddress = 0UL;
        EP_DHCPData.xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;
        /* Force creating a new transaction ID. */
        pxEndPoint->pxDHCPMessage->ucHasUID = 0U;

        /* Create the DHCP socket if it has not already been created. */
        prvCreateDHCPSocket( pxEndPoint );
        FreeRTOS_debug_printf( ( "prvInitialiseDHCP: start after %lu ticks\n", dhcpINITIAL_TIMER_PERIOD ) );
        vIPReloadDHCP_RATimer( pxEndPoint, dhcpINITIAL_TIMER_PERIOD );
    }
/*-----------------------------------------------------------*/

/**
 * @brief Send a DHCPv6 message to a DHCP server.
 *
 * @param[in] pxEndPoint: The end-point for which a message will be sent.
 */
    static void prvSendDHCPMessage( NetworkEndPoint_t * pxEndPoint )
    {
        BaseType_t xRandomOk = pdTRUE;
        DHCPMessage_IPv6_t * pxDHCPMessage = pxEndPoint->pxDHCPMessage;

        configASSERT( pxEndPoint != NULL );

        if( pxDHCPMessage->ucHasUID == 0U )
        {
            uint32_t ulTransactionID;
            time_t uxCurTime;

            xRandomOk = xApplicationGetRandomNumber( &( ulTransactionID ) );
            ulTransactionID &= 0xffffffU;
            time( &( uxCurTime ) );
            pxDHCPMessage->ulTimeStamp = ( uint32_t ) uxCurTime - ( uint32_t ) SECS_FROM_1970_TILL_2000;
            pxDHCPMessage->ucHasUID = 1U;
            pxDHCPMessage->ucTransactionID[ 0 ] = ( uint8_t ) ( ( ulTransactionID >> 16 ) & 0xffU );
            pxDHCPMessage->ucTransactionID[ 1 ] = ( uint8_t ) ( ( ulTransactionID >> 8 ) & 0xffU );
            pxDHCPMessage->ucTransactionID[ 2 ] = ( uint8_t ) ( ulTransactionID & 0xffU );
            pxEndPoint->xDHCPData.ulTransactionId = ulTransactionID;
            FreeRTOS_debug_printf( ( "Created transaction ID : 0x%06lX\n", ulTransactionID ) );
        }

        if( ( xRandomOk == pdPASS ) && ( EP_DHCPData.xDHCPSocket != NULL ) )
        {
            BitCOnfig_t xMessage;
            struct freertos_sockaddr6 xAddress;
            uint8_t ucMessageType = 0;

            xBitConfig_init( &( xMessage ), NULL, 256 ); /* Clear the message. */

            switch( EP_DHCPData.eDHCPState )
            {
                case eWaitingSendFirstDiscover:
                    ucMessageType = DHCPv6_message_Type_Solicit;
                    break;

                case eWaitingOffer:
                    ucMessageType = DHCPv6_message_Type_Request;
                    break;

                default:
                    break;
            }

            if( ucMessageType != 0U )
            {
                xBitConfig_write_8( &( xMessage ), ucMessageType ); /* 1 Solicit, 3, request */
                xBitConfig_write_uc( &( xMessage ), pxDHCPMessage->ucTransactionID, 3 );

                pxDHCPMessage->xClientID.usDUIDType = 1U;
                pxDHCPMessage->xClientID.usHardwareType = 1U;

                /* DHCPv6_Option_Client_Identifier */
                xBitConfig_write_16( &( xMessage ), DHCPv6_Option_Client_Identifier );                             /* Option is 1: Client Identifier */
                xBitConfig_write_16( &( xMessage ), 14U );                                                         /* length is 14 */
                xBitConfig_write_16( &( xMessage ), pxDHCPMessage->xClientID.usDUIDType );                         /* 1 : Link Layer address + time */
                xBitConfig_write_16( &( xMessage ), pxDHCPMessage->xClientID.usHardwareType );                     /* 1 : Ethernet */
                xBitConfig_write_32( &( xMessage ), pxDHCPMessage->ulTimeStamp );                                  /* DUID Time: Jan  3, 2020. */
                xBitConfig_write_uc( &( xMessage ), pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES ); /* Link Layer address, 6 bytes */

                if( pxDHCPMessage->xServerID.uxLength != 0U )
                {
                    /* DHCPv6_Option_Server_Identifier */
                    xBitConfig_write_16( &( xMessage ), DHCPv6_Option_Server_Identifier );        /* Option is 1: Server Identifier */
                    xBitConfig_write_16( &( xMessage ), pxDHCPMessage->xServerID.uxLength + 4U ); /* length is 14 */
                    xBitConfig_write_16( &( xMessage ), pxDHCPMessage->xServerID.usDUIDType );    /* The type of DUID: 1, 2, or 3. */
                    xBitConfig_write_16( &( xMessage ), pxDHCPMessage->xServerID.usHardwareType );
                    xBitConfig_write_uc( &( xMessage ), pxDHCPMessage->xServerID.pucID, pxDHCPMessage->xServerID.uxLength );
                }

                if( EP_DHCPData.eDHCPState == eWaitingSendFirstDiscover )
                {
                    /* DHCPv6_Option_Option_List */
                    xBitConfig_write_16( &( xMessage ), DHCPv6_Option_Option_List );               /* usOption;	Option is 6 */
                    xBitConfig_write_16( &( xMessage ), 4U );                                      /* usLength;	length is 4 */
                    xBitConfig_write_16( &( xMessage ), DHCP6_OPTION_REQUEST_DNS );                /* usOption_1;	00 17 : DNS Recursive name server. */
                    xBitConfig_write_16( &( xMessage ), DHCP6_OPTION_REQUEST_DOMAIN_SEARCH_LIST ); /* usOption_2;	00 18 : Domain search list. */
                }

                /* DHCPv6_Option_Elapsed_Time */
                xBitConfig_write_16( &( xMessage ), DHCPv6_Option_Elapsed_Time ); /* usOption;	Option is 8 * / */
                xBitConfig_write_16( &( xMessage ), 2U );                         /* usLength;	length is 2 * / */
                xBitConfig_write_16( &( xMessage ), 0x0000 );                     /* usTime;		00 00 : 0 ms. * / */

                /* DHCPv6_Option_Identity_Association_for_Prefix_Delegation */
                uint32_t ulIAID = 0x27fe8f95;
                uint32_t ulTime_1 = 3600U;
                uint32_t ulTime_2 = 5400U;

                xBitConfig_write_16( &( xMessage ), DHCPv6_Option_Identity_Association_for_Prefix_Delegation ); /* usOption;	Option is 25 */
                xBitConfig_write_16( &( xMessage ), 41 );                                                       /* usLength;	length is 12 + 29 = 41 */
                xBitConfig_write_32( &( xMessage ), ulIAID );                                                   /* 27 fe 8f 95. */
                xBitConfig_write_32( &( xMessage ), ulTime_1 );                                                 /* 00 00 0e 10: 3600 sec */
                xBitConfig_write_32( &( xMessage ), ulTime_2 );                                                 /* 00 00 15 18: 5400 sec */

                /* DHCPv6_Option_IA_Prefix */
                uint32_t ulPreferredLifeTime = 4500U;
                uint32_t ulPValidLifeTime = 7200U;
                uint8_t ucPrefixLength = 64;

                xBitConfig_write_16( &( xMessage ), DHCPv6_Option_IA_Prefix );                                 /* usOption   Option is 26 */
                xBitConfig_write_16( &( xMessage ), 25 );                                                      /* usLength   length is 25 */
                xBitConfig_write_32( &( xMessage ), ulPreferredLifeTime );                                     /* 4500 */
                xBitConfig_write_32( &( xMessage ), ulPValidLifeTime );                                        /* 7200 */
                xBitConfig_write_8( &( xMessage ), ucPrefixLength );                                           /* 64 bits */
                xBitConfig_write_uc( &( xMessage ), pxEndPoint->xMACAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS ); /* 2001:0:0:fe00:: */

                xBitConfig_write_16( &( xMessage ), DHCPv6_Option_NonTemporaryAddress );                       /* usOption   Option is 3 */
                xBitConfig_write_16( &( xMessage ), 12 );                                                      /* usLength   length is 12 */
                xBitConfig_write_32( &( xMessage ), ulIAID );                                                  /* 27 fe 8f 95. */
                xBitConfig_write_32( &( xMessage ), ulPreferredLifeTime );                                     /* 4500 */
                xBitConfig_write_32( &( xMessage ), ulPValidLifeTime );                                        /* 7200 */

                if( EP_DHCPData.eDHCPState == eWaitingSendFirstDiscover )
                {
                    xBitConfig_write_16( &( xMessage ), DHCPv6_Option_DNS_recursive_name_server ); /* usOption   Option is 23 */
                    xBitConfig_write_16( &( xMessage ), 0U );                                      /* usLength   length is 0 */
                }

                memset( &( xAddress ), 0, sizeof xAddress );
                FreeRTOS_inet_pton6( "ff02::1:2", xAddress.sin_addrv6.ucBytes );
                xAddress.sin_len = sizeof xAddress; /* length of this structure. */
                xAddress.sin_family = FREERTOS_AF_INET6;
                xAddress.sin_port = FreeRTOS_htons( DHCPv6_SERVER_PORT );

                FreeRTOS_sendto( EP_DHCPData.xDHCPSocket, ( const void * ) xMessage.ucContents, xMessage.uxIndex, 0, ( const struct freertos_sockaddr * ) &( xAddress ), sizeof xAddress );
            }

            vBitConfig_release( &( xMessage ) );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Analyse the reply from a DHCP server.
 *
 * @param[in] pucAnswer: The payload text of the incoming packet.
 * @param[in] uxLength: The number of valid bytes in pucAnswer.
 * @param[in] pxDHCPMessage: The DHCP object of the end-point.
 *
 * @return pdTRUE if the analysis was successful.
 */
    static BaseType_t prvDHCPv6Analyse( const uint8_t * pucAnswer,
                                        size_t uxLength,
                                        DHCPMessage_IPv6_t * pxDHCPMessage )
    {
        BitCOnfig_t xMessage;
        BaseType_t xResult = pdPASS;
        uint32_t ulOptionsReceived = 0U;

        if( xBitConfig_init( &xMessage, pucAnswer, uxLength ) != pdFAIL )
        {
            BaseType_t xReady = pdFALSE;

            memset( pxDHCPMessage, 0, sizeof( *pxDHCPMessage ) );

            pxDHCPMessage->uxMessageType = ucBitConfig_read_8( &xMessage );
            xBitConfig_read_uc( &xMessage, pxDHCPMessage->ucTransactionID, 3 );

            pxDHCPMessage->ulTransactionID =
                ( ( ( uint32_t ) pxDHCPMessage->ucTransactionID[ 0 ] ) << 16 ) |
                ( ( ( uint32_t ) pxDHCPMessage->ucTransactionID[ 1 ] ) << 8 ) |
                ( ( ( uint32_t ) pxDHCPMessage->ucTransactionID[ 2 ] ) );

            FreeRTOS_printf( ( "prvDHCPv6Analyse: Message %u ID theirs 0x%06X\n",
                               ( unsigned ) pxDHCPMessage->uxMessageType,
                               ( unsigned ) pxDHCPMessage->ulTransactionID ) );

            switch( pxDHCPMessage->uxMessageType )
            {
                case DHCPv6_message_Type_Advertise:
                case DHCPv6_message_Type_Confirm:
                case DHCPv6_message_Type_Reply:
                case DHCPv6_message_Type_Decline:
                    break;

                default:
                    FreeRTOS_printf( ( "prvDHCPv6Analyse: Can not handle message type %u\n",
                                       ( unsigned ) pxDHCPMessage->uxMessageType ) );
                    xResult = pdFAIL;
                    break;
            }

            if( xResult == pdFAIL )
            {
                /* Ignore the reply because the message type is wrong. */
                xReady = pdTRUE;
            }
            else if( xMessage.xHasError != pdFALSE )
            {
                xReady = pdTRUE;
                xResult = pdFAIL;
            }

            while( xReady == pdFALSE )
            {
                uint16_t usOption;
                size_t uxLength;
                size_t uxStart;

                usOption = usBitConfig_read_16( &xMessage );
                uxLength = ( size_t ) usBitConfig_read_16( &xMessage );
                uxStart = xMessage.uxIndex;

                if( xMessage.xHasError != pdFALSE )
                {
                    FreeRTOS_printf( ( "prvDHCPv6Analyse: bad input\n" ) );
                    xReady = pdTRUE;
                    xResult = pdFAIL;
                }
                else
                {
                    ulOptionsReceived |= ( 1U << usOption );

                    switch( usOption )
                    {
                        case DHCPv6_Option_Client_Identifier:
                           {
                               size_t uxIDSize = uxLength - 4U;

                               /*
                                *  1 : Link-layer address plus time (DUID-LLT)
                                *  2 : Vendor-assigned unique ID based on Enterprise Number (DUID-EN)
                                *  3 : Link-layer address (DUID-LL)
                                */
                               pxDHCPMessage->xClientID.uxLength = uxIDSize;
                               pxDHCPMessage->xClientID.usDUIDType = usBitConfig_read_16( &( xMessage ) );     /* 0x0001 : Link Layer address + time */
                               pxDHCPMessage->xClientID.usHardwareType = usBitConfig_read_16( &( xMessage ) ); /* 1 = Ethernet. */

                               if( uxIDSize <= sizeof( pxDHCPMessage->xClientID.pucID ) )
                               {
                                   xBitConfig_read_uc( &( xMessage ), pxDHCPMessage->xClientID.pucID, uxIDSize ); /* Link Layer address, 6 bytes */
                               }
                               else
                               {
                                   FreeRTOS_printf( ( "prvDHCPv6Analyse: client ID too long\n" ) );
                               }
                           }
                           break;

                        case DHCPv6_Option_Server_Identifier:
                           {
                               size_t uxIDSize = uxLength - 4U;

                               /*
                                *  1 : Link-layer address plus time (DUID-LLT)
                                *  2 : Vendor-assigned unique ID based on Enterprise Number (DUID-EN)
                                *  3 : Link-layer address (DUID-LL)
                                */
                               pxDHCPMessage->xServerID.uxLength = uxIDSize;
                               pxDHCPMessage->xServerID.usDUIDType = usBitConfig_read_16( &( xMessage ) );     /* 0x0001 : Link Layer address + time */
                               pxDHCPMessage->xServerID.usHardwareType = usBitConfig_read_16( &( xMessage ) ); /* 1 = Ethernet. */

                               if( uxIDSize <= sizeof( pxDHCPMessage->xServerID.pucID ) )
                               {
                                   xBitConfig_read_uc( &( xMessage ), pxDHCPMessage->xServerID.pucID, uxIDSize ); /* Link Layer address, 6 bytes */
                               }
                               else
                               {
                                   FreeRTOS_printf( ( "prvDHCPv6Analyse: server ID too long\n" ) );
                               }
                           }
                           break;

                        case DHCPv6_Option_Preference:
                           {
                               uint8_t ucPreference = ucBitConfig_read_8( &xMessage );
                               ( void ) ucPreference;
/*							FreeRTOS_printf( ( "Option preference: %02x\n", ucPreference ) ); */
                           }
                           break;

                        case DHCPv6_Option_DNS_recursive_name_server:
                           {
                               size_t uDNSCount;

                               if( ( uxLength == 0U ) || ( ( uxLength % ipSIZE_OF_IPv6_ADDRESS ) != 0U ) )
                               {
                                   FreeRTOS_printf( ( "prvDHCPv6Analyse: bad DNS length\n" ) );
                                   xReady = pdTRUE;
                                   break;
                               }

                               uDNSCount = uxLength / ipSIZE_OF_IPv6_ADDRESS;

                               while( uDNSCount > 0U )
                               {
                                   xBitConfig_read_uc( &( xMessage ), pxDHCPMessage->ucDNSServer.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                                   FreeRTOS_printf( ( "DNS server: %pip\n", pxDHCPMessage->ucDNSServer.ucBytes ) );
                                   uDNSCount--;
                               }
                           }
                           break;

                        case DHCPv6_Option_Domain_Search_List:
                            xBitConfig_read_uc( &xMessage, NULL, uxLength );
                            break;

                        case DHCPv6_Option_NonTemporaryAddress:
                        case DHCPv6_Option_Identity_Association_for_Prefix_Delegation:
                           {
                               uint32_t ulIAID = ulBitConfig_read_32( &( xMessage ) );
                               uint32_t ulTime_1 = ulBitConfig_read_32( &( xMessage ) );
                               uint32_t ulTime_2 = ulBitConfig_read_32( &( xMessage ) );
                               size_t uxUsed = xMessage.uxIndex - uxStart;
                               size_t uxRemain = 0U;

                               ( void ) ulIAID;
                               ( void ) ulTime_1;
                               ( void ) ulTime_2;

                               if( uxLength > uxUsed )
                               {
                                   uxRemain = uxLength - uxUsed;
                               }

                               while( uxRemain >= 4 )
                               {
                                   uint16_t usOption2 = usBitConfig_read_16( &xMessage );
                                   uint16_t uxLength2 = ( size_t ) usBitConfig_read_16( &xMessage );

                                   ( void ) uxLength2;
                                   uxUsed = xMessage.uxIndex - uxStart;

                                   switch( usOption2 )
                                   {
                                       case DHCPv6_Option_IA_Address:
                                           xBitConfig_read_uc( &( xMessage ), pxDHCPMessage->xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                                           pxDHCPMessage->ulPreferredLifeTime = ulBitConfig_read_32( &( xMessage ) );
                                           pxDHCPMessage->ulValidLifeTime = ulBitConfig_read_32( &( xMessage ) );
                                           FreeRTOS_printf( ( "IP Address %pip\n", pxDHCPMessage->xIPAddress.ucBytes ) );
                                           break;

                                       case DHCPv6_Option_IA_Prefix:
                                           pxDHCPMessage->ulPreferredLifeTime = ulBitConfig_read_32( &( xMessage ) );
                                           pxDHCPMessage->ulValidLifeTime = ulBitConfig_read_32( &( xMessage ) );
                                           pxDHCPMessage->ucprefixLength = ucBitConfig_read_8( &( xMessage ) );
                                           xBitConfig_read_uc( &( xMessage ), pxDHCPMessage->xPrefixAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                                           FreeRTOS_printf( ( "Address prefix: %pip length %d\n", pxDHCPMessage->xPrefixAddress.ucBytes, pxDHCPMessage->ucprefixLength ) );
                                           break;

                                       case DHCPv6_Option_Status_Code:
                                          {
                                              uint16_t usStatus = usBitConfig_read_16( &( xMessage ) );
                                              uxUsed = xMessage.uxIndex - uxStart;

                                              FreeRTOS_printf( ( "%s %s with status %u\n",
                                                                 ( usOption == DHCPv6_Option_NonTemporaryAddress ) ? "Address assignment" : "Prefix Delegation",
                                                                 ( usStatus == 0 ) ? "succeeded" : "failed", usStatus ) );

                                              if( uxLength > uxUsed )
                                              {
                                                  uxRemain = uxLength - uxUsed;
                                                  uint8_t ucMessage[ 100 ];

                                                  xBitConfig_read_uc( &( xMessage ), ucMessage, uxRemain );
                                                  ucMessage[ uxRemain ] = 0;
                                                  FreeRTOS_printf( ( "Msg: '%s'\n", ucMessage ) );
                                              }
                                          }
                                          break;

                                       default:
                                           uxRemain = uxLength - uxUsed;
                                           xBitConfig_read_uc( &( xMessage ), NULL, uxRemain );
                                           FreeRTOS_printf( ( "prvDHCPv6Analyse: skipped unknown option %u\n", usOption2 ) );
                                           break;
                                   }

                                   uxUsed = xMessage.uxIndex - uxStart;
                                   uxRemain = 0U;

                                   if( uxLength > uxUsed )
                                   {
                                       uxRemain = uxLength - uxUsed;
                                   }
                               }
                           }
                           break;

                        default:
                            FreeRTOS_printf( ( "prvDHCPv6Analyse: Option %u not implemented\n", usOption ) );
                            xBitConfig_read_uc( &xMessage, NULL, uxLength );
                            break;
                    }
                }

                if( xMessage.xHasError != pdFALSE )
                {
                    FreeRTOS_printf( ( "prvDHCPv6Analyse: bad input\n" ) );
                    xReady = pdTRUE;
                    xResult = pdFAIL;
                }
                else if( xMessage.uxIndex == xMessage.uxSize )
                {
                    /*FreeRTOS_printf( ( "prvDHCPv6Analyse: end of message\n" ) ); */
                    xReady = pdTRUE;
                }
            } /* while( xReady == pdFALSE ) */

            vBitConfig_release( &( xMessage ) );

            if( xResult == pdPASS )
            {
                ulOptionsReceived &= dhcpMANDATORY_OPTIONS;

                if( ulOptionsReceived != dhcpMANDATORY_OPTIONS )
                {
                    xResult = pdFAIL;
                    FreeRTOS_printf( ( "prvDHCPv6Analyse: Missing options: %lX != %lX\n", ulOptionsReceived, dhcpMANDATORY_OPTIONS ) );
                }
            }
        } /* if( xBitConfig_init() ) */
        else
        {
            xResult = pdFAIL;
        }

        return xResult;
    }
/*-----------------------------------------------------------*/

/**
 * @brief transform a state number in a descriptive string.
 *
 * @param[in] eState: The DHCP state number.
 *
 * @return A descriptive string.
 */
    static const char * prvStateName( eDHCPState_t eState )
    {
        switch( eState )
        {
            case eInitialWait:
                return "eInitialWait";

            case eWaitingSendFirstDiscover:
                return "eWaitingSendFirstDiscover";

            case eWaitingOffer:
                return "eWaitingOffer";

            case eWaitingAcknowledge:
                return "eWaitingAcknowledge";

                #if ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 )
                    case eGetLinkLayerAddress:
                        return "eGetLinkLayerAddress";
                #endif
            case eLeasedAddress:
                return "eLeasedAddress";

            case eNotUsingLeasedAddress:
                return "eNotUsingLeasedAddress";
        }

        return "Unknown state";
    }

#endif /* ( ipconfigUSE_IPv6 != 0 ) && ( ipconfigUSE_DHCPv6 != 0 ) */
