/*
 * FreeRTOS+TCP V3.1.0
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
 * @file FreeRTOS_DHCP.c
 * @brief Implements the Dynamic Host Configuration Protocol for the FreeRTOS+TCP network stack.
 */

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_IP_Timers.h"


/* Exclude the entire file if DHCP is not enabled. */
#if ( ipconfigUSE_DHCP != 0 )

    #include "NetworkInterface.h"
    #include "NetworkBufferManagement.h"

/** @brief The UDP socket used for all incoming and outgoing DHCP traffic. */
    _static Socket_t xDHCPSocket;

    #if ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 )
        /* Define the Link Layer IP address: 169.254.x.x */
        #define LINK_LAYER_ADDRESS_0    169
        #define LINK_LAYER_ADDRESS_1    254

/* Define the netmask used: 255.255.0.0 */
        #define LINK_LAYER_NETMASK_0    255
        #define LINK_LAYER_NETMASK_1    255
        #define LINK_LAYER_NETMASK_2    0
        #define LINK_LAYER_NETMASK_3    0
    #endif


/*
 * Generate a DHCP discover message and send it on the DHCP socket.
 */
    static BaseType_t prvSendDHCPDiscover( void );

/*
 * Interpret message received on the DHCP socket.
 */
    _static BaseType_t prvProcessDHCPReplies( BaseType_t xExpectedMessageType );

/*
 * Generate a DHCP request packet, and send it on the DHCP socket.
 */
    static BaseType_t prvSendDHCPRequest( void );

/*
 * Prepare to start a DHCP transaction.  This initialises some state variables
 * and creates the DHCP socket if necessary.
 */
    static void prvInitialiseDHCP( void );

/*
 * Creates the part of outgoing DHCP messages that are common to all outgoing
 * DHCP messages.
 */
    static uint8_t * prvCreatePartDHCPMessage( struct freertos_sockaddr * pxAddress,
                                               BaseType_t xOpcode,
                                               const uint8_t * const pucOptionsArray,
                                               size_t * pxOptionsArraySize );

/*
 * Create the DHCP socket, if it has not been created already.
 */
    _static void prvCreateDHCPSocket( void );

/*
 * Close the DHCP socket.
 */
    static void prvCloseDHCPSocket( void );

/*
 * After DHCP has failed to answer, prepare everything to start searching
 * for (trying-out) LinkLayer IP-addresses, using the random method: Send
 * a gratuitous ARP request and wait if another device responds to it.
 */
    #if ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 )
        static void prvPrepareLinkLayerIPLookUp( void );
    #endif

/*-----------------------------------------------------------*/

/** @brief Hold information in between steps in the DHCP state machine. */
    _static DHCPData_t xDHCPData;

/*-----------------------------------------------------------*/

/**
 * @brief Check whether a given socket is the DHCP socket or not.
 *
 * @param[in] xSocket: The socket to be checked.
 *
 * @return If the socket given as parameter is the DHCP socket - return
 *         pdTRUE, else pdFALSE.
 */
    BaseType_t xIsDHCPSocket( const ConstSocket_t xSocket )
    {
        BaseType_t xReturn;

        if( xDHCPSocket == xSocket )
        {
            xReturn = pdTRUE;
        }
        else
        {
            xReturn = pdFALSE;
        }

        return xReturn;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief The application can indicate a preferred IP address by calling this function.
 *        before starting up the IP-task by calling FreeRTOS_IPInit().
 *
 * @param[in] ulIPAddress: The preferred IP-address.
 *
 * @return The previous value of ulPreferredIPAddress.
 */
    uint32_t vDHCPSetPreferredIPAddress( uint32_t ulIPAddress )
    {
        uint32_t ulPrevious = xDHCPData.ulPreferredIPAddress;

        xDHCPData.ulPreferredIPAddress = ulIPAddress;

        return ulPrevious;
    }

/**
 * @brief Returns the current state of a DHCP process.
 *
 * @return The current state ( eDHCPState_t ) of the DHCP process.
 */
    eDHCPState_t eGetDHCPState( void )
    {
        return EP_DHCPData.eDHCPState;
    }

/**
 * @brief Process the DHCP state machine based on current state.
 *
 * @param[in] xReset: Is the DHCP state machine starting over? pdTRUE/pdFALSE.
 * @param[in] eExpectedState: The function will only run if the state is expected.
 */
    void vDHCPProcess( BaseType_t xReset,
                       eDHCPState_t eExpectedState )
    {
        BaseType_t xGivingUp = pdFALSE;

        #if ( ipconfigUSE_DHCP_HOOK != 0 )
            eDHCPCallbackAnswer_t eAnswer;
        #endif /* ipconfigUSE_DHCP_HOOK */

        /* Is DHCP starting over? */
        if( xReset != pdFALSE )
        {
            EP_DHCPData.eDHCPState = eInitialWait;
        }

        if( ( EP_DHCPData.eDHCPState != eExpectedState ) && ( xReset == pdFALSE ) )
        {
            /* When the DHCP event was generated, the DHCP client was
            * in a different state.  Therefore, ignore this event. */
            FreeRTOS_debug_printf( ( "DHCP wrong state: expect: %d got: %d : ignore\n",
                                     eExpectedState, EP_DHCPData.eDHCPState ) );
        }
        else
        {
            switch( EP_DHCPData.eDHCPState )
            {
                case eInitialWait:

                    /* Initial state.  Create the DHCP socket, timer, etc. if they
                     * have not already been created. */
                    prvInitialiseDHCP();
                    EP_DHCPData.eDHCPState = eWaitingSendFirstDiscover;
                    break;

                case eWaitingSendFirstDiscover:
                    /* Ask the user if a DHCP discovery is required. */
                    #if ( ipconfigUSE_DHCP_HOOK != 0 )
                        eAnswer = xApplicationDHCPHook( eDHCPPhasePreDiscover, xNetworkAddressing.ulDefaultIPAddress );

                        if( eAnswer == eDHCPContinue )
                    #endif /* ipconfigUSE_DHCP_HOOK */
                    {
                        /* See if prvInitialiseDHCP() has creates a socket. */
                        if( xDHCPSocket == NULL )
                        {
                            xGivingUp = pdTRUE;
                        }
                        else
                        {
                            *ipLOCAL_IP_ADDRESS_POINTER = 0U;

                            /* Send the first discover request. */
                            EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();

                            if( prvSendDHCPDiscover() == pdPASS )
                            {
                                EP_DHCPData.eDHCPState = eWaitingOffer;
                            }
                            else
                            {
                                /* Either the creation of a message buffer failed, or sendto().
                                 * Try again in the next cycle. */
                                FreeRTOS_debug_printf( ( "Send failed during eWaitingSendFirstDiscover\n" ) );
                            }
                        }
                    }

                    #if ( ipconfigUSE_DHCP_HOOK != 0 )
                        else
                        {
                            if( eAnswer == eDHCPUseDefaults )
                            {
                                ( void ) memcpy( &( xNetworkAddressing ), &( xDefaultAddressing ), sizeof( xNetworkAddressing ) );
                            }

                            /* The user indicates that the DHCP process does not continue. */
                            xGivingUp = pdTRUE;
                        }
                    #endif /* ipconfigUSE_DHCP_HOOK */
                    break;

                case eSendDHCPRequest:

                    if( prvSendDHCPRequest() == pdPASS )
                    {
                        /* Send succeeded, go to state 'eWaitingAcknowledge'. */
                        EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();
                        EP_DHCPData.xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;
                        EP_DHCPData.eDHCPState = eWaitingAcknowledge;
                    }
                    else
                    {
                        /* Either the creation of a message buffer failed, or sendto().
                         * Try again in the next cycle. */
                        FreeRTOS_debug_printf( ( "Send failed during eSendDHCPRequest.\n" ) );
                    }

                    break;

                case eWaitingOffer:

                    xGivingUp = pdFALSE;

                    /* Look for offers coming in. */
                    if( prvProcessDHCPReplies( dhcpMESSAGE_TYPE_OFFER ) == pdPASS )
                    {
                        #if ( ipconfigUSE_DHCP_HOOK != 0 )
                            /* Ask the user if a DHCP request is required. */
                            eAnswer = xApplicationDHCPHook( eDHCPPhasePreRequest, EP_DHCPData.ulOfferedIPAddress );

                            if( eAnswer == eDHCPContinue )
                        #endif /* ipconfigUSE_DHCP_HOOK */
                        {
                            /* An offer has been made, the user wants to continue,
                             * generate the request. */
                            if( prvSendDHCPRequest() == pdPASS )
                            {
                                EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();
                                EP_DHCPData.xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;
                                EP_DHCPData.eDHCPState = eWaitingAcknowledge;
                            }
                            else
                            {
                                /* Either the creation of a message buffer failed, or sendto().
                                 * Try again in the next cycle. */
                                FreeRTOS_debug_printf( ( "Send failed during eWaitingOffer/1.\n" ) );
                                EP_DHCPData.eDHCPState = eSendDHCPRequest;
                            }

                            break;
                        }

                        #if ( ipconfigUSE_DHCP_HOOK != 0 )
                            if( eAnswer == eDHCPUseDefaults )
                            {
                                ( void ) memcpy( &( xNetworkAddressing ), &( xDefaultAddressing ), sizeof( xNetworkAddressing ) );
                            }

                            /* The user indicates that the DHCP process does not continue. */
                            xGivingUp = pdTRUE;
                        #endif /* ipconfigUSE_DHCP_HOOK */
                    }

                    /* Is it time to send another Discover? */
                    else if( ( xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod )
                    {
                        /* It is time to send another Discover.  Increase the time
                         * period, and if it has not got to the point of giving up - send
                         * another discovery. */
                        EP_DHCPData.xDHCPTxPeriod <<= 1;

                        if( EP_DHCPData.xDHCPTxPeriod <= ( TickType_t ) ipconfigMAXIMUM_DISCOVER_TX_PERIOD )
                        {
                            if( xApplicationGetRandomNumber( &( EP_DHCPData.ulTransactionId ) ) != pdFALSE )
                            {
                                EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();

                                if( EP_DHCPData.xUseBroadcast != pdFALSE )
                                {
                                    EP_DHCPData.xUseBroadcast = pdFALSE;
                                }
                                else
                                {
                                    EP_DHCPData.xUseBroadcast = pdTRUE;
                                }

                                if( prvSendDHCPDiscover() == pdPASS )
                                {
                                    FreeRTOS_debug_printf( ( "vDHCPProcess: timeout %lu ticks\n", EP_DHCPData.xDHCPTxPeriod ) );
                                }
                                else
                                {
                                    /* Either the creation of a message buffer failed, or sendto().
                                     * Try again in the next cycle. */
                                    FreeRTOS_debug_printf( ( "Send failed during eWaitingOffer/2.\n" ) );
                                    EP_DHCPData.eDHCPState = eInitialWait;
                                }
                            }
                            else
                            {
                                FreeRTOS_debug_printf( ( "vDHCPProcess: failed to generate a random Transaction ID\n" ) );
                            }
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
                                    prvPrepareLinkLayerIPLookUp();

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

                    /* Look for acks coming in. */
                    if( prvProcessDHCPReplies( dhcpMESSAGE_TYPE_ACK ) == pdPASS )
                    {
                        FreeRTOS_debug_printf( ( "vDHCPProcess: acked %xip\n", ( unsigned ) FreeRTOS_ntohl( EP_DHCPData.ulOfferedIPAddress ) ) );

                        /* DHCP completed.  The IP address can now be used, and the
                         * timer set to the lease timeout time. */
                        *ipLOCAL_IP_ADDRESS_POINTER = EP_DHCPData.ulOfferedIPAddress;

                        /* Setting the 'local' broadcast address, something like
                         * '192.168.1.255'. */
                        EP_IPv4_SETTINGS.ulBroadcastAddress = ( EP_DHCPData.ulOfferedIPAddress & xNetworkAddressing.ulNetMask ) | ~xNetworkAddressing.ulNetMask;
                        EP_DHCPData.eDHCPState = eLeasedAddress;

                        iptraceDHCP_SUCCEDEED( EP_DHCPData.ulOfferedIPAddress );

                        /* DHCP failed, the default configured IP-address will be used
                         * Now call vIPNetworkUpCalls() to send the network-up event and
                         * start the ARP timer. */
                        vIPNetworkUpCalls();

                        /* Close socket to ensure packets don't queue on it. */
                        prvCloseDHCPSocket();

                        if( EP_DHCPData.ulLeaseTime == 0U )
                        {
                            EP_DHCPData.ulLeaseTime = ( uint32_t ) dhcpDEFAULT_LEASE_TIME;
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
                        vARPSendGratuitous();
                        vDHCPTimerReload( EP_DHCPData.ulLeaseTime );
                    }
                    else
                    {
                        /* Is it time to send another Discover? */
                        if( ( xTaskGetTickCount() - EP_DHCPData.xDHCPTxTime ) > EP_DHCPData.xDHCPTxPeriod )
                        {
                            /* Increase the time period, and if it has not got to the
                             * point of giving up - send another request. */
                            EP_DHCPData.xDHCPTxPeriod <<= 1;

                            if( EP_DHCPData.xDHCPTxPeriod <= ( TickType_t ) ipconfigMAXIMUM_DISCOVER_TX_PERIOD )
                            {
                                EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();

                                if( prvSendDHCPRequest() == pdPASS )
                                {
                                    /* The message is sent. Stay in state 'eWaitingAcknowledge'. */
                                }
                                else
                                {
                                    /* Either the creation of a message buffer failed, or sendto().
                                     * Try again in the next cycle. */
                                    FreeRTOS_debug_printf( ( "Send failed during eWaitingAcknowledge.\n" ) );
                                    EP_DHCPData.eDHCPState = eSendDHCPRequest;
                                }
                            }
                            else
                            {
                                /* Give up, start again. */
                                EP_DHCPData.eDHCPState = eInitialWait;
                            }
                        }
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

                                    /* Auto-IP succeeded, the default configured IP-address will
                                     * be used.  Now call vIPNetworkUpCalls() to send the
                                     * network-up event and start the ARP timer. */
                                    vIPNetworkUpCalls();
                                    EP_DHCPData.eDHCPState = eNotUsingLeasedAddress;
                                }
                                else
                                {
                                    /* ARP clashed - try another IP address. */
                                    prvPrepareLinkLayerIPLookUp();

                                    /* Setting an IP address manually so set to not using leased
                                     * address mode. */
                                    EP_DHCPData.eDHCPState = eGetLinkLayerAddress;
                                }
                            }
                            break;
                    #endif /* ipconfigDHCP_FALL_BACK_AUTO_IP */

                case eLeasedAddress:

                    if( FreeRTOS_IsNetworkUp() != 0 )
                    {
                        /* Resend the request at the appropriate time to renew the lease. */
                        prvCreateDHCPSocket();

                        if( xDHCPSocket != NULL )
                        {
                            uint32_t ulID = 0U;

                            if( xApplicationGetRandomNumber( &( ulID ) ) != pdFALSE )
                            {
                                EP_DHCPData.ulTransactionId = ulID;
                            }

                            EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();
                            EP_DHCPData.xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;

                            if( prvSendDHCPRequest() == pdPASS )
                            {
                                /* The packet was sent successfully, wait for an acknowledgement. */
                                EP_DHCPData.eDHCPState = eWaitingAcknowledge;
                            }
                            else
                            {
                                /* The packet was not sent, try sending it later. */
                                EP_DHCPData.eDHCPState = eSendDHCPRequest;
                                FreeRTOS_debug_printf( ( "Send failed eLeasedAddress.\n" ) );
                            }

                            /* From now on, we should be called more often */
                            vDHCPTimerReload( dhcpINITIAL_TIMER_PERIOD );
                        }
                    }
                    else
                    {
                        /* See PR #53 on github/freertos/freertos */
                        FreeRTOS_printf( ( "DHCP: lease time finished but network is down\n" ) );
                        vDHCPTimerReload( pdMS_TO_TICKS( 5000U ) );
                    }

                    break;

                case eNotUsingLeasedAddress:

                    vIPSetDHCPTimerEnableState( pdFALSE );
                    break;

                default:
                    /* Lint: all options are included. */
                    break;
            }

            if( xGivingUp != pdFALSE )
            {
                /* xGivingUp became true either because of a time-out, or because
                 * xApplicationDHCPHook() returned another value than 'eDHCPContinue',
                 * meaning that the conversion is cancelled from here. */

                /* Revert to static IP address. */
                taskENTER_CRITICAL();
                {
                    *ipLOCAL_IP_ADDRESS_POINTER = xNetworkAddressing.ulDefaultIPAddress;
                    iptraceDHCP_REQUESTS_FAILED_USING_DEFAULT_IP_ADDRESS( xNetworkAddressing.ulDefaultIPAddress );
                }
                taskEXIT_CRITICAL();

                EP_DHCPData.eDHCPState = eNotUsingLeasedAddress;
                vIPSetDHCPTimerEnableState( pdFALSE );

                /* DHCP failed, the default configured IP-address will be used.  Now
                 * call vIPNetworkUpCalls() to send the network-up event and start the ARP
                 * timer. */
                vIPNetworkUpCalls();

                /* Close socket to ensure packets don't queue on it. */
                prvCloseDHCPSocket();
            }
        }
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Close the DHCP socket.
 */
    static void prvCloseDHCPSocket( void )
    {
        if( xDHCPSocket != NULL )
        {
            /* This modules runs from the IP-task. Use the internal
             * function 'vSocketClose()` to close the socket. */
            ( void ) vSocketClose( xDHCPSocket );
            xDHCPSocket = NULL;
        }
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Create a DHCP socket with the defined timeouts.
 */
    _static void prvCreateDHCPSocket( void )
    {
        struct freertos_sockaddr xAddress;
        BaseType_t xReturn;
        TickType_t xTimeoutTime = ( TickType_t ) 0;

        /* Create the socket, if it has not already been created. */
        if( xDHCPSocket == NULL )
        {
            xDHCPSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

            /* MISRA Ref 11.4.1 [Socket error and integer to pointer conversion] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
            /* coverity[misra_c_2012_rule_11_4_violation] */
            if( xDHCPSocket != FREERTOS_INVALID_SOCKET )
            {
                /* Ensure the Rx and Tx timeouts are zero as the DHCP executes in the
                 * context of the IP task. */
                ( void ) FreeRTOS_setsockopt( xDHCPSocket, 0, FREERTOS_SO_RCVTIMEO, &( xTimeoutTime ), sizeof( TickType_t ) );
                ( void ) FreeRTOS_setsockopt( xDHCPSocket, 0, FREERTOS_SO_SNDTIMEO, &( xTimeoutTime ), sizeof( TickType_t ) );

                /* Bind to the standard DHCP client port. */
                xAddress.sin_port = ( uint16_t ) dhcpCLIENT_PORT_IPv4;
                xReturn = vSocketBind( xDHCPSocket, &xAddress, sizeof( xAddress ), pdFALSE );

                if( xReturn != 0 )
                {
                    /* Binding failed, close the socket again. */
                    prvCloseDHCPSocket();
                }
            }
            else
            {
                /* Change to NULL for easier testing. */
                xDHCPSocket = NULL;
            }
        }
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Initialise the DHCP state machine by creating DHCP socket and
 *        begin the transaction.
 */
    static void prvInitialiseDHCP( void )
    {
        /* Initialise the parameters that will be set by the DHCP process. Per
         * https://www.ietf.org/rfc/rfc2131.txt, Transaction ID should be a random
         * value chosen by the client. */

        /* Check for random number generator API failure. */
        if( xApplicationGetRandomNumber( &( EP_DHCPData.ulTransactionId ) ) != pdFALSE )
        {
            EP_DHCPData.xUseBroadcast = 0;
            EP_DHCPData.ulOfferedIPAddress = 0U;
            EP_DHCPData.ulDHCPServerAddress = 0U;
            EP_DHCPData.xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;

            /* Create the DHCP socket if it has not already been created. */
            prvCreateDHCPSocket();
            FreeRTOS_debug_printf( ( "prvInitialiseDHCP: start after %lu ticks\n", dhcpINITIAL_TIMER_PERIOD ) );
            vDHCPTimerReload( dhcpINITIAL_TIMER_PERIOD );
        }
        else
        {
            /* There was a problem with the randomiser. */
        }
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Check whether the DHCP response from the server has all valid
 *        invariant parameters and valid (non broadcast and non localhost)
 *        IP address being assigned to the device.
 *
 * @param[in] pxDHCPMessage: The DHCP message.
 *
 * @return pdPASS if the DHCP response has correct parameters; pdFAIL otherwise.
 */
    static BaseType_t prvIsValidDHCPResponse( const DHCPMessage_IPv4_t * pxDHCPMessage )
    {
        BaseType_t xReturn = pdPASS;

        if( ( pxDHCPMessage->ulDHCPCookie != ( uint32_t ) dhcpCOOKIE ) ||
            ( pxDHCPMessage->ucOpcode != ( uint8_t ) dhcpREPLY_OPCODE ) ||
            ( pxDHCPMessage->ucAddressType != ( uint8_t ) dhcpADDRESS_TYPE_ETHERNET ) ||
            ( pxDHCPMessage->ucAddressLength != ( uint8_t ) dhcpETHERNET_ADDRESS_LENGTH ) ||
            ( ( FreeRTOS_ntohl( pxDHCPMessage->ulYourIPAddress_yiaddr ) & 0xFFU ) == 0xFFU ) ||
            ( ( ( pxDHCPMessage->ulYourIPAddress_yiaddr & 0x7FU ) ^ 0x7FU ) == 0x00U ) )
        {
            /* Invalid cookie OR
             * Unexpected opcode OR
             * Incorrect address type OR
             * Incorrect address length OR
             * The DHCP server is trying to assign a broadcast address to the device OR
             * The DHCP server is trying to assign a localhost address to the device. */
            xReturn = pdFAIL;
        }

        return xReturn;
    }

/**
 * @brief Process the DHCP replies.
 *
 * @param[in] xExpectedMessageType: The type of the message the DHCP state machine is expecting.
 *                                  Messages of different type will be dropped.
 *
 * @return pdPASS: if DHCP options are received correctly; pdFAIL: Otherwise.
 */
    _static BaseType_t prvProcessDHCPReplies( BaseType_t xExpectedMessageType )
    {
        uint8_t * pucUDPPayload;
        int32_t lBytes;
        const DHCPMessage_IPv4_t * pxDHCPMessage;
        const uint8_t * pucByte;
        uint8_t ucOptionCode;
        uint32_t ulProcessed, ulParameter;
        BaseType_t xReturn = pdFALSE;
        const uint32_t ulMandatoryOptions = 2U; /* DHCP server address, and the correct DHCP message type must be present in the options. */
        /* memcpy() helper variables for MISRA Rule 21.15 compliance*/
        const void * pvCopySource;
        void * pvCopyDest;

        /* Passing the address of a pointer (pucUDPPayload) because FREERTOS_ZERO_COPY is used. */
        lBytes = FreeRTOS_recvfrom( xDHCPSocket, &pucUDPPayload, 0U, FREERTOS_ZERO_COPY, NULL, NULL );

        if( lBytes > 0 )
        {
            /* Map a DHCP structure onto the received data. */

            /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            pxDHCPMessage = ( ( DHCPMessage_IPv4_t * ) pucUDPPayload );

            /* Sanity check. */
            if( lBytes < ( int32_t ) sizeof( DHCPMessage_IPv4_t ) )
            {
                /* Not enough bytes. */
            }
            else if( prvIsValidDHCPResponse( pxDHCPMessage ) == pdFAIL )
            {
                /* Invalid values in DHCP response. */
            }
            else if( ( pxDHCPMessage->ulTransactionID != FreeRTOS_htonl( EP_DHCPData.ulTransactionId ) ) )
            {
                /* Transaction ID does not match. */
            }
            else /* Looks like a valid DHCP response, with the same transaction ID. */
            {
                if( memcmp( pxDHCPMessage->ucClientHardwareAddress,
                            ipLOCAL_MAC_ADDRESS,
                            sizeof( MACAddress_t ) ) != 0 )
                {
                    /* Target MAC address doesn't match. */
                }
                else
                {
                    size_t uxIndex, uxPayloadDataLength, uxLength;

                    /* None of the essential options have been processed yet. */
                    ulProcessed = 0U;

                    /* Walk through the options until the dhcpOPTION_END_BYTE byte
                     * is found, taking care not to walk off the end of the options. */
                    pucByte = &( pucUDPPayload[ sizeof( DHCPMessage_IPv4_t ) ] );
                    uxIndex = 0;
                    uxPayloadDataLength = ( ( size_t ) lBytes ) - sizeof( DHCPMessage_IPv4_t );

                    while( uxIndex < uxPayloadDataLength )
                    {
                        ucOptionCode = pucByte[ uxIndex ];

                        if( ucOptionCode == ( uint8_t ) dhcpOPTION_END_BYTE )
                        {
                            /* Ready, the last byte has been seen. */
                            /* coverity[break_stmt] : Break statement terminating the loop */
                            break;
                        }

                        if( ucOptionCode == ( uint8_t ) dhcpIPv4_ZERO_PAD_OPTION_CODE )
                        {
                            /* The value zero is used as a pad byte,
                             * it is not followed by a length byte. */
                            uxIndex = uxIndex + 1U;
                            continue;
                        }

                        /* Stop if the response is malformed. */
                        if( ( uxIndex + 1U ) < uxPayloadDataLength )
                        {
                            /* Fetch the length byte. */
                            uxLength = ( size_t ) pucByte[ uxIndex + 1U ];
                            uxIndex = uxIndex + 2U;

                            if( !( ( ( uxIndex + uxLength ) - 1U ) < uxPayloadDataLength ) )
                            {
                                /* There are not as many bytes left as there should be. */
                                break;
                            }
                        }
                        else
                        {
                            /* The length byte is missing. */
                            break;
                        }

                        /* In most cases, a 4-byte network-endian parameter follows,
                         * just get it once here and use later. */
                        if( uxLength >= sizeof( ulParameter ) )
                        {
                            /*
                             * Use helper variables for memcpy() to remain
                             * compliant with MISRA Rule 21.15.  These should be
                             * optimized away.
                             */
                            pvCopySource = &pucByte[ uxIndex ];
                            pvCopyDest = &ulParameter;
                            ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( ulParameter ) );
                            /* 'uxIndex' will be increased at the end of this loop. */
                        }
                        else
                        {
                            ulParameter = 0;
                        }

                        /* Confirm uxIndex is still a valid index after adjustments to uxIndex above */
                        if( !( uxIndex < uxPayloadDataLength ) )
                        {
                            break;
                        }

                        /* Option-specific handling. */
                        switch( ucOptionCode )
                        {
                            case dhcpIPv4_MESSAGE_TYPE_OPTION_CODE:

                                if( pucByte[ uxIndex ] == ( uint8_t ) xExpectedMessageType )
                                {
                                    /* The message type is the message type the
                                     * state machine is expecting. */
                                    ulProcessed++;
                                }
                                else
                                {
                                    if( pucByte[ uxIndex ] == ( uint8_t ) dhcpMESSAGE_TYPE_NACK )
                                    {
                                        if( xExpectedMessageType == ( BaseType_t ) dhcpMESSAGE_TYPE_ACK )
                                        {
                                            /* Start again. */
                                            EP_DHCPData.eDHCPState = eInitialWait;
                                        }
                                    }

                                    /* Stop processing further options. */
                                    uxLength = 0;
                                }

                                break;

                            case dhcpIPv4_SUBNET_MASK_OPTION_CODE:

                                if( uxLength == sizeof( uint32_t ) )
                                {
                                    EP_IPv4_SETTINGS.ulNetMask = ulParameter;
                                }

                                break;

                            case dhcpIPv4_GATEWAY_OPTION_CODE:

                                /* The DHCP server may send more than 1 gateway addresses. */
                                if( uxLength >= sizeof( uint32_t ) )
                                {
                                    /* ulProcessed is not incremented in this case
                                     * because the gateway is not essential. */
                                    EP_IPv4_SETTINGS.ulGatewayAddress = ulParameter;
                                }

                                break;

                            case dhcpIPv4_DNS_SERVER_OPTIONS_CODE:

                                /* The DHCP server may send more than 1 DNS server addresses. */
                                if( uxLength >= sizeof( uint32_t ) )
                                {
                                    /* ulProcessed is not incremented in this case
                                     * because the DNS server is not essential.  Only the
                                     * first DNS server address is taken. */
                                    EP_IPv4_SETTINGS.ulDNSServerAddress = ulParameter;
                                }

                                break;

                            case dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE:

                                if( uxLength == sizeof( uint32_t ) )
                                {
                                    if( xExpectedMessageType == ( BaseType_t ) dhcpMESSAGE_TYPE_OFFER )
                                    {
                                        /* Offers state the replying server. */
                                        ulProcessed++;
                                        EP_DHCPData.ulDHCPServerAddress = ulParameter;
                                    }
                                    else
                                    {
                                        /* The ack must come from the expected server. */
                                        if( EP_DHCPData.ulDHCPServerAddress == ulParameter )
                                        {
                                            ulProcessed++;
                                        }
                                    }
                                }

                                break;

                            case dhcpIPv4_LEASE_TIME_OPTION_CODE:

                                if( uxLength == sizeof( EP_DHCPData.ulLeaseTime ) )
                                {
                                    /* ulProcessed is not incremented in this case
                                     * because the lease time is not essential. */

                                    /* The DHCP parameter is in seconds, convert
                                     * to host-endian format. */
                                    EP_DHCPData.ulLeaseTime = FreeRTOS_ntohl( ulParameter );

                                    /* Divide the lease time by two to ensure a renew
                                     * request is sent before the lease actually expires. */
                                    EP_DHCPData.ulLeaseTime >>= 1;

                                    /* Multiply with configTICK_RATE_HZ to get clock ticks. */
                                    EP_DHCPData.ulLeaseTime = ( uint32_t ) configTICK_RATE_HZ * ( uint32_t ) EP_DHCPData.ulLeaseTime;
                                }

                                break;

                            default:

                                /* Not interested in this field. */

                                break;
                        }

                        /* Jump over the data to find the next option code. */
                        if( uxLength == 0U )
                        {
                            break;
                        }

                        uxIndex = uxIndex + uxLength;
                    }

                    /* Were all the mandatory options received? */
                    if( ulProcessed >= ulMandatoryOptions )
                    {
                        /* HT:endian: used to be network order */
                        EP_DHCPData.ulOfferedIPAddress = pxDHCPMessage->ulYourIPAddress_yiaddr;
                        FreeRTOS_printf( ( "vDHCPProcess: offer %xip\n", ( unsigned ) FreeRTOS_ntohl( EP_DHCPData.ulOfferedIPAddress ) ) );
                        xReturn = pdPASS;
                    }
                }
            }

            FreeRTOS_ReleaseUDPPayloadBuffer( pucUDPPayload );
        } /* if( lBytes > 0 ) */

        return xReturn;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Create a partial DHCP message by filling in all the 'constant' fields.
 *
 * @param[out] pxAddress: Address to be filled in.
 * @param[out] xOpcode: Opcode to be filled in the packet. Will always be 'dhcpREQUEST_OPCODE'.
 * @param[in] pucOptionsArray: The options to be added to the packet.
 * @param[in,out] pxOptionsArraySize: Byte count of the options. Its value might change.
 *
 * @return Ethernet buffer of the partially created DHCP packet.
 */
    static uint8_t * prvCreatePartDHCPMessage( struct freertos_sockaddr * pxAddress,
                                               BaseType_t xOpcode,
                                               const uint8_t * const pucOptionsArray,
                                               size_t * pxOptionsArraySize )
    {
        DHCPMessage_IPv4_t * pxDHCPMessage;
        size_t uxRequiredBufferSize = sizeof( DHCPMessage_IPv4_t ) + *pxOptionsArraySize;
        const NetworkBufferDescriptor_t * pxNetworkBuffer;
        uint8_t * pucUDPPayloadBuffer = NULL;

        #if ( ipconfigDHCP_REGISTER_HOSTNAME == 1 )
            const char * pucHostName = pcApplicationHostnameHook();
            size_t uxNameLength = strlen( pucHostName );
            uint8_t * pucPtr;

/* memcpy() helper variables for MISRA Rule 21.15 compliance*/
            const void * pvCopySource;
            void * pvCopyDest;

            /* Two extra bytes for option code and length. */
            uxRequiredBufferSize += ( 2U + uxNameLength );
        #endif /* if ( ipconfigDHCP_REGISTER_HOSTNAME == 1 ) */

        /* Obtain a network buffer with the required amount of storage.  It doesn't make much sense
         * to use a time-out here, because that would cause the IP-task to wait for itself. */
        pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( sizeof( UDPPacket_t ) + uxRequiredBufferSize, 0U );

        if( pxNetworkBuffer != NULL )
        {
            /* Leave space for the UDP header. */
            pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );

            /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            pxDHCPMessage = ( ( DHCPMessage_IPv4_t * ) pucUDPPayloadBuffer );

            /* Most fields need to be zero. */
            ( void ) memset( pxDHCPMessage, 0x00, sizeof( DHCPMessage_IPv4_t ) );

            /* Create the message. */
            pxDHCPMessage->ucOpcode = ( uint8_t ) xOpcode;
            pxDHCPMessage->ucAddressType = ( uint8_t ) dhcpADDRESS_TYPE_ETHERNET;
            pxDHCPMessage->ucAddressLength = ( uint8_t ) dhcpETHERNET_ADDRESS_LENGTH;
            pxDHCPMessage->ulTransactionID = FreeRTOS_htonl( EP_DHCPData.ulTransactionId );
            pxDHCPMessage->ulDHCPCookie = ( uint32_t ) dhcpCOOKIE;

            if( EP_DHCPData.xUseBroadcast != pdFALSE )
            {
                pxDHCPMessage->usFlags = ( uint16_t ) dhcpBROADCAST;
            }
            else
            {
                pxDHCPMessage->usFlags = 0U;
            }

            ( void ) memcpy( &( pxDHCPMessage->ucClientHardwareAddress[ 0 ] ), ipLOCAL_MAC_ADDRESS, sizeof( MACAddress_t ) );

            /* Copy in the const part of the options options. */
            ( void ) memcpy( &( pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET ] ), pucOptionsArray, *pxOptionsArraySize );

            #if ( ipconfigDHCP_REGISTER_HOSTNAME == 1 )
                {
                    /* With this option, the hostname can be registered as well which makes
                     * it easier to lookup a device in a router's list of DHCP clients. */

                    /* Point to where the OPTION_END was stored to add data. */
                    pucPtr = &( pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET + ( *pxOptionsArraySize - 1U ) ] );
                    pucPtr[ 0U ] = dhcpIPv4_DNS_HOSTNAME_OPTIONS_CODE;
                    pucPtr[ 1U ] = ( uint8_t ) uxNameLength;

                    /*
                     * Use helper variables for memcpy() to remain
                     * compliant with MISRA Rule 21.15.  These should be
                     * optimized away.
                     */
                    pvCopySource = pucHostName;
                    pvCopyDest = &pucPtr[ 2U ];

                    ( void ) memcpy( pvCopyDest, pvCopySource, uxNameLength );
                    pucPtr[ 2U + uxNameLength ] = ( uint8_t ) dhcpOPTION_END_BYTE;
                    *pxOptionsArraySize += ( size_t ) ( 2U + uxNameLength );
                }
            #endif /* if ( ipconfigDHCP_REGISTER_HOSTNAME == 1 ) */

            /* Map in the client identifier. */
            ( void ) memcpy( &( pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET + dhcpCLIENT_IDENTIFIER_OFFSET ] ),
                             ipLOCAL_MAC_ADDRESS, sizeof( MACAddress_t ) );

            /* Set the addressing. */
            pxAddress->sin_addr = ipBROADCAST_IP_ADDRESS;
            pxAddress->sin_port = ( uint16_t ) dhcpSERVER_PORT_IPv4;
        }

        return pucUDPPayloadBuffer;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Create and send a DHCP request message through the DHCP socket.
 * @return Returns pdPASS when the message is successfully created and sent.
 */
    static BaseType_t prvSendDHCPRequest( void )
    {
        BaseType_t xResult = pdFAIL;
        uint8_t * pucUDPPayloadBuffer;
        struct freertos_sockaddr xAddress;
        static const uint8_t ucDHCPRequestOptions[] =
        {
            /* Do not change the ordering without also changing
             * dhcpCLIENT_IDENTIFIER_OFFSET, dhcpREQUESTED_IP_ADDRESS_OFFSET and
             * dhcpDHCP_SERVER_IP_ADDRESS_OFFSET. */
            dhcpIPv4_MESSAGE_TYPE_OPTION_CODE,       1, dhcpMESSAGE_TYPE_REQUEST, /* Message type option. */
            dhcpIPv4_CLIENT_IDENTIFIER_OPTION_CODE,  7, 1, 0, 0, 0, 0, 0, 0,      /* Client identifier. */
            dhcpIPv4_REQUEST_IP_ADDRESS_OPTION_CODE, 4, 0, 0, 0, 0,               /* The IP address being requested. */
            dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE,  4, 0, 0, 0, 0,               /* The IP address of the DHCP server. */
            dhcpOPTION_END_BYTE
        };
        size_t uxOptionsLength = sizeof( ucDHCPRequestOptions );
        /* memcpy() helper variables for MISRA Rule 21.15 compliance*/
        const void * pvCopySource;
        void * pvCopyDest;

        pucUDPPayloadBuffer = prvCreatePartDHCPMessage( &xAddress,
                                                        ( BaseType_t ) dhcpREQUEST_OPCODE,
                                                        ucDHCPRequestOptions,
                                                        &( uxOptionsLength ) );

        if( pucUDPPayloadBuffer != NULL )
        {
            /* Copy in the IP address being requested. */

            /*
             * Use helper variables for memcpy() source & dest to remain
             * compliant with MISRA Rule 21.15.  These should be
             * optimized away.
             */
            pvCopySource = &EP_DHCPData.ulOfferedIPAddress;
            pvCopyDest = &pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET + dhcpREQUESTED_IP_ADDRESS_OFFSET ];
            ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( EP_DHCPData.ulOfferedIPAddress ) );

            /* Copy in the address of the DHCP server being used. */
            pvCopySource = &EP_DHCPData.ulDHCPServerAddress;
            pvCopyDest = &pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET + dhcpDHCP_SERVER_IP_ADDRESS_OFFSET ];
            ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( EP_DHCPData.ulDHCPServerAddress ) );

            FreeRTOS_debug_printf( ( "vDHCPProcess: reply %xip\n", ( unsigned ) FreeRTOS_ntohl( EP_DHCPData.ulOfferedIPAddress ) ) );
            iptraceSENDING_DHCP_REQUEST();

            if( FreeRTOS_sendto( xDHCPSocket, pucUDPPayloadBuffer, sizeof( DHCPMessage_IPv4_t ) + uxOptionsLength, FREERTOS_ZERO_COPY, &xAddress, ( socklen_t ) sizeof( xAddress ) ) == 0 )
            {
                /* The packet was not successfully queued for sending and must be
                 * returned to the stack. */
                FreeRTOS_ReleaseUDPPayloadBuffer( pucUDPPayloadBuffer );
            }
            else
            {
                xResult = pdPASS;
            }
        }

        return xResult;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Create and send a DHCP discover packet through the DHCP socket.
 * @return Returns pdPASS when the message is successfully created and sent.
 */
    static BaseType_t prvSendDHCPDiscover( void )
    {
        BaseType_t xResult = pdFAIL;
        uint8_t * pucUDPPayloadBuffer;
        struct freertos_sockaddr xAddress;
        static const uint8_t ucDHCPDiscoverOptions[] =
        {
            /* Do not change the ordering without also changing dhcpCLIENT_IDENTIFIER_OFFSET. */
            dhcpIPv4_MESSAGE_TYPE_OPTION_CODE,       1, dhcpMESSAGE_TYPE_DISCOVER,                                                                        /* Message type option. */
            dhcpIPv4_CLIENT_IDENTIFIER_OPTION_CODE,  7, 1,                                0,                            0, 0, 0, 0, 0,                    /* Client identifier. */
            dhcpIPv4_REQUEST_IP_ADDRESS_OPTION_CODE, 4, 0,                                0,                            0, 0,                             /* The IP address being requested. */
            dhcpIPv4_PARAMETER_REQUEST_OPTION_CODE,  3, dhcpIPv4_SUBNET_MASK_OPTION_CODE, dhcpIPv4_GATEWAY_OPTION_CODE, dhcpIPv4_DNS_SERVER_OPTIONS_CODE, /* Parameter request option. */
            dhcpOPTION_END_BYTE
        };
        size_t uxOptionsLength = sizeof( ucDHCPDiscoverOptions );

        pucUDPPayloadBuffer = prvCreatePartDHCPMessage( &xAddress,
                                                        ( BaseType_t ) dhcpREQUEST_OPCODE,
                                                        ucDHCPDiscoverOptions,
                                                        &( uxOptionsLength ) );

        if( pucUDPPayloadBuffer != NULL )
        {
            const void * pvCopySource;
            void * pvCopyDest;

            FreeRTOS_debug_printf( ( "vDHCPProcess: discover\n" ) );
            iptraceSENDING_DHCP_DISCOVER();

            if( xDHCPData.ulPreferredIPAddress != 0U )
            {
                /* Fill in the IPv4 address. */
                pvCopySource = &xDHCPData.ulPreferredIPAddress;
                pvCopyDest = &( pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET + dhcpREQUESTED_IP_ADDRESS_OFFSET ] );
                ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( EP_DHCPData.ulPreferredIPAddress ) );
            }
            else
            {
                /* Remove option-50 from the list because it is not used. */
                size_t uxCopyLength;
                /* Exclude this line from branch coverage as the not-taken condition will never happen unless the code is modified */
                configASSERT( uxOptionsLength > ( dhcpOPTION_50_OFFSET + dhcpOPTION_50_SIZE ) ); /* LCOV_EXCL_BR_LINE */
                uxCopyLength = uxOptionsLength - ( dhcpOPTION_50_OFFSET + dhcpOPTION_50_SIZE );
                pvCopySource = &( pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET + dhcpOPTION_50_OFFSET + dhcpOPTION_50_SIZE ] );
                pvCopyDest = &( pucUDPPayloadBuffer[ dhcpFIRST_OPTION_BYTE_OFFSET + dhcpOPTION_50_OFFSET ] );
                ( void ) memmove( pvCopyDest, pvCopySource, uxCopyLength );
                /* Send 6 bytes less than foreseen. */
                uxOptionsLength -= dhcpOPTION_50_SIZE;
            }

            if( FreeRTOS_sendto( xDHCPSocket,
                                 pucUDPPayloadBuffer,
                                 sizeof( DHCPMessage_IPv4_t ) + uxOptionsLength,
                                 FREERTOS_ZERO_COPY,
                                 &( xAddress ),
                                 ( socklen_t ) sizeof( xAddress ) ) == 0 )
            {
                /* The packet was not successfully queued for sending and must be
                 * returned to the stack. */
                FreeRTOS_ReleaseUDPPayloadBuffer( pucUDPPayloadBuffer );
            }
            else
            {
                xResult = pdTRUE;
            }
        }

        return xResult;
    }
    /*-----------------------------------------------------------*/


    #if ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 )

/**
 * @brief When DHCP has failed, the code can assign a Link-Layer address, and check if
 *        another device already uses the IP-address.
 */
        static void prvPrepareLinkLayerIPLookUp( void )
        {
            uint8_t ucLinkLayerIPAddress[ 2 ];
            uint32_t ulNumbers[ 2 ];

            /* After DHCP has failed to answer, prepare everything to start
             * trying-out LinkLayer IP-addresses, using the random method. */
            EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();

            xApplicationGetRandomNumber( &( ulNumbers[ 0 ] ) );
            xApplicationGetRandomNumber( &( ulNumbers[ 1 ] ) );
            ucLinkLayerIPAddress[ 0 ] = ( uint8_t ) 1 + ( uint8_t ) ( ulNumbers[ 0 ] % 0xFDU ); /* get value 1..254 for IP-address 3rd byte of IP address to try. */
            ucLinkLayerIPAddress[ 1 ] = ( uint8_t ) 1 + ( uint8_t ) ( ulNumbers[ 1 ] % 0xFDU ); /* get value 1..254 for IP-address 4th byte of IP address to try. */

            EP_IPv4_SETTINGS.ulGatewayAddress = 0U;

            /* prepare xDHCPData with data to test. */
            EP_DHCPData.ulOfferedIPAddress =
                FreeRTOS_inet_addr_quick( LINK_LAYER_ADDRESS_0, LINK_LAYER_ADDRESS_1, ucLinkLayerIPAddress[ 0 ], ucLinkLayerIPAddress[ 1 ] );

            EP_DHCPData.ulLeaseTime = dhcpDEFAULT_LEASE_TIME; /*  don't care about lease time. just put anything. */

            EP_IPv4_SETTINGS.ulNetMask =
                FreeRTOS_inet_addr_quick( LINK_LAYER_NETMASK_0, LINK_LAYER_NETMASK_1, LINK_LAYER_NETMASK_2, LINK_LAYER_NETMASK_3 );

            /* DHCP completed.  The IP address can now be used, and the
             * timer set to the lease timeout time. */
            *( ipLOCAL_IP_ADDRESS_POINTER ) = EP_DHCPData.ulOfferedIPAddress;

            /* Setting the 'local' broadcast address, something like 192.168.1.255' */
            EP_IPv4_SETTINGS.ulBroadcastAddress = ( EP_DHCPData.ulOfferedIPAddress & EP_IPv4_SETTINGS.ulNetMask ) | ~EP_IPv4_SETTINGS.ulNetMask;

            /* Close socket to ensure packets don't queue on it. not needed anymore as DHCP failed. but still need timer for ARP testing. */
            prvCloseDHCPSocket();

            xApplicationGetRandomNumber( &( ulNumbers[ 0 ] ) );
            EP_DHCPData.xDHCPTxPeriod = pdMS_TO_TICKS( 3000U + ( ulNumbers[ 0 ] & 0x3ffU ) ); /*  do ARP test every (3 + 0-1024mS) seconds. */

            xARPHadIPClash = pdFALSE;                                                         /* reset flag that shows if have ARP clash. */
            vARPSendGratuitous();
        }

    #endif /* ipconfigDHCP_FALL_BACK_AUTO_IP */
/*-----------------------------------------------------------*/

#endif /* ipconfigUSE_DHCP != 0 */
