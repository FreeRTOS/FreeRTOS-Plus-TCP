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

/* Exclude the entire file if DHCP is not enabled. */
#if ( ipconfigUSE_DHCP != 0 )

    #include "NetworkInterface.h"
    #include "NetworkBufferManagement.h"

    #include "FreeRTOS_Routing.h"

    #if ( ipconfigUSE_DHCP != 0 ) && ( ipconfigNETWORK_MTU < 586U )

/* DHCP must be able to receive an options field of 312 bytes, the fixed
 * part of the DHCP packet is 240 bytes, and the IP/UDP headers take 28 bytes. */
        #error ipconfigNETWORK_MTU needs to be at least 586 to use DHCP
    #endif

/* Parameter widths in the DHCP packet. */
    #define dhcpCLIENT_HARDWARE_ADDRESS_LENGTH    16  /**< Client hardware address length.*/
    #define dhcpSERVER_HOST_NAME_LENGTH           64  /**< Server host name length. */
    #define dhcpBOOT_FILE_NAME_LENGTH             128 /**< Boot file name length. */

    #ifndef dhcpINITIAL_TIMER_PERIOD
        /** @brief The time to wait before sending the first DHCP request. */
        #define dhcpINITIAL_TIMER_PERIOD    ( pdMS_TO_TICKS( 250U ) )
    #endif

    #ifndef dhcpINITIAL_DHCP_TX_PERIOD

/** @brief The initial time to wait for a reply from the DHCP server.
 * When repeating the request, the waiting time shall be doubled.*/
        #define dhcpINITIAL_DHCP_TX_PERIOD    ( pdMS_TO_TICKS( 5000U ) )
    #endif

/* Codes of interest found in the DHCP options field. */
    #define dhcpIPv4_ZERO_PAD_OPTION_CODE              ( 0U )  /**< Used to pad other options to make them aligned. See RFC 2132. */
    #define dhcpIPv4_SUBNET_MASK_OPTION_CODE           ( 1U )  /**< Subnet mask. See RFC 2132. */
    #define dhcpIPv4_GATEWAY_OPTION_CODE               ( 3U )  /**< Available routers. See RFC 2132. */
    #define dhcpIPv4_DNS_SERVER_OPTIONS_CODE           ( 6U )  /**< Domain name server. See RFC 2132. */
    #define dhcpIPv4_DNS_HOSTNAME_OPTIONS_CODE         ( 12U ) /**< Host name. See RFC 2132. */
    #define dhcpIPv4_REQUEST_IP_ADDRESS_OPTION_CODE    ( 50U ) /**< Requested IP-address. See RFC 2132. */
    #define dhcpIPv4_LEASE_TIME_OPTION_CODE            ( 51U ) /**< IP-address lease time. See RFC 2132. */
    #define dhcpIPv4_MESSAGE_TYPE_OPTION_CODE          ( 53U ) /**< DHCP message type. See RFC 2132. */
    #define dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE     ( 54U ) /**< Server Identifier. See RFC 2132. */
    #define dhcpIPv4_PARAMETER_REQUEST_OPTION_CODE     ( 55U ) /**< Parameter Request list. See RFC 2132. */
    #define dhcpIPv4_CLIENT_IDENTIFIER_OPTION_CODE     ( 61U ) /**<  Client Identifier. See RFC 2132. */

/* The four DHCP message types of interest. */
    #define dhcpMESSAGE_TYPE_DISCOVER                  ( 1 ) /**< DHCP discover message. */
    #define dhcpMESSAGE_TYPE_OFFER                     ( 2 ) /**< DHCP offer message. */
    #define dhcpMESSAGE_TYPE_REQUEST                   ( 3 ) /**< DHCP request message. */
    #define dhcpMESSAGE_TYPE_ACK                       ( 5 ) /**< DHCP acknowledgement. */
    #define dhcpMESSAGE_TYPE_NACK                      ( 6 ) /**< DHCP NACK. (Negative acknowledgement) */

/* Offsets into the transmitted DHCP options fields at which various parameters
 * are located. */
    #define dhcpCLIENT_IDENTIFIER_OFFSET               ( 6U )  /**< Offset for the client ID option. */
    #define dhcpREQUESTED_IP_ADDRESS_OFFSET            ( 14U ) /**< Offset for the requested IP-address option. */
    #define dhcpDHCP_SERVER_IP_ADDRESS_OFFSET          ( 20U ) /**< Offset for the server IP-address option. */

/* Values used in the DHCP packets. */
    #define dhcpREQUEST_OPCODE                         ( 1U ) /**< DHCP request opcode. */
    #define dhcpREPLY_OPCODE                           ( 2U ) /**< DHCP reply opcode. */
    #define dhcpADDRESS_TYPE_ETHERNET                  ( 1U ) /**< Address type: ethernet opcode. */
    #define dhcpETHERNET_ADDRESS_LENGTH                ( 6U ) /**< Ethernet address length opcode. */

/* The following define is temporary and serves to make the /single source
 * code more similar to the /multi version. */

    #define EP_DHCPData                     pxEndPoint->xDHCPData     /**< Temporary define to make /single source similar to /multi version. */
    #define EP_IPv4_SETTINGS                pxEndPoint->ipv4_settings /**< Temporary define to make /single source similar to /multi version. */

/** @brief If a lease time is not received, use the default of two days (48 hours in ticks).
 * Can not use pdMS_TO_TICKS() as integer overflow can occur. */
    #define dhcpDEFAULT_LEASE_TIME          ( ( 48UL * 60UL * 60UL ) * configTICK_RATE_HZ )

/** @brief Don't allow the lease time to be too short. */
    #define dhcpMINIMUM_LEASE_TIME          ( pdMS_TO_TICKS( 60000UL ) )        /* 60 seconds in ticks. */

/** @brief Marks the end of the variable length options field in the DHCP packet. */
    #define dhcpOPTION_END_BYTE             0xffu

/** @brief Offset into a DHCP message at which the first byte of the options is
 * located. */
    #define dhcpFIRST_OPTION_BYTE_OFFSET    ( 0xf0U )

/* Standard DHCP port numbers and magic cookie value.
 * DHCPv4 uses UDP port number  68 for clients and port number  67 for servers.
 * DHCPv6 uses UDP port number 546 for clients and port number 547 for servers.
 */
    #if ( ipconfigBYTE_ORDER == pdFREERTOS_LITTLE_ENDIAN )
        #define dhcpCLIENT_PORT_IPv4    0x4400U      /**< Little endian representation of port 68. */
        #define dhcpSERVER_PORT_IPv4    0x4300U      /**< Little endian representation of port 67. */
        #define dhcpCOOKIE              0x63538263UL /**< Little endian representation of magic cookie. */
        #define dhcpBROADCAST           0x0080U      /**< Little endian representation of broadcast flag. */
    #else
        #define dhcpCLIENT_PORT_IPv4    0x0044U      /**< Big endian representation of port 68. */
        #define dhcpSERVER_PORT_IPv4    0x0043U      /**< Big endian representation of port 68. */
        #define dhcpCOOKIE              0x63825363UL /**< Big endian representation of magic cookie. */
        #define dhcpBROADCAST           0x8000U      /**< Big endian representation of broadcast flag. */
    #endif /* ( ipconfigBYTE_ORDER == pdFREERTOS_LITTLE_ENDIAN ) */

    #include "pack_struct_start.h"

/**
 * @brief A detailed description of a DHCP/IPv4 packet. */
    * /
    struct xDHCPMessage_IPv4
    {
        uint8_t ucOpcode;                                                      /**< Operation Code: Specifies the general type of message. */
        uint8_t ucAddressType;                                                 /**< Hardware type used on the local network. */
        uint8_t ucAddressLength;                                               /**< Hardware Address Length: Specifies how long hardware
                                                                                * addresses are in this message. */
        uint8_t ucHops;                                                        /**< Hops. */
        uint32_t ulTransactionID;                                              /**< A 32-bit identification field generated by the client,
                                                                                * to allow it to match up the request with replies received
                                                                                * from DHCP servers. */
        uint16_t usElapsedTime;                                                /**< Number of seconds elapsed since a client began an attempt to acquire or renew a lease. */
        uint16_t usFlags;                                                      /**< Just one bit used to indicate broadcast. */
        uint32_t ulClientIPAddress_ciaddr;                                     /**< Client's IP address if it has one or 0 is put in this field. */
        uint32_t ulYourIPAddress_yiaddr;                                       /**< The IP address that the server is assigning to the client. */
        uint32_t ulServerIPAddress_siaddr;                                     /**< The DHCP server address that the client should use. */
        uint32_t ulRelayAgentIPAddress_giaddr;                                 /**< Gateway IP address in case the server client are on different subnets. */
        uint8_t ucClientHardwareAddress[ dhcpCLIENT_HARDWARE_ADDRESS_LENGTH ]; /**< The client hardware address. */
        uint8_t ucServerHostName[ dhcpSERVER_HOST_NAME_LENGTH ];               /**< Server's hostname. */
        uint8_t ucBootFileName[ dhcpBOOT_FILE_NAME_LENGTH ];                   /**< Boot file full directory path. */
        uint32_t ulDHCPCookie;                                                 /**< Magic cookie option. */
        /* Option bytes from here on. */
    }
    #include "pack_struct_end.h"
    typedef struct xDHCPMessage_IPv4 DHCPMessage_IPv4_t;

/**
 * @brief Function to cast pointers to DHCPMessage_IPv4_t.
 */
    static portINLINE ipDECL_CAST_PTR_FUNC_FOR_TYPE( DHCPMessage_IPv4_t )
    {
        return ( DHCPMessage_IPv4_t * ) pvArgument;
    }

/**
 * @brief Function to cast const pointers to DHCPMessage_IPv4_t.
 */
    static portINLINE ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( DHCPMessage_IPv4_t )
    {
        return ( const DHCPMessage_IPv4_t * ) pvArgument;
    }


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

/** @brief The number of end-points that are making use of the UDP-socket. */
    static BaseType_t xDHCPSocketUserCount;

/*
 * Generate a DHCP discover message and send it on the DHCP socket.
 */
    static void prvSendDHCPDiscover( NetworkEndPoint_t * pxEndPoint );

/*
 * Interpret message received on the DHCP socket.
 */
    _static BaseType_t prvProcessDHCPReplies( BaseType_t xExpectedMessageType,
                                              NetworkEndPoint_t * pxEndPoint );

/*
 * Generate a DHCP request packet, and send it on the DHCP socket.
 */
    static void prvSendDHCPRequest( NetworkEndPoint_t * pxEndPoint );

/*
 * Prepare to start a DHCP transaction.  This initialises some state variables
 * and creates the DHCP socket if necessary.
 */
    static void prvInitialiseDHCP( NetworkEndPoint_t * pxEndPoint );

/*
 * Creates the part of outgoing DHCP messages that are common to all outgoing
 * DHCP messages.
 */
    static uint8_t * prvCreatePartDHCPMessage( struct freertos_sockaddr * pxAddress,
                                               BaseType_t xOpcode,
                                               const uint8_t * const pucOptionsArray,
                                               size_t * pxOptionsArraySize,
                                               NetworkEndPoint_t * pxEndPoint );

/*
 * Create the DHCP socket, if it has not been created already.
 */
    _static void prvCreateDHCPSocket( NetworkEndPoint_t * pxEndPoint );

/*
 * Close the DHCP socket, only when not in use anymore (i.e. xDHCPSocketUserCount = 0).
 */
    static void prvCloseDHCPSocket( NetworkEndPoint_t * pxEndPoint );

    static void vDHCPProcessEndPoint( BaseType_t xReset,
                                      BaseType_t xDoCheck,
                                      NetworkEndPoint_t * pxEndPoint );

/*
 * After DHCP has failed to answer, prepare everything to start searching
 * for (trying-out) LinkLayer IP-addresses, using the random method: Send
 * a gratuitous ARP request and wait if another device responds to it.
 */
    #if ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 )
        static void prvPrepareLinkLayerIPLookUp( NetworkEndPoint_t * pxEndPoint );
    #endif

/*-----------------------------------------------------------*/

/**
 * @brief Check whether a given socket is the DHCP socket or not.
 *
 * @param[in] xSocket: The socket to be checked.
 *
 * @return If the socket given as parameter is the DHCP socket - return
 *         pdTRUE, else pdFALSE.
 */
    BaseType_t xIsDHCPSocket( Socket_t xSocket )
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
 * @brief Returns the current state of a DHCP process.
 *
 * @param[in] pxEndPoint: the end-point which is going through the DHCP process.
 */
    eDHCPState_t eGetDHCPState( struct xNetworkEndPoint * pxEndPoint )
    {
        /* Note that EP_DHCPData is defined as "pxEndPoint->xDHCPData". */
        return EP_DHCPData.eDHCPState;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Read and process incoming messages, and run the state machine for a
 *        given end-point.
 *
 * @param[in] xReset: Is the DHCP state machine starting over? pdTRUE/pdFALSE.
 * @param[in] pxEndPoint: The end-point for which the DHCP state machine should
 *                        make one cycle.
 */
    void vDHCPProcess( BaseType_t xReset,
                       struct xNetworkEndPoint * pxEndPoint )
    {
        BaseType_t xDoProcess = pdTRUE;

        /* Is DHCP starting over? */
        if( xReset != pdFALSE )
        {
            EP_DHCPData.eDHCPState = eInitialWait;
        }

        /* If there is a socket, check for incoming messages first. */
        if( xDHCPSocket != NULL )
        {
            uint8_t * pucUDPPayload;
            const DHCPMessage_IPv4_t * pxDHCPMessage;
            BaseType_t lBytes;

            for( ; ; )
            {
                NetworkEndPoint_t * pxIterator = NULL;

                /* Peek the next UDP message. */
                lBytes = FreeRTOS_recvfrom( xDHCPSocket, &( pucUDPPayload ), 0, ( BaseType_t ) ( ( UBaseType_t ) FREERTOS_ZERO_COPY | ( UBaseType_t ) FREERTOS_MSG_PEEK ), NULL, NULL );

                if( lBytes <= 0 )
                {
                    if( ( lBytes < 0 ) && ( lBytes != -pdFREERTOS_ERRNO_EAGAIN ) )
                    {
                        FreeRTOS_printf( ( "vDHCPProcess: FreeRTOS_recvfrom returns %d\n", ( int ) lBytes ) );
                    }

                    break;
                }

                /* Map a DHCP structure onto the received data. */
                pxDHCPMessage = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( DHCPMessage_IPv4_t, pucUDPPayload );

                /* Sanity check. */
                if( ( pxDHCPMessage->ulDHCPCookie == dhcpCOOKIE ) && ( pxDHCPMessage->ucOpcode == dhcpREPLY_OPCODE ) )
                {
                    pxIterator = pxNetworkEndPoints;

                    /* Find the end-point with given transaction ID. */
                    while( pxIterator != NULL )
                    {
                        if( pxDHCPMessage->ulTransactionID == FreeRTOS_htonl( pxIterator->xDHCPData.ulTransactionId ) )
                        {
                            break;
                        }

                        pxIterator = pxIterator->pxNext;
                    }
                }

                if( ( pxIterator != NULL ) && ( pxIterator->xDHCPData.eDHCPState == eLeasedAddress ) )
                {
                    /* No DHCP messages are expected while in eLeasedAddress state. */
                    pxIterator = NULL;
                }

                if( pxIterator != NULL )
                {
                    /* The second parameter pdTRUE tells to check for a UDP message. */
                    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxIterator );

                    if( pxEndPoint == pxIterator )
                    {
                        xDoProcess = pdFALSE;
                    }
                }
                else
                {
                    /* Target not found, fetch the message and delete it. */
                    /* PAss the address of a pointer pucUDPPayload, because zero-copy is used. */
                    lBytes = FreeRTOS_recvfrom( xDHCPSocket, &( pucUDPPayload ), 0, FREERTOS_ZERO_COPY, NULL, NULL );

                    if( lBytes > 0 )
                    {
                        /* Remove it now, destination not found. */
                        FreeRTOS_ReleaseUDPPayloadBuffer( pucUDPPayload );
                        FreeRTOS_printf( ( "vDHCPProcess: Removed a %d-byte message: target not found\n", ( int ) lBytes ) );
                    }
                }
            }
        }

        if( ( pxEndPoint != NULL ) && ( xDoProcess != pdFALSE ) )
        {
            /* Process the end-point, but do not expect incoming packets. */
            vDHCPProcessEndPoint( xReset, pdFALSE, pxEndPoint );
        }
    }

/**
 * @brief Process the DHCP state machine based on current state.
 *
 * @param[in] xReset: Is the DHCP state machine starting over? pdTRUE/pdFALSE.
 * @param[in] xDoCheck: true when an incoming message is to be expected, and
 *                      prvProcessDHCPReplies() will be called.
 * @param[in] pxEndPoint: The end-point for which the DHCP state machine should
 *                        make one cycle.
 */
    static void vDHCPProcessEndPoint( BaseType_t xReset,
                                      BaseType_t xDoCheck,
                                      NetworkEndPoint_t * pxEndPoint )
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
                static eDHCPState_t eLastState = eNotUsingLeasedAddress;

                if( eLastState != EP_DHCPData.eDHCPState )
                {
                    eLastState = EP_DHCPData.eDHCPState;
                    FreeRTOS_debug_printf( ( "vDHCPProcessEndPoint: enter %d\n", EP_DHCPData.eDHCPState ) );
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
                        /* See if prvInitialiseDHCP() has creates a socket. */
                        if( xDHCPSocket == NULL )
                        {
                            xGivingUp = pdTRUE;
                        }
                        else
                        {
                            /* Put 'ulIPAddress' to zero to indicate that the end-point is down. */
                            EP_IPv4_SETTINGS.ulIPAddress = 0UL;

                            /* Send the first discover request. */
                            EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();
                            prvSendDHCPDiscover( pxEndPoint );
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
                            xGivingUp = pdTRUE;
                        }
                    #endif /* ipconfigUSE_DHCP_HOOK */
                    break;

                case eWaitingOffer:

                    xGivingUp = pdFALSE;

                    /* Look for offers coming in. */
                    if( xDoCheck != pdFALSE )
                    {
                        if( prvProcessDHCPReplies( dhcpMESSAGE_TYPE_OFFER, pxEndPoint ) == pdPASS )
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
                                prvSendDHCPRequest( pxEndPoint );
                                EP_DHCPData.eDHCPState = eWaitingAcknowledge;
                                break;
                            }

                            #if ( ipconfigUSE_DHCP_HOOK != 0 )
                                if( eAnswer == eDHCPUseDefaults )
                                {
                                    ( void ) memcpy( &( pxEndPoint->ipv4_settings ), &( pxEndPoint->ipv4_defaults ), sizeof( pxEndPoint->ipv4_settings ) );
                                }

                                /* The user indicates that the DHCP process does not continue. */
                                xGivingUp = pdTRUE;
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

                                prvSendDHCPDiscover( pxEndPoint );
                                FreeRTOS_debug_printf( ( "vDHCPProcess: timeout %lu ticks\n", EP_DHCPData.xDHCPTxPeriod ) );
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

                    if( xDoCheck == pdFALSE )
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
                                prvSendDHCPRequest( pxEndPoint );
                            }
                            else
                            {
                                /* Give up, start again. */
                                EP_DHCPData.eDHCPState = eInitialWait;
                            }
                        }
                    }
                    else if( prvProcessDHCPReplies( dhcpMESSAGE_TYPE_ACK, pxEndPoint ) == pdPASS )
                    {
                        FreeRTOS_debug_printf( ( "vDHCPProcess: acked %lxip\n", FreeRTOS_ntohl( EP_DHCPData.ulOfferedIPAddress ) ) );

                        /* DHCP completed.  The IP address can now be used, and the
                         * timer set to the lease timeout time. */
                        EP_IPv4_SETTINGS.ulIPAddress = EP_DHCPData.ulOfferedIPAddress;

                        /* Setting the 'local' broadcast address, something like
                         * '192.168.1.255'. */
                        EP_IPv4_SETTINGS.ulBroadcastAddress = EP_DHCPData.ulOfferedIPAddress | ~( EP_IPv4_SETTINGS.ulNetMask );
                        EP_DHCPData.eDHCPState = eLeasedAddress;

                        iptraceDHCP_SUCCEDEED( EP_DHCPData.ulOfferedIPAddress );

                        /* DHCP failed, the default configured IP-address will be used
                         * Now call vIPNetworkUpCalls() to send the network-up event and
                         * start the ARP timer. */
                        vIPNetworkUpCalls( pxEndPoint );
                        /* Close socket to ensure packets don't queue on it. */
                        prvCloseDHCPSocket( pxEndPoint );

                        if( EP_DHCPData.ulLeaseTime == 0UL )
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
                        vIPReloadDHCP_RATimer( ( struct xNetworkEndPoint * ) pxEndPoint, EP_DHCPData.ulLeaseTime );
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

                                    /* Auto-IP succeeded, the default configured IP-address will
                                     * be used.  Now call vIPNetworkUpCalls() to send the
                                     * network-up event and start the ARP timer. */
                                    vIPNetworkUpCalls( pxEndPoint );
                                    EP_DHCPData.eDHCPState = eNotUsingLeasedAddress;
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

                    if( FreeRTOS_IsEndPointUp( pxEndPoint ) != 0 )
                    {
                        /* Resend the request at the appropriate time to renew the lease. */
                        prvCreateDHCPSocket( pxEndPoint );

                        if( xDHCPSocket != NULL )
                        {
                            EP_DHCPData.xDHCPTxTime = xTaskGetTickCount();
                            EP_DHCPData.xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;
                            prvSendDHCPRequest( pxEndPoint );
                            EP_DHCPData.eDHCPState = eWaitingAcknowledge;

                            /* From now on, we should be called more often */
                            vIPReloadDHCP_RATimer( pxEndPoint, dhcpINITIAL_TIMER_PERIOD );
                        }
                    }
                    else
                    {
                        /* See PR #53 on github/freertos/freertos */
                        FreeRTOS_printf( ( "DHCP: lease time finished but network is down\n" ) );
                        vIPReloadDHCP_RATimer( ( struct xNetworkEndPoint * ) pxEndPoint, pdMS_TO_TICKS( 5000U ) );
                    }

                    break;

                case eNotUsingLeasedAddress:

                    vIPSetDHCP_RATimerEnableState( pxEndPoint, pdFALSE );
                    break;

                default:
                    /* Lint: all options are included. */
                    break;
            }

            {
                static eDHCPState_t eLastState = eNotUsingLeasedAddress;

                if( eLastState != EP_DHCPData.eDHCPState )
                {
                    eLastState = EP_DHCPData.eDHCPState;
                    FreeRTOS_debug_printf( ( "vDHCPProcessEndPoint: exit %d\n", EP_DHCPData.eDHCPState ) );
                }
            }

            if( xGivingUp != pdFALSE )
            {
                /* xGivingUp became true either because of a time-out, or because
                 * xApplicationDHCPHook() returned another value than 'eDHCPContinue',
                 * meaning that the conversion is cancelled from here. */

                /* Revert to static IP address. */
                taskENTER_CRITICAL();
                {
                    EP_IPv4_SETTINGS.ulIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
                    iptraceDHCP_REQUESTS_FAILED_USING_DEFAULT_IP_ADDRESS( pxEndPoint->ipv4_defaults.ulIPAddress );
                }
                taskEXIT_CRITICAL();

                EP_DHCPData.eDHCPState = eNotUsingLeasedAddress;
                vIPSetDHCP_RATimerEnableState( pxEndPoint, pdFALSE );

                /* DHCP failed, the default configured IP-address will be used. Now
                 * call vIPNetworkUpCalls() to send the network-up event and start the ARP
                 * timer. */
                vIPNetworkUpCalls( pxEndPoint );

                /* Close socket to ensure packets don't queue on it. */
                prvCloseDHCPSocket( pxEndPoint );
            }
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Close the DHCP socket, but only when there are no other end-points
 *        using it.
 * @param[in] pxEndPoint: The end-point that stops using the socket.
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
/*-----------------------------------------------------------*/

/**
 * @brief Create a DHCP socket with the defined timeouts. The same socket
 *        will be shared among all end-points that need DHCP.
 */
    _static void prvCreateDHCPSocket( NetworkEndPoint_t * pxEndPoint )
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
            xAddress.sin_port = ( uint16_t ) dhcpCLIENT_PORT_IPv4;
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
 * @brief Initialise the DHCP state machine by creating DHCP socket and
 *        begin the transaction.
 *
 * @param[in] pxEndPoint: The end-point that needs DHCP.
 */
    static void prvInitialiseDHCP( NetworkEndPoint_t * pxEndPoint )
    {
        /* Initialise the parameters that will be set by the DHCP process. Per
         * https://www.ietf.org/rfc/rfc2131.txt, Transaction ID should be a random
         * value chosen by the client. */

        /* Check for random number generator API failure. */
        if( xApplicationGetRandomNumber( &( EP_DHCPData.ulTransactionId ) ) != pdFALSE )
        {
            EP_DHCPData.xUseBroadcast = 0;
            EP_DHCPData.ulOfferedIPAddress = 0UL;
            EP_DHCPData.ulDHCPServerAddress = 0UL;
            EP_DHCPData.xDHCPTxPeriod = dhcpINITIAL_DHCP_TX_PERIOD;

            /* Create the DHCP socket if it has not already been created. */
            prvCreateDHCPSocket( pxEndPoint );
            FreeRTOS_debug_printf( ( "prvInitialiseDHCP: start after %lu ticks\n", dhcpINITIAL_TIMER_PERIOD ) );
            vIPReloadDHCP_RATimer( pxEndPoint, dhcpINITIAL_TIMER_PERIOD );
        }
        else
        {
            /* There was a problem with the randomiser. */
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Process the DHCP replies.
 *
 * @param[in] xExpectedMessageType: The type of the message the DHCP state machine is expecting.
 *                                  Messages of different type will be dropped.
 * @param[in] pxEndPoint: The end-point to whom the replies are addressed.
 *
 * @return pdPASS: if DHCP options are received correctly; pdFAIL: Otherwise.
 */
    _static BaseType_t prvProcessDHCPReplies( BaseType_t xExpectedMessageType,
                                              NetworkEndPoint_t * pxEndPoint )
    {
        uint8_t * pucUDPPayload;
        int32_t lBytes;
        const DHCPMessage_IPv4_t * pxDHCPMessage;
        const uint8_t * pucByte;
        uint8_t ucOptionCode;
        uint32_t ulProcessed, ulParameter;
        BaseType_t xReturn = pdFALSE;
        const uint32_t ulMandatoryOptions = 2UL; /* DHCP server address, and the correct DHCP message type must be present in the options. */
/* memcpy() helper variables for MISRA Rule 21.15 compliance*/
        const void * pvCopySource;
        void * pvCopyDest;

        /* Passing the address of a pointer (pucUDPPayload) because FREERTOS_ZERO_COPY is used. */
        lBytes = FreeRTOS_recvfrom( xDHCPSocket, &pucUDPPayload, 0UL, FREERTOS_ZERO_COPY, NULL, NULL );

        if( lBytes > 0 )
        {
            /* Map a DHCP structure onto the received data. */
            pxDHCPMessage = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( DHCPMessage_IPv4_t, pucUDPPayload );

            /* Sanity check. */
            if( lBytes < ( int32_t ) sizeof( DHCPMessage_IPv4_t ) )
            {
                /* Not enough bytes. */
            }
            else if( ( pxDHCPMessage->ulDHCPCookie != ( uint32_t ) dhcpCOOKIE ) ||
                     ( pxDHCPMessage->ucOpcode != ( uint8_t ) dhcpREPLY_OPCODE ) )
            {
                /* Invalid cookie or unexpected opcode. */
            }
            else if( ( pxDHCPMessage->ulTransactionID != FreeRTOS_htonl( EP_DHCPData.ulTransactionId ) ) )
            {
                /* Transaction ID does not match. */
            }
            else /* Looks like a valid DHCP response, with the same transaction ID. */
            {
                if( memcmp( pxDHCPMessage->ucClientHardwareAddress,
                            pxEndPoint->xMACAddress.ucBytes,
                            sizeof( MACAddress_t ) ) != 0 )
                {
                    /* Target MAC address doesn't match. */
                }
                else
                {
                    size_t uxIndex, uxPayloadDataLength, uxLength;

                    /* None of the essential options have been processed yet. */
                    ulProcessed = 0UL;

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

                                /* ulProcessed is not incremented in this case
                                 * because the DNS server is not essential.  Only the
                                 * first DNS server address is taken. */
                                FreeRTOS_printf( ( "DNS address: %lxip\n", ulParameter ) );
                                EP_IPv4_SETTINGS.ulDNSServerAddresses[ 0 ] = ulParameter;
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
                                    EP_DHCPData.ulLeaseTime >>= 1UL;

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
                        FreeRTOS_printf( ( "vDHCPProcess: offer %lxip\n", FreeRTOS_ntohl( EP_DHCPData.ulOfferedIPAddress ) ) );
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
 * @param[in] pxEndPoint: The end-point to which the message will be sent.
 *
 * @return Ethernet buffer of the partially created DHCP packet.
 */
    static uint8_t * prvCreatePartDHCPMessage( struct freertos_sockaddr * pxAddress,
                                               BaseType_t xOpcode,
                                               const uint8_t * const pucOptionsArray,
                                               size_t * pxOptionsArraySize,
                                               NetworkEndPoint_t * pxEndPoint )
    {
        DHCPMessage_IPv4_t * pxDHCPMessage;
        size_t uxRequiredBufferSize = sizeof( DHCPMessage_IPv4_t ) + *pxOptionsArraySize;
        NetworkBufferDescriptor_t * pxNetworkBuffer;
        uint8_t * pucUDPPayloadBuffer;

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

        /* Get a buffer.  This uses a maximum delay, but the delay will be capped
         * to ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS so the return value still needs to
         * be test. */
        do
        {
            /* Obtain a network buffer with the required amount of storage. */
            pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( sizeof( UDPPacket_t ) + uxRequiredBufferSize, portMAX_DELAY );
        } while( pxNetworkBuffer == NULL );

        /* Leave space for the UDP header. */
        pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
        pxDHCPMessage = ipCAST_PTR_TO_TYPE_PTR( DHCPMessage_IPv4_t, pucUDPPayloadBuffer );

        #if ( ipconfigUSE_IPv6 != 0 )
            {
                uint8_t * pucIPType;

                pucIPType = pucUDPPayloadBuffer - ipUDP_PAYLOAD_IP_TYPE_OFFSET;
                *pucIPType = ipTYPE_IPv4;
            }
        #endif /* ipconfigUSE_IPv6 */

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

        ( void ) memcpy( &( pxDHCPMessage->ucClientHardwareAddress[ 0 ] ), pxEndPoint->xMACAddress.ucBytes, sizeof( MACAddress_t ) );

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
                         pxEndPoint->xMACAddress.ucBytes, sizeof( MACAddress_t ) );

        /* Set the addressing. */
        pxAddress->sin_addr = ipBROADCAST_IP_ADDRESS;
        pxAddress->sin_port = ( uint16_t ) dhcpSERVER_PORT_IPv4;
        pxNetworkBuffer->pxEndPoint = pxEndPoint;

        return pucUDPPayloadBuffer;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Create and send a DHCP request message through the DHCP socket.
 *
 * param[in] pxEndPoint: The end-point for which the request will be sent.
 */
    static void prvSendDHCPRequest( NetworkEndPoint_t * pxEndPoint )
    {
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
                                                        &( uxOptionsLength ),
                                                        pxEndPoint );

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

        FreeRTOS_debug_printf( ( "vDHCPProcess: reply %lxip\n", FreeRTOS_ntohl( EP_DHCPData.ulOfferedIPAddress ) ) );
        iptraceSENDING_DHCP_REQUEST();

        if( FreeRTOS_sendto( xDHCPSocket, pucUDPPayloadBuffer, sizeof( DHCPMessage_IPv4_t ) + uxOptionsLength, FREERTOS_ZERO_COPY, &xAddress, sizeof( xAddress ) ) == 0 )
        {
            /* The packet was not successfully queued for sending and must be
             * returned to the stack. */
            FreeRTOS_ReleaseUDPPayloadBuffer( pucUDPPayloadBuffer );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Create and send a DHCP discover packet through the DHCP socket.
 *
 * param[in] pxEndPoint: the end-point for which the discover message will be sent.
 */
    static void prvSendDHCPDiscover( NetworkEndPoint_t * pxEndPoint )
    {
        uint8_t const * pucUDPPayloadBuffer;
        struct freertos_sockaddr xAddress;
        static const uint8_t ucDHCPDiscoverOptions[] =
        {
            /* Do not change the ordering without also changing dhcpCLIENT_IDENTIFIER_OFFSET. */
            dhcpIPv4_MESSAGE_TYPE_OPTION_CODE,      1, dhcpMESSAGE_TYPE_DISCOVER,                                                                        /* Message type option. */
            dhcpIPv4_CLIENT_IDENTIFIER_OPTION_CODE, 7, 1,                                0,                            0, 0, 0, 0, 0,                    /* Client identifier. */
            dhcpIPv4_PARAMETER_REQUEST_OPTION_CODE, 3, dhcpIPv4_SUBNET_MASK_OPTION_CODE, dhcpIPv4_GATEWAY_OPTION_CODE, dhcpIPv4_DNS_SERVER_OPTIONS_CODE, /* Parameter request option. */
            dhcpOPTION_END_BYTE
        };
        size_t uxOptionsLength = sizeof( ucDHCPDiscoverOptions );

        pucUDPPayloadBuffer = prvCreatePartDHCPMessage( &xAddress,
                                                        ( BaseType_t ) dhcpREQUEST_OPCODE,
                                                        ucDHCPDiscoverOptions,
                                                        &( uxOptionsLength ),
                                                        pxEndPoint );

        FreeRTOS_debug_printf( ( "vDHCPProcess: discover\n" ) );
        iptraceSENDING_DHCP_DISCOVER();

        if( FreeRTOS_sendto( xDHCPSocket,
                             pucUDPPayloadBuffer,
                             sizeof( DHCPMessage_IPv4_t ) + uxOptionsLength,
                             FREERTOS_ZERO_COPY,
                             &( xAddress ),
                             sizeof( xAddress ) ) == 0 )
        {
            /* The packet was not successfully queued for sending and must be
             * returned to the stack. */
            FreeRTOS_ReleaseUDPPayloadBuffer( pucUDPPayloadBuffer );
        }
    }
/*-----------------------------------------------------------*/


    #if ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 )

/**
 * @brief When DHCP has failed, the code can assign a Link-Layer address, and check if
 *        another device already uses the IP-address.
 *
 * param[in] pxEndPoint: The end-point that wants to obtain a link-layer address.
 */
        static void prvPrepareLinkLayerIPLookUp( NetworkEndPoint_t * pxEndPoint )
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

            EP_IPv4_SETTINGS.ulGatewayAddress = 0UL;

            /* prepare xDHCPData with data to test. */
            EP_DHCPData.ulOfferedIPAddress =
                FreeRTOS_inet_addr_quick( LINK_LAYER_ADDRESS_0, LINK_LAYER_ADDRESS_1, ucLinkLayerIPAddress[ 0 ], ucLinkLayerIPAddress[ 1 ] );

            EP_DHCPData.ulLeaseTime = dhcpDEFAULT_LEASE_TIME; /*  don't care about lease time. just put anything. */

            EP_IPv4_SETTINGS.ulNetMask =
                FreeRTOS_inet_addr_quick( LINK_LAYER_NETMASK_0, LINK_LAYER_NETMASK_1, LINK_LAYER_NETMASK_2, LINK_LAYER_NETMASK_3 );

            /* DHCP completed.  The IP address can now be used, and the
             * timer set to the lease timeout time. */
            EP_IPv4_SETTINGS.ulIPAddress = EP_DHCPData.ulOfferedIPAddress;

            /* Setting the 'local' broadcast address, something like 192.168.1.255' */
            EP_IPv4_SETTINGS.ulBroadcastAddress = ( EP_DHCPData.ulOfferedIPAddress & EP_IPv4_SETTINGS.ulNetMask ) | ~EP_IPv4_SETTINGS.ulNetMask;

            /* Close socket to ensure packets don't queue on it. not needed anymore as DHCP failed. but still need timer for ARP testing. */
            prvCloseDHCPSocket( pxEndPoint );

            xApplicationGetRandomNumber( &( ulNumbers[ 0 ] ) );
            EP_DHCPData.xDHCPTxPeriod = pdMS_TO_TICKS( 3000UL + ( ulNumbers[ 0 ] & 0x3ffUL ) ); /*  do ARP test every (3 + 0-1024mS) seconds. */

            xARPHadIPClash = pdFALSE;                                                           /* reset flag that shows if have ARP clash. */
            vARPSendGratuitous();
        }

    #endif /* ipconfigDHCP_FALL_BACK_AUTO_IP */
/*-----------------------------------------------------------*/

#endif /* ipconfigUSE_DHCP != 0 */
