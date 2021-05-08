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
 * @file FreeRTOS_IP.c
 * @brief Implements the basic functionality for the FreeRTOS+TCP network stack.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#if ( ipconfigUSE_DHCPv6 == 1 )
    #include "FreeRTOS_DHCPv6.h"
#endif
#include "NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_Routing.h"
#include "FreeRTOS_ND.h"

#if !defined( ipconfigMULTI_INTERFACE ) || ( ipconfigMULTI_INTERFACE == 0 )
    #ifndef _lint
        #error Please define ipconfigMULTI_INTERFACE as 1 to use the multi version

/* It can be used in combination with 'ipconfigCOMPATIBLE_WITH_SINGLE' in order
 * to get backward compatibility. */
    #endif
#endif

/* Used to ensure the structure packing is having the desired effect.  The
 * 'volatile' is used to prevent compiler warnings about comparing a constant with
 * a constant. */
#ifndef _lint
    #define ipEXPECTED_EthernetHeader_t_SIZE    ( ( size_t ) 14 ) /**< Ethernet Header size in bytes. */
    #define ipEXPECTED_ARPHeader_t_SIZE         ( ( size_t ) 28 ) /**< ARP header size in bytes. */
    #define ipEXPECTED_IPHeader_t_SIZE          ( ( size_t ) 20 ) /**< IP header size in bytes. */
    #define ipEXPECTED_ICMPHeader_t_SIZE        ( ( size_t ) 8 )  /**< ICMP header size in bytes. */
    #define ipEXPECTED_UDPHeader_t_SIZE         ( ( size_t ) 8 )  /**< UDP header size in bytes. */
    #define ipEXPECTED_TCPHeader_t_SIZE         ( ( size_t ) 20 ) /**< TCP header size in bytes. */
#endif

/* ICMP protocol definitions. */
#define ipICMP_ECHO_REQUEST    ( ( uint8_t ) 8 )          /**< ICMP echo request. */
#define ipICMP_ECHO_REPLY      ( ( uint8_t ) 0 )          /**< ICMP echo reply. */

#if ( ipconfigUSE_IPv6 != 0 )
    /* IPv6 multicast MAC address starts with 33-33-. */
    #define ipMULTICAST_MAC_ADDRESS_IPv6_0    0x33U
    #define ipMULTICAST_MAC_ADDRESS_IPv6_1    0x33U
#endif

/* IPv4 multi-cast addresses range from 224.0.0.0.0 to 240.0.0.0. */
#define ipFIRST_MULTI_CAST_IPv4             0xE0000000U /**< Lower bound of the IPv4 multicast address. */
#define ipLAST_MULTI_CAST_IPv4              0xF0000000U /**< Higher bound of the IPv4 multicast address. */

/* The first byte in the IPv4 header combines the IP version (4) with
 * with the length of the IP header. */
#define ipIPV4_VERSION_HEADER_LENGTH_MIN    0x45U /**< Minimum IPv4 header length. */
#define ipIPV4_VERSION_HEADER_LENGTH_MAX    0x4FU /**< Maximum IPv4 header length. */

/** @brief Time delay between repeated attempts to initialise the network hardware. */
#ifndef ipINITIALISATION_RETRY_DELAY
    #define ipINITIALISATION_RETRY_DELAY    ( pdMS_TO_TICKS( 3000U ) )
#endif

/** @brief Defines how often the ARP timer callback function is executed.  The time is
 * shorter in the Windows simulator as simulated time is not real time. */
#ifndef ipARP_TIMER_PERIOD_MS
    #ifdef _WINDOWS_
        #define ipARP_TIMER_PERIOD_MS    ( 500U ) /* For windows simulator builds. */
    #else
        #define ipARP_TIMER_PERIOD_MS    ( 10000U )
    #endif
#endif

#ifndef iptraceIP_TASK_STARTING
    #define iptraceIP_TASK_STARTING()    do {} while( ipFALSE_BOOL ) /**< Empty definition in case iptraceIP_TASK_STARTING is not defined. */
#endif

#if ( ( ipconfigUSE_TCP == 1 ) && !defined( ipTCP_TIMER_PERIOD_MS ) )
    /** @brief When initialising the TCP timer, give it an initial time-out of 1 second. */
    #define ipTCP_TIMER_PERIOD_MS    ( 1000U )
#endif

/** @brief If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
 * driver will filter incoming packets and only pass the stack those packets it
 * considers need processing.  In this case ipCONSIDER_FRAME_FOR_PROCESSING() can
 * be #-defined away.  If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 0
 * then the Ethernet driver will pass all received packets to the stack, and the
 * stack must do the filtering itself.  In this case ipCONSIDER_FRAME_FOR_PROCESSING
 * needs to call eConsiderFrameForProcessing.
 */
#if ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#endif

#if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 0 )
    #if ( ipconfigBYTE_ORDER == pdFREERTOS_LITTLE_ENDIAN )
        /** @brief The bits in the two byte IP header field that make up the fragment offset value. */
        #define ipFRAGMENT_OFFSET_BIT_MASK    ( ( uint16_t ) 0xff0f )
    #else
        /** @brief The bits in the two byte IP header field that make up the fragment offset value. */
        #define ipFRAGMENT_OFFSET_BIT_MASK    ( ( uint16_t ) 0x0fff )
    #endif /* ipconfigBYTE_ORDER */
#endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */

/** @brief The maximum time the IP task is allowed to remain in the Blocked state if no
 * events are posted to the network event queue. */
#ifndef ipconfigMAX_IP_TASK_SLEEP_TIME
    #define ipconfigMAX_IP_TASK_SLEEP_TIME    ( pdMS_TO_TICKS( 10000U ) )
#endif

/** @brief Returned as the (invalid) checksum when the protocol being checked is not
 * handled.  The value is chosen simply to be easy to spot when debugging. */
#define ipUNHANDLED_PROTOCOL    0x4321U

/** @brief Returned to indicate a valid checksum. */
#define ipCORRECT_CRC           0xffffU

/** @brief Returned to indicate incorrect checksum. */
#define ipWRONG_CRC             0x0000U

/** @brief Returned as the (invalid) checksum when the length of the data being checked
 * had an invalid length. */
#define ipINVALID_LENGTH        0x1234U

/* Trace macros to aid in debugging, disabled if ipconfigHAS_PRINTF != 1 */
#if ( ipconfigHAS_PRINTF == 1 )
    #define DEBUG_DECLARE_TRACE_VARIABLE( type, var, init )    type var = ( init ) /**< Trace macro to set "type var = init". */
    #define DEBUG_SET_TRACE_VARIABLE( var, value )             var = ( value )     /**< Trace macro to set var = value. */
#else
    #define DEBUG_DECLARE_TRACE_VARIABLE( type, var, init )                        /**< Empty definition since ipconfigHAS_PRINTF != 1. */
    #define DEBUG_SET_TRACE_VARIABLE( var, value )                                 /**< Empty definition since ipconfigHAS_PRINTF != 1. */
#endif

/**
 * @brief Helper function to do a cast to a NetworkInterface_t pointer.
 *
 * @note NetworkInterface_t: the name of a type.
 *
 * @return the converted pointer.
 */
static portINLINE ipDECL_CAST_PTR_FUNC_FOR_TYPE( NetworkInterface_t )
{
    return ( NetworkInterface_t * ) pvArgument;
}

/**
 * @brief Helper function to do a cast to a NetworkEndPoint_t pointer.
 *
 * @note NetworkEndPoint_t: the name of a type.
 *
 * @return the converted pointer.
 */
static portINLINE ipDECL_CAST_PTR_FUNC_FOR_TYPE( NetworkEndPoint_t )
{
    return ( NetworkEndPoint_t * ) pvArgument;
}

static void prvCallDHCP_RA_Handler( NetworkEndPoint_t * pxEndPoint );

#if ( ipconfigUSE_IPv6 != 0 )
    static BaseType_t prvChecksumIPv6Checks( const uint8_t * pucEthernetBuffer,
                                             size_t uxBufferLength,
                                             struct xPacketSummary * pxSet );
#endif

static BaseType_t prvChecksumIPv4Checks( const uint8_t * pucEthernetBuffer,
                                         size_t uxBufferLength,
                                         struct xPacketSummary * pxSet );

static BaseType_t prvChecksumProtocolChecks( size_t uxBufferLength,
                                             struct xPacketSummary * pxSet );

static BaseType_t prvChecksumProtocolMTUCheck( struct xPacketSummary * pxSet );

static void prvChecksumProtocolCalculate( BaseType_t xOutgoingPacket,
                                          const uint8_t * pucEthernetBuffer,
                                          struct xPacketSummary * pxSet );

static void prvChecksumProtocolSetChecksum( BaseType_t xOutgoingPacket,
                                            const uint8_t * pucEthernetBuffer,
                                            size_t uxBufferLength,
                                            struct xPacketSummary * pxSet );

/*-----------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )
    const struct xIPv6_Address in6addr_any = { 0 };
    const struct xIPv6_Address in6addr_loopback = { { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 } };
#endif

/*-----------------------------------------------------------*/

/*
 * The main TCP/IP stack processing task.  This task receives commands/events
 * from the network hardware drivers and tasks that are using sockets.  It also
 * maintains a set of protocol timers.
 */
static void prvIPTask( void * pvParameters );

/*
 * Called when new data is available from the network interface.
 */
static void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

/*
 * Process incoming IP packets.
 */
static eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                                    NetworkBufferDescriptor_t * const pxNetworkBuffer );

#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

/*
 * Process incoming ICMP packets.
 */
    static eFrameProcessingResult_t prvProcessICMPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );
#endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */

/*
 * Turns around an incoming ping request to convert it into a ping reply.
 */
#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 )
    static eFrameProcessingResult_t prvProcessICMPEchoRequest( ICMPPacket_t * const pxICMPPacket );
#endif /* ipconfigREPLY_TO_INCOMING_PINGS */

/*
 * Processes incoming ping replies.  The application callback function
 * vApplicationPingReplyHook() is called with the results.
 */
#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
    static void prvProcessICMPEchoReply( ICMPPacket_t * const pxICMPPacket );
#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

/*
 * Called to create a network connection when the stack is first started, or
 * when the network connection is lost.
 */
static void prvProcessNetworkDownEvent( NetworkInterface_t * pxInterface );

/*
 * Checks the ARP, DHCP and TCP timers to see if any periodic or timeout
 * processing is required.
 */
static void prvCheckNetworkTimers( void );

/*
 * Determine how long the IP task can sleep for, which depends on when the next
 * periodic or timeout processing must be performed.
 */
static TickType_t prvCalculateSleepTime( void );

/*
 * The network card driver has received a packet.  In the case that it is part
 * of a linked packet chain, walk through it to handle every message.
 */
static void prvHandleEthernetPacket( NetworkBufferDescriptor_t * pxBuffer );

/* Handle the 'eNetworkTxEvent': forward a packet from an application to the NIC. */
static void prvForwardTxPacket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                BaseType_t xReleaseAfterSend );

/*
 * Utility functions for the light weight IP timers.
 */
static void prvIPTimerStart( IPTimer_t * pxTimer,
                             TickType_t xTime );
static BaseType_t prvIPTimerCheck( IPTimer_t * pxTimer );
static void prvIPTimerReload( IPTimer_t * pxTimer,
                              TickType_t xTime );

/* The function 'prvAllowIPPacket()' checks if a packets should be processed. */
static eFrameProcessingResult_t prvAllowIPPacketIPv4( const IPPacket_t * const pxIPPacket,
                                                      const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                      UBaseType_t uxHeaderLength );

#if ( ipconfigUSE_IPv6 != 0 )
    static eFrameProcessingResult_t prvAllowIPPacketIPv6( const IPHeader_IPv6_t * const pxIPv6Header,
                                                          const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                          UBaseType_t uxHeaderLength );
#endif

static eFrameProcessingResult_t prvCheckIP4HeaderOptions( NetworkBufferDescriptor_t * const pxNetworkBuffer );

static eFrameProcessingResult_t prvProcessUDPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

/*-----------------------------------------------------------*/

/** @brief The queue used to pass events into the IP-task for processing. */
QueueHandle_t xNetworkEventQueue = NULL;

/** @brief The IP packet ID. */
uint16_t usPacketIdentifier = 0U;

/** @brief For convenience, a MAC address of all 0xffs is defined const for quick
 * reference. */
const MACAddress_t xBroadcastMACAddress = { { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff } };


/** @brief Used to ensure network down events cannot be missed when they cannot be
 * posted to the network event queue because the network event queue is already
 * full. */
static volatile BaseType_t xNetworkDownEventPending = pdFALSE;

/** @brief Stores the handle of the task that handles the stack.  The handle is used
 * (indirectly) by some utility function to determine if the utility function is
 * being called by a task (in which case it is ok to block) or by the IP task
 * itself (in which case it is not ok to block). */

static TaskHandle_t xIPTaskHandle = NULL;

#if ( ipconfigUSE_TCP != 0 )

/** @brief Set to a non-zero value if one or more TCP message have been processed
 * within the last round. */
    static BaseType_t xProcessedTCPMessage;
#endif

/** @brief 'xAllNetworksUp' becomes pdTRUE as soon as all network interfaces have
 * been initialised. */
static BaseType_t xAllNetworksUp = pdFALSE;

/** @brief As long as not all networks are up, repeat initialisation by calling the
 * xNetworkInterfaceInitialise() function of the interfaces that are not ready. */
static IPTimer_t xNetworkTimer;

/*
 * A timer for each of the following processes, all of which need attention on a
 * regular basis
 */

/** @brief ARP timer, to check its table entries. */
static IPTimer_t xARPTimer;
#if ( ipconfigUSE_TCP != 0 )
    /** @brief TCP timer, to check for timeouts, resends. */
    static IPTimer_t xTCPTimer;
#endif
#if ( ipconfigDNS_USE_CALLBACKS != 0 )
    /** @brief DNS timer, to check for timeouts when looking-up a domain. */
    static IPTimer_t xDNSTimer;
#endif

/** @brief Set to pdTRUE when the IP task is ready to start processing packets. */
static BaseType_t xIPTaskInitialised = pdFALSE;

#if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
    /** @brief Keep track of the lowest amount of space in 'xNetworkEventQueue'. */
    static UBaseType_t uxQueueMinimumSpace = ipconfigEVENT_QUEUE_LENGTH;
#endif

/*-----------------------------------------------------------*/

/* Coverity wants to make pvParameters const, which would make it incompatible. Leave the
 * function signature as is. */

/**
 * @brief The IP task handles all requests from the user application and the
 *        network interface. It receives messages through a FreeRTOS queue called
 *        'xNetworkEventQueue'. prvIPTask() is the only task which has access to
 *        the data of the IP-stack, and so it has no need of using mutexes.
 *
 * @param[in] pvParameters: Not used.
 */
static void prvIPTask( void * pvParameters )
{
    IPStackEvent_t xReceivedEvent;
    TickType_t xNextIPSleep;
    FreeRTOS_Socket_t * pxSocket;

    #if ( ipconfigUSE_IPv6 != 0 )
        struct freertos_sockaddr6 xAddress;
    #else
        struct freertos_sockaddr xAddress;
    #endif
    NetworkInterface_t * pxInterface;

    /* Just to prevent compiler warnings about unused parameters. */
    ( void ) pvParameters;

    /* A possibility to set some additional task properties. */
    iptraceIP_TASK_STARTING();

    /* Generate a dummy message to say that the network connection has gone
     * down.  This will cause this task to initialise the network interface.  After
     * this it is the responsibility of the network interface hardware driver to
     * send this message if a previously connected network is disconnected. */

    prvIPTimerReload( &( xNetworkTimer ), pdMS_TO_TICKS( ipINITIALISATION_RETRY_DELAY ) );

    for( pxInterface = pxNetworkInterfaces; pxInterface != NULL; pxInterface = pxInterface->pxNext )
    {
        /* Post a 'eNetworkDownEvent' for every interface. */
        FreeRTOS_NetworkDown( pxInterface );
    }

    #if ( ipconfigUSE_TCP == 1 )
        {
            /* Initialise the TCP timer. */
            prvIPTimerReload( &xTCPTimer, pdMS_TO_TICKS( ipTCP_TIMER_PERIOD_MS ) );
        }
    #endif

    #if ( ipconfigDNS_USE_CALLBACKS != 0 )
        {
            /* The following function is declared in FreeRTOS_DNS.c and 'private' to
             * this library */
            vDNSInitialise();
        }
    #endif /* ipconfigDNS_USE_CALLBACKS != 0 */

    /* Initialisation is complete and events can now be processed. */
    xIPTaskInitialised = pdTRUE;

    FreeRTOS_debug_printf( ( "prvIPTask started\n" ) );

    /* Loop, processing IP events. */
    for( ; ; )
    {
        ipconfigWATCHDOG_TIMER();

        /* Check the ARP, DHCP and TCP timers to see if there is any periodic
         * or timeout processing to perform. */
        prvCheckNetworkTimers();

        /* Calculate the acceptable maximum sleep time. */
        xNextIPSleep = prvCalculateSleepTime();

        /* Wait until there is something to do. If the following call exits
         * due to a time out rather than a message being received, set a
         * 'NoEvent' value. */
        if( xQueueReceive( xNetworkEventQueue, ( void * ) &xReceivedEvent, xNextIPSleep ) == pdFALSE )
        {
            xReceivedEvent.eEventType = eNoEvent;
        }

        #if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
            {
                if( xReceivedEvent.eEventType != eNoEvent )
                {
                    UBaseType_t uxCount;

                    uxCount = uxQueueSpacesAvailable( xNetworkEventQueue );

                    if( uxQueueMinimumSpace > uxCount )
                    {
                        uxQueueMinimumSpace = uxCount;
                    }
                }
            }
        #endif /* ipconfigCHECK_IP_QUEUE_SPACE */

        iptraceNETWORK_EVENT_RECEIVED( xReceivedEvent.eEventType );

        switch( xReceivedEvent.eEventType )
        {
            case eNetworkDownEvent:
                /* Attempt to establish a connection. */
                prvProcessNetworkDownEvent( ipCAST_PTR_TO_TYPE_PTR( NetworkInterface_t, xReceivedEvent.pvData ) );
                break;

            case eNetworkRxEvent:

                /* The network hardware driver has received a new packet.  A
                 * pointer to the received buffer is located in the pvData member
                 * of the received event structure. */
                prvHandleEthernetPacket( ipCAST_PTR_TO_TYPE_PTR( NetworkBufferDescriptor_t, xReceivedEvent.pvData ) );
                break;

            case eNetworkTxEvent:

                /* Send a network packet. The ownership will  be transferred to
                 * the driver, which will release it after delivery. */
                prvForwardTxPacket( ipCAST_PTR_TO_TYPE_PTR( NetworkBufferDescriptor_t, xReceivedEvent.pvData ), pdTRUE );
                break;

            case eARPTimerEvent:
                /* The ARP timer has expired, process the ARP cache. */
                vARPAgeCache();
                #if ( ipconfigUSE_IPv6 != 0 )
                    vNDAgeCache();
                #endif /* ( ipconfigUSE_IPv6 != 0 ) */
                break;

            case eSocketBindEvent:

                /* FreeRTOS_bind (a user API) wants the IP-task to bind a socket
                 * to a port. The port number is communicated in the socket field
                 * usLocalPort. vSocketBind() will actually bind the socket and the
                 * API will unblock as soon as the eSOCKET_BOUND event is
                 * triggered. */
                pxSocket = ipCAST_PTR_TO_TYPE_PTR( FreeRTOS_Socket_t, xReceivedEvent.pvData );
                xAddress.sin_len = ( uint8_t ) sizeof( xAddress );
                #if ( ipconfigUSE_IPv6 != 0 )
                    if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
                    {
                        xAddress.sin_family = FREERTOS_AF_INET6;
                        ( void ) memcpy( xAddress.sin_addrv6.ucBytes, pxSocket->xLocalAddress_IPv6.ucBytes, sizeof( xAddress.sin_addrv6.ucBytes ) );
                    }
                    else
                #endif
                {
                    struct freertos_sockaddr * pxAddress = ipCAST_PTR_TO_TYPE_PTR( sockaddr4_t, &( xAddress ) );

                    pxAddress->sin_family = FREERTOS_AF_INET;
                    pxAddress->sin_addr = FreeRTOS_htonl( pxSocket->ulLocalAddress );
                }

                xAddress.sin_port = FreeRTOS_htons( pxSocket->usLocalPort );
                /* 'ulLocalAddress' and 'usLocalPort' will be set again by vSocketBind(). */
                pxSocket->ulLocalAddress = 0;
                pxSocket->usLocalPort = 0;
                ( void ) vSocketBind( pxSocket, ipCAST_PTR_TO_TYPE_PTR( sockaddr4_t, &( xAddress ) ), sizeof( xAddress ), pdFALSE );

                /* Before 'eSocketBindEvent' was sent it was tested that
                 * ( xEventGroup != NULL ) so it can be used now to wake up the
                 * user. */
                pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_BOUND;
                vSocketWakeUpUser( pxSocket );
                break;

            case eSocketCloseEvent:

                /* The user API FreeRTOS_closesocket() has sent a message to the
                 * IP-task to actually close a socket. This is handled in
                 * vSocketClose().  As the socket gets closed, there is no way to
                 * report back to the API, so the API won't wait for the result */
                ( void ) vSocketClose( ipCAST_PTR_TO_TYPE_PTR( FreeRTOS_Socket_t, xReceivedEvent.pvData ) );
                break;

            case eStackTxEvent:

                /* The network stack has generated a packet to send.  A
                 * pointer to the generated buffer is located in the pvData
                 * member of the received event structure. */
                vProcessGeneratedUDPPacket( ipCAST_PTR_TO_TYPE_PTR( NetworkBufferDescriptor_t, xReceivedEvent.pvData ) );
                break;

            case eDHCP_RA_Event:
                prvCallDHCP_RA_Handler( ipCAST_PTR_TO_TYPE_PTR( NetworkEndPoint_t, xReceivedEvent.pvData ) );
                break;

            case eSocketSelectEvent:

                /* FreeRTOS_select() has got unblocked by a socket event,
                 * vSocketSelect() will check which sockets actually have an event
                 * and update the socket field xSocketBits. */
                #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
                    {
                        #if ( ipconfigSELECT_USES_NOTIFY != 0 )
                            {
                                SocketSelectMessage_t * pxMessage = ipCAST_PTR_TO_TYPE_PTR( SocketSelectMessage_t, xReceivedEvent.pvData );
                                vSocketSelect( pxMessage->pxSocketSet );
                                ( void ) xTaskNotifyGive( pxMessage->xTaskhandle );
                            }
                        #else
                            {
                                vSocketSelect( ipCAST_PTR_TO_TYPE_PTR( SocketSelect_t, xReceivedEvent.pvData ) );
                            }
                        #endif /* ( ipconfigSELECT_USES_NOTIFY != 0 ) */
                    }
                #endif /* ipconfigSUPPORT_SELECT_FUNCTION == 1 */
                break;

            case eSocketSignalEvent:
                #if ( ipconfigSUPPORT_SIGNALS != 0 )
                    {
                        /* Some task wants to signal the user of this socket in
                         * order to interrupt a call to recv() or a call to select(). */
                        ( void ) FreeRTOS_SignalSocket( ipPOINTER_CAST( Socket_t, xReceivedEvent.pvData ) );
                    }
                #endif /* ipconfigSUPPORT_SIGNALS */
                break;

            case eTCPTimerEvent:
                #if ( ipconfigUSE_TCP == 1 )
                    {
                        /* Simply mark the TCP timer as expired so it gets processed
                         * the next time prvCheckNetworkTimers() is called. */
                        xTCPTimer.bExpired = pdTRUE_UNSIGNED;
                    }
                #endif /* ipconfigUSE_TCP */
                break;

            case eTCPAcceptEvent:

                /* The API FreeRTOS_accept() was called, the IP-task will now
                 * check if the listening socket (communicated in pvData) actually
                 * received a new connection. */
                #if ( ipconfigUSE_TCP == 1 )
                    {
                        pxSocket = ipCAST_PTR_TO_TYPE_PTR( FreeRTOS_Socket_t, xReceivedEvent.pvData );

                        if( xTCPCheckNewClient( pxSocket ) != pdFALSE )
                        {
                            pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_ACCEPT;
                            vSocketWakeUpUser( pxSocket );
                        }
                    }
                #endif /* ipconfigUSE_TCP */
                break;

            case eTCPNetStat:

                /* FreeRTOS_netstat() was called to have the IP-task print an
                 * overview of all sockets and their connections */
                #if ( ( ipconfigUSE_TCP == 1 ) && ( ipconfigHAS_PRINTF == 1 ) )
                    {
                        vTCPNetStat();
                    }
                #endif /* ipconfigUSE_TCP */
                break;

            case eNoEvent:
                /* xQueueReceive() returned because of a normal time-out. */
                break;

            default:
                /* Should not get here. */
                break;
        }

        if( xNetworkDownEventPending != pdFALSE )
        {
            /* A network down event could not be posted to the network event
             * queue because the queue was full.
             * As this code runs in the IP-task, it can be done directly by
             * calling prvProcessNetworkDownEvent(). */
            xNetworkDownEventPending = pdFALSE;

            for( pxInterface = FreeRTOS_FirstNetworkInterface();
                 pxInterface != NULL;
                 pxInterface = FreeRTOS_NextNetworkInterface( pxInterface ) )
            {
                if( pxInterface->bits.bCallDownEvent != pdFALSE_UNSIGNED )
                {
                    prvProcessNetworkDownEvent( pxInterface );
                    pxInterface->bits.bCallDownEvent = pdFALSE_UNSIGNED;
                }
            }
        }
    }
}
/*-----------------------------------------------------------*/


/**
 * @brief Call the state machine of either DHCP, DHCPv6, or RA, whichever is activated.
 *
 * @param[in] pxEndPoint: The end-point for which the state-machine will be called.
 */
static void prvCallDHCP_RA_Handler( NetworkEndPoint_t * pxEndPoint )
{
    #if ( ipconfigUSE_IPv6 != 0 ) && ( ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_RA == 1 ) )
        BaseType_t xIsIPv6 = pdFALSE;

        if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
        {
            xIsIPv6 = pdTRUE;
        }
    #endif
    /* The DHCP state machine needs processing. */
    #if ( ipconfigUSE_DHCP == 1 )
        {
            if( ( pxEndPoint->bits.bWantDHCP != pdFALSE_UNSIGNED )
                #if ( ipconfigUSE_IPv6 != 0 )
                    && ( xIsIPv6 == pdFALSE )
                #endif
                )
            {
                /* Process DHCP messages for a given end-point. */
                vDHCPProcess( pdFALSE, pxEndPoint );
            }
        }
    #endif /* ipconfigUSE_DHCP */
    #if ( ipconfigUSE_DHCPv6 == 1 )
        {
            if( ( xIsIPv6 == pdTRUE ) && ( pxEndPoint->bits.bWantDHCP != pdFALSE_UNSIGNED ) )
            {
                /* Process DHCPv6 messages for a given end-point. */
                vDHCPv6Process( pdFALSE, pxEndPoint );
            }
        }
    #endif /* ipconfigUSE_DHCPv6 */
    #if ( ipconfigUSE_RA == 1 )
        {
            if( ( xIsIPv6 == pdTRUE ) && ( pxEndPoint->bits.bWantRA != pdFALSE_UNSIGNED ) )
            {
                /* Process RA messages for a given end-point. */
                vRAProcess( pdFALSE, pxEndPoint );
            }
        }
    #endif /* ipconfigUSE_RA */
    /* Mention pxEndPoint in case it has not been used. */
    ( void ) pxEndPoint;
}
/*-----------------------------------------------------------*/

/**
 * @brief Function to check whether the current context belongs to
 *        the IP-task.
 *
 * @return If the current context belongs to the IP-task, then pdTRUE is
 *         returned. Else pdFALSE is returned.
 *
 * @note Very important: the IP-task is not allowed to call its own API's,
 *        because it would easily get into a dead-lock.
 */
BaseType_t xIsCallingFromIPTask( void )
{
    BaseType_t xReturn;

    if( xTaskGetCurrentTaskHandle() == xIPTaskHandle )
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
 * @brief The variable 'xIPTaskHandle' is declared static.  This function
 *        gives read-only access to it.
 *
 * @return The handle of the IP-task.
 */
TaskHandle_t FreeRTOS_GetIPTaskHandle( void )
{
    return xIPTaskHandle;
}
/*-----------------------------------------------------------*/

/**
 * @brief Handle the incoming Ethernet packets.
 *
 * @param[in] pxBuffer: Linked/un-linked network buffer descriptor(s)
 *                      to be processed.
 */
static void prvHandleEthernetPacket( NetworkBufferDescriptor_t * pxBuffer )
{
    #if ( ipconfigUSE_LINKED_RX_MESSAGES == 0 )
        {
            /* When ipconfigUSE_LINKED_RX_MESSAGES is not set to 0 then only one
             * buffer will be sent at a time.  This is the default way for +TCP to pass
             * messages from the MAC to the TCP/IP stack. */
            prvProcessEthernetPacket( pxBuffer );
        }
    #else /* ipconfigUSE_LINKED_RX_MESSAGES */
        {
            NetworkBufferDescriptor_t * pxNextBuffer;

            /* An optimisation that is useful when there is high network traffic.
             * Instead of passing received packets into the IP task one at a time the
             * network interface can chain received packets together and pass them into
             * the IP task in one go.  The packets are chained using the pxNextBuffer
             * member.  The loop below walks through the chain processing each packet
             * in the chain in turn. */
            do
            {
                /* Store a pointer to the buffer after pxBuffer for use later on. */
                pxNextBuffer = pxBuffer->pxNextBuffer;

                /* Make it NULL to avoid using it later on. */
                pxBuffer->pxNextBuffer = NULL;

                prvProcessEthernetPacket( pxBuffer );
                pxBuffer = pxNextBuffer;

                /* While there is another packet in the chain. */
            } while( pxBuffer != NULL );
        }
    #endif /* ipconfigUSE_LINKED_RX_MESSAGES */
}
/*-----------------------------------------------------------*/

/**
 * @brief Send a network packet.
 *
 * @param[in] pxNetworkBuffer: The message buffer.
 * @param[in] xReleaseAfterSend: When true, the network interface will own the buffer and is responsible for it's release.
 */
static void prvForwardTxPacket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                BaseType_t xReleaseAfterSend )
{
    iptraceNETWORK_INTERFACE_OUTPUT( pxNetworkBuffer->xDataLength, pxNetworkBuffer->pucEthernetBuffer );

    if( pxNetworkBuffer->pxInterface != NULL )
    {
        ( void ) pxNetworkBuffer->pxInterface->pfOutput( pxNetworkBuffer->pxInterface, pxNetworkBuffer, xReleaseAfterSend );
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Calculate the maximum sleep time remaining. It will go through all
 *        timers to see which timer will expire first. That will be the amount
 *        of time to block in the next call to xQueueReceive().
 *
 * @return The maximum sleep time or ipconfigMAX_IP_TASK_SLEEP_TIME,
 *         whichever is smaller.
 */
static TickType_t prvCalculateSleepTime( void )
{
    TickType_t xMaximumSleepTime;

    /* Start with the maximum sleep time, then check this against the remaining
     * time in any other timers that are active. */
    xMaximumSleepTime = ipconfigMAX_IP_TASK_SLEEP_TIME;

    if( xARPTimer.bActive != pdFALSE_UNSIGNED )
    {
        if( xARPTimer.ulRemainingTime < xMaximumSleepTime )
        {
            xMaximumSleepTime = xARPTimer.ulReloadTime;
        }
    }

    #if ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 )
        {
            NetworkEndPoint_t * pxEndPoint = pxNetworkEndPoints;

            while( pxEndPoint != NULL )
            {
                if( pxEndPoint->xDHCP_RATimer.bActive != pdFALSE_UNSIGNED )
                {
                    if( pxEndPoint->xDHCP_RATimer.ulRemainingTime < xMaximumSleepTime )
                    {
                        xMaximumSleepTime = pxEndPoint->xDHCP_RATimer.ulRemainingTime;
                    }
                }

                pxEndPoint = pxEndPoint->pxNext;
            }
        }
    #endif /* ipconfigUSE_DHCP */

    #if ( ipconfigUSE_TCP == 1 )
        {
            if( xTCPTimer.ulRemainingTime < xMaximumSleepTime )
            {
                xMaximumSleepTime = xTCPTimer.ulRemainingTime;
            }
        }
    #endif

    #if ( ipconfigDNS_USE_CALLBACKS != 0 )
        {
            if( xDNSTimer.bActive != pdFALSE_UNSIGNED )
            {
                if( xDNSTimer.ulRemainingTime < xMaximumSleepTime )
                {
                    xMaximumSleepTime = xDNSTimer.ulRemainingTime;
                }
            }
        }
    #endif

    return xMaximumSleepTime;
}
/*-----------------------------------------------------------*/

/**
 * @brief Check the network timers (ARP/DHCP/DNS/TCP) and if they are
 *        expired, send an event to the IP-Task.
 */
static void prvCheckNetworkTimers( void )
{
    NetworkInterface_t * pxInterface;

    /* Is it time for ARP processing? */
    if( prvIPTimerCheck( &xARPTimer ) != pdFALSE )
    {
        ( void ) xSendEventToIPTask( eARPTimerEvent );
    }

    #if ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 )
        {
            /* Is it time for DHCP processing? */
            NetworkEndPoint_t * pxEndPoint = pxNetworkEndPoints;

            while( pxEndPoint != NULL )
            {
                if( prvIPTimerCheck( &( pxEndPoint->xDHCP_RATimer ) ) != pdFALSE )
                {
                    #if ( ipconfigUSE_DHCP == 1 )
                        if( END_POINT_USES_DHCP( pxEndPoint ) )
                        {
                            ( void ) xSendDHCPEvent( pxEndPoint );
                        }
                    #endif /* ( ipconfigUSE_DHCP == 1 ) */

                    #if ( ipconfigUSE_RA != 0 )
                        if( END_POINT_USES_RA( pxEndPoint ) )
                        {
                            vRAProcess( pdFALSE, pxEndPoint );
                        }
                    #endif /* ( ipconfigUSE_RA != 0 ) */
                }

                pxEndPoint = pxEndPoint->pxNext;
            }
        }
    #endif /* ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA != 0 ) */

    #if ( ipconfigDNS_USE_CALLBACKS != 0 )
        {
            /* Is it time for DNS processing? */
            if( prvIPTimerCheck( &xDNSTimer ) != pdFALSE )
            {
                vDNSCheckCallBack( NULL );
            }
        }
    #endif /* ipconfigDNS_USE_CALLBACKS */

    #if ( ipconfigUSE_TCP == 1 )
        {
            BaseType_t xWillSleep;
            TickType_t xNextTime;
            BaseType_t xCheckTCPSockets;

            /* If the IP task has messages waiting to be processed then
             * it will not sleep in any case. */
            if( uxQueueMessagesWaiting( xNetworkEventQueue ) == 0U )
            {
                xWillSleep = pdTRUE;
            }
            else
            {
                xWillSleep = pdFALSE;
            }

            /* Sockets need to be checked if the TCP timer has expired. */
            xCheckTCPSockets = prvIPTimerCheck( &xTCPTimer );

            /* Sockets will also be checked if there are TCP messages but the
            * message queue is empty (indicated by xWillSleep being true). */
            if( ( xProcessedTCPMessage != pdFALSE ) && ( xWillSleep != pdFALSE ) )
            {
                xCheckTCPSockets = pdTRUE;
            }

            if( xCheckTCPSockets != pdFALSE )
            {
                /* Attend to the sockets, returning the period after which the
                 * check must be repeated. */
                xNextTime = xTCPTimerCheck( xWillSleep );
                prvIPTimerStart( &xTCPTimer, xNextTime );
                xProcessedTCPMessage = 0;
            }
        }
    #endif /* ipconfigUSE_TCP == 1 */

    /* Is it time to trigger the repeated NetworkDown events? */
    if( xAllNetworksUp == pdFALSE )
    {
        if( prvIPTimerCheck( &( xNetworkTimer ) ) != pdFALSE )
        {
            BaseType_t xUp = pdTRUE;

            for( pxInterface = pxNetworkInterfaces; pxInterface != NULL; pxInterface = pxInterface->pxNext )
            {
                if( pxInterface->bits.bInterfaceUp == pdFALSE_UNSIGNED )
                {
                    xUp = pdFALSE;
                    FreeRTOS_NetworkDown( pxInterface );
                }
            }

            xAllNetworksUp = xUp;
        }
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Start an IP timer. The IP-task has its own implementation of a timer
 *        called 'IPTimer_t', which is based on the FreeRTOS 'TimeOut_t'.
 *
 * @param[in] pxTimer: Pointer to the IP timer. When zero, the timer is marked
 *                     as expired.
 * @param[in] xTime: Time to be loaded into the IP timer.
 */
static void prvIPTimerStart( IPTimer_t * pxTimer,
                             TickType_t xTime )
{
    vTaskSetTimeOutState( &pxTimer->xTimeOut );
    pxTimer->ulRemainingTime = xTime;

    if( xTime == ( TickType_t ) 0 )
    {
        pxTimer->bExpired = pdTRUE_UNSIGNED;
    }
    else
    {
        pxTimer->bExpired = pdFALSE_UNSIGNED;
    }

    pxTimer->bActive = pdTRUE_UNSIGNED;
}
/*-----------------------------------------------------------*/

/**
 * @brief Sets the reload time of an IP timer and restarts it.
 *
 * @param[in] pxTimer: Pointer to the IP timer.
 * @param[in] xTime: Time to be reloaded into the IP timer.
 */
static void prvIPTimerReload( IPTimer_t * pxTimer,
                              TickType_t xTime )
{
    pxTimer->ulReloadTime = xTime;
    prvIPTimerStart( pxTimer, xTime );
}
/*-----------------------------------------------------------*/

/**
 * @brief Check the IP timer to see whether an IP event should be processed or not.
 *
 * @param[in] pxTimer: Pointer to the IP timer.
 *
 * @return If the timer is expired then pdTRUE is returned. Else pdFALSE.
 */
static BaseType_t prvIPTimerCheck( IPTimer_t * pxTimer )
{
    BaseType_t xReturn;

    if( pxTimer->bActive == pdFALSE_UNSIGNED )
    {
        /* The timer is not enabled. */
        xReturn = pdFALSE;
    }
    else
    {
        /* The timer might have set the bExpired flag already, if not, check the
         * value of xTimeOut against ulRemainingTime. */
        if( pxTimer->bExpired == pdFALSE_UNSIGNED )
        {
            if( xTaskCheckForTimeOut( &( pxTimer->xTimeOut ), &( pxTimer->ulRemainingTime ) ) != pdFALSE )
            {
                pxTimer->bExpired = pdTRUE_UNSIGNED;
            }
        }

        if( pxTimer->bExpired != pdFALSE_UNSIGNED )
        {
            prvIPTimerStart( pxTimer, pxTimer->ulReloadTime );
            xReturn = pdTRUE;
        }
        else
        {
            xReturn = pdFALSE;
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Send a network down event to the IP-task. If it fails to post a message,
 *         the failure will be noted in the variable 'xNetworkDownEventPending'
 *         and later on a 'network-down' event, it will be executed.
 *
 * @param[in] pxNetworkInterface: The interface that goes down.
 */
void FreeRTOS_NetworkDown( struct xNetworkInterface * pxNetworkInterface )
{
    IPStackEvent_t xNetworkDownEvent;
    const TickType_t xDontBlock = 0;

    pxNetworkInterface->bits.bInterfaceUp = pdFALSE_UNSIGNED;
    xNetworkDownEvent.eEventType = eNetworkDownEvent;
    xNetworkDownEvent.pvData = pxNetworkInterface;

    /* Simply send the network task the appropriate event. */
    if( xSendEventStructToIPTask( &xNetworkDownEvent, xDontBlock ) != pdPASS )
    {
        /* Could not send the message, so it is still pending. */
        pxNetworkInterface->bits.bCallDownEvent = pdTRUE;
        xNetworkDownEventPending = pdTRUE;
    }
    else
    {
        /* Message was sent so it is not pending. */
        pxNetworkInterface->bits.bCallDownEvent = pdFALSE;
    }

    iptraceNETWORK_DOWN();
}
/*-----------------------------------------------------------*/

/**
 * @brief Utility function. Process Network Down event from ISR.
 *        This function is supposed to be called form an ISR. It is recommended
 *        use 'FreeRTOS_NetworkDown()', when calling from a normal task.
 *
 * @param[in] pxNetworkInterface: The interface that goes down.
 *
 * @return If the event was processed successfully, then return pdTRUE.
 *         Else pdFALSE.
 */
BaseType_t FreeRTOS_NetworkDownFromISR( struct xNetworkInterface * pxNetworkInterface )
{
    static IPStackEvent_t xNetworkDownEvent;
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    xNetworkDownEvent.eEventType = eNetworkDownEvent;
    xNetworkDownEvent.pvData = pxNetworkInterface;

    /* Simply send the network task the appropriate event. */
    if( xQueueSendToBackFromISR( xNetworkEventQueue, &xNetworkDownEvent, &xHigherPriorityTaskWoken ) != pdPASS )
    {
        /* Could not send the message, so it is still pending. */
        pxNetworkInterface->bits.bCallDownEvent = pdTRUE;
        xNetworkDownEventPending = pdTRUE;
    }
    else
    {
        /* Message was sent so it is not pending. */
        pxNetworkInterface->bits.bCallDownEvent = pdFALSE;
    }

    iptraceNETWORK_DOWN();

    return xHigherPriorityTaskWoken;
}
/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
#if ( ipconfigUSE_IPv6 == 1 )

/**
 * @brief Obtain a buffer big enough for a UDP payload of given size.
 *
 * @param[in] uxRequestedSizeBytes: The size of the UDP payload.
 * @param[in] uxBlockTimeTicks: Maximum amount of time for which this call
 *            can block. This value is capped internally.
 * @param[in] ucIPType: Either ipTYPE_IPv4 (0x40) or ipTYPE_IPv6 (0x60)
 *
 * @return If a buffer was created then the pointer to that buffer is returned,
 *         else a NULL pointer is returned.
 */
    void * FreeRTOS_GetUDPPayloadBuffer( size_t uxRequestedSizeBytes,
                                         TickType_t uxBlockTimeTicks,
                                         uint8_t ucIPType )
#else /* #if ( ipconfigUSE_IPv6 == 1 ) */

/**
 * @brief Obtain a buffer big enough for a UDP payload of given size.
 *
 * @param[in] uxRequestedSizeBytes: The size of the UDP payload.
 * @param[in] uxBlockTimeTicks: Maximum amount of time for which this call
 *            can block. This value is capped internally.
 *
 * @return If a buffer was created then the pointer to that buffer is returned,
 *         else a NULL pointer is returned.
 */
    void * FreeRTOS_GetUDPPayloadBuffer( size_t uxRequestedSizeBytes,
                                         TickType_t uxBlockTimeTicks )
#endif /* #if ( ipconfigUSE_IPv6 == 1 ) */
/* *INDENT-ON* */
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    void * pvReturn;
    TickType_t uxBlockTime = uxBlockTimeTicks;

    /* Cap the block time.  The reason for this is explained where
     * ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS is defined (assuming an official
     * FreeRTOSIPConfig.h header file is being used). */
    if( uxBlockTime > ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS )
    {
        uxBlockTime = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS;
    }

    /* Obtain a network buffer with the required amount of storage. */
    pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, uxBlockTime );

    if( pxNetworkBuffer != NULL )
    {
        #if ( ipconfigUSE_IPv6 != 0 )
            {
                uint8_t * pucIPType;
                size_t uxIPHeaderLength;

                /* Calculate the distance between the beginning of
                 * UDP payload until the hidden byte that reflects
                 * the IP-type: either ipTYPE_IPv4 or ipTYPE_IPv6.
                 */
                size_t uxIndex = ipUDP_PAYLOAD_IP_TYPE_OFFSET;
                BaseType_t xPayloadIPTypeOffset = ( BaseType_t ) uxIndex;

                if( ucIPType == ipTYPE_IPv6 )
                {
                    uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
                }
                else
                {
                    uxIPHeaderLength = ipSIZE_OF_IPv4_HEADER;
                }

                /* Skip 3 headers. */
                pvReturn = ipPOINTER_CAST( void *,
                                           &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderLength + ipSIZE_OF_UDP_HEADER ] ) );

                /* Later a pointer to a UDP payload is used to retrieve a NetworkBuffer.
                 * Store the packet type at 48 bytes before the start of the UDP payload. */
                pucIPType = ipPOINTER_CAST( uint8_t *, pvReturn );
                pucIPType = &( pucIPType[ -xPayloadIPTypeOffset ] );

                /* For a IPv4 packet, pucIPType points to 6 bytes before the
                 * pucEthernetBuffer, for a IPv6 packet, pucIPType will point to the
                 * first byte of the IP-header: 'ucVersionTrafficClass'. */
                *pucIPType = ucIPType;
            }
        #else /* if ( ipconfigUSE_IPv6 != 0 ) */
            {
                /* Set the actual packet size in case a bigger buffer was returned. */
                pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t ) + uxRequestedSizeBytes;
                /* Skip 3 headers. */
                pvReturn = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_t ) ] );
            }
        #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
    }
    else
    {
        pvReturn = NULL;
    }

    return ( void * ) pvReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Duplicate the given network buffer descriptor with a modified length.
 *
 * @param[in] pxNetworkBuffer: The network buffer to be duplicated.
 * @param[in] uxNewLength: The length for the new buffer.
 *
 * @return If properly duplicated, then the duplicate network buffer or else, NULL.
 */
NetworkBufferDescriptor_t * pxDuplicateNetworkBufferWithDescriptor( const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                    size_t uxNewLength )
{
    NetworkBufferDescriptor_t * pxNewBuffer;

    /* This function is only used when 'ipconfigZERO_COPY_TX_DRIVER' is set to 1.
     * The transmit routine wants to have ownership of the network buffer
     * descriptor, because it will pass the buffer straight to DMA. */
    pxNewBuffer = pxGetNetworkBufferWithDescriptor( uxNewLength, ( TickType_t ) 0 );

    if( pxNewBuffer != NULL )
    {
        /* Set the actual packet size in case a bigger buffer than requested
         * was returned. */
        pxNewBuffer->xDataLength = uxNewLength;

        /* Copy the original packet information. */
        pxNewBuffer->ulIPAddress = pxNetworkBuffer->ulIPAddress;
        pxNewBuffer->usPort = pxNetworkBuffer->usPort;
        pxNewBuffer->usBoundPort = pxNetworkBuffer->usBoundPort;
        pxNewBuffer->pxInterface = pxNetworkBuffer->pxInterface;
        pxNewBuffer->pxEndPoint = pxNetworkBuffer->pxEndPoint;
        ( void ) memcpy( pxNewBuffer->pucEthernetBuffer, pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength );
        #if ( ipconfigUSE_IPv6 != 0 )
            {
                ( void ) memcpy( pxNewBuffer->xIPv6Address.ucBytes, pxNetworkBuffer->xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
            }
        #endif /* ipconfigUSE_IPv6 != 0 */
    }

    return pxNewBuffer;
}
/*-----------------------------------------------------------*/

/**
 * @brief uintptr_t is an unsigned integer type that is capable of storing a data pointer.
 *        Therefore it is safe to convert from a void pointer to a uintptr_t, using a union.
 */
union uIntPtr
{
    uintptr_t uxPtr;    /**< THe numeric value. */
    const void * pvPtr; /**< THe void pointer. */
};

/**
 * @brief Helper function: cast a pointer to a numeric value 'uintptr_t',
 *        using a union as defined here above.
 * @param[in] pvPointer A void pointer to be converted.
 * @return The value of the void pointer as an unsigned number.
 */
static uintptr_t void_ptr_to_uintptr( const void * pvPointer )
{
    /* The type 'uintptr_t' has the same size as a pointer.
     * Therefore, it is safe to use a union to convert it. */
    union uIntPtr intPtr;

    intPtr.pvPtr = pvPointer;
    return intPtr.uxPtr;
}

/**
 * @brief Get the network buffer descriptor from the packet buffer.
 *
 * @param[in] pvBuffer: The pointer to packet buffer.
 * @param[in] uxOffset: Additional offset (such as the packet length of UDP packet etc.).
 *
 * @return The network buffer descriptor if the alignment is correct. Else a NULL is returned.
 */
static NetworkBufferDescriptor_t * prvPacketBuffer_to_NetworkBuffer( const void * pvBuffer,
                                                                     size_t uxOffset )
{
    uintptr_t uxBuffer;
    NetworkBufferDescriptor_t * pxResult;

    if( pvBuffer == NULL )
    {
        pxResult = NULL;
    }
    else
    {
        /* Obtain the network buffer from the zero copy pointer. */
        /* The size of uintptr_t uxBuffer is equal to the size of a void*. */
        /* coverity[misra_c_2012_rule_11_6_violation] */
        /* uxBuffer = pvBuffer; */
        uxBuffer = void_ptr_to_uintptr( pvBuffer );

        /* The input here is a pointer to a packet buffer plus some offset.  Subtract
         * this offset, and also the size of the header in the network buffer, usually
         * 8 + 2 bytes. */
        uxBuffer -= ( uintptr_t ) ( uxOffset + ipBUFFER_PADDING );

        /* Here a pointer was placed to the network descriptor.  As a
         * pointer is dereferenced, make sure it is well aligned. */
        if( ( uxBuffer & ( ( ( uintptr_t ) sizeof( uxBuffer ) ) - 1U ) ) == ( uintptr_t ) 0U )
        {
            /* The following statement may trigger a:
             * warning: cast increases required alignment of target type [-Wcast-align].
             * It has been confirmed though that the alignment is suitable. */
            pxResult = *( ( NetworkBufferDescriptor_t ** ) uxBuffer );
        }
        else
        {
            pxResult = NULL;
        }
    }

    return pxResult;
}
/*-----------------------------------------------------------*/

#if ( ipconfigZERO_COPY_TX_DRIVER != 0 ) || ( ipconfigZERO_COPY_RX_DRIVER != 0 )

/**
 * @brief Get the network buffer from the packet buffer.
 *
 * @param[in] pvBuffer: Pointer to the packet buffer.
 *
 * @return The network buffer if the alignment is correct. Else a NULL is returned.
 */
    NetworkBufferDescriptor_t * pxPacketBuffer_to_NetworkBuffer( const void * pvBuffer )
    {
        return prvPacketBuffer_to_NetworkBuffer( pvBuffer, 0U );
    }

#endif /* ( ipconfigZERO_COPY_TX_DRIVER != 0 ) || ( ipconfigZERO_COPY_RX_DRIVER != 0 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Get the network buffer from the UDP Payload buffer.
 *
 * @param[in] pvBuffer: Pointer to the UDP payload buffer.
 *
 * @return The network buffer if the alignment is correct. Else a NULL is returned.
 */
NetworkBufferDescriptor_t * pxUDPPayloadBuffer_to_NetworkBuffer( const void * pvBuffer )
{
    NetworkBufferDescriptor_t * pxResult;

    if( pvBuffer == NULL )
    {
        pxResult = NULL;
    }
    else
    {
        size_t uxOffset;

        /* The input here is a pointer to a payload buffer.  Subtract
         * the total size of a UDP/IP packet plus the size of the header in
         * the network buffer, usually 8 + 2 bytes. */
        #if ( ipconfigUSE_IPv6 != 0 )
            {
                uintptr_t uxTypeOffset;
                const uint8_t * pucIPType;
                uint8_t ucIPType;

                /* When IPv6 is supported, find out the type of the packet.
                 * It is stored 48 bytes before the payload buffer as 0x40 or 0x60. */
                uxTypeOffset = void_ptr_to_uintptr( pvBuffer );
                uxTypeOffset -= ipUDP_PAYLOAD_IP_TYPE_OFFSET;
                pucIPType = ( const uint8_t * ) uxTypeOffset;

                /* For an IPv4 packet, pucIPType points to 6 bytes before the pucEthernetBuffer,
                 * for a IPv6 packet, pucIPType will point to the first byte of the IP-header: 'ucVersionTrafficClass'. */
                ucIPType = pucIPType[ 0 ] & 0xf0U;

                /* To help the translation from a UDP payload pointer to a networkBuffer,
                 * a byte was stored at a certain negative offset (-48 bytes).
                 * It must have a value of either 0x4x or 0x6x. */
                configASSERT( ( ucIPType == ipTYPE_IPv4 ) || ( ucIPType == ipTYPE_IPv6 ) );

                if( ucIPType == ipTYPE_IPv6 )
                {
                    uxOffset = sizeof( UDPPacket_IPv6_t );
                }
                else /* ucIPType == ipTYPE_IPv4 */
                {
                    uxOffset = sizeof( UDPPacket_t );
                }
            }
        #else /* if ( ipconfigUSE_IPv6 != 0 ) */
            {
                uxOffset = sizeof( UDPPacket_t );
            }
        #endif /* ipconfigUSE_IPv6 */

        pxResult = prvPacketBuffer_to_NetworkBuffer( pvBuffer, uxOffset );
    }

    return pxResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Given a message buffer, find the first byte of the payload of a UDP packet.
 *        It works for both IPv4 and IPv6.  Note that the frame-type must be valid.
 *
 * @param[in] pxNetworkBuffer: The network buffer.
 *
 * @return A byte pointer pointing to the first byte of the UDP payload.
 */
uint8_t * pcNetworkBuffer_to_UDPPayloadBuffer( NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    uint8_t * pcResult;
    size_t uxOffset = ipUDP_PAYLOAD_OFFSET_IPv4;

    #if ( ipconfigUSE_IPv6 != 0 )
        {
            EthernetHeader_t * pxHeader = ipCAST_PTR_TO_TYPE_PTR( EthernetHeader_t, pxNetworkBuffer->pucEthernetBuffer );

            if( pxHeader->usFrameType == ( uint16_t ) ipIPv6_FRAME_TYPE )
            {
                uxOffset = ipUDP_PAYLOAD_OFFSET_IPv6;
            }
        }
    #endif /* ( ipconfigUSE_IPv6 != 0 ) */
    pcResult = &( pxNetworkBuffer->pucEthernetBuffer[ uxOffset ] );

    return pcResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Release the UDP payload buffer.
 *
 * @param[in] pvBuffer: Pointer to the UDP buffer that is to be released.
 */
void FreeRTOS_ReleaseUDPPayloadBuffer( void const * pvBuffer )
{
    NetworkBufferDescriptor_t * pxBuffer;

    pxBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pvBuffer );
    configASSERT( pxBuffer != NULL );
    vReleaseNetworkBufferAndDescriptor( pxBuffer );
}
/*-----------------------------------------------------------*/

/**
 * @brief Initialise the FreeRTOS-Plus-TCP network stack and initialise the IP-task.
 *        Before calling this function, at least 1 interface and 1 end-point must
 *        have been set-up.
 */
BaseType_t FreeRTOS_IPStart( void )
{
    BaseType_t xReturn = pdFALSE;
    NetworkEndPoint_t * pxFirstEndPoint;

    /* There must be at least one interface and one end-point. */
    configASSERT( FreeRTOS_FirstNetworkInterface() != NULL );

    pxFirstEndPoint = FreeRTOS_FirstEndPoint( NULL );

    #if ( ipconfigUSE_IPv6 != 0 )
        for( ;
             pxFirstEndPoint != NULL;
             pxFirstEndPoint = FreeRTOS_NextEndPoint( NULL, pxFirstEndPoint ) )
        {
            if( ENDPOINT_IS_IPv4( pxFirstEndPoint ) )
            {
                break;
            }
        }
    #endif /* ( ipconfigUSE_IPv6 != 0 ) */

    /* At least one IPv4 end-point must be defined. */
    configASSERT( pxFirstEndPoint != NULL );

    /* This function should only be called once. */
    configASSERT( xIPIsNetworkTaskReady() == pdFALSE );
    configASSERT( xNetworkEventQueue == NULL );
    configASSERT( xIPTaskHandle == NULL );

    #ifndef _lint
        {
            /* Check if MTU is big enough. */
            configASSERT( ( ( size_t ) ipconfigNETWORK_MTU ) >= ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER + ipconfigTCP_MSS ) );
            /* Check structure packing is correct. */
            configASSERT( sizeof( EthernetHeader_t ) == ipEXPECTED_EthernetHeader_t_SIZE );
            configASSERT( sizeof( ARPHeader_t ) == ipEXPECTED_ARPHeader_t_SIZE );
            configASSERT( sizeof( IPHeader_t ) == ipEXPECTED_IPHeader_t_SIZE );
            configASSERT( sizeof( ICMPHeader_t ) == ipEXPECTED_ICMPHeader_t_SIZE );
            configASSERT( sizeof( UDPHeader_t ) == ipEXPECTED_UDPHeader_t_SIZE );
            #if ipconfigUSE_TCP == 1
                {
                    configASSERT( sizeof( TCPHeader_t ) == ( ipEXPECTED_TCPHeader_t_SIZE + ipSIZE_TCP_OPTIONS ) );
                }
            #endif
            configASSERT( sizeof( ICMPHeader_t ) == ipEXPECTED_ICMPHeader_t_SIZE );
        }
    #endif /* ifndef _lint */
    /* Attempt to create the queue used to communicate with the IP task. */
    xNetworkEventQueue = xQueueCreate( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ) );
    configASSERT( xNetworkEventQueue != NULL );

    if( xNetworkEventQueue != NULL )
    {
        #if ( configQUEUE_REGISTRY_SIZE > 0 )
            {
                /* A queue registry is normally used to assist a kernel aware
                 * debugger.  If one is in use then it will be helpful for the debugger
                 * to show information about the network event queue. */
                vQueueAddToRegistry( xNetworkEventQueue, "NetEvnt" );
            }
        #endif /* configQUEUE_REGISTRY_SIZE */

        if( xNetworkBuffersInitialise() == pdPASS )
        {
            /* Prepare the sockets interface. */
            vNetworkSocketsInit();

            /* Create the task that processes Ethernet and stack events. */
            xReturn = xTaskCreate( prvIPTask,
                                   "IP-task",
                                   ipconfigIP_TASK_STACK_SIZE_WORDS,
                                   NULL,
                                   ipconfigIP_TASK_PRIORITY,
                                   &( xIPTaskHandle ) );
        }
        else
        {
            FreeRTOS_debug_printf( ( "FreeRTOS_IPStart: xNetworkBuffersInitialise() failed\n" ) );

            /* Clean up. */
            vQueueDelete( xNetworkEventQueue );
            xNetworkEventQueue = NULL;
        }
    }
    else
    {
        FreeRTOS_debug_printf( ( "FreeRTOS_IPStart: Network event queue could not be created\n" ) );
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigCOMPATIBLE_WITH_SINGLE != 0 )

/* Provide backward-compatibility with the earlier FreeRTOS+TCP which only had
 * single network interface. */
    BaseType_t FreeRTOS_IPInit( const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                                const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ],
                                const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                                const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                                const uint8_t ucMACAddressP[ ipMAC_ADDRESS_LENGTH_BYTES ] )
    {
        static NetworkInterface_t xInterfaces[ 1 ];
        static NetworkEndPoint_t xEndPoints[ 1 ];

        /* IF the following function should be declared in the NetworkInterface.c
         * linked in the project. */
        pxFillInterfaceDescriptor( 0, &( xInterfaces[ 0 ] ) );
        FreeRTOS_FillEndPoint( &( xInterfaces[ 0 ] ), &( xEndPoints[ 0 ] ), ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddressP );
        #if ( ipconfigUSE_DHCP != 0 )
            {
                xEndPoints[ 0 ].bits.bWantDHCP = pdTRUE;
            }
        #endif /* ipconfigUSE_DHCP */
        FreeRTOS_IPStart();
        return 1;
    }
#endif /* ( ipconfigCOMPATIBLE_WITH_SINGLE != 0 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Get the current address configuration. Only non-NULL pointers will
 *        be filled in. pxEndPoint must be non-NULL.
 *
 * @param[out] pulIPAddress: The current IP-address assigned.
 * @param[out] pulNetMask: The netmask used for current subnet.
 * @param[out] pulGatewayAddress: The gateway address.
 * @param[out] pulDNSServerAddress: The DNS server address.
 * @param[in] pxEndPoint: The end-point which is being questioned.
 */
void FreeRTOS_GetEndPointConfiguration( uint32_t * pulIPAddress,
                                        uint32_t * pulNetMask,
                                        uint32_t * pulGatewayAddress,
                                        uint32_t * pulDNSServerAddress,
                                        struct xNetworkEndPoint * pxEndPoint )
{
    #if ( ipconfigUSE_IPv6 != 0 )
        if( ENDPOINT_IS_IPv4( pxEndPoint ) )
    #endif
    {
        /* Return the address configuration to the caller. */

        if( pulIPAddress != NULL )
        {
            *pulIPAddress = pxEndPoint->ipv4_settings.ulIPAddress;
        }

        if( pulNetMask != NULL )
        {
            *pulNetMask = pxEndPoint->ipv4_settings.ulNetMask;
        }

        if( pulGatewayAddress != NULL )
        {
            *pulGatewayAddress = pxEndPoint->ipv4_settings.ulGatewayAddress;
        }

        if( pulDNSServerAddress != NULL )
        {
            *pulDNSServerAddress = pxEndPoint->ipv4_settings.ulDNSServerAddresses[ 0 ]; /*_RB_ Only returning the address of the first DNS server. */
        }
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Set the current network address configuration. Only non-NULL pointers will
 *        be used. pxEndPoint must pointer to a valid end-point.
 *
 * @param[in] pulIPAddress: The current IP-address assigned.
 * @param[in] pulNetMask: The netmask used for current subnet.
 * @param[in] pulGatewayAddress: The gateway address.
 * @param[in] pulDNSServerAddress: The DNS server address.
 * @param[in] pxEndPoint: The end-point which is being questioned.
 */
void FreeRTOS_SetEndPointConfiguration( const uint32_t * pulIPAddress,
                                        const uint32_t * pulNetMask,
                                        const uint32_t * pulGatewayAddress,
                                        const uint32_t * pulDNSServerAddress,
                                        struct xNetworkEndPoint * pxEndPoint )
{
    /* Update the address configuration. */

    #if ( ipconfigUSE_IPv6 != 0 )
        if( ENDPOINT_IS_IPv4( pxEndPoint ) )
    #endif
    {
        if( pulIPAddress != NULL )
        {
            pxEndPoint->ipv4_settings.ulIPAddress = *pulIPAddress;
        }

        if( pulNetMask != NULL )
        {
            pxEndPoint->ipv4_settings.ulNetMask = *pulNetMask;
        }

        if( pulGatewayAddress != NULL )
        {
            pxEndPoint->ipv4_settings.ulGatewayAddress = *pulGatewayAddress;
        }

        if( pulDNSServerAddress != NULL )
        {
            pxEndPoint->ipv4_settings.ulDNSServerAddresses[ 0 ] = *pulDNSServerAddress;
        }
    }
}
/*-----------------------------------------------------------*/

#if ( ipconfigCOMPATIBLE_WITH_SINGLE == 1 )
    void FreeRTOS_GetAddressConfiguration( uint32_t * pulIPAddress,
                                           uint32_t * pulNetMask,
                                           uint32_t * pulGatewayAddress,
                                           uint32_t * pulDNSServerAddress )
    {
        struct xNetworkEndPoint * pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

        FreeRTOS_GetEndPointConfiguration( pulIPAddress, pulNetMask, pulGatewayAddress, pulDNSServerAddress, pxEndPoint );
    }
#endif /* ( ipconfigCOMPATIBLE_WITH_SINGLE ) */

#if ( ipconfigCOMPATIBLE_WITH_SINGLE == 1 )
    void FreeRTOS_SetAddressConfiguration( const uint32_t * pulIPAddress,
                                           const uint32_t * pulNetMask,
                                           const uint32_t * pulGatewayAddress,
                                           const uint32_t * pulDNSServerAddress )
    {
        struct xNetworkEndPoint * pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

        FreeRTOS_SetEndPointConfiguration( pulIPAddress, pulNetMask, pulGatewayAddress, pulDNSServerAddress, pxEndPoint );
    }
#endif /* ( ipconfigCOMPATIBLE_WITH_SINGLE == 1 ) */

#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

/**
 * @brief Send a ping request to the given IP address. After receiving a reply,
 *        IP-task will call a user-supplied function 'vApplicationPingReplyHook()'.
 *
 * @param[in] ulIPAddress: The IP address to which the ping is to be sent.
 * @param[in] uxNumberOfBytesToSend: Number of bytes in the ping request.
 * @param[in] uxBlockTimeTicks: Maximum number of ticks to wait.
 *
 * @return If successfully sent to IP task for processing then the sequence
 *         number of the ping packet or else, pdFAIL.
 */
    BaseType_t FreeRTOS_SendPingRequest( uint32_t ulIPAddress,
                                         size_t uxNumberOfBytesToSend,
                                         TickType_t uxBlockTimeTicks )
    {
        NetworkBufferDescriptor_t * pxNetworkBuffer;
        ICMPHeader_t * pxICMPHeader;
        EthernetHeader_t * pxEthernetHeader;
        BaseType_t xReturn = pdFAIL;
        static uint16_t usSequenceNumber = 0;
        uint8_t * pucChar;
        size_t uxTotalLength;
        IPStackEvent_t xStackTxEvent = { eStackTxEvent, NULL };

        uxTotalLength = uxNumberOfBytesToSend + sizeof( ICMPPacket_t );
        BaseType_t xEnoughSpace;

/*      xARPWaitResolution( ulIPAddress, uxBlockTimeTicks ); */

        if( uxNumberOfBytesToSend < ( ipconfigNETWORK_MTU - ( sizeof( IPHeader_t ) + sizeof( ICMPHeader_t ) ) ) )
        {
            xEnoughSpace = pdTRUE;
        }
        else
        {
            xEnoughSpace = pdFALSE;
        }

        if( ( uxGetNumberOfFreeNetworkBuffers() >= 4U ) && ( uxNumberOfBytesToSend >= 1U ) && ( xEnoughSpace != pdFALSE ) )
        {
            pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxTotalLength, uxBlockTimeTicks );

            if( pxNetworkBuffer != NULL )
            {
                pxEthernetHeader = ipCAST_PTR_TO_TYPE_PTR( EthernetHeader_t, pxNetworkBuffer->pucEthernetBuffer );
                pxEthernetHeader->usFrameType = ipIPv4_FRAME_TYPE;

                pxICMPHeader = ipCAST_PTR_TO_TYPE_PTR( ICMPHeader_t, &( pxNetworkBuffer->pucEthernetBuffer[ ipIP_PAYLOAD_OFFSET ] ) );
                usSequenceNumber++;

                /* Fill in the basic header information. */
                pxICMPHeader->ucTypeOfMessage = ipICMP_ECHO_REQUEST;
                pxICMPHeader->ucTypeOfService = 0;
                pxICMPHeader->usIdentifier = usSequenceNumber;
                pxICMPHeader->usSequenceNumber = usSequenceNumber;

                /* Find the start of the data. */
                pucChar = ( uint8_t * ) pxICMPHeader;
                pucChar = &( pucChar[ sizeof( ICMPHeader_t ) ] );

                /* Just memset the data to a fixed value. */
                ( void ) memset( pucChar, ( int ) ipECHO_DATA_FILL_BYTE, uxNumberOfBytesToSend );

                /* The message is complete, IP and checksum's are handled by
                 * vProcessGeneratedUDPPacket */
                pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] = FREERTOS_SO_UDPCKSUM_OUT;
                pxNetworkBuffer->ulIPAddress = ulIPAddress;
                pxNetworkBuffer->usPort = ipPACKET_CONTAINS_ICMP_DATA;
                /* xDataLength is the size of the total packet, including the Ethernet header. */
                pxNetworkBuffer->xDataLength = uxTotalLength;

                /* Send to the stack. */
                xStackTxEvent.pvData = pxNetworkBuffer;

                if( xSendEventStructToIPTask( &( xStackTxEvent ), uxBlockTimeTicks ) != pdPASS )
                {
                    vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
                    iptraceSTACK_TX_EVENT_LOST( ipSTACK_TX_EVENT );
                }
                else
                {
                    xReturn = ( BaseType_t ) usSequenceNumber;
                }
            }
        }
        else
        {
            /* The requested number of bytes will not fit in the available space
             * in the network buffer. */
        }

        return xReturn;
    }

#endif /* ipconfigSUPPORT_OUTGOING_PINGS == 1 */
/*-----------------------------------------------------------*/

/**
 * @brief Send an event to the IP task. It calls 'xSendEventStructToIPTask' internally.
 *
 * @param[in] eEvent: The event to be sent.
 *
 * @return pdPASS if the event was sent (or the desired effect was achieved). Else, pdFAIL.
 */
BaseType_t xSendEventToIPTask( eIPEvent_t eEvent )
{
    IPStackEvent_t xEventMessage;
    const TickType_t xDontBlock = ( TickType_t ) 0;

    xEventMessage.eEventType = eEvent;
    xEventMessage.pvData = ( void * ) NULL;

    return xSendEventStructToIPTask( &xEventMessage, xDontBlock );
}
/*-----------------------------------------------------------*/

/**
 * @brief Send an event (in form of struct) to the IP task to be processed.
 *
 * @param[in] pxEvent: The event to be sent.
 * @param[in] uxTimeout: Timeout for waiting in case the queue is full. 0 for non-blocking calls.
 *
 * @return pdPASS if the event was sent (or the desired effect was achieved). Else, pdFAIL.
 */
BaseType_t xSendEventStructToIPTask( const IPStackEvent_t * pxEvent,
                                     TickType_t uxTimeout )
{
    BaseType_t xReturn, xSendMessage;
    TickType_t uxUseTimeout = uxTimeout;

    if( ( xIPIsNetworkTaskReady() == pdFALSE ) && ( pxEvent->eEventType != eNetworkDownEvent ) )
    {
        /* Only allow eNetworkDownEvent events if the IP task is not ready
         * yet.  Not going to attempt to send the message so the send failed. */
        xReturn = pdFAIL;
    }
    else
    {
        xSendMessage = pdTRUE;

        #if ( ipconfigUSE_TCP == 1 )
            {
                if( pxEvent->eEventType == eTCPTimerEvent )
                {
                    /* TCP timer events are sent to wake the timer task when
                     * xTCPTimer has expired, but there is no point sending them if the
                     * IP task is already awake processing other message. */
                    xTCPTimer.bExpired = pdTRUE;

                    if( uxQueueMessagesWaiting( xNetworkEventQueue ) != 0U )
                    {
                        /* Not actually going to send the message but this is not a
                         * failure as the message didn't need to be sent. */
                        xSendMessage = pdFALSE;
                    }
                }
            }
        #endif /* ipconfigUSE_TCP */

        if( xSendMessage != pdFALSE )
        {
            /* The IP task cannot block itself while waiting for itself to
             * respond. */
            if( ( xIsCallingFromIPTask() == pdTRUE ) && ( uxUseTimeout > ( TickType_t ) 0U ) )
            {
                uxUseTimeout = ( TickType_t ) 0;
            }

            xReturn = xQueueSendToBack( xNetworkEventQueue, pxEvent, uxUseTimeout );

            if( xReturn == pdFAIL )
            {
                /* A message should have been sent to the IP task, but wasn't. */
                FreeRTOS_debug_printf( ( "xSendEventStructToIPTask: CAN NOT ADD %d\n", pxEvent->eEventType ) );
                iptraceSTACK_TX_EVENT_LOST( pxEvent->eEventType );
            }
        }
        else
        {
            /* It was not necessary to send the message to process the event so
             * even though the message was not sent the call was successful. */
            xReturn = pdPASS;
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 )

/**
 * @brief Create a DHCP event.
 *
 * @return pdPASS or pdFAIL, depending on whether xSendEventStructToIPTask()
 *         succeeded.
 * @param pxEndPoint: The end-point that needs DHCP.
 */
    BaseType_t xSendDHCPEvent( struct xNetworkEndPoint * pxEndPoint )
    {
        IPStackEvent_t xEventMessage;
        const TickType_t uxDontBlock = 0U;

        #if ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 )
            eDHCPState_t uxOption = eGetDHCPState( pxEndPoint );
        #endif

        xEventMessage.eEventType = eDHCP_RA_Event;
        xEventMessage.pvData = ( void * ) pxEndPoint;
        #if ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 )
            {
                pxEndPoint->xDHCPData.eExpectedState = uxOption;
            }
        #endif

        return xSendEventStructToIPTask( &xEventMessage, uxDontBlock );
    }
#endif /* if ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 ) */

/**
 * @brief Analyse an incoming packet and decide if the packet should be considered for processing.
 *
 * @param[in] pucEthernetBuffer: The buffer containing the full Ethernet packet.
 *
 * @return Either eProcessBuffer or eReleaseBuffer.
 */
eFrameProcessingResult_t eConsiderFrameForProcessing( const uint8_t * const pucEthernetBuffer )
{
    eFrameProcessingResult_t eReturn;
    const EthernetHeader_t * pxEthernetHeader;
    NetworkEndPoint_t * pxEndPoint;

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( EthernetHeader_t, pucEthernetBuffer );

    /* Examine the destination MAC from the Ethernet header to see if it matches
     * that of an end point managed by FreeRTOS+TCP. */
    pxEndPoint = FreeRTOS_FindEndPointOnMAC( &( pxEthernetHeader->xDestinationAddress ), NULL );

    if( pxEndPoint != NULL )
    {
        /* The packet was directed to this node - process it. */
        eReturn = eProcessBuffer;
    }
    else if( memcmp( xBroadcastMACAddress.ucBytes, pxEthernetHeader->xDestinationAddress.ucBytes, sizeof( MACAddress_t ) ) == 0 )
    {
        /* The packet was a broadcast - process it. */
        eReturn = eProcessBuffer;
    }
    else
    #if ( ipconfigUSE_LLMNR == 1 )
        if( memcmp( xLLMNR_MacAdress.ucBytes, pxEthernetHeader->xDestinationAddress.ucBytes, sizeof( MACAddress_t ) ) == 0 )
        {
            /* The packet is a request for LLMNR - process it. */
            eReturn = eProcessBuffer;
        }
        else
    #endif /* ipconfigUSE_LLMNR */

    #if ( ipconfigUSE_IPv6 != 0 )
        if( ( pxEthernetHeader->xDestinationAddress.ucBytes[ 0 ] == ipMULTICAST_MAC_ADDRESS_IPv6_0 ) &&
            ( pxEthernetHeader->xDestinationAddress.ucBytes[ 1 ] == ipMULTICAST_MAC_ADDRESS_IPv6_1 ) )
        {
            /* The packet is a request for LLMNR - process it. */
            eReturn = eProcessBuffer;
        }
        else
    #endif /* ipconfigUSE_IPv6 */
    {
        /* The packet was not a broadcast, or for this node, just release
         * the buffer without taking any other action. */
        eReturn = eReleaseBuffer;
    }

    #if ( ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES == 1 )
        {
            uint16_t usFrameType;

            if( eReturn == eProcessBuffer )
            {
                usFrameType = pxEthernetHeader->usFrameType;
                usFrameType = FreeRTOS_ntohs( usFrameType );

                if( usFrameType <= 0x600U )
                {
                    /* Not an Ethernet II frame. */
                    eReturn = eReleaseBuffer;
                }
            }
        }
    #endif /* ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES == 1  */

    return eReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Process a 'Network down' event and complete required processing.
 * @param pxInterface: The interface that goes down.
 */
static void prvProcessNetworkDownEvent( NetworkInterface_t * pxInterface )
{
    NetworkEndPoint_t * pxEndPoint;

    configASSERT( pxInterface != NULL );
    configASSERT( pxInterface->pfInitialise != NULL );

    /* The first network down event is generated by the IP stack itself to
     * initialise the network hardware, so do not call the network down event
     * the first time through. */

    /*_RB_ Similarly it is not clear to me why there is not a one to one
     * mapping between the interface and the end point, which would negate
     * the need for this loop.  Likewise the loop further down the same function. */
    /*_HT_ Because a single interface can have multiple end-points. */
    for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
         pxEndPoint != NULL;
         pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
    {
        /* The bit 'bEndPointUp' stays low until vIPNetworkUpCalls() is called. */
        pxEndPoint->bits.bEndPointUp = pdFALSE_UNSIGNED;
        #if ipconfigUSE_NETWORK_EVENT_HOOK == 1
            {
                if( pxEndPoint->bits.bCallDownHook != pdFALSE_UNSIGNED )
                {
                    #if ( ipconfigCOMPATIBLE_WITH_SINGLE == 1 )
                        {
                            vApplicationIPNetworkEventHook( eNetworkDown );
                        }
                    #else
                        {
                            vApplicationIPNetworkEventHook( eNetworkDown, pxEndPoint );
                        }
                    #endif
                }
                else
                {
                    /* The next time NetworkEventHook will be called for this end-point. */
                    pxEndPoint->bits.bCallDownHook = pdTRUE_UNSIGNED;
                }
            }
        #endif /* ipconfigUSE_NETWORK_EVENT_HOOK */
    }

    /* Per the ARP Cache Validation section of https://tools.ietf.org/html/rfc1122,
     * treat network down as a "delivery problem" and flush the ARP cache for this
     * interface. */
    FreeRTOS_ClearARP( ipCAST_PTR_TO_TYPE_PTR( NetworkEndPoint_t, pxInterface ) );

    /* The network has been disconnected (or is being initialised for the first
     * time).  Perform whatever hardware processing is necessary to bring it up
     * again, or wait for it to be available again.  This is hardware dependent. */

    if( pxInterface->pfInitialise( pxInterface ) == pdPASS )
    {
        pxInterface->bits.bInterfaceUp = pdTRUE_UNSIGNED;
        /* Set remaining time to 0 so it will become active immediately. */

        /* The network is not up until DHCP has completed.
         * Start it now for all associated end-points. */

        for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
             pxEndPoint != NULL;
             pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
        {
            #if ( ipconfigUSE_DHCP == 1 )
                if( END_POINT_USES_DHCP( pxEndPoint ) )
                {
                    #if ( ipconfigUSE_DHCPv6 != 0 )
                        if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
                        {
                            vDHCPv6Process( pdTRUE, pxEndPoint );
                        }
                        else
                    #endif /* ipconfigUSE_DHCPv6 */
                    {
                        /* Reset the DHCP process for this end-point. */
                        vDHCPProcess( pdTRUE, pxEndPoint );
                    }
                }
                else /* Yes this else ought to be here. */
            #endif /* ( ipconfigUSE_DHCP == 1 ) */

            #if ( ipconfigUSE_RA != 0 )
                if( END_POINT_USES_RA( pxEndPoint ) )
                {
                    /* Reset the RA/SLAAC process for this end-point. */
                    vRAProcess( pdTRUE, pxEndPoint );
                }
                else
            #endif /* ( #if( ipconfigUSE_IPv6 != 0 ) */

            {
                #if ( ipconfigUSE_IPv6 != 0 )
                    if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
                    {
                        ( void ) memcpy( &( pxEndPoint->ipv6_settings ), &( pxEndPoint->ipv6_defaults ), sizeof( pxEndPoint->ipv6_settings ) );
                    }
                    else
                #endif
                {
                    ( void ) memcpy( &( pxEndPoint->ipv4_settings ), &( pxEndPoint->ipv4_defaults ), sizeof( pxEndPoint->ipv4_settings ) );
                }

                /* DHCP or Router Advertisement are not enabled for this end-point.
                 * Perform any necessary 'network up' processing. */
                vIPNetworkUpCalls( pxEndPoint );
            }
        }
    }
    else
    {
        /* Nothing to do. When the 'xNetworkTimer' expires, all interfaces
         * with bits.bInterfaceUp cleared will get a new 'eNetworkDownEvent' */
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Perform all the required tasks when the network gets connected.
 *
 * @param pxEndPoint: The end-point which goes up.
 */
void vIPNetworkUpCalls( struct xNetworkEndPoint * pxEndPoint )
{
    pxEndPoint->bits.bEndPointUp = pdTRUE_UNSIGNED;

    #if ( ipconfigUSE_NETWORK_EVENT_HOOK == 1 )
        {
            #if ( ipconfigCOMPATIBLE_WITH_SINGLE == 1 )
                {
                    vApplicationIPNetworkEventHook( eNetworkUp );
                }
            #else
                {
                    vApplicationIPNetworkEventHook( eNetworkUp, pxEndPoint );
                }
            #endif /* ( ipconfigCOMPATIBLE_WITH_SINGLE == 1 ) */
        }
    #endif /* ipconfigUSE_NETWORK_EVENT_HOOK */

    /* The call to vDNSInitialise() has been moved to an earlier stage. */

    /* Set remaining time to 0 so it will become active immediately. */
    prvIPTimerReload( &xARPTimer, pdMS_TO_TICKS( ipARP_TIMER_PERIOD_MS ) );
}
/*-----------------------------------------------------------*/

/**
 * @brief Process the Ethernet packet.
 *
 * @param[in,out] pxNetworkBuffer: the network buffer containing the ethernet packet. If the
 *                                 buffer is large enough, it may be reused to send a reply.
 */
static void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    const EthernetHeader_t * pxEthernetHeader;
    eFrameProcessingResult_t eReturned = eReleaseBuffer;

    configASSERT( pxNetworkBuffer != NULL );

    iptraceNETWORK_INTERFACE_INPUT( pxNetworkBuffer->xDataLength, pxNetworkBuffer->pucEthernetBuffer );

    /* Interpret the Ethernet frame. */
    if( pxNetworkBuffer->xDataLength >= sizeof( EthernetHeader_t ) )
    {
        eReturned = ipCONSIDER_FRAME_FOR_PROCESSING( pxNetworkBuffer->pucEthernetBuffer );

        /* Map the buffer onto the Ethernet Header struct for easy access to the fields. */
        pxEthernetHeader = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( EthernetHeader_t, pxNetworkBuffer->pucEthernetBuffer );

        /* The condition "eReturned == eProcessBuffer" must be true. */
        #if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
            if( eReturned == eProcessBuffer )
        #endif
        {
            /* Interpret the received Ethernet packet. */
            switch( pxEthernetHeader->usFrameType )
            {
                case ipARP_FRAME_TYPE:

                    /* The Ethernet frame contains an ARP packet. */
                    if( pxNetworkBuffer->xDataLength >= sizeof( ARPPacket_t ) )
                    {
                        eReturned = eARPProcessPacket( pxNetworkBuffer );
                    }
                    else
                    {
                        eReturned = eReleaseBuffer;
                    }

                    break;

                case ipIPv4_FRAME_TYPE:
                    #if ( ipconfigUSE_IPv6 != 0 )
                        case ipIPv6_FRAME_TYPE:
                    #endif

                    /* The Ethernet frame contains an IP packet. */
                    if( pxNetworkBuffer->xDataLength >= sizeof( IPPacket_t ) )
                    {
                        eReturned = prvProcessIPPacket( ipCAST_PTR_TO_TYPE_PTR( IPPacket_t, pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer );
                    }
                    else
                    {
                        eReturned = eReleaseBuffer;
                    }

                    break;

                default:
                    /* No other packet types are handled.  Nothing to do. */
                    eReturned = eReleaseBuffer;
                    break;
            }
        }
    }

    /* Perform any actions that resulted from processing the Ethernet frame. */
    switch( eReturned )
    {
        case eReturnEthernetFrame:

            /* The Ethernet frame will have been updated (maybe it was
             * an ARP request or a PING request?) and should be sent back to
             * its source. */
            vReturnEthernetFrame( pxNetworkBuffer, pdTRUE );

            /* parameter pdTRUE: the buffer must be released once
             * the frame has been transmitted */
            break;

        case eFrameConsumed:

            /* The frame is in use somewhere, don't release the buffer
             * yet. */
            break;

        case eReleaseBuffer:
        case eProcessBuffer:
        default:

            /* The frame is not being used anywhere, and the
             * NetworkBufferDescriptor_t structure containing the frame should
             * just be released back to the list of free buffers. */
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
            break;
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Is the IP address an IPv4 multicast address.
 *
 * @param[in] ulIPAddress: The IP address being checked.
 *
 * @return pdTRUE if the IP address is a multicast address or else, pdFALSE.
 */
BaseType_t xIsIPv4Multicast( uint32_t ulIPAddress )
{
    BaseType_t xReturn;
    uint32_t ulIP = FreeRTOS_ntohl( ulIPAddress );

    if( ( ulIP >= ipFIRST_MULTI_CAST_IPv4 ) && ( ulIP < ipLAST_MULTI_CAST_IPv4 ) )
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

#if ( ipconfigUSE_IPv6 != 0 )
    BaseType_t xIsIPv6Multicast( const IPv6_Address_t * pxIPAddress )
    {
        BaseType_t xReturn;

        if( pxIPAddress->ucBytes[ 0 ] == 0xffU )
        {
            xReturn = pdTRUE;
        }
        else
        {
            xReturn = pdFALSE;
        }

        return xReturn;
    }
#endif /* ipconfigUSE_IPv6 */
/*-----------------------------------------------------------*/

/**
 * @brief Set multicast MAC address.
 *
 * @param[in] ulIPAddress: IP address.
 * @param[out] pxMACAddress: Pointer to MAC address.
 */
void vSetMultiCastIPv4MacAddress( uint32_t ulIPAddress,
                                  MACAddress_t * pxMACAddress )
{
    uint32_t ulIP = FreeRTOS_ntohl( ulIPAddress );
    uint32_t ulP2 = ( ulIP >> 16 ) & 0xEFU; /* Use 7 bits. */
    uint32_t ulP1 = ( ulIP >> 8 ) & 0xFFU;  /* Use 8 bits. */
    uint32_t ulP0 = ( ulIP ) & 0xFFU;       /* Use 8 bits. */
    uint8_t * ucBytes = pxMACAddress->ucBytes;

    ucBytes[ 0 ] = 0x01;
    ucBytes[ 1 ] = 0x00;
    ucBytes[ 2 ] = 0x5E;
    ucBytes[ 3 ] = ( uint8_t ) ulP2;
    ucBytes[ 4 ] = ( uint8_t ) ulP1;
    ucBytes[ 5 ] = ( uint8_t ) ulP0;
}
/*-----------------------------------------------------------*/
#if ( ipconfigUSE_IPv6 != 0 )

    void vSetMultiCastIPv6MacAddress( IPv6_Address_t * pxAddress,
                                      MACAddress_t * pxMACAddress )
    {
        pxMACAddress->ucBytes[ 0 ] = 0x33U;
        pxMACAddress->ucBytes[ 1 ] = 0x33U;
        pxMACAddress->ucBytes[ 2 ] = pxAddress->ucBytes[ 12 ];
        pxMACAddress->ucBytes[ 3 ] = pxAddress->ucBytes[ 13 ];
        pxMACAddress->ucBytes[ 4 ] = pxAddress->ucBytes[ 14 ];
        pxMACAddress->ucBytes[ 5 ] = pxAddress->ucBytes[ 15 ];
    }
/*-----------------------------------------------------------*/
#endif /* ( ipconfigUSE_IPv6 != 0 ) */

#if ( ipconfigUSE_IPv6 != 0 )
    BaseType_t xCompareIPv6_Address( const IPv6_Address_t * pxLeft,
                                     const IPv6_Address_t * pxRight,
                                     size_t uxPrefixLength )
    {
        BaseType_t xResult;

        /* 0    2    4    6    8    10   12   14 */
        /* ff02:0000:0000:0000:0000:0001:ff66:4a81 */
        if( ( pxRight->ucBytes[ 0 ] == 0xffU ) &&
            ( pxRight->ucBytes[ 1 ] == 0x02U ) &&
            ( pxRight->ucBytes[ 12 ] == 0xffU ) )
        {
            /* This is an LLMNR address. */
            xResult = memcmp( &( pxLeft->ucBytes[ 13 ] ), &( pxRight->ucBytes[ 13 ] ), 3 );
        }
        else
        if( ( pxRight->ucBytes[ 0 ] == 0xffU ) &&
            ( pxRight->ucBytes[ 1 ] == 0x02U ) )
        {
            /* FF02::1 is all node address to reach out all nodes in the same link. */
            xResult = 0;
        }
        else
        if( ( pxRight->ucBytes[ 0 ] == 0xfeU ) &&
            ( pxRight->ucBytes[ 1 ] == 0x80U ) &&
            ( pxLeft->ucBytes[ 0 ] == 0xfeU ) &&
            ( pxLeft->ucBytes[ 1 ] == 0x80U ) )
        {
            /* Both are local addresses. */
            xResult = 0;
        }
        else
        {
            if( uxPrefixLength == 0U )
            {
                xResult = 0;
            }
            else if( uxPrefixLength == ( 8U * ipSIZE_OF_IPv6_ADDRESS ) )
            {
                xResult = memcmp( pxLeft->ucBytes, pxRight->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
            }
            else
            {
                size_t uxLength = uxPrefixLength / 8U;

                xResult = 0;

                if( uxLength > 0U )
                {
                    xResult = memcmp( pxLeft->ucBytes, pxRight->ucBytes, uxLength );
                }

                if( ( xResult == 0 ) && ( ( uxPrefixLength % 8U ) != 0U ) )
                {
                    /* One byte has both a network- and a host-address. */
                    size_t uxBits = uxPrefixLength % 8U;
                    size_t uxHostLen = 8U - uxBits;
                    uint32_t uxHostMask = ( ( ( uint32_t ) 1U ) << uxHostLen ) - 1U;
                    uint8_t ucNetMask = ( uint8_t ) ~( uxHostMask );

                    if( ( pxLeft->ucBytes[ uxLength ] & ucNetMask ) != ( pxRight->ucBytes[ uxLength ] & ucNetMask ) )
                    {
                        xResult = 1;
                    }
                }
            }
        }

        return xResult;
    }
#endif /* ipconfigUSE_IPv6 */

#if ( ipconfigUSE_IPv6 != 0 )

/**
 * @brief Check whether this IPv6 packet is to be allowed or to be dropped.
 *
 * @param[in] pxIPv6Header: The IP packet under consideration.
 * @param[in] pxNetworkBuffer: The whole network buffer.
 * @param[in] uxHeaderLength: The length of the header.
 *
 * @return Whether the packet should be processed or dropped.
 */
    static eFrameProcessingResult_t prvAllowIPPacketIPv6( const IPHeader_IPv6_t * const pxIPv6Header,
                                                          const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                          UBaseType_t uxHeaderLength )
    {
        eFrameProcessingResult_t eReturn;

        #if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 0 )
            {
                /* In systems with a very small amount of RAM, it might be advantageous
                 * to have incoming messages checked earlier, by the network card driver.
                 * This method may decrease the usage of sparse network buffers. */
                const IPv6_Address_t * pxDestinationIPAddress = &( pxIPv6Header->xDestinationAddress );

                /* Is the packet for this IP address? */
                if( ( FreeRTOS_FindEndPointOnIP_IPv6( pxDestinationIPAddress ) != NULL ) ||
                    /* Is it the multicast address FF00::/8 ? */
                    ( xIsIPv6Multicast( pxDestinationIPAddress ) != pdFALSE ) ||
                    /* Or (during DHCP negotiation) we have no IP-address yet? */
                    ( FreeRTOS_IsNetworkUp() == 0 ) )
                {
                    /* Packet is not for this node, or the network is still not up,
                     * release it */
                    eReturn = eProcessBuffer;
                }
                else
                {
                    eReturn = eReleaseBuffer;
                    FreeRTOS_printf( ( "prvAllowIPPacketIPv6: drop %pip (from %pip)\n", pxDestinationIPAddress->ucBytes, pxIPv6Header->xSourceAddress.ucBytes ) );
                }
            }
        #else /* if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 0 ) */
            {
                ( void ) pxIPv6Header;
                /* The packet has been checked by the network interface. */
                eReturn = eProcessBuffer;
            }
        #endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */

        #if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 )
            {
                /* Some drivers of NIC's with checksum-offloading will enable the above
                 * define, so that the checksum won't be checked again here */
                if( eReturn == eProcessBuffer )
                {
                    const IPPacket_t * pxIPPacket = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( IPPacket_t, pxNetworkBuffer->pucEthernetBuffer );
                    NetworkEndPoint_t * pxEndPoint = FreeRTOS_FindEndPointOnMAC( &( pxIPPacket->xEthernetHeader.xSourceAddress ), NULL );

                    /* IPv6 does not have a separate checksum in the IP-header */
                    /* Is the upper-layer checksum (TCP/UDP/ICMP) correct? */
                    /* Do not check the checksum of loop-back messages. */
                    if( pxEndPoint == NULL )
                    {
                        if( usGenerateProtocolChecksum( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE ) != ipCORRECT_CRC )
                        {
                            /* Protocol checksum not accepted. */
                            eReturn = eReleaseBuffer;
                        }
                    }
                }
            }
        #else /* if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 ) */
            {
                /* to avoid warning unused parameters */
                ( void ) pxNetworkBuffer;
            }
        #endif /* ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 */
        ( void ) uxHeaderLength;

        return eReturn;
    }
#endif /* ipconfigUSE_IPv6 */
/*-----------------------------------------------------------*/

/**
 * @brief Check whether this IPv4 packet is to be allowed or to be dropped.
 *
 * @param[in] pxIPPacket: The IP packet under consideration.
 * @param[in] pxNetworkBuffer: The whole network buffer.
 * @param[in] uxHeaderLength: The length of the header.
 *
 * @return Whether the packet should be processed or dropped.
 */
static eFrameProcessingResult_t prvAllowIPPacketIPv4( const IPPacket_t * const pxIPPacket,
                                                      const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                      UBaseType_t uxHeaderLength )
{
    eFrameProcessingResult_t eReturn = eProcessBuffer;

    #if ( ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 0 ) || ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 ) )
        const IPHeader_t * pxIPHeader = &( pxIPPacket->xIPHeader );
    #else

        /* or else, the parameter won't be used and the function will be optimised
         * away */
        ( void ) pxIPPacket;
    #endif

    #if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 0 )
        {
            /* In systems with a very small amount of RAM, it might be advantageous
             * to have incoming messages checked earlier, by the network card driver.
             * This method may decrease the usage of sparse network buffers. */
            uint32_t ulDestinationIPAddress = pxIPHeader->ulDestinationIPAddress;

            /* Ensure that the incoming packet is not fragmented (fragmentation
             * was only supported for outgoing packets, and is not currently
             * not supported at all). */
            if( ( pxIPHeader->usFragmentOffset & ipFRAGMENT_OFFSET_BIT_MASK ) != 0U )
            {
                /* Can not handle, fragmented packet. */
                eReturn = eReleaseBuffer;
            }

            /* Test if the length of the IP-header is between 20 and 60 bytes,
             * and if the IP-version is 4. */
            else if( ( pxIPHeader->ucVersionHeaderLength < ipIPV4_VERSION_HEADER_LENGTH_MIN ) ||
                     ( pxIPHeader->ucVersionHeaderLength > ipIPV4_VERSION_HEADER_LENGTH_MAX ) )
            {
                /* Can not handle, unknown or invalid header version. */
                eReturn = eReleaseBuffer;
            }
            else if(
                ( pxNetworkBuffer->pxEndPoint == NULL ) &&
                ( FreeRTOS_FindEndPointOnIP_IPv4( ulDestinationIPAddress, 4 ) == NULL ) &&
                /* Is it an IPv4 broadcast address x.x.x.255 ? */
                ( ( FreeRTOS_ntohl( ulDestinationIPAddress ) & 0xffU ) != 0xffU ) &&
                ( xIsIPv4Multicast( ulDestinationIPAddress ) == pdFALSE ) &&
                /* Or (during DHCP negotiation) we have no IP-address yet? */
                ( FreeRTOS_IsNetworkUp() != pdFALSE ) )
            {
                /* Packet is not for this node, release it */
                eReturn = eReleaseBuffer;
            }
            else
            {
                /* Packet is not fragmented, destination is this device. */
            }
        }
    #endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */

    #if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 )
        {
            /* Some drivers of NIC's with checksum-offloading will enable the above
             * define, so that the checksum won't be checked again here */
            if( eReturn == eProcessBuffer )
            {
                NetworkEndPoint_t * pxEndPoint = FreeRTOS_FindEndPointOnMAC( &( pxIPPacket->xEthernetHeader.xSourceAddress ), NULL );

                /* Do not check the checksum of loop-back messages. */
                if( pxEndPoint == NULL )
                {
                    /* Is the IP header checksum correct? */
                    if( usGenerateChecksum( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength ) != ipCORRECT_CRC )
                    {
                        /* Check sum in IP-header not correct. */
                        eReturn = eReleaseBuffer;
                    }
                    /* Is the upper-layer checksum (TCP/UDP/ICMP) correct? */
                    else if( usGenerateProtocolChecksum( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE ) != ipCORRECT_CRC )
                    {
                        /* Protocol checksum not accepted. */
                        eReturn = eReleaseBuffer;
                    }
                    else
                    {
                        /* The checksum of the received packet is OK. */
                    }
                }
            }
        }
    #else /* if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 ) */
        {
            if( eReturn == eProcessBuffer )
            {
                /*#warning Please create a xCheckSizeFields() in stead if calling usGenerateProtocolChecksum() */

                if( usGenerateProtocolChecksum( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE ) != ipCORRECT_CRC )
                {
                    /* Some of the length checks were not successful. */
                    eReturn = eReleaseBuffer;
                }
            }

            #if ( ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS == 0 )
                {
                    /* Check if this is a UDP packet without a checksum. */
                    if( eReturn == eProcessBuffer )
                    {
                        uint8_t ucProtocol;
                        ProtocolHeaders_t * pxProtocolHeaders;
                        #if ( ipconfigUSE_IPv6 != 0 )
                            const IPHeader_IPv6_t * pxIPPacket_IPv6;

                            pxIPPacket_IPv6 = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( IPHeader_IPv6_t, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );

                            if( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
                            {
                                ucProtocol = pxIPPacket_IPv6->ucNextHeader;
                                pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] ) );
                            }
                            else
                        #endif /* ( ipconfigUSE_IPv6 != 0 ) */
                        {
                            ucProtocol = pxIPPacket->xIPHeader.ucProtocol;
                            pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ( size_t ) ipSIZE_OF_IPv4_HEADER ] ) );
                        }

                        if( ucProtocol == ( uint8_t ) ipPROTOCOL_UDP )
                        {
                            if( pxProtocolHeaders->xUDPHeader.usChecksum == ( uint16_t ) 0U )
                            {
                                #if ( ipconfigHAS_PRINTF != 0 )
                                    {
                                        static BaseType_t xCount = 0;

                                        if( xCount < 5 )
                                        {
                                            FreeRTOS_printf( ( "prvAllowIPPacket: UDP packet from %lxip without CRC dropped\n",
                                                               FreeRTOS_ntohl( pxIPPacket->xIPHeader.ulSourceIPAddress ) ) );
                                            xCount++;
                                        }
                                    }
                                #endif /* ( ipconfigHAS_PRINTF != 0 ) */

                                /* Protocol checksum not accepted. */
                                eReturn = eReleaseBuffer;
                            }
                        }
                    }
                }
            #endif /* ( ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS == 0 ) */

            /* to avoid warning unused parameters */
            ( void ) pxNetworkBuffer;
            ( void ) uxHeaderLength;
        }
    #endif /* ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 */

    return eReturn;
}
/*-----------------------------------------------------------*/

/** @brief Check if the IP-header is carrying options.
 * @param[in] pxNetworkBuffer: the network buffer that contains the packet.
 *
 * @return Either 'eProcessBuffer' or 'eReleaseBuffer'
 */
static eFrameProcessingResult_t prvCheckIP4HeaderOptions( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    eFrameProcessingResult_t eReturn = eReleaseBuffer;

    /* This function is only called for IPv4 packets, with an IP-header
     * which is larger than 20 bytes.  The extra space is used for IP-options.
     * The options will either be removed, or the packet shall be dropped,
     * depending on a user define. */

    #if ( ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS != 0 )
        {
            size_t uxHeaderLength;

            IPHeader_t * pxIPHeader = ipCAST_PTR_TO_TYPE_PTR( IPHeader_t, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );

            /* All structs of headers expect a IP header size of 20 bytes
             * IP header options were included, we'll ignore them and cut them out. */
            size_t uxLength = ( size_t ) pxIPHeader->ucVersionHeaderLength;

            /* Check if the IP headers are acceptable and if it has our destination.
             * The lowest four bits of 'ucVersionHeaderLength' indicate the IP-header
             * length in multiples of 4. */
            uxHeaderLength = ( size_t ) ( ( uxLength & 0x0FU ) << 2 );

            const size_t optlen = ( ( size_t ) uxHeaderLength ) - ipSIZE_OF_IPv4_HEADER;

            if( optlen > 0U )
            {
                /* From: the previous start of UDP/ICMP/TCP data. */
                const uint8_t * pucSource = ( const uint8_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( EthernetHeader_t ) + uxHeaderLength ] );
                /* To: the usual start of UDP/ICMP/TCP data at offset 20 (decimal ) from IP header. */
                uint8_t * pucTarget = ( uint8_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( EthernetHeader_t ) + ipSIZE_OF_IPv4_HEADER ] );
                /* How many: total length minus the options and the lower headers. */
                const size_t xMoveLen = pxNetworkBuffer->xDataLength - ( optlen + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_ETH_HEADER );

                ( void ) memmove( pucTarget, pucSource, xMoveLen );
                pxNetworkBuffer->xDataLength -= optlen;
            }

            /* Rewrite the Version/IHL byte to indicate that this packet has no IP options. */
            pxIPHeader->ucVersionHeaderLength = ( pxIPHeader->ucVersionHeaderLength & 0xF0U ) | /* High nibble is the version. */
                                                ( ( ipSIZE_OF_IPv4_HEADER >> 2 ) & 0x0FU );
            eReturn = eProcessBuffer;
        }
    #else /* if ( ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS != 0 ) */
        {
            /* 'ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS' is not set, so packets carrying
            * IP-options will be dropped.  The function will return 'eReleaseBuffer'. */
        }
    #endif /* if ( ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS != 0 ) */

    return eReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Check the sizes of the UDP packet and forward it to the UDP module
 *        ( xProcessReceivedUDPPacket() )
 * @param[in] pxNetworkBuffer: The network buffer containing the UDP packet.
 * @return eReleaseBuffer ( please release the buffer ).
 *         eFrameConsumed ( the buffer has now been released ).
 */

static eFrameProcessingResult_t prvProcessUDPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    eFrameProcessingResult_t eReturn = eReleaseBuffer;

    /* The IP packet contained a UDP frame. */
    UDPPacket_t * pxUDPPacket = ipCAST_PTR_TO_TYPE_PTR( UDPPacket_t, pxNetworkBuffer->pucEthernetBuffer );
    UDPHeader_t * pxUDPHeader = &( pxUDPPacket->xUDPHeader );

    size_t uxMinSize = ipSIZE_OF_ETH_HEADER + ( size_t ) uxIPHeaderSizePacket( pxNetworkBuffer ) + ipSIZE_OF_UDP_HEADER;
    size_t uxLength;
    uint16_t usLength;

    #if ( ipconfigUSE_IPv6 != 0 )
        if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
        {
            ProtocolHeaders_t * pxProtocolHeaders;

            pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] ) );
            pxUDPHeader = &( pxProtocolHeaders->xUDPHeader );
        }
    #endif

    usLength = FreeRTOS_ntohs( pxUDPHeader->usLength );
    uxLength = ( size_t ) usLength;

    /* Note the header values required prior to the checksum
     * generation as the checksum pseudo header may clobber some of
     * these values. */
    if( ( pxNetworkBuffer->xDataLength >= uxMinSize ) &&
        ( uxLength >= sizeof( UDPHeader_t ) ) )
    {
        size_t uxPayloadSize_1, uxPayloadSize_2;

        /* Ensure that downstream UDP packet handling has the lesser
         * of: the actual network buffer Ethernet frame length, or
         * the sender's UDP packet header payload length, minus the
         * size of the UDP header.
         *
         * The size of the UDP packet structure in this implementation
         * includes the size of the Ethernet header, the size of
         * the IP header, and the size of the UDP header. */
        uxPayloadSize_1 = pxNetworkBuffer->xDataLength - uxMinSize;
        uxPayloadSize_2 = uxLength - ipSIZE_OF_UDP_HEADER;

        if( uxPayloadSize_1 > uxPayloadSize_2 )
        {
            pxNetworkBuffer->xDataLength = uxPayloadSize_2 + uxMinSize;
        }

        pxNetworkBuffer->usPort = pxUDPHeader->usSourcePort;
        pxNetworkBuffer->ulIPAddress = pxUDPPacket->xIPHeader.ulSourceIPAddress;

        /* ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM:
         * In some cases, the upper-layer checksum has been calculated
         * by the NIC driver. */

        /* Pass the packet payload to the UDP sockets
         * implementation. */
        if( xProcessReceivedUDPPacket( pxNetworkBuffer,
                                       pxUDPHeader->usDestinationPort ) == pdPASS )
        {
            eReturn = eFrameConsumed;
        }
    }
    else
    {
        /* Length checks failed, the buffer will be released. */
    }

    return eReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Process an IP-packet.
 *
 * @param[in] pxIPPacket: The IP packet to be processed.
 * @param[in] pxNetworkBuffer: The networkbuffer descriptor having the IP packet.
 *
 * @return An enum to show whether the packet should be released/kept/processed etc.
 */
static eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                                    NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    eFrameProcessingResult_t eReturn;
    IPHeader_t * pxIPHeader = &( pxIPPacket->xIPHeader );

    #if ( ipconfigUSE_IPv6 != 0 )
        const IPHeader_IPv6_t * pxIPHeader_IPv6;
    #endif
    UBaseType_t uxHeaderLength;
    uint8_t ucProtocol;

    #if ( ipconfigUSE_IPv6 != 0 )
        pxIPHeader_IPv6 = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( IPHeader_IPv6_t, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );

        if( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
        {
            uxHeaderLength = ipSIZE_OF_IPv6_HEADER;
            ucProtocol = pxIPHeader_IPv6->ucNextHeader;
            eReturn = prvAllowIPPacketIPv6( ipCAST_PTR_TO_TYPE_PTR( IPHeader_IPv6_t, &( pxIPPacket->xIPHeader ) ), pxNetworkBuffer, uxHeaderLength );

            /* The IP-header type is copied to a location 6 bytes before the messages
             * starts.  It might be needed later on when a UDP-payload buffer is being
             * used. */
            pxNetworkBuffer->pucEthernetBuffer[ 0 - ( BaseType_t ) ipIP_TYPE_OFFSET ] = pxIPHeader_IPv6->ucVersionTrafficClass;
        }
        else
    #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
    {
        size_t uxLength = ( size_t ) pxIPHeader->ucVersionHeaderLength;

        /* Check if the IP headers are acceptable and if it has our destination.
         * The lowest four bits of 'ucVersionHeaderLength' indicate the IP-header
         * length in multiples of 4. */
        uxHeaderLength = ( size_t ) ( ( uxLength & 0x0FU ) << 2 );
        ucProtocol = pxIPPacket->xIPHeader.ucProtocol;
        eReturn = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );
        #if ( ipconfigUSE_IPv6 != 0 )
            {
                /* The IP-header type is copied to a location 6 bytes before the
                 * messages starts.  It might be needed later on when a UDP-payload
                 * buffer is being used. */
                pxNetworkBuffer->pucEthernetBuffer[ 0 - ( BaseType_t ) ipIP_TYPE_OFFSET ] = pxIPHeader->ucVersionHeaderLength;
            }
        #endif /* ipconfigUSE_IPv6 */
    }

    if( eReturn == eProcessBuffer )
    {
        if( ( pxIPPacket->xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE ) &&
            ( uxHeaderLength > ipSIZE_OF_IPv4_HEADER ) )
        {
            /* See if the IPv4 header carries option. Of so,
             * either drop the packet, or remove the options. */
            eReturn = prvCheckIP4HeaderOptions( pxNetworkBuffer );
        }

        /* If the packet can be processed. */
        if( eReturn != eReleaseBuffer )
        {
            /* Add the IP and MAC addresses to the ARP table if they are not
             * already there - otherwise refresh the age of the existing
             * entry. */
            if( ucProtocol != ( uint8_t ) ipPROTOCOL_UDP )
            {
                /* Refresh the ARP cache with the IP/MAC-address of the received
                 *  packet.  For UDP packets, this will be done later in
                 *  xProcessReceivedUDPPacket(), as soon as it's know that the message
                 *  will be handled.  This will prevent the ARP cache getting
                 *  overwritten with the IP address of useless broadcast packets. */
                #if ( ipconfigUSE_IPv6 != 0 )
                    if( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
                    {
                        vNDRefreshCacheEntry( &( pxIPPacket->xEthernetHeader.xSourceAddress ), &( pxIPHeader_IPv6->xSourceAddress ), pxNetworkBuffer->pxEndPoint );
                    }
                    else
                #endif /* ipconfigUSE_IPv6 */
                {
                    vARPRefreshCacheEntry( &( pxIPPacket->xEthernetHeader.xSourceAddress ), pxIPHeader->ulSourceIPAddress, pxNetworkBuffer->pxEndPoint );
                }
            }

            switch( ucProtocol )
            {
                #if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
                    case ipPROTOCOL_ICMP:
                        /* As for now, only ICMP/ping messages are recognised. */
                        eReturn = prvProcessICMPPacket( pxNetworkBuffer );
                        break;
                #endif

                #if ( ipconfigUSE_IPv6 != 0 )
                    case ipPROTOCOL_ICMP_IPv6:
                        eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );
                        break;
                #endif

                case ipPROTOCOL_UDP:
                    eReturn = prvProcessUDPPacket( pxNetworkBuffer );
                    break;

                    #if ipconfigUSE_TCP == 1
                        case ipPROTOCOL_TCP:

                            if( xProcessReceivedTCPPacket( pxNetworkBuffer ) == pdPASS )
                            {
                                eReturn = eFrameConsumed;
                            }

                            /* Setting this variable will cause xTCPTimerCheck()
                             * to be called just before the IP-task blocks. */
                            xProcessedTCPMessage++;
                            break;
                    #endif /* if ipconfigUSE_TCP == 1 */
                default:
                    /* Not a supported protocol type. */
                    break;
            }
        }
    }

    return eReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

/**
 * @brief Process an ICMP echo reply.
 *
 * @param[in] pxICMPPacket: The IP packet that contains the ICMP message.
 */
    static void prvProcessICMPEchoReply( ICMPPacket_t * const pxICMPPacket )
    {
        ePingReplyStatus_t eStatus = eSuccess;
        uint16_t usDataLength, usCount;
        uint8_t * pucByte;

        /* Find the total length of the IP packet. */
        usDataLength = pxICMPPacket->xIPHeader.usLength;
        usDataLength = FreeRTOS_ntohs( usDataLength );

        /* Remove the length of the IP headers to obtain the length of the ICMP
         * message itself. */
        usDataLength = ( uint16_t ) ( ( ( uint32_t ) usDataLength ) - ipSIZE_OF_IPv4_HEADER );

        /* Remove the length of the ICMP header, to obtain the length of
         * data contained in the ping. */
        usDataLength = ( uint16_t ) ( ( ( uint32_t ) usDataLength ) - ipSIZE_OF_ICMPv4_HEADER );

        /* Checksum has already been checked before in prvProcessIPPacket */

        /* Find the first byte of the data within the ICMP packet. */
        pucByte = ( uint8_t * ) pxICMPPacket;
        pucByte = &( pucByte[ sizeof( ICMPPacket_t ) ] );

        /* Check each byte. */
        for( usCount = 0; usCount < usDataLength; usCount++ )
        {
            if( *pucByte != ( uint8_t ) ipECHO_DATA_FILL_BYTE )
            {
                eStatus = eInvalidData;
                break;
            }

            pucByte++;
        }

        /* Call back into the application to pass it the result. */
        vApplicationPingReplyHook( eStatus, pxICMPPacket->xICMPHeader.usIdentifier );
    }

#endif /* if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 )

/**
 * @brief Process an ICMP echo request.
 *
 * @param[in,out] pxICMPPacket: The IP packet that contains the ICMP message.
 */
    static eFrameProcessingResult_t prvProcessICMPEchoRequest( ICMPPacket_t * const pxICMPPacket )
    {
        ICMPHeader_t * pxICMPHeader;
        IPHeader_t * pxIPHeader;
        uint16_t usRequest;
        uint32_t ulIPAddress;

        pxICMPHeader = &( pxICMPPacket->xICMPHeader );
        pxIPHeader = &( pxICMPPacket->xIPHeader );

        /* HT:endian: changed back */
        iptraceSENDING_PING_REPLY( pxIPHeader->ulSourceIPAddress );

        /* The checksum can be checked here - but a ping reply should be
         * returned even if the checksum is incorrect so the other end can
         * tell that the ping was received - even if the ping reply contains
         * invalid data. */
        pxICMPHeader->ucTypeOfMessage = ( uint8_t ) ipICMP_ECHO_REPLY;
        ulIPAddress = pxIPHeader->ulDestinationIPAddress;
        pxIPHeader->ulDestinationIPAddress = pxIPHeader->ulSourceIPAddress;
        pxIPHeader->ulSourceIPAddress = ulIPAddress;

        /* Update the checksum because the ucTypeOfMessage member in the header
         * has been changed to ipICMP_ECHO_REPLY.  This is faster than calling
         * usGenerateChecksum(). */

        /* due to compiler warning "integer operation result is out of range" */

        usRequest = ( uint16_t ) ( ( uint16_t ) ipICMP_ECHO_REQUEST << 8 );

        if( pxICMPHeader->usChecksum >= FreeRTOS_htons( 0xFFFFU - usRequest ) )
        {
            pxICMPHeader->usChecksum = pxICMPHeader->usChecksum + FreeRTOS_htons( usRequest + 1U );
        }
        else
        {
            pxICMPHeader->usChecksum = pxICMPHeader->usChecksum + FreeRTOS_htons( usRequest );
        }

        return eReturnEthernetFrame;
    }

#endif /* ipconfigREPLY_TO_INCOMING_PINGS == 1 */
/*-----------------------------------------------------------*/

#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

/**
 * @brief Process an ICMP packet. Only echo requests and echo replies are recognised and handled.
 *
 * @param[in,out] pxICMPPacket: The IP packet that contains the ICMP message.
 *
 * @return eReleaseBuffer when the message buffer should be released, or eReturnEthernetFrame
 *                        when the packet should be returned.
 */

    static eFrameProcessingResult_t prvProcessICMPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
    {
        eFrameProcessingResult_t eReturn = eReleaseBuffer;

        iptraceICMP_PACKET_RECEIVED();

        if( pxNetworkBuffer->xDataLength >= sizeof( ICMPPacket_t ) )
        {
            /* Map the buffer onto a ICMP-Packet struct to easily access the
             * fields of ICMP packet. */
            ICMPPacket_t * pxICMPPacket = ipCAST_PTR_TO_TYPE_PTR( ICMPPacket_t, pxNetworkBuffer->pucEthernetBuffer );

            switch( pxICMPPacket->xICMPHeader.ucTypeOfMessage )
            {
                case ipICMP_ECHO_REQUEST:
                    #if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 )
                        {
                            eReturn = prvProcessICMPEchoRequest( pxICMPPacket );
                        }
                    #endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) */
                    break;

                case ipICMP_ECHO_REPLY:
                    #if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
                        {
                            prvProcessICMPEchoReply( pxICMPPacket );
                        }
                    #endif /* ipconfigSUPPORT_OUTGOING_PINGS */
                    break;

                default:
                    /* Only ICMP echo packets are handled. */
                    break;
            }
        }

        return eReturn;
    }

#endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )

/** @brief Do the first IPv6 length checks at the IP-header level.
 * @param[in] pucEthernetBuffer: The buffer containing the packet.
 * @param[in] uxBufferLength: The number of bytes to be sent or received.
 * @param[in] pxSet: A struct describing this packet.
 *
 * @return Non-zero in case of an error.
 */
    static BaseType_t prvChecksumIPv6Checks( const uint8_t * pucEthernetBuffer,
                                             size_t uxBufferLength,
                                             struct xPacketSummary * pxSet )
    {
        BaseType_t xReturn = 0;

        pxSet->xIsIPv6 = pdTRUE;

        pxSet->uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;

        /* Check for minimum packet size: ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER (54 bytes) */
        if( uxBufferLength < sizeof( IPPacket_IPv6_t ) )
        {
            pxSet->usChecksum = ipINVALID_LENGTH;
            xReturn = 1;
        }
        else
        {
            pxSet->ucProtocol = pxSet->pxIPPacket_IPv6->ucNextHeader;
            pxSet->pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] ) );
            pxSet->usPayloadLength = FreeRTOS_ntohs( pxSet->pxIPPacket_IPv6->usPayloadLength );
            /* For IPv6, the number of bytes in the protocol is indicated. */
            pxSet->usProtocolBytes = pxSet->usPayloadLength;

            size_t uxNeeded = ( size_t ) pxSet->usPayloadLength;
            uxNeeded += ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;

            if( uxBufferLength < uxNeeded )
            {
                /* The packet does not contain a complete IPv6 packet. */
                pxSet->usChecksum = ipINVALID_LENGTH;
                xReturn = 2;
            }
        }

        return xReturn;
    }
#endif /* ( ipconfigUSE_IPv6 != 0 ) */
/*-----------------------------------------------------------*/

/** @brief Do the first IPv4 length checks at the IP-header level.
 * @param[in] pucEthernetBuffer: The buffer containing the packet.
 * @param[in] uxBufferLength: The number of bytes to be sent or received.
 * @param[in] pxSet: A struct describing this packet.
 *
 * @return Non-zero in case of an error.
 */
static BaseType_t prvChecksumIPv4Checks( const uint8_t * pucEthernetBuffer,
                                         size_t uxBufferLength,
                                         struct xPacketSummary * pxSet )
{
    BaseType_t xReturn = 0;
    uint8_t ucVersion;

    /* Check for minimum packet size. */
    if( uxBufferLength < sizeof( IPPacket_t ) )
    {
        pxSet->usChecksum = ipINVALID_LENGTH;
        xReturn = 3;
    }

    if( xReturn == 0 )
    {
        /* IPv4 : the lower nibble in 'ucVersionHeaderLength' indicates the length
         * of the IP-header, expressed in number of 4-byte words. Usually 5 words.
         */
        ucVersion = pxSet->pxIPPacket->xIPHeader.ucVersionHeaderLength & ( uint8_t ) 0x0FU;
        pxSet->uxIPHeaderLength = ( size_t ) ucVersion;
        pxSet->uxIPHeaderLength *= 4U;

        /* Check for minimum packet size. */
        if( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + pxSet->uxIPHeaderLength ) )
        {
            /* The packet does not contain the full IP-headers so drop it. */
            pxSet->usChecksum = ipINVALID_LENGTH;
            xReturn = 4;
        }
    }

    if( xReturn == 0 )
    {
        /* xIPHeader.usLength is the total length, minus the Ethernet header. */
        pxSet->usPayloadLength = FreeRTOS_ntohs( pxSet->pxIPPacket->xIPHeader.usLength );

        size_t uxNeeded = pxSet->usPayloadLength;
        uxNeeded += ipSIZE_OF_ETH_HEADER;

        if( uxBufferLength < uxNeeded )
        {
            /* The payload is longer than the packet appears to contain. */
            pxSet->usChecksum = ipINVALID_LENGTH;
            xReturn = 5;
        }
    }

    if( xReturn == 0 )
    {
        /* Identify the next protocol. */
        pxSet->ucProtocol = pxSet->pxIPPacket->xIPHeader.ucProtocol;
        pxSet->pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t, &( pucEthernetBuffer[ pxSet->uxIPHeaderLength + ipSIZE_OF_ETH_HEADER ] ) );
        /* For IPv4, the number of bytes in IP-header + the protocol is indicated. */
        pxSet->usProtocolBytes = pxSet->usPayloadLength - ( ( uint16_t ) pxSet->uxIPHeaderLength );
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )

/**
 * @brief Check the buffer lengths of an ICMPv6 packet.
 * @param[in] uxBufferLength: The total length of the packet.
 * @param[in] pxSet A struct describing this packet.
 * @return Non-zero in case of an error.
 */
    static BaseType_t prvChecksumICMPv6Checks( size_t uxBufferLength,
                                               struct xPacketSummary * pxSet )
    {
        BaseType_t xReturn = 0;
        size_t xICMPLength;

        switch( pxSet->pxProtocolHeaders->xICMPHeaderIPv6.ucTypeOfMessage )
        {
            case ipICMP_PING_REQUEST_IPv6:
            case ipICMP_PING_REPLY_IPv6:
                xICMPLength = sizeof( ICMPEcho_IPv6_t );
                break;

            case ipICMP_ROUTER_SOLICITATION_IPv6:
                xICMPLength = sizeof( ICMPRouterSolicitation_IPv6_t );
                break;

            default:
                xICMPLength = ipSIZE_OF_ICMPv6_HEADER;
                break;
        }

        if( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + pxSet->uxIPHeaderLength + xICMPLength ) )
        {
            pxSet->usChecksum = ipINVALID_LENGTH;
            xReturn = 10;
        }

        if( xReturn == 0 )
        {
            pxSet->pusChecksum = ( uint16_t * ) ( &( pxSet->pxProtocolHeaders->xICMPHeader.usChecksum ) );
            pxSet->uxProtocolHeaderLength = xICMPLength;
            #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
                {
                    pxSet->pcType = "ICMP_IPv6";
                }
            #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */
        }

        return xReturn;
    }
#endif /* ( ipconfigUSE_IPv6 != 0 ) */

/** @brief Get and check the specific lengths depending on the protocol ( TCP/UDP/ICMP/IGMP ).
 * @param[in] uxBufferLength: The number of bytes to be sent or received.
 * @param[in] pxSet: A struct describing this packet.
 *
 * @return Non-zero in case of an error.
 */
static BaseType_t prvChecksumProtocolChecks( size_t uxBufferLength,
                                             struct xPacketSummary * pxSet )
{
    BaseType_t xReturn = 0;

    /* Both in case of IPv4, as well as IPv6, it has been confirmed that the packet
     * is long enough to contain the promised data. */

    /* Switch on the Layer 3/4 protocol. */
    if( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_UDP )
    {
        if( ( pxSet->usProtocolBytes < ipSIZE_OF_UDP_HEADER ) ||
            ( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + pxSet->uxIPHeaderLength + ipSIZE_OF_UDP_HEADER ) ) )
        {
            pxSet->usChecksum = ipINVALID_LENGTH;
            xReturn = 7;
        }

        if( xReturn == 0 )
        {
            pxSet->pusChecksum = ( uint16_t * ) ( &( pxSet->pxProtocolHeaders->xUDPHeader.usChecksum ) );
            pxSet->uxProtocolHeaderLength = sizeof( pxSet->pxProtocolHeaders->xUDPHeader );
            #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
                {
                    pxSet->pcType = "UDP";
                }
            #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */
        }
    }
    else if( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_TCP )
    {
        if( ( pxSet->usProtocolBytes < ipSIZE_OF_TCP_HEADER ) ||
            ( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + pxSet->uxIPHeaderLength + ipSIZE_OF_TCP_HEADER ) ) )
        {
            pxSet->usChecksum = ipINVALID_LENGTH;
            xReturn = 8;
        }

        if( xReturn == 0 )
        {
            uint8_t ucLength = ( ( ( pxSet->pxProtocolHeaders->xTCPHeader.ucTCPOffset >> 4U ) - 5U ) << 2U );
            size_t uxOptionsLength = ( size_t ) ucLength;
            pxSet->pusChecksum = ( uint16_t * ) ( &( pxSet->pxProtocolHeaders->xTCPHeader.usChecksum ) );
            pxSet->uxProtocolHeaderLength = ipSIZE_OF_TCP_HEADER + uxOptionsLength;
            #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
                {
                    pxSet->pcType = "TCP";
                }
            #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */
        }
    }
    else if( ( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP ) ||
             ( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_IGMP ) )
    {
        if( ( pxSet->usProtocolBytes < ipSIZE_OF_ICMPv4_HEADER ) ||
            ( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + pxSet->uxIPHeaderLength + ipSIZE_OF_ICMPv4_HEADER ) ) )
        {
            pxSet->usChecksum = ipINVALID_LENGTH;
            xReturn = 9;
        }

        if( xReturn == 0 )
        {
            pxSet->uxProtocolHeaderLength = sizeof( pxSet->pxProtocolHeaders->xICMPHeader );
            pxSet->pusChecksum = ( uint16_t * ) ( &( pxSet->pxProtocolHeaders->xICMPHeader.usChecksum ) );

            #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
                {
                    if( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP )
                    {
                        pxSet->pcType = "ICMP";
                    }
                    else
                    {
                        pxSet->pcType = "IGMP";
                    }
                }
            #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */
        }
    }

    #if ( ipconfigUSE_IPv6 != 0 )
        else if( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP_IPv6 )
        {
            prvChecksumICMPv6Checks( uxBufferLength, pxSet );
        }
    #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
    else
    {
        /* Unhandled protocol, other than ICMP, IGMP, UDP, or TCP. */
        pxSet->usChecksum = ipUNHANDLED_PROTOCOL;
        xReturn = 11;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/** @brief See if the packet doesn't get bigger than the value of MTU.
 * @param[in] pxSet: A struct describing this packet.
 *
 * @return Non-zero in case of an error.
 */
static BaseType_t prvChecksumProtocolMTUCheck( struct xPacketSummary * pxSet )
{
    BaseType_t xReturn = 0;

    /* Here, 'pxSet->usProtocolBytes' contains the size of the protocol data
     * ( headers and payload ). */

    /* The Ethernet header is excluded from the MTU. */
    uint32_t ulMaxLength = ipconfigNETWORK_MTU;

    ulMaxLength -= ( uint32_t ) pxSet->uxIPHeaderLength;

    if( ( pxSet->usProtocolBytes < ( uint16_t ) pxSet->uxProtocolHeaderLength ) ||
        ( pxSet->usProtocolBytes > ulMaxLength ) )
    {
        #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
            {
                FreeRTOS_debug_printf( ( "usGenerateProtocolChecksum[%s]: len invalid: %u\n", pxSet->pcType, pxSet->usProtocolBytes ) );
            }
        #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */

        /* Again, in a 16-bit return value there is no space to indicate an
         * error.  For incoming packets, 0x1234 will cause dropping of the packet.
         * For outgoing packets, there is a serious problem with the
         * format/length */
        pxSet->usChecksum = ipINVALID_LENGTH;
        xReturn = 13;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/** @brief Do the actual checksum calculations, both the pseudo header, and the payload.
 * @param[in] xOutgoingPacket: pdTRUE when the packet is to be sent.
 * @param[in] pucEthernetBuffer: The buffer containing the packet.
 * @param[in] pxSet: A struct describing this packet.
 */
static void prvChecksumProtocolCalculate( BaseType_t xOutgoingPacket,
                                          const uint8_t * pucEthernetBuffer,
                                          struct xPacketSummary * pxSet )
{
    #if ( ipconfigUSE_IPv6 != 0 )
        if( pxSet->xIsIPv6 != pdFALSE )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                uint32_t pulHeader[ 2 ];
            #endif

            /* IPv6 has a 40-byte pseudo header:
             * 0..15 Source IPv6 address
             * 16..31 Target IPv6 address
             * 32..35 Length of payload
             * 36..38 three zero's
             * 39 Next Header, i.e. the protocol type. */

            pulHeader[ 0 ] = FreeRTOS_htonl( pxSet->usProtocolBytes );
            pulHeader[ 1 ] = ( uint32_t ) pxSet->pxIPPacket_IPv6->ucNextHeader;
            pulHeader[ 1 ] = FreeRTOS_htonl( pulHeader[ 1 ] );

            pxSet->usChecksum = usGenerateChecksum( 0U,
                                                    &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + offsetof( IPHeader_IPv6_t, xSourceAddress ) ] ),
                                                    ( size_t ) ( 2U * sizeof( pxSet->pxIPPacket_IPv6->xSourceAddress ) ) );

            pxSet->usChecksum = usGenerateChecksum( pxSet->usChecksum,
                                                    ( const uint8_t * ) pulHeader,
                                                    ( size_t ) ( sizeof( pulHeader ) ) );
        }
    #endif /* if ( ipconfigUSE_IPv6 != 0 ) */

    if( ( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP ) || ( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_IGMP ) )
    {
        /* ICMP/IGMP do not have a pseudo header for CRC-calculation. */
        pxSet->usChecksum = ( uint16_t )
                            ( ~usGenerateChecksum( 0U, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + pxSet->uxIPHeaderLength ] ), ( size_t ) pxSet->usProtocolBytes ) );
    }

    #if ( ipconfigUSE_IPv6 != 0 )
        else if( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP_IPv6 )
        {
            pxSet->usChecksum = ( uint16_t )
                                ( ~usGenerateChecksum( pxSet->usChecksum,
                                                       ( uint8_t * ) &( pxSet->pxProtocolHeaders->xTCPHeader ),
                                                       ( size_t ) pxSet->usProtocolBytes ) );
        }
    #endif /* ipconfigUSE_IPv6 */
    else
    {
        #if ( ipconfigUSE_IPv6 != 0 )
            if( pxSet->xIsIPv6 != pdFALSE )
            {
                /* The CRC of the IPv6 pseudo-header has already been calculated. */
                pxSet->usChecksum = ( uint16_t )
                                    ( ~usGenerateChecksum( pxSet->usChecksum,
                                                           ( uint8_t * ) &( pxSet->pxProtocolHeaders->xUDPHeader.usSourcePort ),
                                                           ( size_t ) ( pxSet->usProtocolBytes ) ) );
            }
            else
        #endif /* ipconfigUSE_IPv6 */
        {
            /* The IPv4 pseudo header contains 2 IP-addresses, totalling 8 bytes. */
            uint32_t ulByteCount = pxSet->usProtocolBytes;
            ulByteCount += 2U * ipSIZE_OF_IPv4_ADDRESS;

            /* For UDP and TCP, sum the pseudo header, i.e. IP protocol + length
             * fields */
            pxSet->usChecksum = ( uint16_t ) ( pxSet->usProtocolBytes + ( ( uint16_t ) pxSet->ucProtocol ) );

            /* And then continue at the IPv4 source and destination addresses. */
            pxSet->usChecksum = ( uint16_t )
                                ( ~usGenerateChecksum( pxSet->usChecksum,
                                                       ipPOINTER_CAST( const uint8_t *, &( pxSet->pxIPPacket->xIPHeader.ulSourceIPAddress ) ),
                                                       ulByteCount ) );
        }

        /* Sum TCP header and data. */
    }

    if( xOutgoingPacket == pdFALSE )
    {
        /* This is in incoming packet. If the CRC is correct, it should be zero. */
        if( pxSet->usChecksum == 0U )
        {
            pxSet->usChecksum = ( uint16_t ) ipCORRECT_CRC;
        }
    }
    else
    {
        if( ( pxSet->usChecksum == 0U ) && ( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_UDP ) )
        {
            /* In case of UDP, a calculated checksum of 0x0000 is transmitted
             * as 0xffff. A value of zero would mean that the checksum is not used. */
            pxSet->usChecksum = ( uint16_t ) 0xffffu;
        }
    }

    pxSet->usChecksum = FreeRTOS_htons( pxSet->usChecksum );
}
/*-----------------------------------------------------------*/

/** @brief For outgoing packets, set the checksum in the packet,
 *        for incoming packets: show logging in case an error occurred.
 * @param[in] xOutgoingPacket: Non-zero if this is an outgoing packet.
 * @param[in] pucEthernetBuffer: The buffer containing the packet.
 * @param[in] uxBufferLength: the total number of bytes received, or the number of bytes written
 * @param[in] pxSet: A struct describing this packet.
 */
static void prvChecksumProtocolSetChecksum( BaseType_t xOutgoingPacket,
                                            const uint8_t * pucEthernetBuffer,
                                            size_t uxBufferLength,
                                            struct xPacketSummary * pxSet )
{
    if( xOutgoingPacket != pdFALSE )
    {
        *( pxSet->pusChecksum ) = pxSet->usChecksum;
    }

    #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
        else if( ( xOutgoingPacket == pdFALSE ) && ( pxSet->usChecksum != ipCORRECT_CRC ) )
        {
            uint16_t usGot, usCalculated;
            usGot = *pxSet->pusChecksum;
            usCalculated = ~usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, pdTRUE );
            FreeRTOS_debug_printf( ( "usGenerateProtocolChecksum[%s]: len %d ID %04X: from %xip to %xip cal %04X got %04X\n",
                                     pxSet->pcType,
                                     pxSet->usProtocolBytes,
                                     FreeRTOS_ntohs( pxSet->pxIPPacket->xIPHeader.usIdentification ),
                                     ( unsigned ) FreeRTOS_ntohl( pxSet->pxIPPacket->xIPHeader.ulSourceIPAddress ),
                                     ( unsigned ) FreeRTOS_ntohl( pxSet->pxIPPacket->xIPHeader.ulDestinationIPAddress ),
                                     FreeRTOS_ntohs( usCalculated ),
                                     FreeRTOS_ntohs( usGot ) ) );
        }
        else
        {
            /* This is an incoming packet and it doesn't need debug logging. */
        }
    #else /* if ( ipconfigHAS_DEBUG_PRINTF != 0 ) */
        /* Mention parameters that are not used by the function. */
        ( void ) uxBufferLength;
        ( void ) pucEthernetBuffer;
    #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */
}
/*-----------------------------------------------------------*/

/**
 * @brief Generate or check the protocol checksum of the data sent in the first parameter.
 *        At the same time, the length of the packet and the length of the different layers
 *        will be checked.
 *
 * @param[in] pucEthernetBuffer: The Ethernet buffer for which the checksum is to be calculated
 *                               or checked.  'pucEthernetBuffer' is now non-const because the
 *                               function will set the checksum fields, in case 'xOutgoingPacket'
 *                               is pdTRUE.
 * @param[in] uxBufferLength: the total number of bytes received, or the number of bytes written
 *                            in the packet buffer.
 * @param[in] xOutgoingPacket: Whether this is an outgoing packet or not.
 *
 * @return When xOutgoingPacket is false: the error code can be either: ipINVALID_LENGTH,
 *         ipUNHANDLED_PROTOCOL, ipWRONG_CRC, or ipCORRECT_CRC.
 *         When xOutgoingPacket is true: either ipINVALID_LENGTH or ipCORRECT_CRC.
 */
uint16_t usGenerateProtocolChecksum( uint8_t * pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    struct xPacketSummary xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );

    DEBUG_DECLARE_TRACE_VARIABLE( BaseType_t, xLocation, 0 );

    #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
        {
            xSet.pcType = "???";
        }
    #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */

    /* Introduce a do-while loop to allow use of break statements.
     * Note: MISRA prohibits use of 'goto', thus replaced with breaks. */
    do
    {
        BaseType_t xResult;

        /* Parse the packet length. */
        xSet.pxIPPacket = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( IPPacket_t, pucEthernetBuffer );

        #if ( ipconfigUSE_IPv6 != 0 )
            xSet.pxIPPacket_IPv6 = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( IPHeader_IPv6_t, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );

            if( xSet.pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
            {
                xResult = prvChecksumIPv6Checks( pucEthernetBuffer, uxBufferLength, &( xSet ) );

                if( xResult != 0 )
                {
                    DEBUG_SET_TRACE_VARIABLE( xLocation, xResult );
                    break;
                }
            }
            else
        #endif /* ( ipconfigUSE_IPv6 != 0 ) */
        {
            xResult = prvChecksumIPv4Checks( pucEthernetBuffer, uxBufferLength, &( xSet ) );

            if( xResult != 0 )
            {
                DEBUG_SET_TRACE_VARIABLE( xLocation, xResult );
                break;
            }
        }

        {
            xResult = prvChecksumProtocolChecks( uxBufferLength, &( xSet ) );

            if( xResult != 0 )
            {
                DEBUG_SET_TRACE_VARIABLE( xLocation, xResult );
                break;
            }
        }

        /* The protocol and checksum field have been identified. Check the direction
         * of the packet. */
        if( xOutgoingPacket != pdFALSE )
        {
            /* This is an outgoing packet. Before calculating the checksum, set it
             * to zero. */
            *( xSet.pusChecksum ) = 0U;
        }
        else if( ( *( xSet.pusChecksum ) == 0U ) && ( xSet.ucProtocol == ( uint8_t ) ipPROTOCOL_UDP ) )
        {
            #if ( ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS == 0 )
                {
                    /* Sender hasn't set the checksum, drop the packet because
                     * ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS is not set. */
                    xSet.usChecksum = ipWRONG_CRC;
                }
            #else /* if ( ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS == 0 ) */
                {
                    /* Sender hasn't set the checksum, no use to calculate it. */
                    xSet.usChecksum = ipCORRECT_CRC;
                }
            #endif /* if ( ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS == 0 ) */
            DEBUG_SET_TRACE_VARIABLE( xLocation, 12 );
            break;
        }
        else
        {
            /* This is an incoming packet, not being an UDP packet without a checksum. */
        }

        xResult = prvChecksumProtocolMTUCheck( &( xSet ) );

        if( xResult != 0 )
        {
            DEBUG_SET_TRACE_VARIABLE( xLocation, xResult );
            break;
        }

        /* Do the actual calculations. */
        prvChecksumProtocolCalculate( xOutgoingPacket, pucEthernetBuffer, &( xSet ) );

        /* For outgoing packets, set the checksum in the packet,
         * for incoming packets: show logging in case an error occurred. */
        prvChecksumProtocolSetChecksum( xOutgoingPacket, pucEthernetBuffer, uxBufferLength, &( xSet ) );
    } while( ipFALSE_BOOL );

    #if ( ipconfigHAS_PRINTF == 1 )
        if( xLocation != 0 )
        {
            FreeRTOS_printf( ( "CRC error: %04x location %ld\n", xSet.usChecksum, xLocation ) );
        }
    #endif /* ( ipconfigHAS_PRINTF == 1 ) */

    return xSet.usChecksum;
}
/*-----------------------------------------------------------*/

/**
 * @brief Calculates the 16-bit checksum of an array of bytes.
 *        About the arguments:
 *          ulSum: This argument provides a value to initialise the progressive summation
 *          of the header's values to. It is often 0, but protocols like TCP or UDP
 *          can have pseudo-header fields which need to be included in the checksum.
 *
 *          pucNextData: This argument contains the address of the first byte which this
 *          method should process. The method's memory iterator is initialised to this value.
 *
 *          uxDataLengthBytes: This argument contains the number of bytes that this method
 *          should process.
 * @param[in] usSum: The initial sum, obtained from earlier data.
 * @param[in] pucNextData: The actual data.
 * @param[in] uxByteCount: The number of bytes.
 *
 * @return The 16-bit one's complement of the one's complement sum of all 16-bit
 *         words in the buffer.
 */
uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
    uint32_t ulAccum = FreeRTOS_htons( usSum );
    const uint16_t * pusPointer;
    const size_t uxUnrollCount = 16U;
    const uint8_t * pucData = pucNextData;
    uintptr_t uxBufferAddress;
    BaseType_t xUnaligned = pdFALSE;
    uint16_t usTerm = 0U;
    size_t uxBytesLeft = uxByteCount;

    if( uxBytesLeft >= 1U )
    {
        /* Transform a pointer to a numeric value, in order to determine
         * the alignment. */
        uxBufferAddress = ( uintptr_t ) pucData;

        if( ( uxBufferAddress & 1U ) != 0U )
        {
            ulAccum = ( ( ulAccum & 0xffU ) << 8 ) | ( ( ulAccum & 0xff00U ) >> 8 );
            usTerm = pucData[ 0 ];
            usTerm = FreeRTOS_htons( usTerm );
            /* Now make pucData 16-bit aligned. */
            uxBufferAddress++;
            /* One byte has been summed. */
            uxBytesLeft--;
            xUnaligned = pdTRUE;
        }

        /* The alignment of 'pucData' has just been tested and corrected
         * when necessary.
         */
        pusPointer = ( const uint16_t * ) uxBufferAddress;

        /* Sum 'uxUnrollCount' shorts in each loop. */
        while( uxBytesLeft >= ( sizeof( *pusPointer ) * uxUnrollCount ) )
        {
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );
            ulAccum += *( pusPointer++ );

            uxBytesLeft -= sizeof( *pusPointer ) * uxUnrollCount;
        }

        /* Between 0 and 7 shorts might be left. */
        while( uxBytesLeft >= sizeof( *pusPointer ) )
        {
            ulAccum += *( pusPointer++ );
            uxBytesLeft -= sizeof( *pusPointer );
        }

        /* A single byte may be left. */
        if( uxBytesLeft == 1U )
        {
            usTerm |= ( *pusPointer ) & FreeRTOS_htons( ( ( uint16_t ) 0xFF00U ) );
        }

        ulAccum += usTerm;

        /* Add the carry bits. */
        while( ( ulAccum >> 16 ) != 0U )
        {
            ulAccum = ( ulAccum & 0xffffU ) + ( ulAccum >> 16 );
        }

        if( xUnaligned == pdTRUE )
        {
            /* Quite unlikely, but pucNextData might be non-aligned, which would
            * mean that a checksum is calculated starting at an odd position. */
            ulAccum = ( ( ulAccum & 0xffU ) << 8 ) | ( ( ulAccum & 0xff00U ) >> 8 );
        }
    }

    /* The high bits are all zero now. */
    return FreeRTOS_ntohs( ( uint16_t ) ulAccum );
}
/*-----------------------------------------------------------*/

/* This function is used in other files, has external linkage e.g. in
 * FreeRTOS_DNS.c. Not to be made static. */

/**
 * @brief Send the Ethernet frame after checking for some conditions.
 *
 * @param[in,out] pxNetworkBuffer: The network buffer which is to be sent.
 * @param[in] xReleaseAfterSend: Whether this network buffer is to be released or not.
 */
void vReturnEthernetFrame( NetworkBufferDescriptor_t * pxNetworkBuffer,
                           BaseType_t xReleaseAfterSend )
{
    IPPacket_t * pxIPPacket;
/* memcpy() helper variables for MISRA Rule 21.15 compliance*/
    const void * pvCopySource;
    void * pvCopyDest;

    #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
        NetworkBufferDescriptor_t * pxNewBuffer;
    #endif

    #if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES )
        {
            if( pxNetworkBuffer->xDataLength < ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES )
            {
                BaseType_t xIndex;

                FreeRTOS_printf( ( "vReturnEthernetFrame: length %u\n", ( unsigned ) pxNetworkBuffer->xDataLength ) );

                for( xIndex = ( BaseType_t ) pxNetworkBuffer->xDataLength; xIndex < ( BaseType_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES; xIndex++ )
                {
                    pxNetworkBuffer->pucEthernetBuffer[ xIndex ] = 0U;
                }

                pxNetworkBuffer->xDataLength = ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES;
            }
        }
    #endif /* if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES ) */

    #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
        if( xReleaseAfterSend == pdFALSE )
        {
            pxNewBuffer = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, pxNetworkBuffer->xDataLength );

            if( pxNewBuffer != NULL )
            {
                xReleaseAfterSend = pdTRUE;
                /* Want no rounding up. */
                pxNewBuffer->xDataLength = pxNetworkBuffer->xDataLength;
            }

            pxNetworkBuffer = pxNewBuffer;
        }

        if( pxNetworkBuffer != NULL )
    #endif /* if ( ipconfigZERO_COPY_TX_DRIVER != 0 ) */
    {
        pxIPPacket = ipCAST_PTR_TO_TYPE_PTR( IPPacket_t, pxNetworkBuffer->pucEthernetBuffer );

        /* Send! */
        if( pxNetworkBuffer->pxEndPoint == NULL )
        {
            /* _HT_ I wonder if this ad-hoc search of an end-point it necessary. */
            FreeRTOS_printf( ( "vReturnEthernetFrame: No pxEndPoint yet for %lxip?\n", FreeRTOS_ntohl( pxIPPacket->xIPHeader.ulDestinationIPAddress ) ) );
            #if ( ipconfigUSE_IPv6 != 0 )
                if( ( ipCAST_PTR_TO_TYPE_PTR( EthernetHeader_t, pxNetworkBuffer->pucEthernetBuffer ) )->usFrameType == ipIPv6_FRAME_TYPE )
                {
                    /* To do */
                }
                else
            #endif /* ipconfigUSE_IPv6 */
            {
                pxNetworkBuffer->pxEndPoint = FreeRTOS_FindEndPointOnNetMask( pxIPPacket->xIPHeader.ulDestinationIPAddress, 7 );
            }
        }

        if( pxNetworkBuffer->pxEndPoint != NULL )
        {
            NetworkInterface_t * pxInterface = pxNetworkBuffer->pxEndPoint->pxNetworkInterface; /*_RB_ Why not use the pxNetworkBuffer->pxNetworkInterface directly? */

            /* Swap source and destination MAC addresses. */
            pvCopySource = &( pxIPPacket->xEthernetHeader.xSourceAddress );
            pvCopyDest = &( pxIPPacket->xEthernetHeader.xDestinationAddress );
            ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( pxIPPacket->xEthernetHeader.xDestinationAddress ) );

            pvCopySource = pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes;
            pvCopyDest = &( pxIPPacket->xEthernetHeader.xSourceAddress );
            ( void ) memcpy( pvCopyDest, pvCopySource, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
            /* Send! */
            iptraceNETWORK_INTERFACE_OUTPUT( pxNetworkBuffer->xDataLength, pxNetworkBuffer->pucEthernetBuffer );
            ( void ) pxInterface->pfOutput( pxInterface, pxNetworkBuffer, xReleaseAfterSend );
        }
    }
}
/*-----------------------------------------------------------*/


#if ( ipconfigHAS_PRINTF != 0 )

    #ifndef ipMONITOR_MAX_HEAP

/* As long as the heap has more space than e.g. 1 MB, there
 * will be no messages. */
        #define ipMONITOR_MAX_HEAP    ( 1024U * 1024U )
    #endif /* ipMONITOR_MAX_HEAP */

    #ifndef ipMONITOR_PERCENTAGE_90
        /* Make this number lower to get less logging messages. */
        #define ipMONITOR_PERCENTAGE_90    ( 90U )
    #endif

    #define ipMONITOR_PERCENTAGE_100       ( 100U )

/**
 * @brief A function that monitors a three resources: the heap, the space in the message
 *        queue of the IP-task, the number of available network buffer descriptors.
 */
    void vPrintResourceStats( void )
    {
        static UBaseType_t uxLastMinBufferCount = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
        static size_t uxMinLastSize = 0u;
        UBaseType_t uxCurrentBufferCount;
        size_t uxMinSize;

        /* When setting up and testing a project with FreeRTOS+TCP, it is
         * can be helpful to monitor a few resources: the number of network
         * buffers and the amount of available heap.
         * This function will issue some logging when a minimum value has
         * changed. */
        uxCurrentBufferCount = uxGetMinimumFreeNetworkBuffers();

        if( uxLastMinBufferCount > uxCurrentBufferCount )
        {
            /* The logging produced below may be helpful
             * while tuning +TCP: see how many buffers are in use. */
            uxLastMinBufferCount = uxCurrentBufferCount;
            FreeRTOS_printf( ( "Network buffers: %lu lowest %lu\n",
                               uxGetNumberOfFreeNetworkBuffers(),
                               uxCurrentBufferCount ) );
        }

        uxMinSize = xPortGetMinimumEverFreeHeapSize();

        if( uxMinLastSize == 0U )
        {
            /* Probably the first time this function is called. */
            uxMinLastSize = uxMinSize;
        }
        else if( uxMinSize >= ipMONITOR_MAX_HEAP )
        {
            /* There is more than enough heap space. No need for logging. */
        }
        /* Write logging if there is a 10% decrease since the last time logging was written. */
        else if( ( uxMinLastSize * ipMONITOR_PERCENTAGE_90 ) > ( uxMinSize * ipMONITOR_PERCENTAGE_100 ) )
        {
            uxMinLastSize = uxMinSize;
            FreeRTOS_printf( ( "Heap: current %d lowest %u\n", xPortGetFreeHeapSize(), uxMinSize ) );
        }
        else
        {
            /* Nothing to log. */
        }

        #if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
            {
                static UBaseType_t uxLastMinQueueSpace = 0;
                UBaseType_t uxCurrentCount = 0u;

                uxCurrentCount = uxGetMinimumIPQueueSpace();

                if( uxLastMinQueueSpace != uxCurrentCount )
                {
                    /* The logging produced below may be helpful
                     * while tuning +TCP: see how many buffers are in use. */
                    uxLastMinQueueSpace = uxCurrentCount;
                    FreeRTOS_printf( ( "Queue space: lowest %lu\n", uxCurrentCount ) );
                }
            }
        #endif /* ipconfigCHECK_IP_QUEUE_SPACE */
    }
#endif /* ( ipconfigHAS_PRINTF != 0 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Returns the IP address of the NIC.
 *
 * @return The IP address of the NIC.
 */
uint32_t FreeRTOS_GetIPAddress( void )
{
    NetworkEndPoint_t * pxEndPoint;
    uint32_t ulIPAddress;

    pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

    #if ( ipconfigUSE_IPv6 != 0 )
        for( ;
             pxEndPoint != NULL;
             pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
        {
            if( ENDPOINT_IS_IPv4( pxEndPoint ) )
            {
                break;
            }
        }
    #endif /* ( ipconfigUSE_IPv6 != 0 ) */

    /* Returns the IP address of the NIC. */
    if( pxEndPoint == NULL )
    {
        ulIPAddress = 0U;
    }
    else if( pxEndPoint->ipv4_settings.ulIPAddress != 0U )
    {
        ulIPAddress = pxEndPoint->ipv4_settings.ulIPAddress;
    }
    else
    {
        ulIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    }

    return ulIPAddress;
}
/*-----------------------------------------------------------*/

#if ( ipconfigCOMPATIBLE_WITH_SINGLE != 0 )

/*
 * The helper functions here below assume that there is a single
 * interface and a single end-point (ipconfigCOMPATIBLE_WITH_SINGLE)
 */

/**
 * @brief Set the IP-address of device.
 *
 * @param ulIPAddress: The new IP-address.
 */
    void FreeRTOS_SetIPAddress( uint32_t ulIPAddress )
    {
        /* Sets the IP address of the NIC. */
        NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

        if( pxEndPoint != NULL )
        {
            pxEndPoint->ipv4_settings.ulIPAddress = ulIPAddress;
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Get the gateway address of the subnet.
 *
 * @return The IP-address of the gateway, zero if a gateway is
 *         not used/defined.
 */
    uint32_t FreeRTOS_GetGatewayAddress( void )
    {
        uint32_t ulIPAddress = 0U;
        NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

        if( pxEndPoint != NULL )
        {
            ulIPAddress = pxEndPoint->ipv4_settings.ulGatewayAddress;
        }

        return ulIPAddress;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Get the DNS server address.
 *
 * @return The IP address of the DNS server.
 */
    uint32_t FreeRTOS_GetDNSServerAddress( void )
    {
        uint32_t ulIPAddress = 0U;
        NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

        if( pxEndPoint != NULL )
        {
            ulIPAddress = pxEndPoint->ipv4_settings.ulDNSServerAddresses[ 0 ];
        }

        return ulIPAddress;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Get the netmask for the subnet.
 *
 * @return The 32 bit netmask for the subnet.
 */
    uint32_t FreeRTOS_GetNetmask( void )
    {
        uint32_t ulIPAddress = 0U;
        NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

        if( pxEndPoint != NULL )
        {
            ulIPAddress = pxEndPoint->ipv4_settings.ulNetMask;
        }

        return ulIPAddress;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Update the MAC address.
 *
 * @param[in] ucMACAddress: the MAC address to be set.
 */
    void FreeRTOS_UpdateMACAddress( const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] )
    {
        NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

        if( pxEndPoint != NULL )
        {
            /* Copy the MAC address at the start of the default packet header fragment. */
            ( void ) memcpy( pxEndPoint->xMACAddress.ucBytes, ( const void * ) ucMACAddress, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Get the MAC address.
 *
 * @return The pointer to MAC address.
 */
    const uint8_t * FreeRTOS_GetMACAddress( void )
    {
        const uint8_t * pucReturn = NULL;
        NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

        if( pxEndPoint != NULL )
        {
            /* Copy the MAC address at the start of the default packet header fragment. */
            pucReturn = pxEndPoint->xMACAddress.ucBytes;
        }

        return pucReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Set the netmask for the subnet.
 *
 * @param[in] ulNetmask: The 32 bit netmask of the subnet.
 */
    void FreeRTOS_SetNetmask( uint32_t ulNetmask )
    {
        NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

        if( pxEndPoint != NULL )
        {
            pxEndPoint->ipv4_settings.ulNetMask = ulNetmask;
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Set the gateway address.
 *
 * @param[in] ulGatewayAddress: The gateway address.
 */
    void FreeRTOS_SetGatewayAddress( uint32_t ulGatewayAddress )
    {
        NetworkEndPoint_t * pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

        if( pxEndPoint != NULL )
        {
            pxEndPoint->ipv4_settings.ulGatewayAddress = ulGatewayAddress;
        }
    }
/*-----------------------------------------------------------*/
#endif /* ( ipconfigCOMPATIBLE_WITH_SINGLE != 0 ) */

#if ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 ) || ( ipconfigUSE_DHCPv6 == 1 )

/**
 * @brief Enable or disable the DHCP/DHCPv6/RA timer.
 *
 * @param[in] pxEndPoint: The end-point that needs to acquire an IP-address.
 * @param[in] xEnableState: pdTRUE if the timer must be enabled, pdFALSE otherwise.
 */
    void vIPSetDHCP_RATimerEnableState( struct xNetworkEndPoint * pxEndPoint,
                                        BaseType_t xEnableState )
    {
        FreeRTOS_printf( ( "vIPSetDHCP_RATimerEnableState: %s\n", ( xEnableState != 0 ) ? "On" : "Off" ) );

        /* 'xDHCP_RATimer' is shared between DHCP (IPv4) and RA/SLAAC (IPv6). */
        if( xEnableState != 0 )
        {
            pxEndPoint->xDHCP_RATimer.bActive = pdTRUE_UNSIGNED;
        }
        else
        {
            pxEndPoint->xDHCP_RATimer.bActive = pdFALSE_UNSIGNED;
        }
    }
#endif /* ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 )

/**
 * @brief Set the reload time of the DHCP/DHCPv6/RA timer.
 *
 * @param[in] pxEndPoint: The end-point that needs to acquire an IP-address.
 * @param[in] uxClockTicks: The number of clock-ticks after which the timer should expire.
 */
    void vIPReloadDHCP_RATimer( struct xNetworkEndPoint * pxEndPoint,
                                TickType_t uxClockTicks )
    {
        FreeRTOS_printf( ( "vIPReloadDHCP_RATimer: %lu\n", uxClockTicks ) );
        prvIPTimerReload( &( pxEndPoint->xDHCP_RATimer ), uxClockTicks );
    }
#endif /* ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigDNS_USE_CALLBACKS == 1 )

/**
 * @brief Enable/disable the DNS timer.
 *
 * @param[in] xEnableState: pdTRUE - enable timer; pdFALSE - disable timer.
 */
    void vIPSetDnsTimerEnableState( BaseType_t xEnableState )
    {
        if( xEnableState != 0 )
        {
            xDNSTimer.bActive = pdTRUE;
        }
        else
        {
            xDNSTimer.bActive = pdFALSE;
        }
    }

#endif /* ipconfigUSE_DHCP */
/*-----------------------------------------------------------*/

#if ( ipconfigDNS_USE_CALLBACKS != 0 )

/**
 * @brief Reload the DNS timer.
 *
 * @param[in] ulCheckTime: The reload value.
 */
    void vIPReloadDNSTimer( uint32_t ulCheckTime )
    {
        prvIPTimerReload( &xDNSTimer, ulCheckTime );
    }
#endif /* ipconfigDNS_USE_CALLBACKS != 0 */
/*-----------------------------------------------------------*/

/**
 * @brief Returns whether the IP task is ready.
 *
 * @return pdTRUE if IP task is ready, else pdFALSE.
 */
BaseType_t xIPIsNetworkTaskReady( void )
{
    return xIPTaskInitialised;
}
/*-----------------------------------------------------------*/

/**
 * @brief Returns whether all end-points are up.
 *
 * @return pdTRUE if all defined end-points are up.
 */
BaseType_t FreeRTOS_IsNetworkUp( void )
{
    /* IsNetworkUp() is kept for backward compatibility. */
    return FreeRTOS_IsEndPointUp( NULL );
}
/*-----------------------------------------------------------*/

/**
 * @brief Returns whether a particular end-point is up.
 *
 * @return pdTRUE if a particular end-points is up.
 */
BaseType_t FreeRTOS_IsEndPointUp( const struct xNetworkEndPoint * pxEndPoint )
{
    BaseType_t xReturn;

    if( pxEndPoint != NULL )
    {
        /* Is this particular end-point up? */
        xReturn = ( BaseType_t ) pxEndPoint->bits.bEndPointUp;
    }
    else
    {
        /* Are all end-points up? */
        xReturn = FreeRTOS_AllEndPointsUp( NULL );
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Return pdTRUE if all end-points belonging to a given interface are up.  When
 *        pxInterface is null, all end-points will be checked.
 *
 * @param[in] pxInterface: The network interface of interest, or NULL to check all end-points.
 *
 * @return pdTRUE if all end-points are up, otherwise pdFALSE;
 */
BaseType_t FreeRTOS_AllEndPointsUp( const struct xNetworkInterface * pxInterface )
{
    BaseType_t xResult = pdTRUE;
    NetworkEndPoint_t * pxEndPoint = pxNetworkEndPoints;

    while( pxEndPoint != NULL )
    {
        if( ( pxInterface == NULL ) ||
            ( pxEndPoint->pxNetworkInterface == pxInterface ) )

        {
            if( pxEndPoint->bits.bEndPointUp == pdFALSE_UNSIGNED )
            {
                xResult = pdFALSE;
                break;
            }
        }

        pxEndPoint = pxEndPoint->pxNext;
    }

    return xResult;
}
/*-----------------------------------------------------------*/

#if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
    UBaseType_t uxGetMinimumIPQueueSpace( void )
    {
        return uxQueueMinimumSpace;
    }
#endif
/*-----------------------------------------------------------*/

/**
 * @brief Utility function: Convert error number to a human readable
 *        string. Declaration in FreeRTOS_errno_TCP.h.
 *
 * @param[in] xErrnum: The error number.
 * @param[in] pcBuffer: Buffer big enough to be filled with the human readable message.
 * @param[in] uxLength: Maximum length of the buffer.
 *
 * @return The buffer filled with human readable error string.
 */
const char * FreeRTOS_strerror_r( BaseType_t xErrnum,
                                  char * pcBuffer,
                                  size_t uxLength )
{
    const char * pcName;

    switch( xErrnum )
    {
        case pdFREERTOS_ERRNO_EADDRINUSE:
            pcName = "EADDRINUSE";
            break;

        case pdFREERTOS_ERRNO_ENOMEM:
            pcName = "ENOMEM";
            break;

        case pdFREERTOS_ERRNO_EADDRNOTAVAIL:
            pcName = "EADDRNOTAVAIL";
            break;

        case pdFREERTOS_ERRNO_ENOPROTOOPT:
            pcName = "ENOPROTOOPT";
            break;

        case pdFREERTOS_ERRNO_EBADF:
            pcName = "EBADF";
            break;

        case pdFREERTOS_ERRNO_ENOSPC:
            pcName = "ENOSPC";
            break;

        case pdFREERTOS_ERRNO_ECANCELED:
            pcName = "ECANCELED";
            break;

        case pdFREERTOS_ERRNO_ENOTCONN:
            pcName = "ENOTCONN";
            break;

        case pdFREERTOS_ERRNO_EINPROGRESS:
            pcName = "EINPROGRESS";
            break;

        case pdFREERTOS_ERRNO_EOPNOTSUPP:
            pcName = "EOPNOTSUPP";
            break;

        case pdFREERTOS_ERRNO_EINTR:
            pcName = "EINTR";
            break;

        case pdFREERTOS_ERRNO_ETIMEDOUT:
            pcName = "ETIMEDOUT";
            break;

        case pdFREERTOS_ERRNO_EINVAL:
            pcName = "EINVAL";
            break;

        case pdFREERTOS_ERRNO_EWOULDBLOCK:
            pcName = "EWOULDBLOCK";
            break; /* same as EAGAIN */

        case pdFREERTOS_ERRNO_EISCONN:
            pcName = "EISCONN";
            break;

        default:

            /* As all defined values are enumerated,
             * default should not be reached. */
            pcName = "UNKNOWN ERRNO";
            break;
    }

    if( uxLength > 0U )
    {
        ( void ) strncpy( pcBuffer, pcName, uxLength - 1U );
        /* Make sure the result is null-terminated. */
        pcBuffer[ uxLength - 1U ] = '\0';
    }

    return pcBuffer;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the highest value of two int32's.
 * @param[in] a: the first value.
 * @param[in] b: the second value.
 * @return The highest of the two values.
 */
int32_t FreeRTOS_max_int32( int32_t a,
                            int32_t b )
{
    return ( a >= b ) ? a : b;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the highest value of two uint32_t's.
 * @param[in] a: the first value.
 * @param[in] b: the second value.
 * @return The highest of the two values.
 */
uint32_t FreeRTOS_max_uint32( uint32_t a,
                              uint32_t b )
{
    return ( a >= b ) ? a : b;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the highest value of two variables of type size_t.
 * @param[in] a: the first value.
 * @param[in] b: the second value.
 * @return The highest of the two values.
 */
size_t FreeRTOS_max_size_t( size_t a,
                            size_t b )
{
    return ( a >= b ) ? a : b;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the lowest value of two int32_t's.
 * @param[in] a: the first value.
 * @param[in] b: the second value.
 * @return The lowest of the two values.
 */
int32_t FreeRTOS_min_int32( int32_t a,
                            int32_t b )
{
    return ( a <= b ) ? a : b;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the lowest value of two uint32_t's.
 * @param[in] a: the first value.
 * @param[in] b: the second value.
 * @return The lowest of the two values.
 */
uint32_t FreeRTOS_min_uint32( uint32_t a,
                              uint32_t b )
{
    return ( a <= b ) ? a : b;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the lowest value of two variables of type size_t.
 * @param[in] a: the first value.
 * @param[in] b: the second value.
 * @return The lowest of the two values.
 */
size_t FreeRTOS_min_size_t( size_t a,
                            size_t b )
{
    return ( a <= b ) ? a : b;
}
/*-----------------------------------------------------------*/

/**
 * @brief Round-up a number to a multiple of 'd'.
 * @param[in] a: the first value.
 * @param[in] d: the second value.
 * @return A multiple of d.
 */
uint32_t FreeRTOS_round_up( uint32_t a,
                            uint32_t d )
{
    return d * ( ( a + d - 1U ) / d );
}
/*-----------------------------------------------------------*/

/**
 * @defgroup CastingMacroFunctions Utility casting functions
 * @brief These functions are used to cast various types of pointers
 *        to other types. A major use would be to map various
 *        headers/packets on to the incoming byte stream.
 *
 * @param[in] pvArgument: Pointer to be casted to another type.
 *
 * @retval Casted pointer will be returned without violating MISRA
 *         rules.
 * @{
 */

/**
 * @brief Cast a given pointer to EthernetHeader_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( EthernetHeader_t )
{
    return ( EthernetHeader_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to EthernetHeader_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( EthernetHeader_t )
{
    return ( const EthernetHeader_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given pointer to IPHeader_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( IPHeader_t )
{
    return ( IPHeader_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to IPHeader_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( IPHeader_t )
{
    return ( const IPHeader_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given pointer to ICMPHeader_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( ICMPHeader_t )
{
    return ( ICMPHeader_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to ICMPHeader_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( ICMPHeader_t )
{
    return ( const ICMPHeader_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given pointer to ARPPacket_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( ARPPacket_t )
{
    return ( ARPPacket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to ARPPacket_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( ARPPacket_t )
{
    return ( const ARPPacket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given pointer to IPPacket_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( IPPacket_t )
{
    return ( IPPacket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to IPPacket_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( IPPacket_t )
{
    return ( const IPPacket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given pointer to ICMPPacket_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( ICMPPacket_t )
{
    return ( ICMPPacket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given pointer to UDPPacket_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( UDPPacket_t )
{
    return ( UDPPacket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to UDPPacket_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( UDPPacket_t )
{
    return ( const UDPPacket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given pointer to TCPPacket_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( TCPPacket_t )
{
    return ( TCPPacket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to TCPPacket_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( TCPPacket_t )
{
    return ( const TCPPacket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )

/**
 * @brief Cast a given pointer to TCPPacket_IPv6_t type pointer.
 */
    ipDECL_CAST_PTR_FUNC_FOR_TYPE( TCPPacket_IPv6_t )
    {
        return ( TCPPacket_IPv6_t * ) pvArgument;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to TCPPacket_IPv6_t type pointer.
 */
    ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( TCPPacket_IPv6_t )
    {
        return ( const TCPPacket_IPv6_t * ) pvArgument;
    }
    /*-----------------------------------------------------------*/
#endif /* if ( ipconfigUSE_IPv6 != 0 ) */

/**
 * @brief Cast a given pointer to ProtocolPacket_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( ProtocolPacket_t )
{
    return ( ProtocolPacket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to ProtocolPacket_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( ProtocolPacket_t )
{
    return ( const ProtocolPacket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given pointer to ProtocolHeaders_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( ProtocolHeaders_t )
{
    return ( ProtocolHeaders_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to ProtocolHeaders_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( ProtocolHeaders_t )
{
    return ( const ProtocolHeaders_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given pointer to FreeRTOS_Socket_t type pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( FreeRTOS_Socket_t )
{
    return ( FreeRTOS_Socket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to FreeRTOS_Socket_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( FreeRTOS_Socket_t )
{
    return ( const FreeRTOS_Socket_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )

/**
 * @brief Cast a given constant pointer to IPHeader_IPv6_t type pointer.
 */
    ipDECL_CAST_PTR_FUNC_FOR_TYPE( IPHeader_IPv6_t )
    {
        return ( IPHeader_IPv6_t * ) pvArgument;
    }

/**
 * @brief Cast a given pointer to IPHeader_IPv6_t type pointer.
 */
    ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( IPHeader_IPv6_t )
    {
        return ( const IPHeader_IPv6_t * ) pvArgument;
    }

/**
 * @brief Cast a given pointer to IPPacket_IPv6_t type pointer.
 */
    ipDECL_CAST_PTR_FUNC_FOR_TYPE( IPPacket_IPv6_t )
    {
        return ( IPPacket_IPv6_t * ) pvArgument;
    }

/**
 * @brief Cast a given constant pointer to IPPacket_IPv6_t type pointer.
 */
    ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( IPPacket_IPv6_t )
    {
        return ( const IPPacket_IPv6_t * ) pvArgument;
    }

/**
 * @brief Cast a given pointer to UDPPacket_IPv6_t type pointer.
 */
    ipDECL_CAST_PTR_FUNC_FOR_TYPE( UDPPacket_IPv6_t )
    {
        return ( UDPPacket_IPv6_t * ) pvArgument;
    }

/**
 * @brief Cast a given constant pointer to UDPPacket_IPv6_t type pointer.
 */
    ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( UDPPacket_IPv6_t )
    {
        return ( const UDPPacket_IPv6_t * ) pvArgument;
    }
#endif /* ( ipconfigUSE_IPv6 != 0 ) */

#if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 ) || ( ipconfigUSE_TCP == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )

/**
 * @brief Cast a given pointer to ListItem_t type pointer.
 */
    ipDECL_CAST_PTR_FUNC_FOR_TYPE( ListItem_t )
    {
        return ( ListItem_t * ) pvArgument;
    }
/*-----------------------------------------------------------*/
#endif /* ( ipconfigSUPPORT_SELECT_FUNCTION == 1 ) || ( ipconfigUSE_TCP == 1 ) */

/**
 * @brief Cast a given constant pointer to ListItem_t type pointer.
 */
ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( ListItem_t )
{
    return ( const ListItem_t * ) pvArgument;
}
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )

/**
 * @brief Cast a given pointer to SocketSelect_t type pointer.
 */
    ipDECL_CAST_PTR_FUNC_FOR_TYPE( SocketSelect_t )
    {
        return ( SocketSelect_t * ) pvArgument;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to SocketSelect_t type pointer.
 */
    ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( SocketSelect_t )
    {
        return ( const SocketSelect_t * ) pvArgument;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Cast a given pointer to SocketSelectMessage_t type pointer.
 */
    ipDECL_CAST_PTR_FUNC_FOR_TYPE( SocketSelectMessage_t )
    {
        return ( SocketSelectMessage_t * ) pvArgument;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Cast a given constant pointer to SocketSelectMessage_t type pointer.
 */
    ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE( SocketSelectMessage_t )
    {
        return ( const SocketSelectMessage_t * ) pvArgument;
    }
    /*-----------------------------------------------------------*/

#endif /* ( ipconfigSUPPORT_SELECT_FUNCTION == 1 ) */

/**
 * @brief Utility function to cast pointer of a type to pointer of type NetworkBufferDescriptor_t.
 *
 * @return The casted pointer.
 */
ipDECL_CAST_PTR_FUNC_FOR_TYPE( NetworkBufferDescriptor_t )
{
    return ( NetworkBufferDescriptor_t * ) pvArgument;
}
/*-----------------------------------------------------------*/
/* Mark the end of this group of functions. */
/** @} */

/**
 * @brief Convert character array (of size 4) to equivalent 32-bit value.
 *        It is assumed that the value in 'pucPtr' is stored in big endian.
 *        The result will be host-endian ( either big or little ).
 * @param[in] pucPtr: The character array.
 * @return 32-bit equivalent value extracted from the character array.
 *
 * @note Going by MISRA rules, these utility functions should not be defined
 *        if they are not being used anywhere. But their use depends on the
 *        application and hence these functions are defined unconditionally.
 */
uint32_t ulChar2u32( const uint8_t * pucPtr )
{
    return ( ( ( uint32_t ) pucPtr[ 0 ] ) << 24 ) |
           ( ( ( uint32_t ) pucPtr[ 1 ] ) << 16 ) |
           ( ( ( uint32_t ) pucPtr[ 2 ] ) << 8 ) |
           ( ( ( uint32_t ) pucPtr[ 3 ] ) );
}
/*-----------------------------------------------------------*/

/**
 * @brief Convert character array (of size 2) to equivalent 16-bit value.
 * @param[in] pucPtr: The character array.
 * @return 16-bit equivalent value extracted from the character array.
 *
 * @note Going by MISRA rules, these utility functions should not be defined
 *        if they are not being used anywhere. But their use depends on the
 *        application and hence these functions are defined unconditionally.
 */
uint16_t usChar2u16( const uint8_t * pucPtr )
{
    return ( uint16_t )
           ( ( ( ( uint32_t ) pucPtr[ 0 ] ) << 8 ) |
             ( ( ( uint32_t ) pucPtr[ 1 ] ) ) );
}

#if ( ipconfigUSE_IPv6 != 0 )

/**
 * @brief Get the size of the IP-header, by checking the type of the network buffer.
 * @param[in] pxNetworkBuffer: The network buffer.
 * @return The size of the corresponding IP-header.
 */
    size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        size_t uxResult;
        /* Map the buffer onto Ethernet Header struct for easy access to fields. */
        /* misra_c_2012_rule_11_3_violation */
        const EthernetHeader_t * pxHeader = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( EthernetHeader_t, pxNetworkBuffer->pucEthernetBuffer );

        if( pxHeader->usFrameType == ( uint16_t ) ipIPv6_FRAME_TYPE )
        {
            uxResult = ipSIZE_OF_IPv6_HEADER;
        }
        else
        {
            uxResult = ipSIZE_OF_IPv4_HEADER;
        }

        return uxResult;
    }
#else /* if ( ipconfigUSE_IPv6 != 0 ) */

/**
 * @brief Get the size of an IPv4-header, independent of the network buffer.
 * @param[in] pxNetworkBuffer: The network buffer ( ignored ).
 * @return The size of the corresponding IP-header.
 */
    size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        /* As this is IPv4-only code, the parameter 'pxNetworkBuffer' is not used. */
        ( void ) pxNetworkBuffer;

        return ipSIZE_OF_IPv4_HEADER;
    }
#endif /* if ( ipconfigUSE_IPv6 != 0 ) */

#if ( ipconfigUSE_IPv6 != 0 )

/**
 * @brief Get the size of the IP-header, by checking if the socket bIsIPv6 set.
 * @param[in] pxSocket: The socket.
 * @return The size of the corresponding IP-header.
 */
    size_t uxIPHeaderSizeSocket( const FreeRTOS_Socket_t * pxSocket )
    {
        size_t uxResult;

        if( ( pxSocket != NULL ) && ( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED ) )
        {
            uxResult = ipSIZE_OF_IPv6_HEADER;
        }
        else
        {
            uxResult = ipSIZE_OF_IPv4_HEADER;
        }

        return uxResult;
    }
#else /* if ( ipconfigUSE_IPv6 != 0 ) */

/**
 * @brief Get the size of an IPv4-header, independent of the socket setting.
 * @param[in] pxSocket: The socket ( ignored ).
 * @return The size of an IPv4-header.
 */
    size_t uxIPHeaderSizeSocket( const FreeRTOS_Socket_t * pxSocket )
    {
        /* As this is IPv4-only code, the parameter 'pxSocket' is not used. */
        ( void ) pxSocket;

        return ipSIZE_OF_IPv4_HEADER;
    }
#endif /* if ( ipconfigUSE_IPv6 != 0 ) */

/* Provide access to private members for verification. */
#ifdef FREERTOS_TCP_ENABLE_VERIFICATION
    #include "aws_freertos_ip_verification_access_ip_define.h"
#endif
