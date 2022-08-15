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
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ICMP.h"
#include "FreeRTOS_IP_Timers.h"
#include "FreeRTOS_IP_Utils.h"
#include "FreeRTOS_Sockets.h"
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

/** @brief Maximum time to wait for an ARP resolution while holding a packet. */
#ifndef ipARP_RESOLUTION_MAX_DELAY
    #define ipARP_RESOLUTION_MAX_DELAY    ( pdMS_TO_TICKS( 2000U ) )
#endif

#ifndef iptraceIP_TASK_STARTING
    #define iptraceIP_TASK_STARTING()    do {} while( ipFALSE_BOOL ) /**< Empty definition in case iptraceIP_TASK_STARTING is not defined. */
#endif

#if ( ( ipconfigUSE_TCP == 1 ) && !defined( ipTCP_TIMER_PERIOD_MS ) )
    /** @brief When initialising the TCP timer, give it an initial time-out of 1 second. */
    #define ipTCP_TIMER_PERIOD_MS    ( 1000U )
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

static void prvCallDHCP_RA_Handler( NetworkEndPoint_t * pxEndPoint );

static void prvIPTask_Initialise( void );

static void prvIPTask_WaitForEvent( IPStackEvent_t * pxReceivedEvent,
                                    TickType_t xNextIPSleep );

static void prvIPTask_HandleBindEvent( IPStackEvent_t * pxReceivedEvent );

#if ( ipconfigUSE_TCP == 1 )
    static void prvIPTask_HandleAcceptEvent( IPStackEvent_t * pxReceivedEvent );
#endif /* ( ipconfigUSE_TCP == 1 ) */

#if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
    static void prvIPTask_HandleSelectEvent( IPStackEvent_t * pxReceivedEvent );
#endif /* ( ipconfigSUPPORT_SELECT_FUNCTION == 1 ) */

static void prvIPTask_CheckPendingEvents( void );


/*-----------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )
    const struct xIPv6_Address in6addr_any = { 0 };
    const struct xIPv6_Address in6addr_loopback = { { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 } };
#endif

/*-----------------------------------------------------------*/

static void prvProcessIPEventsAndTimers( void );

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

/*
 * The network card driver has received a packet.  In the case that it is part
 * of a linked packet chain, walk through it to handle every message.
 */
static void prvHandleEthernetPacket( NetworkBufferDescriptor_t * pxBuffer );

/* Handle the 'eNetworkTxEvent': forward a packet from an application to the NIC. */
static void prvForwardTxPacket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                BaseType_t xReleaseAfterSend );

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

/** @brief Set to pdTRUE when the IP task is ready to start processing packets. */
static BaseType_t xIPTaskInitialised = pdFALSE;

#if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
    /** @brief Keep track of the lowest amount of space in 'xNetworkEventQueue'. */
    static UBaseType_t uxQueueMinimumSpace = ipconfigEVENT_QUEUE_LENGTH;
#endif

#if ( ipconfigUSE_IPv6 != 0 )
    /** @brief Handle the IPv6 extension headers. */
    static eFrameProcessingResult_t eHandleIPv6ExtensionHeaders( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                 BaseType_t xDoRemove );
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
    /* Just to prevent compiler warnings about unused parameters. */
    ( void ) pvParameters;

    prvIPTask_Initialise();

    FreeRTOS_debug_printf( ( "prvIPTask started\n" ) );

    /* Loop, processing IP events. */
    while( ipFOREVER() )
    {
        prvProcessIPEventsAndTimers();
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Process the events sent to the IP task and process the timers.
 */
static void prvProcessIPEventsAndTimers( void )
{
    IPStackEvent_t xReceivedEvent;
    TickType_t xNextIPSleep;

    ipconfigWATCHDOG_TIMER();

    /* Check the ARP, DHCP and TCP timers to see if there is any periodic
     * or timeout processing to perform. */
    vCheckNetworkTimers();

    /* Calculate the acceptable maximum sleep time. */
    xNextIPSleep = xCalculateSleepTime();

    prvIPTask_WaitForEvent( &( xReceivedEvent ), xNextIPSleep );

    switch( xReceivedEvent.eEventType )
    {
        case eNetworkDownEvent:
            /* Attempt to establish a connection. */
            prvProcessNetworkDownEvent( ( ( NetworkInterface_t * ) xReceivedEvent.pvData ) );
            break;

        case eNetworkRxEvent:

            /* The network hardware driver has received a new packet.  A
             * pointer to the received buffer is located in the pvData member
             * of the received event structure. */
            prvHandleEthernetPacket( ( ( NetworkBufferDescriptor_t * ) xReceivedEvent.pvData ) );
            break;

        case eNetworkTxEvent:

            /* Send a network packet. The ownership will  be transferred to
             * the driver, which will release it after delivery. */
            prvForwardTxPacket( ( ( NetworkBufferDescriptor_t * ) xReceivedEvent.pvData ), pdTRUE );
            break;

        case eARPTimerEvent:
            /* The ARP timer has expired, process the ARP cache. */
            vARPAgeCache();
            #if ( ipconfigUSE_IPv6 != 0 )
                vNDAgeCache();
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */
            break;

        case eSocketBindEvent:
            prvIPTask_HandleBindEvent( &( xReceivedEvent ) );
            break;

        case eSocketCloseEvent:

            /* The user API FreeRTOS_closesocket() has sent a message to the
             * IP-task to actually close a socket. This is handled in
             * vSocketClose().  As the socket gets closed, there is no way to
             * report back to the API, so the API won't wait for the result */
            ( void ) vSocketClose( ( ( FreeRTOS_Socket_t * ) xReceivedEvent.pvData ) );
            break;

        case eStackTxEvent:

            /* The network stack has generated a packet to send.  A
             * pointer to the generated buffer is located in the pvData
             * member of the received event structure. */
            vProcessGeneratedUDPPacket( ( ( NetworkBufferDescriptor_t * ) xReceivedEvent.pvData ) );
            break;

        case eDHCP_RA_Event:
            prvCallDHCP_RA_Handler( ( ( NetworkEndPoint_t * ) xReceivedEvent.pvData ) );
            break;

        case eSocketSelectEvent:

            /* FreeRTOS_select() has got unblocked by a socket event,
             * vSocketSelect() will check which sockets actually have an event
             * and update the socket field xSocketBits. */
            #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
                {
                    prvIPTask_HandleSelectEvent( &( xReceivedEvent ) );
                }
            #endif /* ( ipconfigSUPPORT_SELECT_FUNCTION == 1 ) */
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
                     * the next time vCheckNetworkTimers() is called. */
                    vIPSetTCPTimerEnableState( pdTRUE );
                }
            #endif /* ipconfigUSE_TCP */
            break;

        case eTCPAcceptEvent:

            /* The API FreeRTOS_accept() was called, the IP-task will now
             * check if the listening socket (communicated in pvData) actually
             * received a new connection. */

            #if ( ipconfigUSE_TCP == 1 )
                {
                    prvIPTask_HandleAcceptEvent( &( xReceivedEvent ) );
                }
            #endif
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

    prvIPTask_CheckPendingEvents();
}



/**
 * @brief Helper function for prvIPTask, it does the first initialisations
 *        at start-up. No parameters, no return type.
 */
static void prvIPTask_Initialise( void )
{
    NetworkInterface_t * pxInterface;

    /* A possibility to set some additional task properties. */
    iptraceIP_TASK_STARTING();

    /* Generate a dummy message to say that the network connection has gone
     * down.  This will cause this task to initialise the network interface.  After
     * this it is the responsibility of the network interface hardware driver to
     * send this message if a previously connected network is disconnected. */

    vNetworkTimerReload( pdMS_TO_TICKS( ipINITIALISATION_RETRY_DELAY ) );

    /* Mark the timer as inactive since we are not waiting on any ARP resolution as of now. */
    vIPSetARPResolutionTimerEnableState( pdFALSE );

    for( pxInterface = pxNetworkInterfaces; pxInterface != NULL; pxInterface = pxInterface->pxNext )
    {
        /* Post a 'eNetworkDownEvent' for every interface. */
        FreeRTOS_NetworkDown( pxInterface );
    }

    #if ( ipconfigUSE_TCP == 1 )
        {
            /* Initialise the TCP timer. */
            vTCPTimerReload( pdMS_TO_TICKS( ipTCP_TIMER_PERIOD_MS ) );
        }
    #endif

    #if ( ipconfigDNS_USE_CALLBACKS != 0 )
        {
            /* The following function is declared in FreeRTOS_DNS.c	and 'private' to
             * this library */
            vDNSInitialise();
        }
    #endif /* ipconfigDNS_USE_CALLBACKS != 0 */

    /* Initialisation is complete and events can now be processed. */
    xIPTaskInitialised = pdTRUE;
}
/*-----------------------------------------------------------*/

/**
 * @brief Helper function for prvIPTask, it waits for an event arriving
 *        on the queue, or a time-out.
 * @param[out] pxReceivedEvent: will be filled with the event received, or set
 *             to 'eNoEvent' in case of a time-out.
 * @param[in] xNextIPSleep: the maximum time to wait for a message ( unit:
 *            clock-ticks.
 */
static void prvIPTask_WaitForEvent( IPStackEvent_t * pxReceivedEvent,
                                    TickType_t xNextIPSleep )
{
    /* Wait until there is something to do. If the following call exits
     * due to a time out rather than a message being received, set a
     * 'NoEvent' value. */
    if( xQueueReceive( xNetworkEventQueue, ( void * ) pxReceivedEvent, xNextIPSleep ) == pdFALSE )
    {
        pxReceivedEvent->eEventType = eNoEvent;
    }

    #if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
        {
            if( pxReceivedEvent->eEventType != eNoEvent )
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
}
/*-----------------------------------------------------------*/

/**
 * @brief Helper function for prvIPTask, handle message of the type 'eSocketBindEvent'
 * @param[in] pxReceivedEvent: the pvData field points to a socket.
 */
static void prvIPTask_HandleBindEvent( IPStackEvent_t * pxReceivedEvent )
{
    FreeRTOS_Socket_t * pxSocket;

    #if ( ipconfigUSE_IPv6 != 0 )
        struct freertos_sockaddr6 xAddress;
    #else
        struct freertos_sockaddr xAddress;
    #endif

    /* FreeRTOS_bind (a user API) wants the IP-task to bind a socket
     * to a port. The port number is communicated in the socket field
     * usLocalPort. vSocketBind() will actually bind the socket and the
     * API will unblock as soon as the eSOCKET_BOUND event is
     * triggered. */
    pxSocket = ( ( FreeRTOS_Socket_t * ) pxReceivedEvent->pvData );
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
        struct freertos_sockaddr * pxAddress = ( ( sockaddr4_t * ) &( xAddress ) );

        pxAddress->sin_family = FREERTOS_AF_INET;
        pxAddress->sin_addr = FreeRTOS_htonl( pxSocket->ulLocalAddress );
    }

    xAddress.sin_port = FreeRTOS_htons( pxSocket->usLocalPort );
    /* 'ulLocalAddress' and 'usLocalPort' will be set again by vSocketBind(). */
    pxSocket->ulLocalAddress = 0;
    pxSocket->usLocalPort = 0;
    ( void ) vSocketBind( pxSocket, ( ( sockaddr4_t * ) &( xAddress ) ), sizeof( xAddress ), pdFALSE );

    /* Before 'eSocketBindEvent' was sent it was tested that
     * ( xEventGroup != NULL ) so it can be used now to wake up the
     * user. */
    pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_BOUND;
    vSocketWakeUpUser( pxSocket );
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 )

/**
 * @brief Helper function for prvIPTask, handle message of the type 'eTCPAcceptEvent'
 * @param[in] pxReceivedEvent: the pvData field points to a socket.
 */
    static void prvIPTask_HandleAcceptEvent( IPStackEvent_t * pxReceivedEvent )
    {
        FreeRTOS_Socket_t * pxSocket = ( ( FreeRTOS_Socket_t * ) pxReceivedEvent->pvData );

        if( xTCPCheckNewClient( pxSocket ) != pdFALSE )
        {
            pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_ACCEPT;
            vSocketWakeUpUser( pxSocket );
        }
    }
#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )

/**
 * @brief Helper function for prvIPTask, handle message of the type 'eSocketSelectEvent'
 * @param[in] pxReceivedEvent: the pvData field points to a socket.
 */
    static void prvIPTask_HandleSelectEvent( IPStackEvent_t * pxReceivedEvent )
    {
        #if ( ipconfigSELECT_USES_NOTIFY != 0 )
            {
                SocketSelectMessage_t * pxMessage = ( ( SocketSelectMessage_t * ) pxReceivedEvent->pvData );
                vSocketSelect( pxMessage->pxSocketSet );
                ( void ) xTaskNotifyGive( pxMessage->xTaskhandle );
            }
        #else
            {
                vSocketSelect( ( ( SocketSelect_t * ) pxReceivedEvent->pvData ) );
            }
        #endif /* ( ipconfigSELECT_USES_NOTIFY != 0 ) */
    }
#endif /* ipconfigSUPPORT_SELECT_FUNCTION == 1 */
/*-----------------------------------------------------------*/

/**
 * @brief Check the value of 'xNetworkDownEventPending'. When non-zero, pending
 *        network-down events will be handled.
 */
static void prvIPTask_CheckPendingEvents( void )
{
    NetworkInterface_t * pxInterface;

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
            EthernetHeader_t * pxHeader = ( ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );

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

    vPreCheckConfigs();

    /* Attempt to create the queue used to communicate with the IP task. */
    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        {
            static StaticQueue_t xNetworkEventStaticQueue;
            static uint8_t ucNetworkEventQueueStorageArea[ ipconfigEVENT_QUEUE_LENGTH * sizeof( IPStackEvent_t ) ];
            xNetworkEventQueue = xQueueCreateStatic( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), ucNetworkEventQueueStorageArea, &xNetworkEventStaticQueue );
        }
    #else
        {
            xNetworkEventQueue = xQueueCreate( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ) );
            configASSERT( xNetworkEventQueue != NULL );
        }
    #endif /* configSUPPORT_STATIC_ALLOCATION */

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
            #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
                {
                    static StaticTask_t xIPTaskBuffer;
                    static StackType_t xIPTaskStack[ ipconfigIP_TASK_STACK_SIZE_WORDS ];
                    xIPTaskHandle = xTaskCreateStatic( prvIPTask,
                                                       "IP-Task",
                                                       ipconfigIP_TASK_STACK_SIZE_WORDS,
                                                       NULL,
                                                       ipconfigIP_TASK_PRIORITY,
                                                       xIPTaskStack,
                                                       &xIPTaskBuffer );

                    if( xIPTaskHandle != NULL )
                    {
                        xReturn = pdTRUE;
                    }
                }
            #else /* if ( configSUPPORT_STATIC_ALLOCATION == 1 ) */
                {
                    xReturn = xTaskCreate( prvIPTask,
                                           "IP-task",
                                           ipconfigIP_TASK_STACK_SIZE_WORDS,
                                           NULL,
                                           ipconfigIP_TASK_PRIORITY,
                                           &( xIPTaskHandle ) );
                }
            #endif /* configSUPPORT_STATIC_ALLOCATION */
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
                pxEthernetHeader = ( ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );
                pxEthernetHeader->usFrameType = ipIPv4_FRAME_TYPE;

                pxICMPHeader = ( ( ICMPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipIP_PAYLOAD_OFFSET ] ) );
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
                    vIPSetTCPTimerEnableState( pdTRUE );

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
    pxEthernetHeader = ( ( const EthernetHeader_t * ) pucEthernetBuffer );

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
    #if ( ipconfigUSE_MDNS == 1 )
        if( memcmp( xMDNS_MacAdress.ucBytes, pxEthernetHeader->xDestinationAddress.ucBytes, sizeof( MACAddress_t ) ) == 0 )
        {
            /* The packet is a request for MDNS - process it. */
            eReturn = eProcessBuffer;
        }
        else
    #endif /* ipconfigUSE_MDNS */

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
    vARPTimerReload( pdMS_TO_TICKS( ipARP_TIMER_PERIOD_MS ) );
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
        pxEthernetHeader = ( ( const EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );

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
                        eReturned = prvProcessIPPacket( ( ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer );
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

        case eWaitingARPResolution:

            if( pxARPWaitingNetworkBuffer == NULL )
            {
                pxARPWaitingNetworkBuffer = pxNetworkBuffer;
                vIPTimerStartARPResolution( ipARP_RESOLUTION_MAX_DELAY );

                iptraceDELAYED_ARP_REQUEST_STARTED();
            }
            else
            {
                /* We are already waiting on one ARP resolution. This frame will be dropped. */
                vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );

                iptraceDELAYED_ARP_BUFFER_FULL();
            }

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
                    const IPPacket_t * pxIPPacket = ( ( const IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
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
            uint32_t ulSourceIPAddress = pxIPHeader->ulSourceIPAddress;

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
            else if( ( FreeRTOS_ntohl( ulSourceIPAddress ) & 0xffU ) == 0xffU )
            {
                /* Source IP address is a broadcast address, discard the packet. */
                eReturn = eReleaseBuffer;
            }
            else if( ( memcmp( ( const void * ) xBroadcastMACAddress.ucBytes,
                               ( const void * ) ( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes ),
                               sizeof( MACAddress_t ) ) == 0 ) &&
                     ( ( FreeRTOS_ntohl( ulDestinationIPAddress ) & 0xffU ) != 0xffU ) )
            {
                /* Ethernet address is a broadcast address, but the IP address is not a
                 * broadcast address. */
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

                            pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );

                            if( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
                            {
                                ucProtocol = pxIPPacket_IPv6->ucNextHeader;
                                pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] ) );
                            }
                            else
                        #endif /* ( ipconfigUSE_IPv6 != 0 ) */
                        {
                            ucProtocol = pxIPPacket->xIPHeader.ucProtocol;
                            pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ( size_t ) ipSIZE_OF_IPv4_HEADER ] ) );
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
            uint16_t usTotalLength;

            IPHeader_t * pxIPHeader = ( ( IPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );

            /* All structs of headers expect a IP header size of 20 bytes
             * IP header options were included, we'll ignore them and cut them out. */
            size_t uxLength = ( size_t ) pxIPHeader->ucVersionHeaderLength;

            /* Check if the IP headers are acceptable and if it has our destination.
             * The lowest four bits of 'ucVersionHeaderLength' indicate the IP-header
             * length in multiples of 4. */
            uxHeaderLength = ( size_t ) ( ( uxLength & 0x0FU ) << 2 );

            /* Number of bytes contained in IPv4 header options. */
            const size_t uxOptionsLength = ( ( size_t ) uxHeaderLength ) - ipSIZE_OF_IPv4_HEADER;

            if( uxOptionsLength > 0U )
            {
                /* From: the previous start of UDP/ICMP/TCP data. */
                const uint8_t * pucSource = ( const uint8_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( EthernetHeader_t ) + uxHeaderLength ] );
                /* To: the usual start of UDP/ICMP/TCP data at offset 20 (decimal ) from IP header. */
                uint8_t * pucTarget = ( uint8_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( EthernetHeader_t ) + ipSIZE_OF_IPv4_HEADER ] );
                /* How many: total length minus the options and the lower headers. */
                const size_t xMoveLen = pxNetworkBuffer->xDataLength - ( uxOptionsLength + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_ETH_HEADER );

                ( void ) memmove( pucTarget, pucSource, xMoveLen );
                pxNetworkBuffer->xDataLength -= uxOptionsLength;
            }

            /* Rewrite the Version/IHL byte to indicate that this packet has no IP options. */
            pxIPHeader->ucVersionHeaderLength = ( pxIPHeader->ucVersionHeaderLength & 0xF0U ) | /* High nibble is the version. */
                                                ( ( ipSIZE_OF_IPv4_HEADER >> 2 ) & 0x0FU );

            /* Update the total length of the IP packet after removing options. */
            usTotalLength = FreeRTOS_ntohs( pxIPHeader->usLength );
            usTotalLength -= ( uint16_t ) uxOptionsLength;
            pxIPHeader->usLength = FreeRTOS_htons( usTotalLength );

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
    BaseType_t xIsWaitingARPResolution = pdFALSE;
    /* The IP packet contained a UDP frame. */
    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    UDPHeader_t * pxUDPHeader = &( pxUDPPacket->xUDPHeader );

    size_t uxMinSize = ipSIZE_OF_ETH_HEADER + ( size_t ) uxIPHeaderSizePacket( pxNetworkBuffer ) + ipSIZE_OF_UDP_HEADER;
    size_t uxLength;
    uint16_t usLength;

    #if ( ipconfigUSE_IPv6 != 0 )
        if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
        {
            ProtocolHeaders_t * pxProtocolHeaders;

            pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] ) );
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
                                       pxUDPHeader->usDestinationPort,
                                       &( xIsWaitingARPResolution ) ) == pdPASS )
        {
            eReturn = eFrameConsumed;
        }
        else
        {
            /* Is this packet to be set aside for ARP resolution. */
            if( xIsWaitingARPResolution == pdTRUE )
            {
                eReturn = eWaitingARPResolution;
            }
        }
    }
    else
    {
        /* Length checks failed, the buffer will be released. */
    }

    return eReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )
    static BaseType_t xGetExtensionOrder( uint8_t ucProtocol,
                                          uint8_t ucNextHeader )
    {
        BaseType_t xReturn;

        switch( ucProtocol )
        {
            case ipIPv6_EXT_HEADER_HOP_BY_HOP:
                xReturn = 1;
                break;

            case ipIPv6_EXT_HEADER_DESTINATION_OPTIONS:
                xReturn = 7;

                if( ucNextHeader == ipIPv6_EXT_HEADER_ROUTING_HEADER )
                {
                    xReturn = 2;
                }

                break;

            case ipIPv6_EXT_HEADER_ROUTING_HEADER:
                xReturn = 3;
                break;

            case ipIPv6_EXT_HEADER_FRAGMENT_HEADER:
                xReturn = 4;
                break;

            case ipIPv6_EXT_HEADER_AUTHEN_HEADER:
                xReturn = 5;
                break;

            case ipIPv6_EXT_HEADER_SECURE_PAYLOAD:
                xReturn = 6;
                break;

            /* Destination options may follow here in case there are no routing options. */
            case ipIPv6_EXT_HEADER_MOBILITY_HEADER:
                xReturn = 8;
                break;

            default:
                xReturn = -1;
                break;
        }

        return xReturn;
    }

#endif /* ( ipconfigUSE_IPv6 != 0 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )

/**
 * @brief Handle the IPv6 extension headers.
 *
 * @param[in,out] pxNetworkBuffer: The received packet that contains IPv6 extension headers.
 *
 * @return eProcessBuffer in case the options are removed successfully, otherwise
 *         eReleaseBuffer.
 */
    static eFrameProcessingResult_t eHandleIPv6ExtensionHeaders( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                 BaseType_t xDoRemove )
    {
        eFrameProcessingResult_t eResult = eReleaseBuffer;
        const size_t uxMaxLength = pxNetworkBuffer->xDataLength;
        const uint8_t * pucSource = pxNetworkBuffer->pucEthernetBuffer;
        IPPacket_IPv6_t * pxIPPacket_IPv6 = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
        size_t uxIndex = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;
        size_t uxHopSize = 0U;
        size_t xMoveLen = 0U;
        size_t uxRemovedBytes = 0U;
        uint8_t ucCurrentHeader = pxIPPacket_IPv6->xIPHeader.ucNextHeader;
        uint8_t ucNextHeader = 0U;
        BaseType_t xNextOrder = 0;

        while( ( uxIndex + 8U ) < uxMaxLength )
        {
            BaseType_t xCurrentOrder;
            ucNextHeader = pucSource[ uxIndex ];

            xCurrentOrder = xGetExtensionOrder( ucCurrentHeader, ucNextHeader );

            /* Read the length expressed in number of octets. */
            uxHopSize = ( size_t ) pucSource[ uxIndex + 1U ];
            /* And multiply by 8 and add the minimum size of 8. */
            uxHopSize = ( uxHopSize * 8U ) + 8U;

            if( ( uxIndex + uxHopSize ) >= uxMaxLength )
            {
                uxIndex = uxMaxLength;
                break;
            }

            uxIndex = uxIndex + uxHopSize;

            if( ( ucNextHeader == ipPROTOCOL_TCP ) ||
                ( ucNextHeader == ipPROTOCOL_UDP ) ||
                ( ucNextHeader == ipPROTOCOL_ICMP_IPv6 ) )
            {
                FreeRTOS_debug_printf( ( "Stop at header %u\n", ucNextHeader ) );
                break;
            }

            xNextOrder = xGetExtensionOrder( ucNextHeader, pucSource[ uxIndex ] );

            FreeRTOS_debug_printf( ( "Going from header %2u (%d) to %2u (%d)\n",
                                     ucCurrentHeader,
                                     ( int ) xCurrentOrder,
                                     ucNextHeader,
                                     ( int ) xNextOrder ) );

            if( xNextOrder <= xCurrentOrder )
            {
                FreeRTOS_printf( ( "Wrong order\n" ) );
                uxIndex = uxMaxLength;
                break;
            }

            ucCurrentHeader = ucNextHeader;
        }

        if( uxIndex < uxMaxLength )
        {
            uint8_t * pucTo;
            const uint8_t * pucFrom;
            uint16_t usPayloadLength = FreeRTOS_ntohs( pxIPPacket_IPv6->xIPHeader.usPayloadLength );

            uxRemovedBytes = uxIndex - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

            if( uxRemovedBytes >= ( size_t ) usPayloadLength )
            {
                /* Can not remove more bytes than the payload length. */
            }
            else if( xDoRemove == pdTRUE )
            {
                pxIPPacket_IPv6->xIPHeader.ucNextHeader = ucNextHeader;
                pucTo = &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] );
                pucFrom = &( pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] );
                xMoveLen = uxMaxLength - uxIndex;
                ( void ) memmove( pucTo, pucFrom, xMoveLen );
                pxNetworkBuffer->xDataLength -= uxRemovedBytes;

                usPayloadLength -= ( uint16_t ) uxRemovedBytes;
                pxIPPacket_IPv6->xIPHeader.usPayloadLength = FreeRTOS_htons( usPayloadLength );
                eResult = eProcessBuffer;
            }
            else
            {
                /* xDoRemove is false, so the function is not supposed to
                 * remove extension headers. */
            }
        }

        FreeRTOS_printf( ( "Extension headers : %s Truncated %u bytes. Removed %u, Payload %u xDataLength now %u\n",
                           ( eResult == eProcessBuffer ) ? "good" : "bad",
                           xMoveLen,
                           uxRemovedBytes,
                           FreeRTOS_ntohs( pxIPPacket_IPv6->xIPHeader.usPayloadLength ),
                           pxNetworkBuffer->xDataLength ) );
        return eResult;
    }
#endif /* ( ipconfigUSE_IPv6 != 0 ) */

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
        pxIPHeader_IPv6 = ( ( const IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );

        if( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
        {
            uxHeaderLength = ipSIZE_OF_IPv6_HEADER;
            ucProtocol = pxIPHeader_IPv6->ucNextHeader;
            eReturn = prvAllowIPPacketIPv6( ( ( IPHeader_IPv6_t * ) &( pxIPPacket->xIPHeader ) ), pxNetworkBuffer, uxHeaderLength );

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

        #if ( ipconfigUSE_IPv6 != 0 )
            if( ( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE ) &&
                ( xGetExtensionOrder( ucProtocol, 0U ) > 0 ) )
            {
                eReturn = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );

                if( eReturn != eReleaseBuffer )
                {
                    ucProtocol = pxIPHeader_IPv6->ucNextHeader;
                }
            }
        #endif /* if ( ipconfigUSE_IPv6 != 0 ) */

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
                    if( xCheckRequiresARPResolution( pxNetworkBuffer ) == pdTRUE )
                    {
                        eReturn = eWaitingARPResolution;
                    }
                    else
                    {
                        /* IP address is not on the same subnet, ARP table can be updated. */
                        vARPRefreshCacheEntry( &( pxIPPacket->xEthernetHeader.xSourceAddress ), pxIPHeader->ulSourceIPAddress, pxNetworkBuffer->pxEndPoint );
                    }
                }
            }

            if( ( eReturn != eReleaseBuffer ) && ( eReturn != eWaitingARPResolution ) )
            {
                switch( ucProtocol )
                {
                    #if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
                        case ipPROTOCOL_ICMP:
                            /* As for now, only ICMP/ping messages are recognised. */
                            eReturn = ProcessICMPPacket( pxNetworkBuffer );
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
    }

    return eReturn;
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
        pxIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );

        /* Send! */
        if( pxNetworkBuffer->pxEndPoint == NULL )
        {
            /* _HT_ I wonder if this ad-hoc search of an end-point it necessary. */
            FreeRTOS_printf( ( "vReturnEthernetFrame: No pxEndPoint yet for %lxip?\n", FreeRTOS_ntohl( pxIPPacket->xIPHeader.ulDestinationIPAddress ) ) );
            #if ( ipconfigUSE_IPv6 != 0 )
                if( ( ( ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer ) )->usFrameType == ipIPv6_FRAME_TYPE )
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
 * @brief The variable 'xNetworkDownEventPending' is declared static.  This function
 *        gives read-only access to it.
 *
 * @return pdTRUE if there a network-down event pending. pdFALSE otherwise.
 */
BaseType_t xIsNetworkDownEventPending( void )
{
    return xNetworkDownEventPending;
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
        const EthernetHeader_t * pxHeader = ( ( const EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );

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
