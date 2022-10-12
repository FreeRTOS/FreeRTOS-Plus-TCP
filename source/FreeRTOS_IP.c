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
#include "FreeRTOS_ICMP.h"
#include "FreeRTOS_IP_Timers.h"
#include "FreeRTOS_IP_Utils.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"

/* IPv4 multi-cast addresses range from 224.0.0.0.0 to 240.0.0.0. */
#define ipFIRST_MULTI_CAST_IPv4             0xE0000000U /**< Lower bound of the IPv4 multicast address. */
#define ipLAST_MULTI_CAST_IPv4              0xF0000000U /**< Higher bound of the IPv4 multicast address. */

/* The first byte in the IPv4 header combines the IP version (4) with
 * with the length of the IP header. */
#define ipIPV4_VERSION_HEADER_LENGTH_MIN    0x45U /**< Minimum IPv4 header length. */
#define ipIPV4_VERSION_HEADER_LENGTH_MAX    0x4FU /**< Maximum IPv4 header length. */

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

#if ( ipconfigUSE_TCP != 0 )

/** @brief Set to a non-zero value if one or more TCP message have been processed
 * within the last round. */
    BaseType_t xProcessedTCPMessage;
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
/*-----------------------------------------------------------*/

/** @brief The pointer to buffer with packet waiting for ARP resolution. */
NetworkBufferDescriptor_t * pxARPWaitingNetworkBuffer = NULL;

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

#if ( ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES != 0 )

/*
 * The stack will call this user hook for all Ethernet frames that it
 * does not support, i.e. other than IPv4, IPv6 and ARP ( for the moment )
 * If this hook returns eReleaseBuffer or eProcessBuffer, the stack will
 * release and reuse the network buffer.  If this hook returns
 * eReturnEthernetFrame, that means user code has reused the network buffer
 * to generate a response and the stack will send that response out.
 * If this hook returns eFrameConsumed, the user code has ownership of the
 * network buffer and has to release it when it's done.
 */
    extern eFrameProcessingResult_t eApplicationProcessCustomFrameHook( NetworkBufferDescriptor_t * const pxNetworkBuffer );
#endif /* ( ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES != 0 ) */

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


/* The function 'prvAllowIPPacket()' checks if a packets should be processed. */
static eFrameProcessingResult_t prvAllowIPPacket( const IPPacket_t * const pxIPPacket,
                                                  const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                  UBaseType_t uxHeaderLength );

#if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 1 )

/* Even when the driver takes care of checksum calculations,
 *  the IP-task will still check if the length fields are OK. */
    static BaseType_t xCheckSizeFields( const uint8_t * const pucEthernetBuffer,
                                        size_t uxBufferLength );
#endif /* ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 1 ) */
/*-----------------------------------------------------------*/

/** @brief The queue used to pass events into the IP-task for processing. */
QueueHandle_t xNetworkEventQueue = NULL;

/** @brief The IP packet ID. */
uint16_t usPacketIdentifier = 0U;

/** @brief For convenience, a MAC address of all 0xffs is defined const for quick
 * reference. */
const MACAddress_t xBroadcastMACAddress = { { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff } };

/** @brief Structure that stores the netmask, gateway address and DNS server addresses. */
NetworkAddressingParameters_t xNetworkAddressing = { 0, 0, 0, 0, 0 };

/** @brief Default values for the above struct in case DHCP
 * does not lead to a confirmed request. */

/* MISRA Ref 8.9.1 [File scoped variables] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-89 */
/* coverity[misra_c_2012_rule_8_9_violation] */
NetworkAddressingParameters_t xDefaultAddressing = { 0, 0, 0, 0, 0 };

/** @brief Used to ensure network down events cannot be missed when they cannot be
 * posted to the network event queue because the network event queue is already
 * full. */
static volatile BaseType_t xNetworkDownEventPending = pdFALSE;

/** @brief Stores the handle of the task that handles the stack.  The handle is used
 * (indirectly) by some utility function to determine if the utility function is
 * being called by a task (in which case it is ok to block) or by the IP task
 * itself (in which case it is not ok to block). */

static TaskHandle_t xIPTaskHandle = NULL;

/** @brief Simple set to pdTRUE or pdFALSE depending on whether the network is up or
 * down (connected, not connected) respectively. */
static BaseType_t xNetworkUp = pdFALSE;

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

/* MISRA Ref 8.13.1 [Not decorating a pointer to const parameter with const] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-813 */
/* coverity[misra_c_2012_rule_8_13_violation] */
static void prvIPTask( void * pvParameters )
{
    /* Just to prevent compiler warnings about unused parameters. */
    ( void ) pvParameters;

    /* A possibility to set some additional task properties. */
    iptraceIP_TASK_STARTING();

    /* Generate a dummy message to say that the network connection has gone
     *  down.  This will cause this task to initialise the network interface.  After
     *  this it is the responsibility of the network interface hardware driver to
     *  send this message if a previously connected network is disconnected. */
    FreeRTOS_NetworkDown();

    #if ( ipconfigUSE_TCP == 1 )
        {
            /* Initialise the TCP timer. */
            vTCPTimerReload( pdMS_TO_TICKS( ipTCP_TIMER_PERIOD_MS ) );
        }
    #endif

    /* Mark the timer as inactive since we are not waiting on any ARP resolution as of now. */
    vIPSetARPResolutionTimerEnableState( pdFALSE );

    /* Initialisation is complete and events can now be processed. */
    xIPTaskInitialised = pdTRUE;

    FreeRTOS_debug_printf( ( "prvIPTask started\n" ) );

    /* Loop, processing IP events. */
    while( ipFOREVER() == pdTRUE )
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
    FreeRTOS_Socket_t * pxSocket;
    struct freertos_sockaddr xAddress;

    ipconfigWATCHDOG_TIMER();

    /* Check the ARP, DHCP and TCP timers to see if there is any periodic
     * or timeout processing to perform. */
    vCheckNetworkTimers();

    /* Calculate the acceptable maximum sleep time. */
    xNextIPSleep = xCalculateSleepTime();

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
            xNetworkUp = pdFALSE;
            prvProcessNetworkDownEvent();
            break;

        case eNetworkRxEvent:

            /* The network hardware driver has received a new packet.  A
             * pointer to the received buffer is located in the pvData member
             * of the received event structure. */
            prvHandleEthernetPacket( ( NetworkBufferDescriptor_t * ) xReceivedEvent.pvData );
            break;

        case eNetworkTxEvent:

           {
               NetworkBufferDescriptor_t * pxDescriptor = ( NetworkBufferDescriptor_t * ) xReceivedEvent.pvData;

               /* Send a network packet. The ownership will  be transferred to
                * the driver, which will release it after delivery. */
               iptraceNETWORK_INTERFACE_OUTPUT( pxDescriptor->xDataLength, pxDescriptor->pucEthernetBuffer );
               ( void ) xNetworkInterfaceOutput( pxDescriptor, pdTRUE );
           }

           break;

        case eARPTimerEvent:
            /* The ARP timer has expired, process the ARP cache. */
            vARPAgeCache();
            break;

        case eSocketBindEvent:

            /* FreeRTOS_bind (a user API) wants the IP-task to bind a socket
             * to a port. The port number is communicated in the socket field
             * usLocalPort. vSocketBind() will actually bind the socket and the
             * API will unblock as soon as the eSOCKET_BOUND event is
             * triggered. */
            pxSocket = ( ( FreeRTOS_Socket_t * ) xReceivedEvent.pvData );
            xAddress.sin_addr = 0U; /* For the moment. */
            xAddress.sin_port = FreeRTOS_ntohs( pxSocket->usLocalPort );
            pxSocket->usLocalPort = 0U;
            ( void ) vSocketBind( pxSocket, &xAddress, sizeof( xAddress ), pdFALSE );

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
            ( void ) vSocketClose( ( ( FreeRTOS_Socket_t * ) xReceivedEvent.pvData ) );
            break;

        case eStackTxEvent:

            /* The network stack has generated a packet to send.  A
             * pointer to the generated buffer is located in the pvData
             * member of the received event structure. */
            vProcessGeneratedUDPPacket( ( NetworkBufferDescriptor_t * ) xReceivedEvent.pvData );
            break;

        case eDHCPEvent:
            /* The DHCP state machine needs processing. */
            #if ( ipconfigUSE_DHCP == 1 )
                {
                    uintptr_t uxState;
                    eDHCPState_t eState;

                    /* MISRA Ref 11.6.1 [DHCP events and conversion to void] */
                    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-116 */
                    /* coverity[misra_c_2012_rule_11_6_violation] */
                    uxState = ( uintptr_t ) xReceivedEvent.pvData;
                    /* MISRA Ref 10.5.1 [DHCP events Enum] */
                    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-105 */
                    /* coverity[misra_c_2012_rule_10_5_violation] */
                    eState = ( eDHCPState_t ) uxState;

                    /* Process DHCP messages for a given end-point. */
                    vDHCPProcess( pdFALSE, eState );
                }
            #endif /* ipconfigUSE_DHCP */
            break;

        case eSocketSelectEvent:

            /* FreeRTOS_select() has got unblocked by a socket event,
             * vSocketSelect() will check which sockets actually have an event
             * and update the socket field xSocketBits. */
            #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
                #if ( ipconfigSELECT_USES_NOTIFY != 0 )
                    {
                        SocketSelectMessage_t * pxMessage = ( ( SocketSelectMessage_t * ) xReceivedEvent.pvData );
                        vSocketSelect( pxMessage->pxSocketSet );
                        ( void ) xTaskNotifyGive( pxMessage->xTaskhandle );
                    }
                #else
                    {
                        vSocketSelect( ( ( SocketSelect_t * ) xReceivedEvent.pvData ) );
                    }
                #endif /* ( ipconfigSELECT_USES_NOTIFY != 0 ) */
            #endif /* ipconfigSUPPORT_SELECT_FUNCTION == 1 */
            break;

        case eSocketSignalEvent:
            #if ( ipconfigSUPPORT_SIGNALS != 0 )

                /* Some task wants to signal the user of this socket in
                 * order to interrupt a call to recv() or a call to select(). */
                ( void ) FreeRTOS_SignalSocket( ( Socket_t ) xReceivedEvent.pvData );
            #endif /* ipconfigSUPPORT_SIGNALS */
            break;

        case eTCPTimerEvent:
            #if ( ipconfigUSE_TCP == 1 )

                /* Simply mark the TCP timer as expired so it gets processed
                 * the next time prvCheckNetworkTimers() is called. */
                vIPSetTCPTimerExpiredState( pdTRUE );
            #endif /* ipconfigUSE_TCP */
            break;

        case eTCPAcceptEvent:

            /* The API FreeRTOS_accept() was called, the IP-task will now
             * check if the listening socket (communicated in pvData) actually
             * received a new connection. */
            #if ( ipconfigUSE_TCP == 1 )
                pxSocket = ( ( FreeRTOS_Socket_t * ) xReceivedEvent.pvData );

                if( xTCPCheckNewClient( pxSocket ) != pdFALSE )
                {
                    pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_ACCEPT;
                    vSocketWakeUpUser( pxSocket );
                }
            #endif /* ipconfigUSE_TCP */
            break;

        case eTCPNetStat:

            /* FreeRTOS_netstat() was called to have the IP-task print an
             * overview of all sockets and their connections */
            #if ( ( ipconfigUSE_TCP == 1 ) && ( ipconfigHAS_PRINTF == 1 ) )
                vTCPNetStat();
            #endif /* ipconfigUSE_TCP */
            break;

        case eSocketSetDeleteEvent:
            #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
                {
                    SocketSelect_t * pxSocketSet = ( SocketSelect_t * ) ( xReceivedEvent.pvData );

                    iptraceMEM_STATS_DELETE( pxSocketSet );
                    vEventGroupDelete( pxSocketSet->xSelectGroup );
                    vPortFree( ( void * ) pxSocketSet );
                }
            #endif /* ipconfigSUPPORT_SELECT_FUNCTION == 1 */
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
        prvProcessNetworkDownEvent();
    }
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
 * @brief Perform all the required tasks when the network gets connected.
 */
void vIPNetworkUpCalls( void )
{
    xNetworkUp = pdTRUE;

    #if ( ipconfigUSE_NETWORK_EVENT_HOOK == 1 )
        {
            vApplicationIPNetworkEventHook( eNetworkUp );
        }
    #endif /* ipconfigUSE_NETWORK_EVENT_HOOK */

    #if ( ipconfigDNS_USE_CALLBACKS != 0 )
        {
            /* The following function is declared in FreeRTOS_DNS.c and 'private' to
             * this library */
            extern void vDNSInitialise( void );
            vDNSInitialise();
        }
    #endif /* ipconfigDNS_USE_CALLBACKS != 0 */

    /* Set remaining time to 0 so it will become active immediately. */
    vARPTimerReload( pdMS_TO_TICKS( ipARP_TIMER_PERIOD_MS ) );
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
 * @brief Handle the incoming Ethernet packets.
 *
 * @param[in] pxBuffer: Linked/un-linked network buffer descriptor(s)
 *                      to be processed.
 */
static void prvHandleEthernetPacket( NetworkBufferDescriptor_t * pxBuffer )
{
    #if ( ipconfigUSE_LINKED_RX_MESSAGES == 0 )
        {
            /* When ipconfigUSE_LINKED_RX_MESSAGES is set to 0 then only one
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

            /* While there is another packet in the chain. */
            while( pxBuffer != NULL )
            {
                /* Store a pointer to the buffer after pxBuffer for use later on. */
                pxNextBuffer = pxBuffer->pxNextBuffer;

                /* Make it NULL to avoid using it later on. */
                pxBuffer->pxNextBuffer = NULL;

                prvProcessEthernetPacket( pxBuffer );
                pxBuffer = pxNextBuffer;
            }
        }
    #endif /* ipconfigUSE_LINKED_RX_MESSAGES */
}
/*-----------------------------------------------------------*/

/**
 * @brief Send a network down event to the IP-task. If it fails to post a message,
 *         the failure will be noted in the variable 'xNetworkDownEventPending'
 *         and later on a 'network-down' event, it will be executed.
 */
void FreeRTOS_NetworkDown( void )
{
    static const IPStackEvent_t xNetworkDownEvent = { eNetworkDownEvent, NULL };
    const TickType_t xDontBlock = ( TickType_t ) 0;

    /* Simply send the network task the appropriate event. */
    if( xSendEventStructToIPTask( &xNetworkDownEvent, xDontBlock ) != pdPASS )
    {
        /* Could not send the message, so it is still pending. */
        xNetworkDownEventPending = pdTRUE;
    }
    else
    {
        /* Message was sent so it is not pending. */
        xNetworkDownEventPending = pdFALSE;
    }

    iptraceNETWORK_DOWN();
}
/*-----------------------------------------------------------*/

/**
 * @brief Utility function. Process Network Down event from ISR.
 *        This function is supposed to be called form an ISR. It is recommended
 * - *        use 'FreeRTOS_NetworkDown()', when calling from a normal task.
 *
 * @return If the event was processed successfully, then return pdTRUE.
 *         Else pdFALSE.
 */
BaseType_t FreeRTOS_NetworkDownFromISR( void )
{
    static const IPStackEvent_t xNetworkDownEvent = { eNetworkDownEvent, NULL };
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* Simply send the network task the appropriate event. */
    if( xQueueSendToBackFromISR( xNetworkEventQueue, &xNetworkDownEvent, &xHigherPriorityTaskWoken ) != pdPASS )
    {
        xNetworkDownEventPending = pdTRUE;
    }
    else
    {
        xNetworkDownEventPending = pdFALSE;
    }

    iptraceNETWORK_DOWN();

    return xHigherPriorityTaskWoken;
}
/*-----------------------------------------------------------*/

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
        /* Set the actual packet size in case a bigger buffer was returned. */
        pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t ) + uxRequestedSizeBytes;
        /* Skip 3 headers. */
        pvReturn = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_t ) ] );
    }
    else
    {
        pvReturn = NULL;
    }

    return ( void * ) pvReturn;
}
/*-----------------------------------------------------------*/

/*_RB_ Should we add an error or assert if the task priorities are set such that the servers won't function as expected? */

/*_HT_ There was a bug in FreeRTOS_TCP_IP.c that only occurred when the applications' priority was too high.
 * As that bug has been repaired, there is not an urgent reason to warn.
 * It is better though to use the advised priority scheme. */

/**
 * @brief Initialise the FreeRTOS-Plus-TCP network stack and initialise the IP-task.
 *
 * @param[in] ucIPAddress: Local IP address.
 * @param[in] ucNetMask: Local netmask.
 * @param[in] ucGatewayAddress: Local gateway address.
 * @param[in] ucDNSServerAddress: Local DNS server address.
 * @param[in] ucMACAddress: MAC address of the node.
 *
 * @return pdPASS if the task was successfully created and added to a ready
 * list, otherwise an error code defined in the file projdefs.h
 */
/* coverity[single_use] */
BaseType_t FreeRTOS_IPInit( const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                            const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ],
                            const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                            const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
                            const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] )
{
    BaseType_t xReturn = pdFALSE;

    /* Check that the configuration values are correct and that the IP-task has not
     * already been initialized. */
    vPreCheckConfigs();

    /* Attempt to create the queue used to communicate with the IP task. */
    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        {
            static StaticQueue_t xNetworkEventStaticQueue;
            static uint8_t ucNetworkEventQueueStorageArea[ ipconfigEVENT_QUEUE_LENGTH * sizeof( IPStackEvent_t ) ];
            xNetworkEventQueue = xQueueCreateStatic( ipconfigEVENT_QUEUE_LENGTH,
                                                     sizeof( IPStackEvent_t ),
                                                     ucNetworkEventQueueStorageArea,
                                                     &xNetworkEventStaticQueue );
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
            /* Store the local IP and MAC address. */
            xNetworkAddressing.ulDefaultIPAddress = FreeRTOS_inet_addr_quick( ucIPAddress[ 0 ], ucIPAddress[ 1 ], ucIPAddress[ 2 ], ucIPAddress[ 3 ] );
            xNetworkAddressing.ulNetMask = FreeRTOS_inet_addr_quick( ucNetMask[ 0 ], ucNetMask[ 1 ], ucNetMask[ 2 ], ucNetMask[ 3 ] );
            xNetworkAddressing.ulGatewayAddress = FreeRTOS_inet_addr_quick( ucGatewayAddress[ 0 ], ucGatewayAddress[ 1 ], ucGatewayAddress[ 2 ], ucGatewayAddress[ 3 ] );
            xNetworkAddressing.ulDNSServerAddress = FreeRTOS_inet_addr_quick( ucDNSServerAddress[ 0 ], ucDNSServerAddress[ 1 ], ucDNSServerAddress[ 2 ], ucDNSServerAddress[ 3 ] );
            xNetworkAddressing.ulBroadcastAddress = ( xNetworkAddressing.ulDefaultIPAddress & xNetworkAddressing.ulNetMask ) | ~xNetworkAddressing.ulNetMask;

            ( void ) memcpy( &xDefaultAddressing, &xNetworkAddressing, sizeof( xDefaultAddressing ) );

            #if ipconfigUSE_DHCP == 1
                {
                    /* The IP address is not set until DHCP completes. */
                    *ipLOCAL_IP_ADDRESS_POINTER = 0x00U;
                }
            #else
                {
                    /* The IP address is set from the value passed in. */
                    *ipLOCAL_IP_ADDRESS_POINTER = xNetworkAddressing.ulDefaultIPAddress;

                    /* Added to prevent ARP flood to gateway.  Ensure the
                    * gateway is on the same subnet as the IP address. */
                    if( xNetworkAddressing.ulGatewayAddress != 0U )
                    {
                        configASSERT( ( ( *ipLOCAL_IP_ADDRESS_POINTER ) & xNetworkAddressing.ulNetMask ) == ( xNetworkAddressing.ulGatewayAddress & xNetworkAddressing.ulNetMask ) );
                    }
                }
            #endif /* ipconfigUSE_DHCP == 1 */

            /* The MAC address is stored in the start of the default packet
             * header fragment, which is used when sending UDP packets. */
            ( void ) memcpy( ipLOCAL_MAC_ADDRESS, ucMACAddress, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

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
            FreeRTOS_debug_printf( ( "FreeRTOS_IPInit: xNetworkBuffersInitialise() failed\n" ) );

            /* Clean up. */
            vQueueDelete( xNetworkEventQueue );
            xNetworkEventQueue = NULL;
        }
    }
    else
    {
        FreeRTOS_debug_printf( ( "FreeRTOS_IPInit: Network event queue could not be created\n" ) );
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the current address configuration. Only non-NULL pointers will
 *        be filled in.
 *
 * @param[out] pulIPAddress: The current IP-address assigned.
 * @param[out] pulNetMask: The netmask used for current subnet.
 * @param[out] pulGatewayAddress: The gateway address.
 * @param[out] pulDNSServerAddress: The DNS server address.
 */
void FreeRTOS_GetAddressConfiguration( uint32_t * pulIPAddress,
                                       uint32_t * pulNetMask,
                                       uint32_t * pulGatewayAddress,
                                       uint32_t * pulDNSServerAddress )
{
    /* Return the address configuration to the caller. */

    if( pulIPAddress != NULL )
    {
        *pulIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
    }

    if( pulNetMask != NULL )
    {
        *pulNetMask = xNetworkAddressing.ulNetMask;
    }

    if( pulGatewayAddress != NULL )
    {
        *pulGatewayAddress = xNetworkAddressing.ulGatewayAddress;
    }

    if( pulDNSServerAddress != NULL )
    {
        *pulDNSServerAddress = xNetworkAddressing.ulDNSServerAddress;
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Set the current network address configuration. Only non-NULL pointers will
 *        be used.
 *
 * @param[in] pulIPAddress: The current IP-address assigned.
 * @param[in] pulNetMask: The netmask used for current subnet.
 * @param[in] pulGatewayAddress: The gateway address.
 * @param[in] pulDNSServerAddress: The DNS server address.
 */
void FreeRTOS_SetAddressConfiguration( const uint32_t * pulIPAddress,
                                       const uint32_t * pulNetMask,
                                       const uint32_t * pulGatewayAddress,
                                       const uint32_t * pulDNSServerAddress )
{
    /* Update the address configuration. */

    if( pulIPAddress != NULL )
    {
        *ipLOCAL_IP_ADDRESS_POINTER = *pulIPAddress;
    }

    if( pulNetMask != NULL )
    {
        xNetworkAddressing.ulNetMask = *pulNetMask;
    }

    if( pulGatewayAddress != NULL )
    {
        xNetworkAddressing.ulGatewayAddress = *pulGatewayAddress;
    }

    if( pulDNSServerAddress != NULL )
    {
        xNetworkAddressing.ulDNSServerAddress = *pulDNSServerAddress;
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Release the UDP payload buffer.
 *
 * @param[in] pvBuffer: Pointer to the UDP buffer that is to be released.
 */
void FreeRTOS_ReleaseUDPPayloadBuffer( void const * pvBuffer )
{
    vReleaseNetworkBufferAndDescriptor( pxUDPPayloadBuffer_to_NetworkBuffer( pvBuffer ) );
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 )

/**
 * @brief Release the memory that was previously obtained by calling FreeRTOS_recv()
 *        with the flag 'FREERTOS_ZERO_COPY'.
 *
 * @param[in] xSocket: The socket that was read from.
 * @param[in] pvBuffer: The buffer returned in the call to FreeRTOS_recv().
 * @param[in] xByteCount: The number of bytes that have been used.
 *
 * @return pdPASS if the buffer was released successfully, otherwise pdFAIL is returned.
 */
    BaseType_t FreeRTOS_ReleaseTCPPayloadBuffer( Socket_t xSocket,
                                                 void const * pvBuffer,
                                                 BaseType_t xByteCount )
    {
        BaseType_t xByteCountReleased;
        BaseType_t xReturn = pdFAIL;
        uint8_t * pucData;
        size_t uxBytesAvailable = uxStreamBufferGetPtr( xSocket->u.xTCP.rxStream, &( pucData ) );

        /* Make sure the pointer is correct. */
        configASSERT( pucData == ( uint8_t * ) pvBuffer );

        /* Avoid releasing more bytes than available. */
        configASSERT( uxBytesAvailable >= ( size_t ) xByteCount );

        if( ( pucData == pvBuffer ) && ( uxBytesAvailable >= ( size_t ) xByteCount ) )
        {
            /* Call recv with NULL pointer to advance the circular buffer. */
            xByteCountReleased = FreeRTOS_recv( xSocket,
                                                NULL,
                                                ( size_t ) xByteCount,
                                                FREERTOS_MSG_DONTWAIT );

            configASSERT( xByteCountReleased == xByteCount );

            if( xByteCountReleased == xByteCount )
            {
                xReturn = pdPASS;
            }
        }

        return xReturn;
    }
#endif /* ( ipconfigUSE_TCP == 1 ) */
/*-----------------------------------------------------------*/

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
                    vIPSetTCPTimerExpiredState( pdTRUE );

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
 * @brief Decide whether this packet should be processed or not based on the IP address in the packet.
 *
 * @param[in] pucEthernetBuffer: The ethernet packet under consideration.
 *
 * @return Enum saying whether to release or to process the packet.
 */
eFrameProcessingResult_t eConsiderFrameForProcessing( const uint8_t * const pucEthernetBuffer )
{
    eFrameProcessingResult_t eReturn;
    const EthernetHeader_t * pxEthernetHeader;

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */

    /* MISRA Ref 11.3.1 [Misaligned access] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
    /* coverity[misra_c_2012_rule_11_3_violation] */
    pxEthernetHeader = ( ( const EthernetHeader_t * ) pucEthernetBuffer );

    if( memcmp( ipLOCAL_MAC_ADDRESS, pxEthernetHeader->xDestinationAddress.ucBytes, sizeof( MACAddress_t ) ) == 0 )
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

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
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
                        /* MISRA Ref 11.3.1 [Misaligned access] */
                        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                        /* coverity[misra_c_2012_rule_11_3_violation] */
                        eReturned = eARPProcessPacket( ( ( ARPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer ) );
                    }
                    else
                    {
                        eReturned = eReleaseBuffer;
                    }

                    break;

                case ipIPv4_FRAME_TYPE:

                    /* The Ethernet frame contains an IP packet. */
                    if( pxNetworkBuffer->xDataLength >= sizeof( IPPacket_t ) )
                    {
                        /* MISRA Ref 11.3.1 [Misaligned access] */
                        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                        /* coverity[misra_c_2012_rule_11_3_violation] */
                        eReturned = prvProcessIPPacket( ( ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer );
                    }
                    else
                    {
                        eReturned = eReleaseBuffer;
                    }

                    break;

                default:
                    #if ( ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES != 0 )
                        /* Custom frame handler. */
                        eReturned = eApplicationProcessCustomFrameHook( pxNetworkBuffer );
                    #else
                        /* No other packet types are handled.  Nothing to do. */
                        eReturned = eReleaseBuffer;
                    #endif
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

/**
 * @brief Check whether this IP packet is to be allowed or to be dropped.
 *
 * @param[in] pxIPPacket: The IP packet under consideration.
 * @param[in] pxNetworkBuffer: The whole network buffer.
 * @param[in] uxHeaderLength: The length of the header.
 *
 * @return Whether the packet should be processed or dropped.
 */
static eFrameProcessingResult_t prvAllowIPPacket( const IPPacket_t * const pxIPPacket,
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

            /* Ensure that the incoming packet is not fragmented because the stack
             * doesn't not support IP fragmentation. All but the last fragment coming in will have their
             * "more fragments" flag set and the last fragment will have a non-zero offset.
             * We need to drop the packet in either of those cases. */
            if( ( ( pxIPHeader->usFragmentOffset & ipFRAGMENT_OFFSET_BIT_MASK ) != 0U ) || ( ( pxIPHeader->usFragmentOffset & ipFRAGMENT_FLAGS_MORE_FRAGMENTS ) != 0U ) )
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
            /* Is the packet for this IP address? */
            else if( ( ulDestinationIPAddress != *ipLOCAL_IP_ADDRESS_POINTER ) &&
                     /* Is it the global broadcast address 255.255.255.255 ? */
                     ( ulDestinationIPAddress != ipBROADCAST_IP_ADDRESS ) &&
                     /* Is it a specific broadcast address 192.168.1.255 ? */
                     ( ulDestinationIPAddress != xNetworkAddressing.ulBroadcastAddress ) &&
                     #if ( ipconfigUSE_LLMNR == 1 )
                         /* Is it the LLMNR multicast address? */
                         ( ulDestinationIPAddress != ipLLMNR_IP_ADDR ) &&
                     #endif
                     /* Or (during DHCP negotiation) we have no IP-address yet? */
                     ( *ipLOCAL_IP_ADDRESS_POINTER != 0U ) )
            {
                /* Packet is not for this node, release it */
                eReturn = eReleaseBuffer;
            }
            /* Is the source address correct? */
            else if( ( FreeRTOS_ntohl( ulSourceIPAddress ) & 0xffU ) == 0xffU )
            {
                /* The source address cannot be broadcast address. Replying to this
                 * packet may cause network storms. Drop the packet. */
                eReturn = eReleaseBuffer;
            }
            else if( ( memcmp( xBroadcastMACAddress.ucBytes,
                               pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes,
                               sizeof( MACAddress_t ) ) == 0 ) &&
                     ( ( FreeRTOS_ntohl( ulDestinationIPAddress ) & 0xffU ) != 0xffU ) )
            {
                /* Ethernet address is a broadcast address, but the IP address is not a
                 * broadcast address. */
                eReturn = eReleaseBuffer;
            }
            else if( memcmp( xBroadcastMACAddress.ucBytes,
                             pxIPPacket->xEthernetHeader.xSourceAddress.ucBytes,
                             sizeof( MACAddress_t ) ) == 0 )
            {
                /* Ethernet source is a broadcast address. Drop the packet. */
                eReturn = eReleaseBuffer;
            }
            else if( xIsIPv4Multicast( ulSourceIPAddress ) == pdTRUE )
            {
                /* Source is a multicast IP address. Drop the packet in conformity with RFC 1112 section 7.2. */
                eReturn = eReleaseBuffer;
            }
            else
            {
                /* Packet is not fragmented, destination is this device, source IP and MAC
                 * addresses are correct. */
            }
        }
    #endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */

    #if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 )
        {
            /* Some drivers of NIC's with checksum-offloading will enable the above
             * define, so that the checksum won't be checked again here */
            if( eReturn == eProcessBuffer )
            {
                /* Is the IP header checksum correct?
                 *
                 * NOTE: When the checksum of IP header is calculated while not omitting
                 * the checksum field, the resulting value of the checksum always is 0xffff
                 * which is denoted by ipCORRECT_CRC. See this wiki for more information:
                 * https://en.wikipedia.org/wiki/IPv4_header_checksum#Verifying_the_IPv4_header_checksum
                 * and this RFC: https://tools.ietf.org/html/rfc1624#page-4
                 */
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
    #else /* if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 ) */
        {
            if( eReturn == eProcessBuffer )
            {
                if( xCheckSizeFields( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength ) != pdPASS )
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
                        /* ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS is defined as 0,
                         * and so UDP packets carrying a protocol checksum of 0, will
                         * be dropped. */

                        /* Identify the next protocol. */
                        if( pxIPPacket->xIPHeader.ucProtocol == ( uint8_t ) ipPROTOCOL_UDP )
                        {
                            const ProtocolPacket_t * pxProtPack;

                            /* pxProtPack will point to the offset were the protocols begin. */

                            /* MISRA Ref 11.3.1 [Misaligned access] */
                            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                            /* coverity[misra_c_2012_rule_11_3_violation] */
                            pxProtPack = ( ( ProtocolPacket_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxHeaderLength - ipSIZE_OF_IPv4_HEADER ] ) );

                            if( pxProtPack->xUDPPacket.xUDPHeader.usChecksum == ( uint16_t ) 0U )
                            {
                                #if ( ipconfigHAS_PRINTF != 0 )
                                    {
                                        static BaseType_t xCount = 0;

                                        /* Exclude this from branch coverage as this is only used for debugging. */
                                        if( xCount < 5 ) /* LCOV_EXCL_BR_LINE */
                                        {
                                            FreeRTOS_printf( ( "prvAllowIPPacket: UDP packet from %xip without CRC dropped\n",
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
            ( void ) uxHeaderLength;
        }
    #endif /* ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 */

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
    size_t uxLength = ( size_t ) pxIPHeader->ucVersionHeaderLength;
    UBaseType_t uxHeaderLength = ( UBaseType_t ) ( ( uxLength & 0x0FU ) << 2 );
    uint8_t ucProtocol;

    /* Bound the calculated header length: take away the Ethernet header size,
     * then check if the IP header is claiming to be longer than the remaining
     * total packet size. Also check for minimal header field length. */
    if( ( uxHeaderLength > ( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER ) ) ||
        ( uxHeaderLength < ipSIZE_OF_IPv4_HEADER ) )
    {
        eReturn = eReleaseBuffer;
    }
    else
    {
        ucProtocol = pxIPPacket->xIPHeader.ucProtocol;
        /* Check if the IP headers are acceptable and if it has our destination. */
        eReturn = prvAllowIPPacket( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

        /* MISRA Ref 14.3.1 [Configuration dependent invariant] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-143 */
        /* coverity[misra_c_2012_rule_14_3_violation] */
        /* coverity[cond_const] */
        if( eReturn == eProcessBuffer )
        {
            /* Are there IP-options. */
            if( uxHeaderLength > ipSIZE_OF_IPv4_HEADER )
            {
                /* The size of the IP-header is larger than 20 bytes.
                 * The extra space is used for IP-options. */
                #if ( ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS != 0 )
                    {
                        /* All structs of headers expect a IP header size of 20 bytes
                         * IP header options were included, we'll ignore them and cut them out. */
                        const size_t optlen = ( ( size_t ) uxHeaderLength ) - ipSIZE_OF_IPv4_HEADER;
                        /* From: the previous start of UDP/ICMP/TCP data. */
                        const uint8_t * pucSource = ( const uint8_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( EthernetHeader_t ) + uxHeaderLength ] );
                        /* To: the usual start of UDP/ICMP/TCP data at offset 20 (decimal ) from IP header. */
                        uint8_t * pucTarget = ( uint8_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( EthernetHeader_t ) + ipSIZE_OF_IPv4_HEADER ] );
                        /* How many: total length minus the options and the lower headers. */
                        const size_t xMoveLen = pxNetworkBuffer->xDataLength - ( optlen + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_ETH_HEADER );

                        ( void ) memmove( pucTarget, pucSource, xMoveLen );
                        pxNetworkBuffer->xDataLength -= optlen;
                        pxIPHeader->usLength = FreeRTOS_htons( FreeRTOS_ntohs( pxIPHeader->usLength ) - optlen );

                        /* Rewrite the Version/IHL byte to indicate that this packet has no IP options. */
                        pxIPHeader->ucVersionHeaderLength = ( pxIPHeader->ucVersionHeaderLength & 0xF0U ) | /* High nibble is the version. */
                                                            ( ( ipSIZE_OF_IPv4_HEADER >> 2 ) & 0x0FU );
                    }
                #else /* if ( ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS != 0 ) */
                    {
                        /* 'ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS' is not set, so packets carrying
                         * IP-options will be dropped. */
                        eReturn = eReleaseBuffer;
                    }
                #endif /* if ( ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS != 0 ) */
            }

            /* MISRA Ref 14.3.1 [Configuration dependent invariant] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-143 */
            /* coverity[misra_c_2012_rule_14_3_violation] */
            /* coverity[const] */
            if( eReturn != eReleaseBuffer )
            {
                /* Add the IP and MAC addresses to the ARP table if they are not
                 * already there - otherwise refresh the age of the existing
                 * entry. */
                if( ucProtocol != ( uint8_t ) ipPROTOCOL_UDP )
                {
                    if( xCheckRequiresARPResolution( pxNetworkBuffer ) == pdTRUE )
                    {
                        eReturn = eWaitingARPResolution;
                    }
                    else
                    {
                        /* IP address is not on the same subnet, ARP table can be updated.
                         * Refresh the ARP cache with the IP/MAC-address of the received
                         *  packet. For UDP packets, this will be done later in
                         *  xProcessReceivedUDPPacket(), as soon as it's know that the message
                         *  will be handled.  This will prevent the ARP cache getting
                         *  overwritten with the IP address of useless broadcast packets.
                         */
                        vARPRefreshCacheEntry( &( pxIPPacket->xEthernetHeader.xSourceAddress ), pxIPHeader->ulSourceIPAddress );
                    }
                }

                if( eReturn != eWaitingARPResolution )
                {
                    switch( ucProtocol )
                    {
                        case ipPROTOCOL_ICMP:

                            /* The IP packet contained an ICMP frame.  Don't bother checking
                             * the ICMP checksum, as if it is wrong then the wrong data will
                             * also be returned, and the source of the ping will know something
                             * went wrong because it will not be able to validate what it
                             * receives. */
                            #if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
                                {
                                    if( pxIPHeader->ulDestinationIPAddress == *ipLOCAL_IP_ADDRESS_POINTER )
                                    {
                                        eReturn = ProcessICMPPacket( pxNetworkBuffer );
                                    }
                                }
                            #endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */
                            break;

                        case ipPROTOCOL_UDP:
                           {
                               /* The IP packet contained a UDP frame. */

                               /* Map the buffer onto a UDP-Packet struct to easily access the
                                * fields of UDP packet. */

                               /* MISRA Ref 11.3.1 [Misaligned access] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                               /* coverity[misra_c_2012_rule_11_3_violation] */
                               const UDPPacket_t * pxUDPPacket = ( ( const UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
                               uint16_t usLength;
                               BaseType_t xIsWaitingARPResolution = pdFALSE;

                               /* Note the header values required prior to the checksum
                                * generation as the checksum pseudo header may clobber some of
                                * these values. */
                               usLength = FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength );

                               if( ( pxNetworkBuffer->xDataLength < sizeof( UDPPacket_t ) ) ||
                                   ( ( ( size_t ) usLength ) < sizeof( UDPHeader_t ) ) )
                               {
                                   eReturn = eReleaseBuffer;
                               }
                               else if( usLength > ( FreeRTOS_ntohs( pxIPHeader->usLength ) - ipSIZE_OF_IPv4_HEADER ) )
                               {
                                   /* The UDP packet is bigger than the IP-payload. Something is wrong, drop the packet. */
                                   eReturn = eReleaseBuffer;
                               }
                               else
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
                                   uxPayloadSize_1 = pxNetworkBuffer->xDataLength - sizeof( UDPPacket_t );
                                   uxPayloadSize_2 = ( ( size_t ) usLength ) - sizeof( UDPHeader_t );

                                   if( uxPayloadSize_1 > uxPayloadSize_2 )
                                   {
                                       pxNetworkBuffer->xDataLength = uxPayloadSize_2 + sizeof( UDPPacket_t );
                                   }

                                   /* Fields in pxNetworkBuffer (usPort, ulIPAddress) are network order. */
                                   pxNetworkBuffer->usPort = pxUDPPacket->xUDPHeader.usSourcePort;
                                   pxNetworkBuffer->ulIPAddress = pxUDPPacket->xIPHeader.ulSourceIPAddress;

                                   /* ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM:
                                    * In some cases, the upper-layer checksum has been calculated
                                    * by the NIC driver. */

                                   /* Pass the packet payload to the UDP sockets
                                    * implementation. */
                                   if( xProcessReceivedUDPPacket( pxNetworkBuffer,
                                                                  pxUDPPacket->xUDPHeader.usDestinationPort,
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
                           }
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
                            /* Not a supported frame type. */
                            eReturn = eReleaseBuffer;
                            break;
                    }
                }
            }
        }
    }

    return eReturn;
}

/*-----------------------------------------------------------*/

#if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 1 )

/**
 * @brief Although the driver will take care of checksum calculations, the IP-task
 *        will still check if the length fields are OK.
 *
 * @param[in] pucEthernetBuffer: The Ethernet packet received.
 * @param[in] uxBufferLength: The total number of bytes received.
 *
 * @return pdPASS when the length fields in the packet OK, pdFAIL when the packet
 *         should be dropped.
 */
    static BaseType_t xCheckSizeFields( const uint8_t * const pucEthernetBuffer,
                                        size_t uxBufferLength )
    {
        size_t uxLength;
        const IPPacket_t * pxIPPacket;
        UBaseType_t uxIPHeaderLength;
        uint8_t ucProtocol;
        uint16_t usLength;
        uint16_t ucVersionHeaderLength;
        size_t uxMinimumLength;
        BaseType_t xResult = pdFAIL;

        DEBUG_DECLARE_TRACE_VARIABLE( BaseType_t, xLocation, 0 );

        do
        {
            /* Check for minimum packet size: Ethernet header and an IP-header, 34 bytes */
            if( uxBufferLength < sizeof( IPPacket_t ) )
            {
                DEBUG_SET_TRACE_VARIABLE( xLocation, 1 );
                break;
            }

            /* Map the buffer onto a IP-Packet struct to easily access the
             * fields of the IP packet. */

            /* MISRA Ref 11.3.1 [Misaligned access] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            pxIPPacket = ( ( const IPPacket_t * ) pucEthernetBuffer );

            ucVersionHeaderLength = pxIPPacket->xIPHeader.ucVersionHeaderLength;

            /* Test if the length of the IP-header is between 20 and 60 bytes,
             * and if the IP-version is 4. */
            if( ( ucVersionHeaderLength < ipIPV4_VERSION_HEADER_LENGTH_MIN ) ||
                ( ucVersionHeaderLength > ipIPV4_VERSION_HEADER_LENGTH_MAX ) )
            {
                DEBUG_SET_TRACE_VARIABLE( xLocation, 2 );
                break;
            }

            ucVersionHeaderLength = ( ucVersionHeaderLength & ( uint8_t ) 0x0FU ) << 2;
            uxIPHeaderLength = ( UBaseType_t ) ucVersionHeaderLength;

            /* Check if the complete IP-header is transferred. */
            if( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + uxIPHeaderLength ) )
            {
                DEBUG_SET_TRACE_VARIABLE( xLocation, 3 );
                break;
            }

            /* Check if the complete IP-header plus protocol data have been transferred: */
            usLength = pxIPPacket->xIPHeader.usLength;
            usLength = FreeRTOS_ntohs( usLength );

            if( uxBufferLength < ( size_t ) ( ipSIZE_OF_ETH_HEADER + ( size_t ) usLength ) )
            {
                DEBUG_SET_TRACE_VARIABLE( xLocation, 4 );
                break;
            }

            /* Identify the next protocol. */
            ucProtocol = pxIPPacket->xIPHeader.ucProtocol;

            /* Switch on the Layer 3/4 protocol. */
            if( ucProtocol == ( uint8_t ) ipPROTOCOL_UDP )
            {
                /* Expect at least a complete UDP header. */
                uxMinimumLength = uxIPHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER;
            }
            else if( ucProtocol == ( uint8_t ) ipPROTOCOL_TCP )
            {
                uxMinimumLength = uxIPHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_TCP_HEADER;
            }
            else if( ( ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP ) ||
                     ( ucProtocol == ( uint8_t ) ipPROTOCOL_IGMP ) )
            {
                uxMinimumLength = uxIPHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMP_HEADER;
            }
            else
            {
                /* Unhandled protocol, other than ICMP, IGMP, UDP, or TCP. */
                DEBUG_SET_TRACE_VARIABLE( xLocation, 5 );
                break;
            }

            if( uxBufferLength < uxMinimumLength )
            {
                DEBUG_SET_TRACE_VARIABLE( xLocation, 6 );
                break;
            }

            uxLength = ( size_t ) usLength;
            uxLength -= ( ( uint16_t ) uxIPHeaderLength ); /* normally, minus 20. */

            if( ( uxLength < ( ( size_t ) sizeof( UDPHeader_t ) ) ) ||
                ( uxLength > ( ( size_t ) ipconfigNETWORK_MTU - ( size_t ) uxIPHeaderLength ) ) )
            {
                /* For incoming packets, the length is out of bound: either
                 * too short or too long. For outgoing packets, there is a
                 * serious problem with the format/length. */
                DEBUG_SET_TRACE_VARIABLE( xLocation, 7 );
                break;
            }

            xResult = pdPASS;
        } while( ipFALSE_BOOL );

        if( xResult != pdPASS )
        {
            /* NOP if ipconfigHAS_PRINTF != 1 */
            FreeRTOS_printf( ( "xCheckSizeFields: location %ld\n", xLocation ) );
        }

        return xResult;
    }
#endif /* ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 1 ) */
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
    EthernetHeader_t * pxEthernetHeader;
/* memcpy() helper variables for MISRA Rule 21.15 compliance*/
    const void * pvCopySource;
    void * pvCopyDest;

    #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
        NetworkBufferDescriptor_t * pxNewBuffer;
    #endif

    #if ( ipconfigETHERNET_MINIMUM_PACKET_BYTES > 0 )
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
    #endif /* if( ipconfigETHERNET_MINIMUM_PACKET_BYTES > 0 ) */

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
        /* Map the Buffer to Ethernet Header struct for easy access to fields. */

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        pxEthernetHeader = ( ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );

        /*
         * Use helper variables for memcpy() to remain
         * compliant with MISRA Rule 21.15.  These should be
         * optimized away.
         */
        /* Swap source and destination MAC addresses. */
        pvCopySource = &pxEthernetHeader->xSourceAddress;
        pvCopyDest = &pxEthernetHeader->xDestinationAddress;
        ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( pxEthernetHeader->xDestinationAddress ) );

        pvCopySource = ipLOCAL_MAC_ADDRESS;
        pvCopyDest = &pxEthernetHeader->xSourceAddress;
        ( void ) memcpy( pvCopyDest, pvCopySource, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

        /* Send! */
        iptraceNETWORK_INTERFACE_OUTPUT( pxNetworkBuffer->xDataLength, pxNetworkBuffer->pucEthernetBuffer );
        ( void ) xNetworkInterfaceOutput( pxNetworkBuffer, xReleaseAfterSend );
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
    return *ipLOCAL_IP_ADDRESS_POINTER;
}
/*-----------------------------------------------------------*/

/**
 * @brief Sets the IP address of the NIC.
 *
 * @param[in] ulIPAddress: IP address of the NIC to be set.
 */
void FreeRTOS_SetIPAddress( uint32_t ulIPAddress )
{
    *ipLOCAL_IP_ADDRESS_POINTER = ulIPAddress;
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
    return xNetworkAddressing.ulGatewayAddress;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the DNS server address.
 *
 * @return The IP address of the DNS server.
 */
uint32_t FreeRTOS_GetDNSServerAddress( void )
{
    return xNetworkAddressing.ulDNSServerAddress;
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the netmask for the subnet.
 *
 * @return The 32 bit netmask for the subnet.
 */
uint32_t FreeRTOS_GetNetmask( void )
{
    return xNetworkAddressing.ulNetMask;
}
/*-----------------------------------------------------------*/

/**
 * @brief Update the MAC address.
 *
 * @param[in] ucMACAddress: the MAC address to be set.
 */
void FreeRTOS_UpdateMACAddress( const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] )
{
    /* Copy the MAC address at the start of the default packet header fragment. */
    ( void ) memcpy( ipLOCAL_MAC_ADDRESS, ucMACAddress, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
}
/*-----------------------------------------------------------*/

/**
 * @brief Get the MAC address.
 *
 * @return The pointer to MAC address.
 */
const uint8_t * FreeRTOS_GetMACAddress( void )
{
    return ipLOCAL_MAC_ADDRESS;
}
/*-----------------------------------------------------------*/

/**
 * @brief Set the netmask for the subnet.
 *
 * @param[in] ulNetmask: The 32 bit netmask of the subnet.
 */
void FreeRTOS_SetNetmask( uint32_t ulNetmask )
{
    xNetworkAddressing.ulNetMask = ulNetmask;
}
/*-----------------------------------------------------------*/

/**
 * @brief Set the gateway address.
 *
 * @param[in] ulGatewayAddress: The gateway address.
 */
void FreeRTOS_SetGatewayAddress( uint32_t ulGatewayAddress )
{
    xNetworkAddressing.ulGatewayAddress = ulGatewayAddress;
}
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
 * @brief Returns whether this node is connected to network or not.
 *
 * @return pdTRUE if network is connected, else pdFALSE.
 */
BaseType_t FreeRTOS_IsNetworkUp( void )
{
    return xNetworkUp;
}
/*-----------------------------------------------------------*/

#if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )

/**
 * @brief Get the minimum space in the IP task queue.
 *
 * @return The minimum possible space in the IP task queue.
 */
    UBaseType_t uxGetMinimumIPQueueSpace( void )
    {
        return uxQueueMinimumSpace;
    }
#endif
/*-----------------------------------------------------------*/

/* Provide access to private members for verification. */
#ifdef FREERTOS_TCP_ENABLE_VERIFICATION
    #include "aws_freertos_ip_verification_access_ip_define.h"
#endif
