/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file FreeRTOS_IGMP.c
 * @brief Implements the optional IGMP functionality of the FreeRTOS+TCP network stack.
 */

/* ToDo List ( remove the items below as progress is made )
 * - Add FREERTOS_SO_IP_MULTICAST_IF to specify outgoing interface used for multicasts
 * - Investigate local reception of outgoing multicasts
 * - Write a demo and add to https://github.com/FreeRTOS/FreeRTOS/tree/main/FreeRTOS-Plus/Demo
 * - Documentation: Caution about calling FREERTOS_SO_IP_ADD_MEMBERSHIP followed by FREERTOS_SO_IP_DROP_MEMBERSHIP
 *       in close succession. The DROP may fail because the IP task hasn't handled the ADD yet.
 * - Documentation: The values used for FREERTOS_SO_IP_ADD_MEMBERSHIP and FREERTOS_SO_IP_DROP_MEMBERSHIP
 *       must be exactly the same. This includes the interface pointer!
 * - Documentation: Sockets are either IPv4 or v6, same applies to the groups they can subscribe to.
 * Topics to discuss over email or in a conference call:
 * - Integration with other hardware. For now, only SAME70 target has the proper functions for receive multicasts.
 * - Is local reception of outgoing multicasts really needed? In order to get that feature, we need code that handles every
 *       outgoing multicast as if it were an incoming packet and possibly duplicate it. I don't think this functionality is
 *       really needed and maybe we should leave it for possible future implementation if really needed by the community.
 *       This may also be needed if we want a send/receive demo to work on a single device. An alternative  would be to have a
 *       demo that sends to multicast_A and receives multicast_B and then have a PC-based python script that does the opposite.
 * Need Help Testing:
 * - Multiple interfaces receiving IGMP/MLD queries. Two sockets receiving the same multicast, one socket subscribed on
 *       all interfaces and another socket subscribed on just one of the interfaces. Are the proper reports getting scheduled and sent?
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

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
#include "FreeRTOS_IGMP.h"

/* Exclude the entire file if multicast support is not enabled. */
/* *INDENT-OFF* */
#if ( ipconfigIS_ENABLED( ipconfigSUPPORT_IP_MULTICAST ) )
/* *INDENT-ON* */

/*-----------------------------------------------------------*/

/** @brief A list that holds reports for all multicasts group addresses that this
 * host is subscribed to. The list holds entries for IGMP and MLD reports. */
static List_t prvMulticastReportsList;

static uint16_t prvIPv4_IGMP_Identification = 0;

/*-----------------------------------------------------------*/

static BaseType_t prvSendIGMPv2( IP_Address_t * pxGroupAddress,
                                 uint8_t ucMessageType,
                                 NetworkEndPoint_t * pxEndPoint );
static BaseType_t prvSendMLD_Report_v1( IP_Address_t * pxGroupAddress,
                                        NetworkEndPoint_t * pxEndPoint );

void prvScheduleMulticastReports( BaseType_t xIsIPv6,
                                  void * pvGroupAddress,
                                  NetworkInterface_t * pxInterface,
                                  BaseType_t xMaxCountdown );

static BaseType_t prvSendMulticastReport( MCastReportData_t * pxMRD,
                                          NetworkInterface_t * pxInterface );


/*-----------------------------------------------------------*/

void vIPMulticast_Init( void )
{
    MCastReportData_t * pxMRD;

    vListInitialise( &prvMulticastReportsList );
    #if ( ipconfigIGMP_SNOOPING != 0 )
        extern void vIgmpSnooping_Initialize( void );
        ( void ) vIgmpSnooping_Initialize();
    #endif

    #if ( ipconfigUSE_LLMNR != 0 )
        if( NULL != ( pxMRD = ( MCastReportData_t * ) pvPortMalloc( sizeof( MCastReportData_t ) ) ) )
        {
            listSET_LIST_ITEM_OWNER( &( pxMRD->xListItem ), ( void * ) pxMRD );
            pxMRD->pxInterface = NULL;
            pxMRD->xMCastGroupAddress.xIs_IPv6 = pdFALSE_UNSIGNED;
            pxMRD->xMCastGroupAddress.xIPAddress.ulIP_IPv4 = ipLLMNR_IP_ADDR;
            BaseType_t xReportDataConsumed = xEnlistMulticastReport( pxMRD );

            if( xReportDataConsumed == pdFALSE )
            {
                /* This should not happen, but if it does, free the memory that was used */
                vPortFree( pxMRD );
                pxMRD = NULL;
            }
        }

        #if ( ipconfigUSE_IPv6 == 1 )
            if( NULL != ( pxMRD = ( MCastReportData_t * ) pvPortMalloc( sizeof( MCastReportData_t ) ) ) )
            {
                listSET_LIST_ITEM_OWNER( &( pxMRD->xListItem ), ( void * ) pxMRD );
                pxMRD->pxInterface = NULL;
                pxMRD->xMCastGroupAddress.xIs_IPv6 = pdTRUE_UNSIGNED;
                memcpy( ( void * ) &pxMRD->xMCastGroupAddress.xIPAddress.xIP_IPv6.ucBytes[ 0 ], &ipLLMNR_IP_ADDR_IPv6.ucBytes[ 0 ], sizeof( IPv6_Address_t ) );
                BaseType_t xReportDataConsumed = xEnlistMulticastReport( pxMRD );

                if( xReportDataConsumed == pdFALSE )
                {
                    /* This should not happen, but if it does, free the memory that was used */
                    vPortFree( pxMRD );
                    pxMRD = NULL;
                }
            }
        #endif /* ( ipconfigUSE_IPv6 == 1) */
    #endif /* ipconfigUSE_LLMNR */

    #if ( ipconfigUSE_MDNS == 1 )
        if( NULL != ( pxMRD = ( MCastReportData_t * ) pvPortMalloc( sizeof( MCastReportData_t ) ) ) )
        {
            listSET_LIST_ITEM_OWNER( &( pxMRD->xListItem ), ( void * ) pxMRD );
            pxMRD->pxInterface = NULL;
            pxMRD->xMCastGroupAddress.xIs_IPv6 = pdFALSE_UNSIGNED;
            pxMRD->xMCastGroupAddress.xIPAddress.ulIP_IPv4 = ipMDNS_IP_ADDRESS;
            BaseType_t xReportDataConsumed = xEnlistMulticastReport( pxMRD );

            if( xReportDataConsumed == pdFALSE )
            {
                /* This should not happen, but if it does, free the memory that was used */
                vPortFree( pxMRD );
                pxMRD = NULL;
            }
        }

        #if ( ipconfigUSE_IPv6 == 1 )
            if( NULL != ( pxMRD = ( MCastReportData_t * ) pvPortMalloc( sizeof( MCastReportData_t ) ) ) )
            {
                listSET_LIST_ITEM_OWNER( &( pxMRD->xListItem ), ( void * ) pxMRD );
                pxMRD->pxInterface = NULL;
                pxMRD->xMCastGroupAddress.xIs_IPv6 = pdTRUE_UNSIGNED;
                memcpy( ( void * ) &pxMRD->xMCastGroupAddress.xIPAddress.xIP_IPv6.ucBytes[ 0 ], &ipMDNS_IP_ADDR_IPv6.ucBytes[ 0 ], sizeof( IPv6_Address_t ) );
                BaseType_t xReportDataConsumed = xEnlistMulticastReport( pxMRD );

                if( xReportDataConsumed == pdFALSE )
                {
                    /* This should not happen, but if it does, free the memory that was used */
                    vPortFree( pxMRD );
                    pxMRD = NULL;
                }
            }
        #endif /* ( ipconfigUSE_IPv6 == 1) ) */
    #endif /* ( ipconfigUSE_MDNS == 1) */

    /* Configure a periodic timer to generate events every 100ms.
     * Reuse the timer for MLD, even though MLD uses millisecond resolution. */
    vIPMulticastReportsTimerReload( pdMS_TO_TICKS( igmpTIMING_PERIOD_MS ) );
}

#if ( ipconfigUSE_IPv4 == 1 )

/**
 * @brief Process an IGMP packet.
 *
 * @param[in,out] pxIGMPPacket: The IP packet that contains the IGMP message.
 *
 * @return eReleaseBuffer This function usually returns eReleaseBuffer as IGMP reports are
 * scheduled for later. If however the user has implemented IGMP Snooping, the return is
 * controlled by the eApplicationIgmpFrameReceivedHook function. That function might return
 * eFrameConsumed if it decided to forward the frame somewhere.
 */
    eFrameProcessingResult_t eProcessIGMPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
    {
        eFrameProcessingResult_t eReturn = eReleaseBuffer;
        IGMPPacket_t * pxIGMPPacket;

        if( pxNetworkBuffer->xDataLength >= sizeof( IGMPPacket_t ) )
        {
            pxIGMPPacket = ( IGMPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

            if( igmpIGMP_MEMBERSHIP_QUERY == pxIGMPPacket->xIGMPHeader.ucMessageType )
            {
                prvScheduleMulticastReports( pdFALSE, ( void * ) &( pxIGMPPacket->xIGMPHeader.ulGroupAddress ), pxNetworkBuffer->pxInterface, ( uint16_t ) pxIGMPPacket->xIGMPHeader.ucMaxResponseTime );
            }

            #if ( ipconfigIGMP_SNOOPING != 0 )
                extern eFrameProcessingResult_t eApplicationIgmpFrameReceivedHook( NetworkBufferDescriptor_t * pxNetworkBuffer );
                eReturn = eApplicationIgmpFrameReceivedHook( pxNetworkBuffer );
            #endif /* ( ipconfigIGMP_SNOOPING != 0 ) */
        }

        return eReturn;
    }
#endif /*( ipconfigUSE_IPv4 == 1 ) */

#if ( ipconfigUSE_IPv6 == 1 )
    void vProcessMLDPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
    {
        /* Note: pxNetworkBuffer->xDataLength was already checked to be >= sizeof( MLDv1_Rx_Packet_t ) */
        const MLDv1_Rx_Packet_t * pxMLD_Packet;

        if( pxNetworkBuffer->xDataLength >= sizeof( MLDv1_Rx_Packet_t ) )
        {
            pxMLD_Packet = ( ( const MLDv1_Rx_Packet_t * ) pxNetworkBuffer->pucEthernetBuffer );

            if( pxMLD_Packet->xMLD.ucTypeOfMessage == ipICMP_MULTICAST_LISTENER_QUERY )
            {
                prvScheduleMulticastReports( pdTRUE, ( void * ) ( pxMLD_Packet->xMLD.xGroupAddress.ucBytes ), pxNetworkBuffer->pxInterface, ( FreeRTOS_ntohs( pxMLD_Packet->xMLD.usMaxResponseDelay ) / igmpTIMING_PERIOD_MS ) );
            }

            #if ( ipconfigIGMP_SNOOPING != 0 )
                extern eFrameProcessingResult_t eApplicationIgmpFrameReceivedHook( NetworkBufferDescriptor_t * pxNetworkBuffer );
                ( void ) eApplicationIgmpFrameReceivedHook( pxNetworkBuffer );
            #endif /* ( ipconfigIGMP_SNOOPING != 0 ) */
        }
    }
#endif /* ( ipconfigUSE_IPv4 == 1 ) */

void vRescheduleAllMulticastReports( NetworkInterface_t * pxInterface,
                                     BaseType_t xMaxCountdown )
{
    const ListItem_t * pxIterator;
    const ListItem_t * xEnd;
    uint32_t ulRandom;
    MCastReportData_t * pxMRD;

    if( xMaxCountdown < 1 )
    {
        xMaxCountdown = 1;
    }

    xEnd = listGET_END_MARKER( &prvMulticastReportsList );

    for( pxIterator = ( const ListItem_t * ) listGET_NEXT( xEnd );
         pxIterator != ( const ListItem_t * ) xEnd;
         pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator ) )
    {
        pxMRD = ( MCastReportData_t * ) listGET_LIST_ITEM_OWNER( pxIterator );

        if( ( pxInterface == pxMRD->pxInterface ) || ( pxMRD->pxInterface == NULL ) )
        {
            if( ( pxMRD->xCountDown < 0 ) || ( pxMRD->xCountDown >= xMaxCountdown ) )
            {
                if( xApplicationGetRandomNumber( &( ulRandom ) ) == pdFALSE )
                {
                    /* The random number generator failed. Schedule the report for immediate sending. */
                    ulRandom = 0;
                }
                else
                {
                    /* Everything went well. ulRandom now holds a good random value. */
                }

                /* Generate a random countdown between 0 and usMaxCountdown - 1. */
                pxMRD->xCountDown = ulRandom % xMaxCountdown;
            }
            else
            {
                /* The report is already scheduled for sooner than xMaxCountdown. Do nothing. */
            }
        }
        else
        {
            /* The multicast report is for a different interface. Do nothing. */
        }
    } /* for(;;) iterating over prvMulticastReportsList */
}

void prvScheduleMulticastReports( BaseType_t xIsIPv6,
                                  void * pvGroupAddress,
                                  NetworkInterface_t * pxInterface,
                                  BaseType_t xMaxCountdown )
{
    const ListItem_t * pxIterator;
    const ListItem_t * xEnd;
    uint32_t ulRandom;
    MCastReportData_t * pxMRD;
    const IPv6_Address_t * pxIPv6_GroupAddress;
    static uint32_t ulNonRandomCounter = 0; /* In case the random number generator fails have a "not so random number" ready. */

    /* Go through the list of IGMP reports and schedule them. Note, the IGMP event is set at 100ms */

    /* Sanity enforcement. Technically, there is nothing wrong with trying to schedule reports "right away",
     * but having xMaxCountdown = 0 will cause problems with the modulo operation further down.
     * IGMP maximum response time is stored in single byte. Every count represents 0.1s */
    if( xMaxCountdown < 1 )
    {
        xMaxCountdown = 1;
    }
    else if( xMaxCountdown > UINT8_MAX )
    {
        xMaxCountdown = UINT8_MAX;
    }

    xEnd = listGET_END_MARKER( &prvMulticastReportsList );

    for( pxIterator = ( const ListItem_t * ) listGET_NEXT( xEnd );
         pxIterator != ( const ListItem_t * ) xEnd;
         pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator ) )
    {
        BaseType_t xReschedule = pdFALSE;
        pxMRD = ( MCastReportData_t * ) listGET_LIST_ITEM_OWNER( pxIterator );

        /* Make sure IP versions are the same. */
        if( xIsIPv6 != pxMRD->xMCastGroupAddress.xIs_IPv6 )
        {
            continue;
        }

        if( xIsIPv6 )
        {
            /* IPv6 MLD */
            pxIPv6_GroupAddress = ( const IPv6_Address_t * ) pvGroupAddress;

            /* Skip ahead for specific queries that do not match this report's address. */
            if( ( memcmp( pxIPv6_GroupAddress->ucBytes, FreeRTOS_in6addr_any.ucBytes, sizeof( IPv6_Address_t ) ) != 0 ) &&
                ( ( memcmp( pxIPv6_GroupAddress->ucBytes, pxMRD->xMCastGroupAddress.xIPAddress.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) ) != 0 ) )
            {
                continue;
            }

            /* Lastly, only reschedule if the report is for all interfaces or the interface that this query arrived on. */
            if( ( pxMRD->pxInterface == NULL ) || ( pxMRD->pxInterface == pxInterface ) )
            {
                xReschedule = pdTRUE;
            }
        }
        else
        {
            /* IPv4 IGMP*/
            uint32_t * pulQueryGroupAddress;
            pulQueryGroupAddress = ( uint32_t * ) pvGroupAddress;

            /* Skip ahead for specific queries that do not match this report's address. */
            if( ( *pulQueryGroupAddress != 0U ) && ( *pulQueryGroupAddress != pxMRD->xMCastGroupAddress.xIPAddress.ulIP_IPv4 ) )
            {
                continue;
            }

            /* Lastly, only reschedule if the report is for all interfaces or the interface that this query arrived on. */
            if( ( pxMRD->pxInterface == NULL ) || ( pxMRD->pxInterface == pxInterface ) )
            {
                xReschedule = pdTRUE;
            }
        }

        if( xReschedule )
        {
            /* This report needs to be scheduled for sending. Remember that it may already be scheduled.
             * Negative pxMRD->xCountDown means the report is not scheduled to be sent. If a report is scheduled, and it's
             * scheduled time is before usMaxCountdown, there is nothing to be done. If a
             * report is scheduled for later than usMaxCountdown, or not scheduled at all, we need
             * to schedule it for a random time between 0 and usMaxCountdown - 1. */
            if( ( pxMRD->xCountDown < 0 ) || ( pxMRD->xCountDown >= xMaxCountdown ) )
            {
                if( xApplicationGetRandomNumber( &( ulRandom ) ) == pdFALSE )
                {
                    /* The world is ending, our random number generator has failed. Use a not very random up-counter. */
                    ulRandom = ulNonRandomCounter;
                    ulNonRandomCounter++;
                }

                /* Generate a random countdown between 0 and usMaxCountdown - 1. */
                pxMRD->xCountDown = ulRandom % xMaxCountdown;
            }
            else
            {
                /* This report is currently scheduled to be sent earlier than usMaxCountdown.
                 * Do nothing. */
            }
        }
    } /* for(;;) iterating over prvMulticastReportsList */
}

/**
 * @brief Helper function for vHandleIGMP_Event. Sends an IGMP or MLD report.
 *
 * @param[in] pxMRD The struct describing the report.
 * @param[in] pxInterface The network interface on which the report should be sent.
 */
static BaseType_t prvSendMulticastReport( MCastReportData_t * pxMRD,
                                          NetworkInterface_t * pxInterface )
{
    NetworkEndPoint_t * pxEndPoint;
    NetworkEndPoint_t * pxSelectedEndPoint = NULL;
    BaseType_t xReturn = pdFAIL;

    /* For every end-point of the current interface, pick the first one that is
     * usable as an outgoing end-point for the current multicast report. */
    for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
         pxEndPoint != NULL;
         pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
    {
        /* Skip sending IPv4 reports on IPv6 end-points and vice-versa */
        if( pxMRD->xMCastGroupAddress.xIs_IPv6 != pxEndPoint->bits.bIPv6 )
        {
            continue;
        }

        /* Skip trying to send on end-points that are not UP */
        if( pxEndPoint->bits.bEndPointUp == pdFALSE )
        {
            continue;
        }

        /* Remember the last end-point that fits our search */
        pxSelectedEndPoint = pxEndPoint;

        if( pxMRD->xMCastGroupAddress.xIs_IPv6 == pdTRUE )
        {
            #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )

                /* IPv6 MLD report and end-point.
                 * Only send from the link-local end-point.
                 * https://www.rfc-editor.org/rfc/rfc2710#section-3
                 * https://www.rfc-editor.org/rfc/rfc3810#section-5
                 * If we can't find a link-local end-point, default to the last seen IPv6 end-point.
                 * In this case, prvSendMLD_Report_v1() will set the source address to "::"
                 * https://www.rfc-editor.org/rfc/rfc3810#section-5.2.13 allows it. */
                if( xIPv6_GetIPType( &( pxEndPoint->ipv6_settings.xIPAddress ) ) == eIPv6_LinkLocal )
                {
                    /* Found a link-local end-point. The search is over. */
                    break;
                }
                else
                {
                    /* This IPv6 end-point is not link-local, keep on searching. */
                }
            #endif /* if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) ) */
        }
        else
        {
            #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )

                /* IPv4 IGMP report and end-point.
                 * Note: the way I interpret
                 * https://www.rfc-editor.org/rfc/rfc2236#section-10
                 * https://www.rfc-editor.org/rfc/rfc3376#section-4.2.13
                 * https://www.rfc-editor.org/rfc/rfc3376#section-9.2
                 * Sending reports from any source IPv4 including 0.0.0.0 is allowed,
                 * so any IPv4 end-point will do and the search is over. */
                break;
            #endif
        }
    } /* end-point for(;;) */

    if( pxSelectedEndPoint != NULL )
    {
        if( pxMRD->xMCastGroupAddress.xIs_IPv6 == pdTRUE )
        {
            #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
                xReturn = prvSendMLD_Report_v1( &( pxMRD->xMCastGroupAddress.xIPAddress ), pxSelectedEndPoint );
            #endif
        }
        else
        {
            #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )
                xReturn = prvSendIGMPv2( &( pxMRD->xMCastGroupAddress.xIPAddress ), igmpIGMP_MEMBERSHIP_REPORT_V2, pxSelectedEndPoint );
            #endif
        }
    }

    return xReturn;
}

void vIPMulticast_HandleTimerEvent( void )
{
    /* Go through the list of IGMP reports and send anything that needs to be sent. */
    const ListItem_t * pxIterator;
    const ListItem_t * xEnd = listGET_END_MARKER( &prvMulticastReportsList );
    MCastReportData_t * pxMRD;

    for( pxIterator = ( const ListItem_t * ) listGET_NEXT( xEnd ); pxIterator != ( const ListItem_t * ) xEnd; pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator ) )
    {
        pxMRD = ( MCastReportData_t * ) listGET_LIST_ITEM_OWNER( pxIterator );

        /* Decrement down to 0. Decrementing from 0 to -1 triggers the sending of the scheduled report. */
        if( pxMRD->xCountDown > 0 )
        {
            pxMRD->xCountDown--;
        }
        else if( pxMRD->xCountDown == 0 )
        {
            /* Time to send a report...*/
            /* If the interface is NULL, the report should be sent on all interfaces. */
            if( pxMRD->pxInterface == NULL )
            {
                NetworkInterface_t * pxInterface;

                /* Go through all interfaces. */
                for( pxInterface = FreeRTOS_FirstNetworkInterface();
                     pxInterface != NULL;
                     pxInterface = FreeRTOS_NextNetworkInterface( pxInterface ) )
                {
                    if( prvSendMulticastReport( pxMRD, pxInterface ) == pdPASS )
                    {
                        /* Success on any interface counts... */
                        /* ToDo: This should change once I add per-interface lists. */
                        pxMRD->xCountDown = ipconfigPERIODIC_MULTICAST_REPORT_INTERVAL;
                    }
                }
            }
            else
            {
                /* The report is assigned to a specific interface */
                if( prvSendMulticastReport( pxMRD, pxMRD->pxInterface ) == pdPASS )
                {
                    /* Success */
                    pxMRD->xCountDown = ipconfigPERIODIC_MULTICAST_REPORT_INTERVAL;
                }
                else
                {
                    /* The report could not be sent. Doing nothing here will result in a retry the next time this event is called. */
                }
            }
        }
        else
        {
            /* ( pxMRD->xCountDown < 0 )
             * Do nothing. */
        }
    } /* for(;;) loop iterating over the list of multicast reports */

    #if ( ipconfigIGMP_SNOOPING != 0 )
        extern void vApplicationIgmpEventHook( void );
        ( void ) vApplicationIgmpEventHook();
    #endif
}

/**
 * @brief Send an IGMP/MLD event.
 *
 * @return pdPASS or pdFAIL, depending on whether xSendEventStructToIPTask()
 *         succeeded.
 */
BaseType_t xSendMulticastTimerEvent( void )
{
    IPStackEvent_t xEventMessage;
    const TickType_t uxDontBlock = 0U;
    uintptr_t uxOption = 0U;

    xEventMessage.eEventType = eMulticastTimerEvent;
    xEventMessage.pvData = ( void * ) uxOption;

    return xSendEventStructToIPTask( &xEventMessage, uxDontBlock );
}


/**
 * @brief Locates the IGMP/MLD report for this group. Decrements its socket counter and
 * if the counter becomes zero, removes the report from the list and frees it.
 *
 * @param[in] pxInterface: The network interface on which the report is scheduled.
 * @param[in] pxMulticastAddress: The multicast group descriptor the specifies the group and interface.
 * @param[in] uxIsIPv6: pdTRUE if pxMulticastAddress is a pointer to an IPv6 group address, pdFALSE otherwise.
 */
void vDelistMulticastReport( NetworkInterface_t * pxInterface,
                             IP_Address_t * pxMulticastAddress,
                             UBaseType_t uxIsIPv6 )
{
    const ListItem_t * pxIterator;
    const ListItem_t * xEnd = listGET_END_MARKER( &prvMulticastReportsList );
    MCastReportData_t * pxMRD;

    #ifdef FreeRTOS_debug_printf
    {
        uint8_t ucMCastGroupAddressString[ ( 45 + 1 ) ] = { 0 };

        if( uxIsIPv6 == pdTRUE_UNSIGNED )
        {
            #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
                FreeRTOS_inet_ntop6( &pxMulticastAddress->xIP_IPv6.ucBytes[ 0 ], ucMCastGroupAddressString, ( 45 + 1 ) );
                FreeRTOS_debug_printf( ( "vDelistMulticastReport %s", ucMCastGroupAddressString ) );
            #endif
        }
        else
        {
            #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )
                FreeRTOS_inet_ntop4( &pxMulticastAddress->ulIP_IPv4, ucMCastGroupAddressString, ( 45 + 1 ) );
                FreeRTOS_debug_printf( ( "vDelistMulticastReport %s", ucMCastGroupAddressString ) );
            #endif
        }
    }
    #endif /* FreeRTOS_debug_printf */

    for( pxIterator = ( const ListItem_t * ) listGET_NEXT( xEnd );
         pxIterator != ( const ListItem_t * ) xEnd;
         pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator ) )
    {
        pxMRD = ( MCastReportData_t * ) listGET_LIST_ITEM_OWNER( pxIterator );

        if( pxMRD->pxInterface == pxInterface )
        {
            if( pxMRD->xMCastGroupAddress.xIs_IPv6 == pdTRUE_UNSIGNED )
            {
                if( 0 == memcmp( pxMRD->xMCastGroupAddress.xIPAddress.xIP_IPv6.ucBytes, pxMulticastAddress->xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) )
                {
                    break;
                }
                else
                {
                    /* Address is different Do Nothing. */
                }
            }
            else
            {
                if( pxMRD->xMCastGroupAddress.xIPAddress.ulIP_IPv4 == pxMulticastAddress->ulIP_IPv4 )
                {
                    break;
                }
                else
                {
                    /* Address is different Do Nothing. */
                }
            }
        }
        else
        {
            /* Network interface is different Do Nothing. */
        }
    } /* for(;;) over prvMulticastReportsList */

    if( pxIterator != xEnd )
    {
        /* Found a match. */
        if( pxMRD->xNumSockets > 0 )
        {
            pxMRD->xNumSockets--;
        }

        if( 0 == pxMRD->xNumSockets )
        {
            if( pxMRD->xMCastGroupAddress.xIs_IPv6 )
            {
                /* Todo: Handle leaving IPv6 multicast group. */
            }
            else
            {
                #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )
                    prvSendIGMPv2( &( pxMRD->xMCastGroupAddress.xIPAddress ), igmpIGMP_LEAVE_GROUP, FreeRTOS_FirstEndPoint( NULL ) );
                #endif
            }

            ( void ) uxListRemove( &pxMRD->xListItem );
            vPortFree( pxMRD );
        }
    }
}

/**
 * @brief Adds an IGMP/MLD report to the global list of reports.
 *
 * @param[in] pNewEntry: The multicast group data that describes the report.
 */
BaseType_t xEnlistMulticastReport( struct MCastReportDescription * pNewEntry )
{
    const ListItem_t * pxIterator;
    const ListItem_t * xEnd = listGET_END_MARKER( &prvMulticastReportsList );
    MCastReportData_t * pxMRD;
    UBaseType_t bFoundDuplicate = pdFALSE_UNSIGNED;

    configASSERT( pNewEntry != NULL );

    #ifdef FreeRTOS_debug_printf
    {
        uint8_t ucMCastGroupAddressString[ ( 45 + 1 ) ] = { 0 };

        if( pNewEntry->xMCastGroupAddress.xIs_IPv6 == pdTRUE_UNSIGNED )
        {
            #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )
                FreeRTOS_inet_ntop6( &pNewEntry->xMCastGroupAddress.xIPAddress.xIP_IPv6.ucBytes[ 0 ], ucMCastGroupAddressString, ( 45 + 1 ) );
                FreeRTOS_debug_printf( ( "xEnlistMulticastReport %s", ucMCastGroupAddressString ) );
            #endif
        }
        else
        {
            #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )
                FreeRTOS_inet_ntop4( &pNewEntry->xMCastGroupAddress.xIPAddress.ulIP_IPv4, ucMCastGroupAddressString, ( 45 + 1 ) );
                FreeRTOS_debug_printf( ( "xEnlistMulticastReport %s", ucMCastGroupAddressString ) );
            #endif
        }
    }
    #endif /* FreeRTOS_debug_printf */

    /* Try to find a duplicate entry. A duplicate is a report entry with the same IP address AND the same
     * network interface. It is important that we include the interface in the check as well because
     * we may have multiple sockets subscribed to the same address but on different interfaces.
     * Example: Socket_A subsribes to ff02::17 on eth0. Later Socket_B subscribes to ff02::17 on ALL interfaces.
     * The reports for the two sockets are scheduled differently, so they cannot be bundled into a single entry. */
    for( pxIterator = ( const ListItem_t * ) listGET_NEXT( xEnd );
         pxIterator != ( const ListItem_t * ) xEnd;
         pxIterator = ( const ListItem_t * ) listGET_NEXT( pxIterator ) )
    {
        pxMRD = ( MCastReportData_t * ) listGET_LIST_ITEM_OWNER( pxIterator );

        if( pxMRD->pxInterface == pNewEntry->pxInterface )
        {
            if( pxMRD->xMCastGroupAddress.xIs_IPv6 == pdTRUE_UNSIGNED )
            {
                if( memcmp( &pxMRD->xMCastGroupAddress.xIPAddress.xIP_IPv6.ucBytes[ 0 ], &pNewEntry->xMCastGroupAddress.xIPAddress.xIP_IPv6.ucBytes[ 0 ], sizeof( IPv6_Address_t ) ) == 0 )
                {
                    bFoundDuplicate = pdTRUE_UNSIGNED;
                    break;
                }
                else
                {
                    /* Address is different Do Nothing. */
                }
            }
            else
            {
                if( pxMRD->xMCastGroupAddress.xIPAddress.ulIP_IPv4 == pNewEntry->xMCastGroupAddress.xIPAddress.ulIP_IPv4 )
                {
                    bFoundDuplicate = pdTRUE_UNSIGNED;
                    break;
                }
                else
                {
                    /* Address is different Do Nothing. */
                }
            }
        }
        else
        {
            /* Network interface is different Do Nothing. */
        }
    } /* for(;;) over prvMulticastReportsList */

    if( bFoundDuplicate == pdTRUE_UNSIGNED )
    {
        /* Found a duplicate. All IGMP snooping switches already know that we are interested.
         * Just keep track of how many sockets are interested in this multicast group. */
        pxMRD->xNumSockets++;
    }
    else
    {
        /* Not found. */
        pNewEntry->xNumSockets = 1;

        /* Schedule an unsolicited report to quickly inform IGMP snooping switches that we want
         * to receive this multicast group. */
        pNewEntry->xCountDown = 0;
        vListInsertEnd( &prvMulticastReportsList, &( pNewEntry->xListItem ) );
    }

    /* Inform the caller whether we consumed the item or not. */
    return ( bFoundDuplicate == pdTRUE_UNSIGNED ) ? pdFALSE : pdTRUE;
}



#if ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )
    static BaseType_t prvSendIGMPv2( IP_Address_t * pxGroupAddress,
                                     uint8_t ucMessageType,
                                     NetworkEndPoint_t * pxEndPoint )
    {
        NetworkBufferDescriptor_t * pxNetworkBuffer;
        IGMPPacket_t * pxIGMPPacket;
        portBASE_TYPE xReturn = pdFAIL;

        configASSERT( pxEndPoint != NULL );

        if( NULL != ( pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( sizeof( IGMPPacket_t ), 0 ) ) )
        {
            pxIGMPPacket = ( IGMPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
            uint16_t usEthType = ipIPv4_FRAME_TYPE;

            /* Fill out the Ethernet header */
            vSetMultiCastIPv4MacAddress( pxGroupAddress->ulIP_IPv4, &pxIGMPPacket->xEthernetHeader.xDestinationAddress );
            memcpy( ( void * ) pxIGMPPacket->xEthernetHeader.xSourceAddress.ucBytes, ( void * ) pxEndPoint->xMACAddress.ucBytes, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
            memcpy( ( void * ) &pxIGMPPacket->xEthernetHeader.usFrameType, ( void * ) &usEthType, sizeof( uint16_t ) );


            IPHeader_t * pxIPHeader;

            pxIPHeader = &( pxIGMPPacket->xIPHeader );

            pxIGMPPacket->xIGMPHeader.ucMessageType = ucMessageType;
            pxIGMPPacket->xIGMPHeader.ucMaxResponseTime = 0;
            pxIGMPPacket->xIGMPHeader.ulGroupAddress = pxGroupAddress->ulIP_IPv4;

            pxIPHeader->ulDestinationIPAddress = pxGroupAddress->ulIP_IPv4;
            pxIPHeader->ulSourceIPAddress = pxEndPoint->ipv4_settings.ulIPAddress;
            pxIPHeader->ucProtocol = ipPROTOCOL_IGMP;
            pxIPHeader->usLength = ( uint16_t ) ( 0 + sizeof( IPHeader_t ) + sizeof( IGMPHeader_t ) );
            pxIPHeader->usLength = FreeRTOS_htons( pxIPHeader->usLength );
            pxIPHeader->ucVersionHeaderLength = 0x45U; /*ipIPV4_VERSION_HEADER_LENGTH_MIN; */
            pxIPHeader->ucDifferentiatedServicesCode = 0;
            pxIPHeader->usIdentification = FreeRTOS_ntohs( prvIPv4_IGMP_Identification );
            prvIPv4_IGMP_Identification++;
            pxIPHeader->ucTimeToLive = 1;
            pxIPHeader->usHeaderChecksum = 0U;

            /* The stack doesn't support fragments, so the fragment offset field must always be zero.
             * The header was never memset to zero, so set both the fragment offset and fragmentation flags in one go.
             */
            #if ( ipconfigFORCE_IP_DONT_FRAGMENT != 0 )
                pxIPHeader->usFragmentOffset = ipFRAGMENT_FLAGS_DONT_FRAGMENT;
            #else
                pxIPHeader->usFragmentOffset = 0U;
            #endif


            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
            {
                pxIPHeader->usHeaderChecksum = 0U;
                pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
                pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );
            }
            #endif

            /* Calculate frame length */
            pxNetworkBuffer->xDataLength = sizeof( IGMPPacket_t );

            #if ( ipconfigIGMP_SNOOPING != 0 )

                /* Because we are doing IGMP snooping, let the IGMP Snooping module decide
                 * which port this packet needs to be sent to. */
                extern void vApplicationIgmpSendLocalMessageHook( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                                  uint8_t ucIgmpMsgType,
                                                                  uint32_t uiMulticastGroup );
                ( void ) vApplicationIgmpSendLocalMessageHook( pxNetworkBuffer, ucIgmpMsgType, uiMulticastGroup_NBO );
            #else

                /* Since this is a normal host without an attached switch and IGMP snooping,
                 * we simply send the frame out */
                pxEndPoint->pxNetworkInterface->pfOutput( pxEndPoint->pxNetworkInterface, pxNetworkBuffer, pdTRUE );
            #endif

            xReturn = pdPASS;
        }
        else
        {
            /* Could not allocate a buffer */
        }

        return xReturn;
    }

#endif /* ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) ) */

#if ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) )

/**
 * @brief Send an ICMPv6 Multicast Listener Report version 1.
 *
 * @param[in] pxGroupAddress The multicast group address to that the report is for.
 * @param[in] pxEndPoint The outgoing end-point.
 *
 * @return pdPASS/pdFAIL
 */
    static BaseType_t prvSendMLD_Report_v1( IP_Address_t * pxGroupAddress,
                                            NetworkEndPoint_t * pxEndPoint )
    {
        NetworkBufferDescriptor_t * pxNetworkBuffer;
        MLDv1_Tx_Packet_t * pxMLRPacket;
        BaseType_t xReturn = pdFAIL;

        configASSERT( pxEndPoint != NULL );

        if( ( ( pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( sizeof( MLDv1_Tx_Packet_t ), 0 ) ) != NULL ) )
        {
            pxNetworkBuffer->pxEndPoint = pxEndPoint;

            configASSERT( pxEndPoint->pxNetworkInterface != NULL );

            /* MISRA Ref 11.3.1 [Misaligned access] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            pxMLRPacket = ( ( MLDv1_Tx_Packet_t * ) pxNetworkBuffer->pucEthernetBuffer );
            pxNetworkBuffer->xDataLength = sizeof( MLDv1_Tx_Packet_t );

            /* MLD Reports version 1 are sent to the MAC address corresponding to the multicast address. */
            vSetMultiCastIPv6MacAddress( &( pxGroupAddress->xIP_IPv6 ), &pxMLRPacket->xEthernetHeader.xDestinationAddress );
            ( void ) memcpy( pxMLRPacket->xEthernetHeader.xSourceAddress.ucBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
            pxMLRPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE; /* 12 + 2 = 14 */

            pxMLRPacket->xIPHeader.ucVersionTrafficClass = 0x60;
            pxMLRPacket->xIPHeader.ucTrafficClassFlow = 0;
            pxMLRPacket->xIPHeader.usFlowLabel = 0;

            pxMLRPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( sizeof( ICMPHeader_IPv6_t ) );
            pxMLRPacket->xIPHeader.ucNextHeader = ipIPv6_EXT_HEADER_HOP_BY_HOP;
            pxMLRPacket->xIPHeader.ucHopLimit = 1;

            if( xIPv6_GetIPType( &( pxEndPoint->ipv6_settings.xIPAddress ) ) == eIPv6_LinkLocal )
            {
                /* This end-point has a link-local address. Use it. */
                ( void ) memcpy( pxMLRPacket->xIPHeader.xSourceAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
            }
            else
            {
                /* This end-point doesn't have a link-local address or it still has not */
                /* completed it's DAD ( Duplicate Address Detection ) */
                /* Use "::" as described in https://www.rfc-editor.org/rfc/rfc3810#section-5.2.13 */
                memset( pxMLRPacket->xIPHeader.xSourceAddress.ucBytes, 0x00, ipSIZE_OF_IPv6_ADDRESS );
            }

            ( void ) memcpy( pxMLRPacket->xIPHeader.xDestinationAddress.ucBytes, pxGroupAddress->xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

            /* Fill out the Hop By Hop Router Alert option extension header */
            pxMLRPacket->xRAOption.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
            pxMLRPacket->xRAOption.ucHeaderExtLength = 0;
            pxMLRPacket->xRAOption.xRouterAlert.ucType = ipHOP_BY_HOP_ROUTER_ALERT;
            pxMLRPacket->xRAOption.xRouterAlert.ucLength = sizeof( uint16_t );
            pxMLRPacket->xRAOption.xRouterAlert.usValue = FreeRTOS_htons( ipROUTER_ALERT_VALUE_MLD );
            pxMLRPacket->xRAOption.xPadding.ucType = ipHOP_BY_HOP_PadN;
            pxMLRPacket->xRAOption.xPadding.ucLength = 0; /* in multiples of 8 octets, not counting the first 8 */

            pxMLRPacket->xMLD.ucTypeOfMessage = ipICMP_MULTICAST_LISTENER_REPORT_V1;
            pxMLRPacket->xMLD.ucTypeOfService = 0;
            pxMLRPacket->xMLD.usMaxResponseDelay = FreeRTOS_htons( 0 );
            pxMLRPacket->xMLD.usReserved = FreeRTOS_htons( 0 );
            ( void ) memcpy( pxMLRPacket->xMLD.xGroupAddress.ucBytes, pxGroupAddress->xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
            {
                /* calculate the ICMPv6 checksum for outgoing package */
                ( void ) usGenerateProtocolChecksum( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE );
            }
            #else
            {
                /* Many EMAC peripherals will only calculate the ICMP checksum
                 * correctly if the field is nulled beforehand. */
                pxMLRPacket->xMLD.usChecksum = 0;
            }
            #endif

            if( pxEndPoint->pxNetworkInterface->pfOutput != NULL )
            {
                ( void ) pxEndPoint->pxNetworkInterface->pfOutput( pxEndPoint->pxNetworkInterface, pxNetworkBuffer, pdTRUE );
                xReturn = pdPASS;
            }
        }

        return xReturn;
    }

#endif /* ( ipconfigIS_ENABLED( ipconfigUSE_IPv6 ) ) */


/************************************************************************/
/* Test code below this point                                           */
/************************************************************************/


/*-----------------------------------------------------------*/


/* *INDENT-OFF* */
#endif /* ipconfigIS_ENABLED( ipconfigSUPPORT_IP_MULTICAST ) */
/* *INDENT-ON* */
