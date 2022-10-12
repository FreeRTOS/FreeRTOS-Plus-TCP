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
 * @file FreeRTOS_IP_Utils.c
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
#include "FreeRTOS_IP_Utils.h"
#include "FreeRTOS_IP_Timers.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"

/* Used to ensure the structure packing is having the desired effect.  The
 * 'volatile' is used to prevent compiler warnings about comparing a constant with
 * a constant. */
#ifndef _lint
    #define ipEXPECTED_EthernetHeader_t_SIZE    ( ( size_t ) 14 ) /**< Ethernet Header size in bytes. */
    #define ipEXPECTED_ARPHeader_t_SIZE         ( ( size_t ) 28 ) /**< ARP header size in bytes. */
    #define ipEXPECTED_IPHeader_t_SIZE          ( ( size_t ) 20 ) /**< IP header size in bytes. */
    #define ipEXPECTED_IGMPHeader_t_SIZE        ( ( size_t ) 8 )  /**< IGMP header size in bytes. */
    #define ipEXPECTED_ICMPHeader_t_SIZE        ( ( size_t ) 8 )  /**< ICMP header size in bytes. */
    #define ipEXPECTED_UDPHeader_t_SIZE         ( ( size_t ) 8 )  /**< UDP header size in bytes. */
    #define ipEXPECTED_TCPHeader_t_SIZE         ( ( size_t ) 20 ) /**< TCP header size in bytes. */
#endif

/** @brief Time delay between repeated attempts to initialise the network hardware. */
#ifndef ipINITIALISATION_RETRY_DELAY
    #define ipINITIALISATION_RETRY_DELAY    ( pdMS_TO_TICKS( 3000U ) )
#endif

#if ( ipconfigUSE_NETWORK_EVENT_HOOK == 1 )
    /* used for unit testing */

/* MISRA Ref 8.9.1 [File scoped variables] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-89 */
/* coverity[misra_c_2012_rule_8_9_violation] */
/* coverity[single_use] */
    static BaseType_t xCallEventHook = pdFALSE;
#endif

#if ( ipconfigHAS_PRINTF != 0 )
    /** @brief Last value of minimum buffer count. */
    static UBaseType_t uxLastMinBufferCount = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;

/** @brief Last value of minimum size. Used in printing resource stats. */
    static size_t uxMinLastSize = 0u;
#endif

#if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 ) && ( ipconfigHAS_PRINTF != 0 )
    static UBaseType_t uxLastMinQueueSpace = 0;
#endif

/**
 * Used in checksum calculation.
 */
typedef union _xUnion32
{
    uint32_t u32;      /**< The 32-bit member of the union. */
    uint16_t u16[ 2 ]; /**< The array of 2 16-bit members of the union. */
    uint8_t u8[ 4 ];   /**< The array of 4 8-bit members of the union. */
} xUnion32;

/**
 * Used in checksum calculation.
 */
typedef union _xUnionPtr
{
    const uint32_t * u32ptr; /**< The pointer member to a 32-bit variable. */
    const uint16_t * u16ptr; /**< The pointer member to a 16-bit variable. */
    const uint8_t * u8ptr;   /**< The pointer member to an 8-bit variable. */
} xUnionPtr;

/*
 * Returns the network buffer descriptor that owns a given packet buffer.
 */
static NetworkBufferDescriptor_t * prvPacketBuffer_to_NetworkBuffer( const void * pvBuffer,
                                                                     size_t uxOffset );

#if ( ipconfigUSE_DHCP != 0 )

/**
 * @brief Create a DHCP event.
 *
 * @return pdPASS or pdFAIL, depending on whether xSendEventStructToIPTask()
 *         succeeded.
 */
    BaseType_t xSendDHCPEvent( void )
    {
        IPStackEvent_t xEventMessage;
        const TickType_t uxDontBlock = 0U;
        uintptr_t uxOption = ( uintptr_t ) eGetDHCPState();

        xEventMessage.eEventType = eDHCPEvent;

        /* MISRA Ref 11.6.1 [DHCP events and conversion to void] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-116 */
        /* coverity[misra_c_2012_rule_11_6_violation] */
        xEventMessage.pvData = ( void * ) uxOption;

        return xSendEventStructToIPTask( &xEventMessage, uxDontBlock );
    }
/*-----------------------------------------------------------*/
#endif /* ( ipconfigUSE_DHCP != 0 ) */

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

    pxMACAddress->ucBytes[ 0 ] = ( uint8_t ) 0x01U;
    pxMACAddress->ucBytes[ 1 ] = ( uint8_t ) 0x00U;
    pxMACAddress->ucBytes[ 2 ] = ( uint8_t ) 0x5EU;
    pxMACAddress->ucBytes[ 3 ] = ( uint8_t ) ( ( ulIP >> 16 ) & 0x7fU ); /* Use 7 bits. */
    pxMACAddress->ucBytes[ 4 ] = ( uint8_t ) ( ( ulIP >> 8 ) & 0xffU );  /* Use 8 bits. */
    pxMACAddress->ucBytes[ 5 ] = ( uint8_t ) ( ( ulIP ) & 0xffU );       /* Use 8 bits. */
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
    size_t uxLengthToCopy = uxNewLength;

    /* This function is only used when 'ipconfigZERO_COPY_TX_DRIVER' is set to 1.
     * The transmit routine wants to have ownership of the network buffer
     * descriptor, because it will pass the buffer straight to DMA. */
    pxNewBuffer = pxGetNetworkBufferWithDescriptor( uxNewLength, ( TickType_t ) 0 );

    if( pxNewBuffer != NULL )
    {
        /* Get the minimum of both values to copy the data. */
        if( uxLengthToCopy > pxNetworkBuffer->xDataLength )
        {
            uxLengthToCopy = pxNetworkBuffer->xDataLength;
        }

        /* Set the actual packet size in case a bigger buffer than requested
         * was returned. */
        pxNewBuffer->xDataLength = uxNewLength;

        /* Copy the original packet information. */
        pxNewBuffer->ulIPAddress = pxNetworkBuffer->ulIPAddress;
        pxNewBuffer->usPort = pxNetworkBuffer->usPort;
        pxNewBuffer->usBoundPort = pxNetworkBuffer->usBoundPort;
        ( void ) memcpy( pxNewBuffer->pucEthernetBuffer, pxNetworkBuffer->pucEthernetBuffer, uxLengthToCopy );
    }

    return pxNewBuffer;
}
/*-----------------------------------------------------------*/

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

        /* MISRA Ref 11.6.2 [Pointer arithmetic and hidden pointer] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-116 */
        /* coverity[misra_c_2012_rule_11_6_violation] */
        uxBuffer = ( uintptr_t ) pvBuffer;

        /* The input here is a pointer to a packet buffer plus some offset.  Subtract
         * this offset, and also the size of the header in the network buffer, usually
         * 8 + 2 bytes. */
        uxBuffer -= ( uxOffset + ipBUFFER_PADDING );

        /* Here a pointer was placed to the network descriptor.  As a
         * pointer is dereferenced, make sure it is well aligned. */
        if( ( uxBuffer & ( ( ( uintptr_t ) sizeof( uxBuffer ) ) - 1U ) ) == ( uintptr_t ) 0U )
        {
            /* MISRA Ref 11.4.2 [Validation of pointer alignment] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
            /* coverity[misra_c_2012_rule_11_4_violation] */
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
    return prvPacketBuffer_to_NetworkBuffer( pvBuffer, sizeof( UDPPacket_t ) );
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
    const struct tskTaskControlBlock * const xCurrentHandle = xTaskGetCurrentTaskHandle();
    const struct tskTaskControlBlock * const xCurrentIPTaskHandle = FreeRTOS_GetIPTaskHandle();

    if( xCurrentHandle == xCurrentIPTaskHandle )
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
 * @brief Process a 'Network down' event and complete required processing.
 */
/* MISRA Ref 8.9.1 [File scoped variables] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-89 */
/* coverity[misra_c_2012_rule_8_9_violation] */
/* coverity[single_use] */
void prvProcessNetworkDownEvent( void )
{
    /* Stop the ARP timer while there is no network. */
    vIPSetARPTimerEnableState( pdFALSE );

    #if ( ipconfigUSE_NETWORK_EVENT_HOOK == 1 )
        {
            /* The first network down event is generated by the IP stack itself to
             * initialise the network hardware, so do not call the network down event
             * the first time through. */
            if( xCallEventHook == pdTRUE )
            {
                vApplicationIPNetworkEventHook( eNetworkDown );
            }

            xCallEventHook = pdTRUE;
        }
    #endif /* if ipconfigUSE_NETWORK_EVENT_HOOK == 1 */

    /* Per the ARP Cache Validation section of https://tools.ietf.org/html/rfc1122,
     * treat network down as a "delivery problem" and flush the ARP cache for this
     * interface. */
    FreeRTOS_ClearARP();

    /* The network has been disconnected (or is being initialised for the first
     * time).  Perform whatever hardware processing is necessary to bring it up
     * again, or wait for it to be available again.  This is hardware dependent. */
    if( xNetworkInterfaceInitialise() != pdPASS )
    {
        /* Ideally the network interface initialisation function will only
         * return when the network is available.  In case this is not the case,
         * wait a while before retrying the initialisation. */
        vTaskDelay( ipINITIALISATION_RETRY_DELAY );
        FreeRTOS_NetworkDown();
    }
    else
    {
        /* Set remaining time to 0 so it will become active immediately. */
        #if ipconfigUSE_DHCP == 1
            {
                /* The network is not up until DHCP has completed. */
                vDHCPProcess( pdTRUE, eInitialWait );
            }
        #else
            {
                /* Perform any necessary 'network up' processing. */
                vIPNetworkUpCalls();
            }
        #endif
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Check the values of configuration options and assert on it. Also verify that the IP-task
 *        has not already been initialized.
 */
void vPreCheckConfigs( void )
{
    /* This function should only be called once. */
    configASSERT( xIPIsNetworkTaskReady() == pdFALSE );
    configASSERT( xNetworkEventQueue == NULL );
    configASSERT( FreeRTOS_GetIPTaskHandle() == NULL );

    #if ( configASSERT_DEFINED == 1 )
        {
            volatile size_t uxSize = sizeof( uintptr_t );

            if( uxSize == 8U )
            {
                /* This is a 64-bit platform, make sure there is enough space in
                 * pucEthernetBuffer to store a pointer. */
                configASSERT( ipconfigBUFFER_PADDING >= 14 );
                /* But it must have this strange alignment: */
                configASSERT( ( ( ( ipconfigBUFFER_PADDING ) + 2 ) % 4 ) == 0 );
            }

            /* LCOV_EXCL_BR_START */
            uxSize = ipconfigNETWORK_MTU;
            /* Check if MTU is big enough. */
            configASSERT( uxSize >= ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER + ipconfigTCP_MSS ) );

            uxSize = sizeof( EthernetHeader_t );
            /* Check structure packing is correct. */
            configASSERT( uxSize == ipEXPECTED_EthernetHeader_t_SIZE );

            uxSize = sizeof( ARPHeader_t );
            configASSERT( uxSize == ipEXPECTED_ARPHeader_t_SIZE );

            uxSize = sizeof( IPHeader_t );
            configASSERT( uxSize == ipEXPECTED_IPHeader_t_SIZE );

            uxSize = sizeof( ICMPHeader_t );
            configASSERT( uxSize == ipEXPECTED_ICMPHeader_t_SIZE );

            uxSize = sizeof( UDPHeader_t );
            configASSERT( uxSize == ipEXPECTED_UDPHeader_t_SIZE );
            /* LCOV_EXCL_BR_STOP */
        }
    #endif /* if ( configASSERT_DEFINED == 1 ) */
}

/**
 * @brief Generate or check the protocol checksum of the data sent in the first parameter.
 *        At the same time, the length of the packet and the length of the different layers
 *        will be checked.
 *
 * @param[in] pucEthernetBuffer: The Ethernet buffer for which the checksum is to be calculated
 *                               or checked.
 * @param[in] uxBufferLength: the total number of bytes received, or the number of bytes written
 *                            in the packet buffer.
 * @param[in] xOutgoingPacket: Whether this is an outgoing packet or not.
 *
 * @return When xOutgoingPacket is false: the error code can be either: ipINVALID_LENGTH,
 *         ipUNHANDLED_PROTOCOL, ipWRONG_CRC, or ipCORRECT_CRC.
 *         When xOutgoingPacket is true: either ipINVALID_LENGTH, ipUNHANDLED_PROTOCOL,
 *         or ipCORRECT_CRC.
 */
uint16_t usGenerateProtocolChecksum( uint8_t * pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    uint32_t ulLength;
    uint16_t usChecksum;           /* The checksum as calculated. */
    uint16_t usChecksumFound = 0U; /* The checksum as found in the incoming packet. */
    const IPPacket_t * pxIPPacket;
    UBaseType_t uxIPHeaderLength;
    ProtocolPacket_t * pxProtPack;
    uint8_t ucProtocol;

    #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
        const char * pcType;
    #endif
    uint16_t usLength;
    uint16_t ucVersionHeaderLength;
    DEBUG_DECLARE_TRACE_VARIABLE( BaseType_t, xLocation, 0 );

    /* Introduce a do-while loop to allow use of break statements.
     * Note: MISRA prohibits use of 'goto', thus replaced with breaks. */
    do
    {
        /* Check for minimum packet size. */
        if( uxBufferLength < sizeof( IPPacket_t ) )
        {
            usChecksum = ipINVALID_LENGTH;
            DEBUG_SET_TRACE_VARIABLE( xLocation, 1 );
            break;
        }

        /* Parse the packet length. */

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        pxIPPacket = ( ( const IPPacket_t * ) pucEthernetBuffer );

        /* Per https://tools.ietf.org/html/rfc791, the four-bit Internet Header
         * Length field contains the length of the internet header in 32-bit words. */
        ucVersionHeaderLength = pxIPPacket->xIPHeader.ucVersionHeaderLength;
        ucVersionHeaderLength = ( ucVersionHeaderLength & ( uint8_t ) 0x0FU ) << 2;
        uxIPHeaderLength = ( UBaseType_t ) ucVersionHeaderLength;

        /* Check for minimum packet size. */
        if( uxBufferLength < ( sizeof( IPPacket_t ) + ( uxIPHeaderLength - ipSIZE_OF_IPv4_HEADER ) ) )
        {
            usChecksum = ipINVALID_LENGTH;
            DEBUG_SET_TRACE_VARIABLE( xLocation, 2 );
            break;
        }

        usLength = pxIPPacket->xIPHeader.usLength;
        usLength = FreeRTOS_ntohs( usLength );

        if( usLength < uxIPHeaderLength )
        {
            usChecksum = ipINVALID_LENGTH;
            DEBUG_SET_TRACE_VARIABLE( xLocation, 3 );
            break;
        }

        if( uxBufferLength < ( size_t ) ( ipSIZE_OF_ETH_HEADER + ( size_t ) usLength ) )
        {
            usChecksum = ipINVALID_LENGTH;
            DEBUG_SET_TRACE_VARIABLE( xLocation, 4 );
            break;
        }

        /* Identify the next protocol. */
        ucProtocol = pxIPPacket->xIPHeader.ucProtocol;

        /* N.B., if this IP packet header includes Options, then the following
         * assignment results in a pointer into the protocol packet with the Ethernet
         * and IP headers incorrectly aligned. However, either way, the "third"
         * protocol (Layer 3 or 4) header will be aligned, which is the convenience
         * of this calculation. */

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        pxProtPack = ( ( ProtocolPacket_t * ) &( pucEthernetBuffer[ uxIPHeaderLength - ipSIZE_OF_IPv4_HEADER ] ) );

        /* Switch on the Layer 3/4 protocol. */
        if( ucProtocol == ( uint8_t ) ipPROTOCOL_UDP )
        {
            if( uxBufferLength < ( uxIPHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER ) )
            {
                usChecksum = ipINVALID_LENGTH;
                DEBUG_SET_TRACE_VARIABLE( xLocation, 5 );
                break;
            }

            if( xOutgoingPacket != pdFALSE )
            {
                /* Clear the UDP checksum field before calculating it. */
                pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0U;
            }
            else
            {
                usChecksumFound = pxProtPack->xUDPPacket.xUDPHeader.usChecksum;
            }

            #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
                {
                    pcType = "UDP";
                }
            #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */
        }
        else if( ucProtocol == ( uint8_t ) ipPROTOCOL_TCP )
        {
            if( uxBufferLength < ( uxIPHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_TCP_HEADER ) )
            {
                usChecksum = ipINVALID_LENGTH;
                DEBUG_SET_TRACE_VARIABLE( xLocation, 6 );
                break;
            }

            if( xOutgoingPacket != pdFALSE )
            {
                /* Clear the TCP checksum field before calculating it. */
                pxProtPack->xTCPPacket.xTCPHeader.usChecksum = 0U;
            }
            else
            {
                usChecksumFound = pxProtPack->xTCPPacket.xTCPHeader.usChecksum;
            }

            #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
                {
                    pcType = "TCP";
                }
            #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */
        }
        else if( ( ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP ) ||
                 ( ucProtocol == ( uint8_t ) ipPROTOCOL_IGMP ) )
        {
            if( uxBufferLength < ( uxIPHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMP_HEADER ) )
            {
                usChecksum = ipINVALID_LENGTH;
                DEBUG_SET_TRACE_VARIABLE( xLocation, 7 );
                break;
            }

            if( xOutgoingPacket != pdFALSE )
            {
                /* Clear the ICMP/IGMP checksum field before calculating it. */
                pxProtPack->xICMPPacket.xICMPHeader.usChecksum = 0U;
            }
            else
            {
                usChecksumFound = pxProtPack->xICMPPacket.xICMPHeader.usChecksum;
            }

            #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
                {
                    if( ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP )
                    {
                        pcType = "ICMP";
                    }
                    else
                    {
                        pcType = "IGMP";
                    }
                }
            #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */
        }
        else
        {
            /* Unhandled protocol, other than ICMP, IGMP, UDP, or TCP. */
            usChecksum = ipUNHANDLED_PROTOCOL;
            DEBUG_SET_TRACE_VARIABLE( xLocation, 8 );
            break;
        }

        /* The protocol and checksum field have been identified. Check the direction
         * of the packet. */
        if( xOutgoingPacket != pdFALSE )
        {
            /* This is an outgoing packet. The CRC-field has been cleared. */
        }
        else if( ( usChecksumFound == 0U ) && ( ucProtocol == ( uint8_t ) ipPROTOCOL_UDP ) )
        {
            #if ( ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS == 0 )
                {
                    /* Sender hasn't set the checksum, drop the packet because
                     * ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS is not set. */
                    usChecksum = ipWRONG_CRC;
                    #if ( ipconfigHAS_PRINTF != 0 )
                        {
                            static BaseType_t xCount = 0;

                            /* Exclude this from branch coverage as this is only used for debugging. */
                            if( xCount < 5 ) /* LCOV_EXCL_BR_LINE */
                            {
                                FreeRTOS_printf( ( "usGenerateProtocolChecksum: UDP packet from %xip without CRC dropped\n",
                                                   FreeRTOS_ntohl( pxIPPacket->xIPHeader.ulSourceIPAddress ) ) );
                                xCount++;
                            }
                        }
                    #endif /* ( ipconfigHAS_PRINTF != 0 ) */
                }
            #else /* if ( ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS == 0 ) */
                {
                    /* Sender hasn't set the checksum, no use to calculate it. */
                    usChecksum = ipCORRECT_CRC;
                }
            #endif /* if ( ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS == 0 ) */
            DEBUG_SET_TRACE_VARIABLE( xLocation, 9 );
            break;
        }
        else
        {
            /* Other incoming packet than UDP. */
        }

        usLength = pxIPPacket->xIPHeader.usLength;
        usLength = FreeRTOS_ntohs( usLength );
        ulLength = ( uint32_t ) usLength;
        ulLength -= ( ( uint16_t ) uxIPHeaderLength ); /* normally minus 20 */

        if( ( ulLength < ( ( uint32_t ) sizeof( pxProtPack->xUDPPacket.xUDPHeader ) ) ) ||
            ( ulLength > ( ( uint32_t ) ipconfigNETWORK_MTU - ( uint32_t ) uxIPHeaderLength ) ) )
        {
            #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
                {
                    FreeRTOS_debug_printf( ( "usGenerateProtocolChecksum[%s]: len invalid: %lu\n", pcType, ulLength ) );
                }
            #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */

            /* Again, in a 16-bit return value there is no space to indicate an
             * error.  For incoming packets, 0x1234 will cause dropping of the packet.
             * For outgoing packets, there is a serious problem with the
             * format/length */
            usChecksum = ipINVALID_LENGTH;
            DEBUG_SET_TRACE_VARIABLE( xLocation, 10 );
            break;
        }

        if( ucProtocol <= ( uint8_t ) ipPROTOCOL_IGMP )
        {
            /* ICMP/IGMP do not have a pseudo header for CRC-calculation. */
            usChecksum = ( uint16_t )
                         ( ~usGenerateChecksum( 0U,
                                                ( const uint8_t * ) &( pxProtPack->xICMPPacket.xICMPHeader ), ( size_t ) ulLength ) );
        }
        else
        {
            /* For UDP and TCP, sum the pseudo header, i.e. IP protocol + length
             * fields */
            usChecksum = ( uint16_t ) ( ulLength + ( ( uint16_t ) ucProtocol ) );

            /* And then continue at the IPv4 source and destination addresses. */
            usChecksum = ( uint16_t )
                         ( ~usGenerateChecksum( usChecksum,
                                                ( const uint8_t * ) &( pxIPPacket->xIPHeader.ulSourceIPAddress ),
                                                ( size_t ) ( ( 2U * ( size_t ) ipSIZE_OF_IPv4_ADDRESS ) + ulLength ) ) );
            /* Sum TCP header and data. */
        }

        if( xOutgoingPacket == pdFALSE )
        {
            /* This is in incoming packet. If the CRC is correct, it should be zero. */
            if( usChecksum == 0U )
            {
                usChecksum = ( uint16_t ) ipCORRECT_CRC;
            }
            else
            {
                usChecksum = ( uint16_t ) ipWRONG_CRC;
            }
        }
        else
        {
            if( ( usChecksum == 0U ) && ( ucProtocol == ( uint8_t ) ipPROTOCOL_UDP ) )
            {
                /* In case of UDP, a calculated checksum of 0x0000 is transmitted
                 * as 0xffff. A value of zero would mean that the checksum is not used. */
                usChecksum = ( uint16_t ) 0xffffu;
            }
        }

        usChecksum = FreeRTOS_htons( usChecksum );

        if( xOutgoingPacket != pdFALSE )
        {
            switch( ucProtocol )
            {
                case ipPROTOCOL_UDP:
                    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = usChecksum;
                    break;

                case ipPROTOCOL_TCP:
                    pxProtPack->xTCPPacket.xTCPHeader.usChecksum = usChecksum;
                    break;

                case ipPROTOCOL_ICMP:
                    pxProtPack->xICMPPacket.xICMPHeader.usChecksum = usChecksum;
                    break;

                default: /*  ipPROTOCOL_IGMP */
                    pxProtPack->xICMPPacket.xICMPHeader.usChecksum = usChecksum;
                    break;
            }

            usChecksum = ( uint16_t ) ipCORRECT_CRC;
        }

        #if ( ipconfigHAS_DEBUG_PRINTF != 0 )
            else if( ( xOutgoingPacket == pdFALSE ) && ( usChecksum != ipCORRECT_CRC ) )
            {
                FreeRTOS_debug_printf( ( "usGenerateProtocolChecksum[%s]: ID %04X: from %lxip to %lxip bad crc: %04X\n",
                                         pcType,
                                         FreeRTOS_ntohs( pxIPPacket->xIPHeader.usIdentification ),
                                         FreeRTOS_ntohl( pxIPPacket->xIPHeader.ulSourceIPAddress ),
                                         FreeRTOS_ntohl( pxIPPacket->xIPHeader.ulDestinationIPAddress ),
                                         FreeRTOS_ntohs( usChecksumFound ) ) );
            }
            else
            {
                /* Nothing. */
            }
        #endif /* ipconfigHAS_DEBUG_PRINTF != 0 */
    } while( ipFALSE_BOOL );

    if( ( usChecksum == ipUNHANDLED_PROTOCOL ) ||
        ( usChecksum == ipINVALID_LENGTH ) )
    {
        /* NOP if ipconfigHAS_PRINTF != 0 */
        FreeRTOS_printf( ( "CRC error: %04x location %ld\n", usChecksum, xLocation ) );
    }

    return usChecksum;
}
/*-----------------------------------------------------------*/

/**
 * This method generates a checksum for a given IPv4 header, per RFC791 (page 14).
 * The checksum algorithm is described as:
 *   "[T]he 16 bit one's complement of the one's complement sum of all 16 bit words in the
 *   header.  For purposes of computing the checksum, the value of the checksum field is zero."
 *
 * In a nutshell, that means that each 16-bit 'word' must be summed, after which
 * the number of 'carries' (overflows) is added to the result. If that addition
 * produces an overflow, that 'carry' must also be added to the final result. The final checksum
 * should be the bitwise 'not' (ones-complement) of the result if the packet is
 * meant to be transmitted, but this method simply returns the raw value, probably
 * because when a packet is received, the checksum is verified by checking that
 * ((received & calculated) == 0) without applying a bitwise 'not' to the 'calculated' checksum.
 *
 * This logic is optimized for microcontrollers which have limited resources, so the logic looks odd.
 * It iterates over the full range of 16-bit words, but it does so by processing several 32-bit
 * words at once whenever possible. Its first step is to align the memory pointer to a 32-bit boundary,
 * after which it runs a fast loop to process multiple 32-bit words at once and adding their 'carries'.
 * Finally, it finishes up by processing any remaining 16-bit words, and adding up all of the 'carries'.
 * With 32-bit arithmetic, the number of 16-bit 'carries' produced by sequential additions can be found
 * by looking at the 16 most-significant bits of the 32-bit integer, since a 32-bit int will continue
 * counting up instead of overflowing after 16 bits. That is why the actual checksum calculations look like:
 *   union.u32 = ( uint32_t ) union.u16[ 0 ] + union.u16[ 1 ];
 *
 * Arguments:
 *   ulSum: This argument provides a value to initialise the progressive summation
 *   of the header's values to. It is often 0, but protocols like TCP or UDP
 *   can have pseudo-header fields which need to be included in the checksum.
 *   pucNextData: This argument contains the address of the first byte which this
 *   method should process. The method's memory iterator is initialised to this value.
 *   uxDataLengthBytes: This argument contains the number of bytes that this method
 *   should process.
 */

/**
 * @brief Calculates the 16-bit checksum of an array of bytes
 *
 * @param[in] usSum: The initial sum, obtained from earlier data.
 * @param[in] pucNextData: The actual data.
 * @param[in] uxByteCount: The number of bytes.
 *
 * @return The 16-bit one's complement of the one's complement sum of all 16-bit
 *         words in the header
 */
uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
/* MISRA/PC-lint doesn't like the use of unions. Here, they are a great
 * aid though to optimise the calculations. */
    xUnion32 xSum2;
    xUnion32 xSum;
    xUnion32 xTerm;
    xUnionPtr xSource;
    uintptr_t uxAlignBits;
    uint32_t ulCarry = 0U;
    uint16_t usTemp;
    size_t uxDataLengthBytes = uxByteCount;
    size_t uxSize;
    uintptr_t ulX;

    /* Small MCUs often spend up to 30% of the time doing checksum calculations
    * This function is optimised for 32-bit CPUs; Each time it will try to fetch
    * 32-bits, sums it with an accumulator and counts the number of carries. */

    /* Swap the input (little endian platform only). */
    usTemp = FreeRTOS_ntohs( usSum );
    xSum.u32 = ( uint32_t ) usTemp;
    xTerm.u32 = 0U;

    xSource.u8ptr = pucNextData;

    /* MISRA Ref 11.4.3 [Casting pointer to int for verification] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
    /* coverity[misra_c_2012_rule_11_4_violation] */
    uxAlignBits = ( ( ( uintptr_t ) pucNextData ) & 0x03U );

    /*
     * If pucNextData is non-aligned then the checksum is starting at an
     * odd position and we need to make sure the usSum value now in xSum is
     * as if it had been "aligned" in the same way.
     */
    if( ( uxAlignBits & 1U ) != 0U )
    {
        xSum.u32 = ( ( xSum.u32 & 0xffU ) << 8 ) | ( ( xSum.u32 & 0xff00U ) >> 8 );
    }

    /* If byte (8-bit) aligned... */
    if( ( ( uxAlignBits & 1U ) != 0U ) && ( uxDataLengthBytes >= ( size_t ) 1U ) )
    {
        xTerm.u8[ 1 ] = *( xSource.u8ptr );
        xSource.u8ptr++;
        uxDataLengthBytes--;
        /* Now xSource is word (16-bit) aligned. */
    }

    /* If half-word (16-bit) aligned... */
    if( ( ( uxAlignBits == 1U ) || ( uxAlignBits == 2U ) ) && ( uxDataLengthBytes >= 2U ) )
    {
        xSum.u32 += *( xSource.u16ptr );
        xSource.u16ptr++;
        uxDataLengthBytes -= 2U;
        /* Now xSource is word (32-bit) aligned. */
    }

    /* Word (32-bit) aligned, do the most part. */

    uxSize = ( size_t ) ( ( uxDataLengthBytes / 4U ) * 4U );

    if( uxSize >= ( 3U * sizeof( uint32_t ) ) )
    {
        uxSize -= ( 3U * sizeof( uint32_t ) );
    }
    else
    {
        uxSize = 0U;
    }

    /* In this loop, four 32-bit additions will be done, in total 16 bytes.
     * Indexing with constants (0,1,2,3) gives faster code than using
     * post-increments. */
    for( ulX = 0U; ulX < uxSize; ulX += 4U * sizeof( uint32_t ) )
    {
        /* Use a secondary Sum2, just to see if the addition produced an
         * overflow. */
        xSum2.u32 = xSum.u32 + xSource.u32ptr[ 0 ];

        if( xSum2.u32 < xSum.u32 )
        {
            ulCarry++;
        }

        /* Now add the secondary sum to the major sum, and remember if there was
         * a carry. */
        xSum.u32 = xSum2.u32 + xSource.u32ptr[ 1 ];

        if( xSum2.u32 > xSum.u32 )
        {
            ulCarry++;
        }

        /* And do the same trick once again for indexes 2 and 3 */
        xSum2.u32 = xSum.u32 + xSource.u32ptr[ 2 ];

        if( xSum2.u32 < xSum.u32 )
        {
            ulCarry++;
        }

        xSum.u32 = xSum2.u32 + xSource.u32ptr[ 3 ];

        if( xSum2.u32 > xSum.u32 )
        {
            ulCarry++;
        }

        /* And finally advance the pointer 4 * 4 = 16 bytes. */
        xSource.u32ptr = &( xSource.u32ptr[ 4 ] );
    }

    /* Now add all carries. */
    xSum.u32 = ( uint32_t ) xSum.u16[ 0 ] + xSum.u16[ 1 ] + ulCarry;

    uxDataLengthBytes %= 16U;

    /* Half-word aligned. */
    uxSize = ( ( uxDataLengthBytes & ~( ( size_t ) 1U ) ) );

    for( ulX = 0U; ulX < uxSize; ulX += 1U * sizeof( uint16_t ) )
    {
        /* At least one more short. */
        xSum.u32 += xSource.u16ptr[ 0 ];
        xSource.u16ptr = &xSource.u16ptr[ 1 ];
    }

    if( ( uxDataLengthBytes & ( size_t ) 1U ) != 0U ) /* Maybe one more ? */
    {
        xTerm.u8[ 0 ] = xSource.u8ptr[ 0 ];
    }

    /* MISRA Ref 2.2.1 [Unions and dead code] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-22 */
    /* coverity[misra_c_2012_rule_2_2_violation] */
    /* coverity[assigned_value] */
    xSum.u32 += xTerm.u32;

    /* Now add all carries again. */

    /* Assigning value from "xTerm.u32" to "xSum.u32" here, but that stored value is overwritten before it can be used. */
    /* MISRA Ref 2.2.1 [Unions and dead code] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-22 */
    /* coverity[misra_c_2012_rule_2_2_violation] */
    /* coverity[value_overwrite] */
    xSum.u32 = ( uint32_t ) xSum.u16[ 0 ] + xSum.u16[ 1 ];

    /* MISRA Ref 2.2.1 [Unions and dead code] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-22 */
    /* coverity[misra_c_2012_rule_2_2_violation] */
    /* coverity[value_overwrite] */
    xSum.u32 = ( uint32_t ) xSum.u16[ 0 ] + xSum.u16[ 1 ];

    if( ( uxAlignBits & 1U ) != 0U )
    {
        /* Quite unlikely, but pucNextData might be non-aligned, which would
        * mean that a checksum is calculated starting at an odd position. */
        xSum.u32 = ( ( xSum.u32 & 0xffU ) << 8 ) | ( ( xSum.u32 & 0xff00U ) >> 8 );
    }

    /* swap the output (little endian platform only). */
    return FreeRTOS_htons( ( ( uint16_t ) xSum.u32 ) );
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
            FreeRTOS_printf( ( "Heap: current %lu lowest %lu\n", xPortGetFreeHeapSize(), uxMinSize ) );
        }
        else
        {
            /* Nothing to log. */
        }

        #if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
            {
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
            /* MISRA Ref 21.6.1 [snprintf and logging] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-216 */
            /* coverity[misra_c_2012_rule_21_6_violation] */
            ( void ) snprintf( pcBuffer, uxLength, "Errno %d", ( int ) xErrnum );
            pcName = NULL;
            break;
    }

    if( pcName != NULL )
    {
        /* MISRA Ref 21.6.1 [snprintf and logging] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-216 */
        /* coverity[misra_c_2012_rule_21_6_violation] */
        ( void ) snprintf( pcBuffer, uxLength, "%s", pcName );
    }

    if( uxLength > 0U )
    {
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
 * @brief Get the highest value of two size_t's.
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
 * @brief Get the lowest value of two size_t's.
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
    uint32_t ulResult = a;

    configASSERT( d != 0U );

    if( d != 0U )
    {
        ulResult = d * ( ( a + d - 1U ) / d );
    }

    return ulResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Round-down a number to a multiple of 'd'.
 * @param[in] a: the first value.
 * @param[in] d: the second value.
 * @return A multiple of d.
 */
uint32_t FreeRTOS_round_down( uint32_t a,
                              uint32_t d )
{
    uint32_t ulResult = 0;

    configASSERT( d != 0U );

    if( d != 0U )
    {
        ulResult = d * ( a / d );
    }

    return ulResult;
}
/*-----------------------------------------------------------*/

/**
 * @brief Convert character array (of size 4) to equivalent 32-bit value.
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
/*-----------------------------------------------------------*/
