/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
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
/*-----------------------------------------------------------*/

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

static uintptr_t void_ptr_to_uintptr( const void * pvPointer );

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


#if ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 )

/**
 * @brief Create a DHCP event.
 *
 * @return pdPASS or pdFAIL, depending on whether xSendEventStructToIPTask()
 *         succeeded.
 * @param pxEndPoint: The end-point that needs DHCP.
 */
/*TODO eDHCPEvent - eDHCP_RA_Event */
/*eGetDHCPState and Need if check? */
    /*BaseType_t xSendDHCPEvent( struct xNetworkEndPoint * pxEndPoint ) */
    BaseType_t xSendDHCPEvent( void )
    {
        IPStackEvent_t xEventMessage;
        const TickType_t uxDontBlock = 0U;
        uintptr_t uxOption = ( uintptr_t ) eGetDHCPState();

        xEventMessage.eEventType = eDHCPEvent;
/*TODO */
        /* MISRA Ref 11.6.1 [DHCP events and conversion to void] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-116 */
        /* coverity[misra_c_2012_rule_11_6_violation] */
        xEventMessage.pvData = ( void * ) uxOption;

        return xSendEventStructToIPTask( &xEventMessage, uxDontBlock );
    }
#endif /* if ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 ) */
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
        pxNewBuffer->xIPAddress.xIP_IPv4 = pxNetworkBuffer->xIPAddress.xIP_IPv4;
        pxNewBuffer->usPort = pxNetworkBuffer->usPort;
        pxNewBuffer->usBoundPort = pxNetworkBuffer->usBoundPort;
        pxNewBuffer->pxInterface = pxNetworkBuffer->pxInterface;
        pxNewBuffer->pxEndPoint = pxNetworkBuffer->pxEndPoint;
        ( void ) memcpy( pxNewBuffer->pucEthernetBuffer, pxNetworkBuffer->pucEthernetBuffer, uxLengthToCopy );

        if( uxIPHeaderSizePacket( pxNetworkBuffer ) == ipSIZE_OF_IPv6_HEADER )
        {
            ( void ) memcpy( pxNewBuffer->xIPAddress.xIP_IPv6.ucBytes, pxNetworkBuffer->xIPAddress.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
        }
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
        uxBuffer = void_ptr_to_uintptr( pvBuffer );

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
/*-----------------------------------------------------------*/

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

    else if( ( pxSet->xIsIPv6 != pdFALSE ) && ( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP_IPv6 ) )
    {
        xReturn = prvChecksumICMPv6Checks( uxBufferLength, pxSet );
    }
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
    if( pxSet->xIsIPv6 != pdFALSE )
    {
        uint32_t pulHeader[ 2 ];

        /* IPv6 has a 40-byte pseudo header:
         * 0..15 Source IPv6 address
         * 16..31 Target IPv6 address
         * 32..35 Length of payload
         * 36..38 three zero's
         * 39 Next Header, i.e. the protocol type. */

        pulHeader[ 0 ] = ( uint32_t ) pxSet->usProtocolBytes;
        pulHeader[ 0 ] = FreeRTOS_htonl( pulHeader[ 0 ] );
        pulHeader[ 1 ] = ( uint32_t ) pxSet->pxIPPacket_IPv6->ucNextHeader;
        pulHeader[ 1 ] = FreeRTOS_htonl( pulHeader[ 1 ] );

        pxSet->usChecksum = usGenerateChecksum( 0U,
                                                &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + offsetof( IPHeader_IPv6_t, xSourceAddress ) ] ),
                                                ( size_t ) ( 2U * sizeof( pxSet->pxIPPacket_IPv6->xSourceAddress ) ) );

        pxSet->usChecksum = usGenerateChecksum( pxSet->usChecksum,
                                                ( const uint8_t * ) pulHeader,
                                                ( size_t ) ( sizeof( pulHeader ) ) );
    }

    if( ( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP ) || ( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_IGMP ) )
    {
        /* ICMP/IGMP do not have a pseudo header for CRC-calculation. */
        pxSet->usChecksum = ( uint16_t )
                            ( ~usGenerateChecksum( 0U, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + pxSet->uxIPHeaderLength ] ), ( size_t ) pxSet->usProtocolBytes ) );
    }
    else if( ( pxSet->xIsIPv6 != pdFALSE ) && ( pxSet->ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP_IPv6 ) )
    {
        pxSet->usChecksum = ( uint16_t )
                            ( ~usGenerateChecksum( pxSet->usChecksum,
                                                   ( uint8_t * ) &( pxSet->pxProtocolHeaders->xTCPHeader ),
                                                   ( size_t ) pxSet->usProtocolBytes ) );
    }
    else
    {
        if( pxSet->xIsIPv6 != pdFALSE )
        {
            /* The CRC of the IPv6 pseudo-header has already been calculated. */
            pxSet->usChecksum = ( uint16_t )
                                ( ~usGenerateChecksum( pxSet->usChecksum,
                                                       ( uint8_t * ) &( pxSet->pxProtocolHeaders->xUDPHeader.usSourcePort ),
                                                       ( size_t ) ( pxSet->usProtocolBytes ) ) );
        }
        else
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
            usCalculated = ~usGenerateProtocolChecksum( ( uint8_t * ) pucEthernetBuffer, uxBufferLength, pdTRUE );
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
        #if ( ipconfigUSE_IPV6 != 0 )
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
        #else /* if ( ipconfigUSE_IPV6 != 0 ) */
            {
                uxOffset = sizeof( UDPPacket_t );
            }
        #endif /* ipconfigUSE_IPV6 */

        pxResult = prvPacketBuffer_to_NetworkBuffer( pvBuffer, uxOffset );
    }

    return pxResult;
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
/*TODO - need to be updated according to interface and end point */
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
            #if ipconfigUSE_TCP == 1
                {
                    uxSize = sizeof( TCPHeader_t );
                    configASSERT( uxSize == ( ipEXPECTED_TCPHeader_t_SIZE + ipSIZE_TCP_OPTIONS ) );
                }
            #endif
        }
    #endif /* if ( configASSERT_DEFINED == 1 ) */
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
 *         When xOutgoingPacket is true: either ipINVALID_LENGTH, ipUNHANDLED_PROTOCOL,
 *         or ipCORRECT_CRC.
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
        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        xSet.pxIPPacket = ( ( const IPPacket_t * ) pucEthernetBuffer );

        if( xSet.pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
        {
            xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );

            xResult = prvChecksumIPv6Checks( pucEthernetBuffer, uxBufferLength, &( xSet ) );

            if( xResult != 0 )
            {
                DEBUG_SET_TRACE_VARIABLE( xLocation, xResult );
                break;
            }
        }
        else
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
                    usChecksum = ipCORRECT_CRC;
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
/*TODO: Return value needs to be checked */
const char * FreeRTOS_strerror_r( BaseType_t xErrnum,
                                  char * pcBuffer,
                                  size_t uxLength )
{
    const char * pcName;
    BaseType_t xErrnumPositive = xErrnum;

    if( xErrnumPositive < 0 )
    {
        xErrnumPositive = -xErrnumPositive;
    }

    switch( xErrnumPositive )
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
