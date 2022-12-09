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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 */
 
#ifndef FREERTOS_IPV4_PRIVATE_H
#define FREERTOS_IPV4_PRIVATE_H
/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

#include "FreeRTOS_IP_Private.h"

/* The maximum UDP payload length. */
#define ipMAX_UDP_PAYLOAD_LENGTH        ( ( ipconfigNETWORK_MTU - ipSIZE_OF_IPv4_HEADER ) - ipSIZE_OF_UDP_HEADER )

#define TCP_PACKET_SIZE                 ( sizeof( TCPPacket_t ) )

/* The offset into an IP packet into which the IP data (payload) starts. */
#define ipIP_PAYLOAD_OFFSET             ( sizeof( IPPacket_t ) )
/* The offset into a UDP packet at which the UDP data (payload) starts. */
#define ipUDP_PAYLOAD_OFFSET_IPv4       ( sizeof( UDPPacket_t ) )
/* The value of 'ipUDP_PAYLOAD_IP_TYPE_OFFSET' is 42 + 6 = 48 bytes. */
#define ipUDP_PAYLOAD_IP_TYPE_OFFSET    ( sizeof( UDPPacket_t ) + ipIP_TYPE_OFFSET )

#if ( ipconfigBYTE_ORDER == pdFREERTOS_LITTLE_ENDIAN )

/* Ethernet frame types. */
    #define ipARP_FRAME_TYPE                ( 0x0608U )
    #define ipIPv4_FRAME_TYPE               ( 0x0008U )

/* ARP related definitions. */
    #define ipARP_PROTOCOL_TYPE             ( 0x0008U )
    #define ipARP_HARDWARE_TYPE_ETHERNET    ( 0x0100U )
    #define ipARP_REQUEST                   ( 0x0100U )
    #define ipARP_REPLY                     ( 0x0200U )

#else /* if ( ipconfigBYTE_ORDER == pdFREERTOS_LITTLE_ENDIAN ) */

/* Ethernet frame types. */
    #define ipARP_FRAME_TYPE                ( 0x0806U )
    #define ipIPv4_FRAME_TYPE               ( 0x0800U )

/* ARP related definitions. */
    #define ipARP_PROTOCOL_TYPE             ( 0x0800U )
    #define ipARP_HARDWARE_TYPE_ETHERNET    ( 0x0001U )
    #define ipARP_REQUEST                   ( 0x0001 )
    #define ipARP_REPLY                     ( 0x0002 )

#endif /* ipconfigBYTE_ORDER */

#include "pack_struct_start.h"
struct xIP_HEADER
{
    uint8_t ucVersionHeaderLength;        /**< The version field + internet header length 0 + 1 =  1 */
    uint8_t ucDifferentiatedServicesCode; /**< Differentiated services code point + ECN    1 + 1 =  2 */
    uint16_t usLength;                    /**< Entire Packet size, ex. Ethernet header.   2 + 2 =  4 */
    uint16_t usIdentification;            /**< Identification field                       4 + 2 =  6 */
    uint16_t usFragmentOffset;            /**< Fragment flags and fragment offset         6 + 2 =  8 */
    uint8_t ucTimeToLive;                 /**< Time to live field                         8 + 1 =  9 */
    uint8_t ucProtocol;                   /**< Protocol used in the IP-datagram           9 + 1 = 10 */
    uint16_t usHeaderChecksum;            /**< Checksum of the IP-header                 10 + 2 = 12 */
    uint32_t ulSourceIPAddress;           /**< IP address of the source                  12 + 4 = 16 */
    uint32_t ulDestinationIPAddress;      /**< IP address of the destination             16 + 4 = 20 */
}
#include "pack_struct_end.h"
typedef struct xIP_HEADER IPHeader_t;

#include "pack_struct_start.h"
struct xARP_HEADER
{
    uint16_t usHardwareType;              /**< Network Link Protocol type                     0 +  2 =  2 */
    uint16_t usProtocolType;              /**< The internetwork protocol                      2 +  2 =  4 */
    uint8_t ucHardwareAddressLength;      /**< Length in octets of a hardware address         4 +  1 =  5 */
    uint8_t ucProtocolAddressLength;      /**< Length in octets of the internetwork protocol  5 +  1 =  6 */
    uint16_t usOperation;                 /**< Operation that the sender is performing        6 +  2 =  8 */
    MACAddress_t xSenderHardwareAddress;  /**< Media address of the sender                    8 +  6 = 14 */
    uint8_t ucSenderProtocolAddress[ 4 ]; /**< Internetwork address of sender                14 +  4 = 18  */
    MACAddress_t xTargetHardwareAddress;  /**< Media address of the intended receiver        18 +  6 = 24  */
    uint32_t ulTargetProtocolAddress;     /**< Internetwork address of the intended receiver 24 +  4 = 28  */
}
#include "pack_struct_end.h"
typedef struct xARP_HEADER ARPHeader_t;

/*-----------------------------------------------------------*/
/* Nested protocol packets.                                  */
/*-----------------------------------------------------------*/

#include "pack_struct_start.h"
struct xARP_PACKET
{
    EthernetHeader_t xEthernetHeader; /**< The ethernet header of an ARP Packet  0 + 14 = 14 */
    ARPHeader_t xARPHeader;           /**< The ARP header of an ARP Packet       14 + 28 = 42 */
}
#include "pack_struct_end.h"
typedef struct xARP_PACKET ARPPacket_t;

#include "pack_struct_start.h"
struct xIP_PACKET
{
    EthernetHeader_t xEthernetHeader;
    IPHeader_t xIPHeader;
}
#include "pack_struct_end.h"
typedef struct xIP_PACKET IPPacket_t;

#include "pack_struct_start.h"
struct xICMP_PACKET
{
    EthernetHeader_t xEthernetHeader; /**< The Ethernet header of an ICMP packet. */
    IPHeader_t xIPHeader;             /**< The IP header of an ICMP packet. */
    ICMPHeader_t xICMPHeader;         /**< The ICMP header of an ICMP packet. */
}
#include "pack_struct_end.h"
typedef struct xICMP_PACKET ICMPPacket_t;


#include "pack_struct_start.h"
struct xUDP_PACKET
{
    EthernetHeader_t xEthernetHeader; /**< UDP-Packet ethernet header  0 + 14 = 14 */
    IPHeader_t xIPHeader;             /**< UDP-Packet IP header        14 + 20 = 34 */
    UDPHeader_t xUDPHeader;           /**< UDP-Packet UDP header       34 +  8 = 42 */
}
#include "pack_struct_end.h"
typedef struct xUDP_PACKET UDPPacket_t;

#include "pack_struct_start.h"
struct xTCP_PACKET
{
    EthernetHeader_t xEthernetHeader; /**< The ethernet header  0 + 14 = 14 */
    IPHeader_t xIPHeader;             /**< The IP header        14 + 20 = 34 */
    TCPHeader_t xTCPHeader;           /**< The TCP header       34 + 32 = 66 */
}
#include "pack_struct_end.h"
typedef struct xTCP_PACKET TCPPacket_t;

/*
 * Processes incoming ARP packets.
 */
eFrameProcessingResult_t eARPProcessPacket( ARPPacket_t * const pxARPFrame );

/* *INDENT-OFF* */
#ifdef __cplusplus
    } /* extern "C" */
#endif
/* *INDENT-ON* */

#endif /* FREERTOS_IP_PRIVATE_H */
