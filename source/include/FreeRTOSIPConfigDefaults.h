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
 * @file FreeRTOSIPConfigDefaults.h
 * @brief File that provides default values for configuration options that are
 *        missing from FreeRTOSIPConfig.h.  The complete documentation of the
 *        configuration parameters can be found here:
 *        https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html
 */

#ifndef FREERTOS_IP_CONFIG_DEFAULTS_H
#define FREERTOS_IP_CONFIG_DEFAULTS_H

#ifndef FREERTOS_CONFIG_H
    #error FreeRTOSConfig.h has not been included yet
#endif

#ifndef FREERTOS_IP_CONFIG_H
    #error FreeRTOSIPConfig.h has not been included yet
#endif

#include "FreeRTOSIPDeprecatedDefinitions.h"

/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                                  MACROS                                   */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * Used to define away static keyword for CBMC proofs
 */
#ifndef _static
    #define _static    static
#endif

/*---------------------------------------------------------------------------*/

/*
 * Since all code is made compatible with the MISRA rules, the inline functions
 * disappear.  Normally defined in portmacro.h or FreeRTOSConfig.h.
 */
#ifndef portINLINE
    #define portINLINE    inline
#endif

/*---------------------------------------------------------------------------*/

/*
 * pdFREERTOS_ERRNO_EAFNOSUPPORT
 *
 * Address family not supported by protocol.
 *
 * Note: Now included in FreeRTOS-Kernel/projdefs.h, so this serves as a
 * temporary kernel version check. To be removed in a future version.
 */
#ifndef pdFREERTOS_ERRNO_EAFNOSUPPORT
    #error Missing pdFREERTOS_ERRNO_EAFNOSUPPORT definition, please update FreeRTOS-Kernel
#endif

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                                  MACROS                                   */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                                 IP CONFIG                                 */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigIPv4_BACKWARD_COMPATIBLE
 *
 * If defined this macro enables the APIs that are backward compatible
 * with single end point IPv4 version of the FreeRTOS+TCP library.
 */
#ifndef ipconfigIPv4_BACKWARD_COMPATIBLE
    #define ipconfigIPv4_BACKWARD_COMPATIBLE    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_IPv4
 *
 * Include all API's and code that is needed for the IPv4 protocol.
 * When defined as zero, the application should uses IPv6.
 */
#ifndef ipconfigUSE_IPv4
    #define ipconfigUSE_IPv4    1
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_IPv6
 *
 * Include all API's and code that is needed for the IPv6 protocol.
 * When defined as zero, the application should uses IPv4.
 */
#ifndef ipconfigUSE_IPv6
    #define ipconfigUSE_IPv6    1
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigUSE_IPv4 != 1 ) && ( ipconfigUSE_IPv6 != 1 )
    #error "Invalid build configuration"
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigND_CACHE_ENTRIES
 */
    #ifndef ipconfigND_CACHE_ENTRIES
        #define ipconfigND_CACHE_ENTRIES    24U
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigUSE_RA
 */
    #ifndef ipconfigUSE_RA
        #define ipconfigUSE_RA    1
    #endif

/*-----------------------------------------------------------------------*/

    #if ( ipconfigUSE_RA != 0 )

/*-------------------------------------------------------------------*/

/*
 * ipconfigRA_SEARCH_COUNT
 *
 * RA or Router Advertisement/SLAAC: see end-point flag 'bWantRA'.
 * An Router Solicitation will be sent. It will wait for
 * ipconfigRA_SEARCH_TIME_OUT_MSEC ms. When there is no response, it
 * will be repeated ipconfigRA_SEARCH_COUNT times. Then it will be
 * checked if the chosen IP-address already exists, repeating this
 * ipconfigRA_IP_TEST_COUNT times, each time with a timeout of
 * ipconfigRA_IP_TEST_TIME_OUT_MSEC ms. Finally the end-point will go
 * in the UP state.
 */
        #ifndef ipconfigRA_SEARCH_COUNT
            #define ipconfigRA_SEARCH_COUNT    3U
        #endif

/*-------------------------------------------------------------------*/

/*
 * ipconfigRA_SEARCH_TIME_OUT_MSEC
 */
        #ifndef ipconfigRA_SEARCH_TIME_OUT_MSEC
            #define ipconfigRA_SEARCH_TIME_OUT_MSEC    10000U
        #endif

/*-------------------------------------------------------------------*/

/*
 * ipconfigRA_IP_TEST_COUNT
 */
        #ifndef ipconfigRA_IP_TEST_COUNT
            #define ipconfigRA_IP_TEST_COUNT    3U
        #endif

/*-------------------------------------------------------------------*/

/*
 * ipconfigRA_IP_TEST_TIME_OUT_MSEC
 */
        #ifndef ipconfigRA_IP_TEST_TIME_OUT_MSEC
            #define ipconfigRA_IP_TEST_TIME_OUT_MSEC    1500U
        #endif

/*-------------------------------------------------------------------*/

    #endif /* if ( ipconfigUSE_RA != 0 ) */

/*-----------------------------------------------------------------------*/

#endif /* if ( ipconfigUSE_IPv6 != 0 ) */

/*---------------------------------------------------------------------------*/

/*
 * ipconfigENDPOINT_DNS_ADDRESS_COUNT
 */
#ifndef ipconfigENDPOINT_DNS_ADDRESS_COUNT
    #define ipconfigENDPOINT_DNS_ADDRESS_COUNT    2U
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigFORCE_IP_DONT_FRAGMENT
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigFORCE_IP_DONT_FRAGMENT
 *
 * This macro is about IP-fragmentation. When sending an IP-packet over the
 * Internet, a big packet may be split up into smaller parts which are then
 * combined by the receiver. The sender can determine if this fragmentation is
 * allowed or not. ipconfigFORCE_IP_DONT_FRAGMENT is zero by default, which
 * means that fragmentation is allowed.
 *
 * Note that the FreeRTOS-Plus-TCP stack does not accept received fragmented
 * packets.
 */
#ifndef ipconfigFORCE_IP_DONT_FRAGMENT
    #define ipconfigFORCE_IP_DONT_FRAGMENT    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS
 *
 * If ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS is set to 1, then
 * FreeRTOS-Plus-TCP accepts IP packets that contain IP options, but does not
 * process the options (IP options are not supported).
 *
 * If ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS is set to 0, then
 * FreeRTOS-Plus-TCP will drop IP packets that contain IP options.
 */
#ifndef ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS
    #define ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS    1
#endif

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                                 IP CONFIG                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                               DRIVER CONFIG                               */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigBUFFER_PADDING
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigBUFFER_PADDING
 *
 * Advanced driver implementation use only.
 *
 * When the application requests a network buffer, the size of the network
 * buffer is specified by the application writer, but the size of the network
 * buffer actually obtained is increased by ipconfigBUFFER_PADDING bytes. The
 * first ipconfigBUFFER_PADDING bytes of the buffer is then used to hold
 * metadata about the buffer, and the area that actually stores the data
 * follows the metadata. This mechanism is transparent to the user as the user
 * only see a pointer to the area within the buffer actually used to hold
 * network data.
 *
 * Some network hardware has very specific byte alignment requirements, so
 * ipconfigBUFFER_PADDING is provided as a configurable parameter to allow the
 * writer of the network driver to influence the alignment of the start of the
 * data that follows the metadata.
 */
#ifndef ipconfigBUFFER_PADDING
    #define ipconfigBUFFER_PADDING    0U
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigPACKET_FILLER_SIZE
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigBUFFER_PADDING
 *
 * Advanced driver implementation use only.
 *
 * When the application requests a network buffer, the size of the network
 * buffer is specified by the application writer, but the size of the network
 * buffer actually obtained is increased by ipconfigBUFFER_PADDING bytes. The
 * first ipconfigBUFFER_PADDING bytes of the buffer is then used to hold
 * metadata about the buffer, and the area that actually stores the data
 * follows the metadata. This mechanism is transparent to the user as the user
 * only see a pointer to the area within the buffer actually used to hold
 * network data.
 *
 * Some network hardware has very specific byte alignment requirements, so
 * ipconfigBUFFER_PADDING is provided as a configurable parameter to allow the
 * writer of the network driver to influence the alignment of the start of the
 * data that follows the metadata.
 */
#ifndef ipconfigPACKET_FILLER_SIZE
    #define ipconfigPACKET_FILLER_SIZE    2U
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigBYTE_ORDER
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigBYTE_ORDER
 *
 * If the microcontroller on which FreeRTOS-Plus-TCP is running is big endian
 * then ipconfigBYTE_ORDER must be set to pdFREERTOS_BIG_ENDIAN. If the
 * microcontroller is little endian then ipconfigBYTE_ORDER must be set to
 * pdFREERTOS_LITTLE_ENDIAN. The Byte Order and Endian section of the Embedded
 * Networking Basics and Glossary page provides an explanation of byte order
 * considerations in IP networks.
 */
#ifndef ipconfigBYTE_ORDER
    #error The macro 'ipconfigBYTE_ORDER' must be defined at this point
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
 *
 * If the network driver or network hardware is calculating the IP, TCP and UDP
 * checksums of incoming packets, and discarding packets that are found to
 * contain invalid checksums, then set ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
 * to 1, otherwise set ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM to 0.
 *
 * Throughput and processor load are greatly improved by implementing drivers
 * that make use of hardware checksum calculations.
 *
 * Note: From FreeRTOS-Plus-TCP V2.3.0, the length is checked in software even
 * when it has already been checked in hardware.
 */
#ifndef ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
 *
 * If the network driver or network hardware is calculating the IP, TCP and UDP
 * checksums of outgoing packets then set
 * ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM to 1, otherwise set
 * ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM to 0.
 *
 * Throughput and processor load are greatly improved by implementing drivers
 * that make use of hardware checksum calculations.
 */
#ifndef ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * A MISRA note: The macros 'ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES'
 * and 'ipconfigETHERNET_DRIVER_FILTERS_PACKETS' are too long: the first 32
 * bytes are equal, which might cause problems for some compilers.
 */

/*
 * ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES
 *
 * Ethernet/hardware MAC addresses are used to address Ethernet frames. If the
 * network driver or hardware is discarding packets that do not contain a MAC
 * address of interest then set ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES to
 * 1. Otherwise set ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES to 0.
 *
 * Throughput and processor load are greatly improved by implementing network
 * address filtering in hardware. Most network interfaces allow multiple MAC
 * addresses to be defined so filtering can allow through the unique hardware
 * address of the node, the broadcast address, and various multicast addresses.
 *
 * When disabled, the IP-task will call 'eConsiderFrameForProcessing()'
 * to check incoming packets.
 */

#ifndef ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES
    #define ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES    1
#endif

/*---------------------------------------------------------------------------*/

/*
 * A MISRA note: The macros 'ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES'
 * and 'ipconfigETHERNET_DRIVER_FILTERS_PACKETS' are too long: the first 32
 * bytes are equal, which might cause problems for some compilers.
 */

/*
 * ipconfigETHERNET_DRIVER_FILTERS_PACKETS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigETHERNET_DRIVER_FILTERS_PACKETS
 *
 * For expert users only.
 *
 * Whereas ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is used to specify
 * whether or not the network driver or hardware filters Ethernet frames,
 * ipconfigETHERNET_DRIVER_FILTERS_PACKETS is used to specify whether or not
 * the network driver filters the IP, UDP or TCP data within the Ethernet
 * frame.
 *
 * The TCP/IP stack is only interested in receiving data that is either
 * addresses to a socket (IP address and port number) on the local node, or is
 * a broadcast or multicast packet. Throughput and process load can be greatly
 * improved by preventing packets that do not meet these criteria from being
 * sent to the TCP/IP stack. FreeRTOS provides some features that allow such
 * filtering to take place in the network driver. For example,
 * xPortHasUDPSocket() can be used as follows:
 *
 * if( ( xPortHasUdpSocket( xUDPHeader->usDestinationPort ) )
 *     #if( ipconfigUSE_DNS == 1 )/* DNS is also UDP. *
 *         || ( xUDPHeader->usSourcePort == FreeRTOS_ntohs( ipDNS_PORT ) )
 *     #endif
 *     #if( ipconfigUSE_LLMNR == 1 ) /* LLMNR is also UDP. *
 *         || ( xUDPHeader->usDestinationPort == FreeRTOS_ntohs( ipLLMNR_PORT ) )
 *     #endif
 *     #if( ipconfigUSE_NBNS == 1 ) /* NBNS is also UDP. *
 *         || ( xUDPHeader->usDestinationPort == FreeRTOS_ntohs( ipNBNS_PORT ) )
 *     #endif
 *    )
 * {
 *     /* Forward packet to the IP-stack. *
 * }
 * else
 * {
 *     /* Discard the UDP packet. *
 * }
 *
 * When disabled, the IP-task will perform sanity checks on the IP-header,
 * also checking the target IP address. Also when disabled, xPortHasUDPSocket()
 * won't be included.  That means that the IP-task can access the
 * 'xBoundUDPSocketsList' without locking.
 */
#ifndef ipconfigETHERNET_DRIVER_FILTERS_PACKETS
    #define ipconfigETHERNET_DRIVER_FILTERS_PACKETS    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigETHERNET_MINIMUM_PACKET_BYTES
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigETHERNET_MINIMUM_PACKET_BYTES
 *
 * When the device is connected to a LAN, it is strongly recommended to give
 * each outgoing packet a minimum length of 60 bytes (plus 4 bytes CRC). The
 * macro ipconfigETHERNET_MINIMUM_PACKET_BYTES determines the minimum length.
 * By default, it is defined as zero, meaning that packets will be sent as they
 * are.
 */
#ifndef ipconfigETHERNET_MINIMUM_PACKET_BYTES
    #define ipconfigETHERNET_MINIMUM_PACKET_BYTES    0U
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES
 *
 * If ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES is set to 1 then Ethernet
 * frames that are not in Ethernet II format will be dropped. This option
 * is included for potential future IP stack developments.
 *
 * When enabled, the function 'eConsiderFrameForProcessing()' will also
 * check if the Ethernet frame type is acceptable.
 */
    #ifndef ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES
        #define ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES    1
    #endif

/*-----------------------------------------------------------------------*/

#endif /* if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 ) */

/*---------------------------------------------------------------------------*/

/*
 * ipconfigNETWORK_MTU
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigNETWORK_MTU
 *
 * The MTU is the maximum number of bytes the payload of a network frame can
 * contain. For normal Ethernet V2 frames the maximum MTU is 1500 (although a
 * lower number may be required for Internet routing). Setting a lower value
 * can save RAM, depending on the buffer management scheme used.
 */
#ifndef ipconfigNETWORK_MTU
    #define ipconfigNETWORK_MTU    1500U
#endif

#if ( ipconfigNETWORK_MTU > ( SIZE_MAX >> 1 ) )
    #error ipconfigNETWORK_MTU overflows a size_t.
#elif ( ipconfigNETWORK_MTU < 46 )
    #error ipconfigNETWORK_MTU must be at least 46.
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS
 *
 * ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS defines the total number of network
 * buffer that are available to the TCP/IP stack. The total number of network
 * buffers is limited to ensure the total amount of RAM that can be consumed by
 * the TCP/IP stack is capped to a pre-determinable value. How the storage area
 * is actually allocated to the network buffer structures is not fixed, but
 * part of the portable layer. The simplest scheme simply allocates the exact
 * amount of storage as it is required.
 *
 * More information on network buffers and network buffer descriptors is
 * provided on the pages that describe porting FreeRTOS-Plus-TCP to other
 * hardware and the pxGetNetworkBufferWithDescriptor() porting specific API
 * function.
 */
#ifndef ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS
    #define ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS    45U
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_LINKED_RX_MESSAGES
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_LINKED_RX_MESSAGES
 *
 * Advanced users only.
 *
 * When pconfigUSE_LINKED_RX_MESSAGES is set to 1 it is possible to reduce CPU
 * load during periods of heavy network traffic by linking multiple received
 * packets together, then passing all the linked packets to the IP RTOS task in
 * one go.
 */
#ifndef ipconfigUSE_LINKED_RX_MESSAGES
    #define ipconfigUSE_LINKED_RX_MESSAGES    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigZERO_COPY_RX_DRIVER
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigZERO_COPY_RX_DRIVER
 *
 * Advanced users only.
 *
 * If ipconfigZERO_COPY_RX_DRIVER is set to 1 then the network interface will
 * assign network buffers NetworkBufferDescriptor_t::pucEthernetBuffer to the
 * DMA of the EMAC. When a packet is received, no data is copied. Instead, the
 * buffer is sent directly to the IP-task. If the TX zero-copy option is
 * disabled, every received packet will be copied from the DMA buffer to the
 * network buffer of type NetworkBufferDescriptor_t.
 */
#ifndef ipconfigZERO_COPY_RX_DRIVER
    #define ipconfigZERO_COPY_RX_DRIVER    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigZERO_COPY_TX_DRIVER
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigZERO_COPY_TX_DRIVER
 *
 * Advanced users only.
 *
 * If ipconfigZERO_COPY_TX_DRIVER is set to 1 then the driver function
 * xNetworkInterfaceOutput() will always be called with its bReleaseAfterSend
 * parameter set to pdTRUE - meaning it is always the driver that is
 * responsible for freeing the network buffer and network buffer descriptor.
 *
 * This is useful if the driver implements a zero-copy scheme whereby the
 * packet data is sent directly from within the network buffer (for example by
 * pointing a DMA descriptor at the data within the network buffer), instead of
 * copying the data out of the network buffer before the data is sent (for
 * example by copying the data into a separate pre-allocated DMA descriptor).
 * In such cases the driver needs to take ownership of the network buffer
 * because the network buffer can only be freed after the data has actually
 * been transmitted - which might be some time after the
 * xNetworkInterfaceOutput() function returns. See the examples on the Porting
 * FreeRTOS to a Different Microcontroller documentation page for worked
 * examples.
 */
#ifndef ipconfigZERO_COPY_TX_DRIVER
    #define ipconfigZERO_COPY_TX_DRIVER    0
#endif

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                               DRIVER CONFIG                               */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                             TCP/IP TASK CONFIG                            */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigEVENT_QUEUE_LENGTH
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigEVENT_QUEUE_LENGTH
 *
 * A FreeRTOS queue is used to send events from application tasks to the IP
 * stack. ipconfigEVENT_QUEUE_LENGTH sets the maximum number of events that can
 * be queued for processing at any one time. The event queue must be a minimum
 * of 5 greater than the total number of network buffers.
 */
#ifndef ipconfigEVENT_QUEUE_LENGTH
    #define ipconfigEVENT_QUEUE_LENGTH    ( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS + 5U )
#endif

#if ( ipconfigEVENT_QUEUE_LENGTH < ( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS + 5U ) )
    #error The ipconfigEVENT_QUEUE_LENGTH parameter must be at least ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS + 5
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigIP_TASK_PRIORITY
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigIP_TASK_PRIORITY
 *
 * the TCP/IP stack executes it its own RTOS task (although any application
 * RTOS task can make use of its services through the published sockets API).
 * ipconfigIP_TASK_PRIORITY sets the priority of the RTOS task that executes
 * the TCP/IP stack.
 *
 * The priority is a standard FreeRTOS task priority so it can take any value
 * from 0 (the lowest priority) to (configMAX_PRIORITIES - 1)
 * (the highest priority). configMAX_PRIORITIES is a standard FreeRTOS
 * configuration parameter defined in FreeRTOSConfig.h, not FreeRTOSIPConfig.h.
 *
 * Consideration needs to be given as to the priority assigned to the RTOS task
 * executing the TCP/IP stack relative to the priority assigned to tasks that
 * use the TCP/IP stack.
 */
#ifndef ipconfigIP_TASK_PRIORITY
    #define ipconfigIP_TASK_PRIORITY    ( configMAX_PRIORITIES - 2U )
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigIP_TASK_STACK_SIZE_WORDS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigIP_TASK_STACK_SIZE_WORDS
 *
 * The size, in words (not bytes), of the stack allocated to the
 * FreeRTOS-Plus-TCP RTOS task. FreeRTOS includes optional stack overflow
 * detection.
 */
#ifndef ipconfigIP_TASK_STACK_SIZE_WORDS
    #define ipconfigIP_TASK_STACK_SIZE_WORDS    ( configMINIMAL_STACK_SIZE * 5U )
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES
 *
 * If ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES is set to 1, then the TCP/IP stack
 * will call eApplicationProcessCustomFrameHook to process any unknown frame,
 * that is, any frame that expects ARP or IP.
 */
#ifndef ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES
    #define ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_NETWORK_EVENT_HOOK
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_NETWORK_EVENT_HOOK
 *
 * If ipconfigUSE_NETWORK_EVENT_HOOK is set to 1 then FreeRTOS-Plus-TCP will
 * call the network event hook at the appropriate times. If
 * ipconfigUSE_NETWORK_EVENT_HOOK is not set to 1 then the network event hook
 * will never be called.
 */
#ifndef ipconfigUSE_NETWORK_EVENT_HOOK
    #define ipconfigUSE_NETWORK_EVENT_HOOK    0
#endif

/*---------------------------------------------------------------------------*/

/* 
 * Set to 1 if you want to receive eNetworkDown notification via vApplicationIPNetworkEventHook() callback.
 * Not all drivers support this feature. 
 */
#ifndef ipconfigSUPPORT_NETWORK_DOWN_EVENT
    #define ipconfigSUPPORT_NETWORK_DOWN_EVENT    0
#endif

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                             TCP/IP TASK CONFIG                            */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                                TCP CONFIG                                 */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_TCP
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_TCP
 *
 * Set ipconfigUSE_TCP to 1 to enable TCP. If ipconfigUSE_TCP is set to 0 then
 * only UDP is available.
 */
#ifndef ipconfigUSE_TCP
    #define ipconfigUSE_TCP    1
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigUSE_TCP != 0 )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigIGNORE_UNKNOWN_PACKETS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigIGNORE_UNKNOWN_PACKETS
 *
 * Normally TCP packets that have a bad or unknown destination will result
 * in a RESET being sent back to the remote host. If
 * ipconfigIGNORE_UNKNOWN_PACKETS is set to 1 then such resets will be
 * suppressed (not sent).
 */
    #ifndef ipconfigIGNORE_UNKNOWN_PACKETS
        #define ipconfigIGNORE_UNKNOWN_PACKETS    0
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigTCP_HANG_PROTECTION
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigTCP_HANG_PROTECTION
 *
 * If ipconfigTCP_HANG_PROTECTION is set to 1 then FreeRTOS-Plus-TCP will
 * mark a socket as closed if there is no status change on the socket
 * within the period of time specified by ipconfigTCP_HANG_PROTECTION_TIME.
 */
    #ifndef ipconfigTCP_HANG_PROTECTION
        #define ipconfigTCP_HANG_PROTECTION    1
    #endif

/*-----------------------------------------------------------------------*/

    #if ( ipconfigTCP_HANG_PROTECTION != 0 )

/*-------------------------------------------------------------------*/

/*
 * ipconfigTCP_HANG_PROTECTION_TIME
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigTCP_HANG_PROTECTION_TIME
 *
 * If ipconfigTCP_HANG_PROTECTION is set to 1 then
 * ipconfigTCP_HANG_PROTECTION_TIME sets the interval in seconds
 * between the status of a socket last changing and the anti-hang
 * mechanism marking the socket as closed.
 */
        #ifndef ipconfigTCP_HANG_PROTECTION_TIME
            #define ipconfigTCP_HANG_PROTECTION_TIME    30U
        #endif

/*-------------------------------------------------------------------*/

    #endif /* if ( ipconfigTCP_HANG_PROTECTION != 0 ) */

/*-----------------------------------------------------------------------*/

/*
 * ipconfigTCP_KEEP_ALIVE
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigTCP_KEEP_ALIVE
 *
 * Sockets that are connected but do not transmit any data for an extended
 * period can be disconnected by routers or firewalls that time out. This
 * can be avoided at the application level by ensuring the application
 * periodically sends a packet. Alternatively FreeRTOS-Plus-TCP can be
 * configured to automatically send keep alive messages when it detects
 * that a connection is dormant. Note that, while having FreeRTOS-Plus-TCP
 * automatically send keep alive messages is the more convenient method, it
 * is also the least reliable method because some routers will discard keep
 * alive messages.
 *
 * Set ipconfigTCP_KEEP_ALIVE to 1 to have FreeRTOS-Plus-TCP periodically
 * send keep alive messages on connected but dormant sockets. Set
 * ipconfigTCP_KEEP_ALIVE to 0 to prevent the automatic transmission of
 * keep alive messages.
 *
 * If FreeRTOS-Plus-TCP does not receive a reply to a keep alive message
 * then the connection will be broken and the socket will be marked as
 * closed. Subsequent FreeRTOS_recv() calls on the socket will return
 * -pdFREERTOS_ERRNO_ENOTCONN.
 */
    #ifndef ipconfigTCP_KEEP_ALIVE
        #define ipconfigTCP_KEEP_ALIVE    0
    #endif

/*-----------------------------------------------------------------------*/

    #if ( ipconfigTCP_KEEP_ALIVE != 0 )

/*-------------------------------------------------------------------*/

/*
 * ipconfigTCP_KEEP_ALIVE_INTERVAL
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigTCP_KEEP_ALIVE_INTERVAL
 *
 * If ipconfigTCP_KEEP_ALIVE is set to 1 then
 * ipconfigTCP_KEEP_ALIVE_INTERVAL sets the interval in seconds between
 * successive keep alive messages. Keep alive messages are not sent at
 * all unless ipconfigTCP_KEEP_ALIVE_INTERVAL seconds have passed since
 * the last packet was sent or received.
 */
        #ifndef ipconfigTCP_KEEP_ALIVE_INTERVAL
            #define ipconfigTCP_KEEP_ALIVE_INTERVAL    20U
        #endif

/*-------------------------------------------------------------------*/

    #endif /* if ( ipconfigTCP_KEEP_ALIVE != 0 ) */

/*-----------------------------------------------------------------------*/

/*
 * ipconfigTCP_MSS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigTCP_MSS
 *
 * Sets the MSS value (in bytes) for all TCP packets.
 *
 * Note that FreeRTOS-Plus-TCP contains checks that the defined
 * ipconfigNETWORK_MTU and ipconfigTCP_MSS values are consistent with each
 * other.
 */
    #ifndef ipconfigTCP_MSS
        #define ipconfigTCP_MSS    ( ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER ) )
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigTCP_RX_BUFFER_LENGTH
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigTCP_RX_BUFFER_LENGTH
 *
 * Each TCP socket has a buffer for reception and a separate buffer for
 * transmission.
 *
 * The default buffer size is (4 * ipconfigTCP_MSS).
 *
 * FreeRTOS_setsockopt() can be used with the FREERTOS_SO_RCVBUF and
 * FREERTOS_SO_SNDBUF parameters to set the receive and send buffer sizes
 * respectively - but this must be done between the time that the socket is
 * created and the buffers used by the socket are created. The receive
 * buffer is not created until data is actually received, and the transmit
 * buffer is not created until data is actually sent to the socket for
 * transmission. Once the buffers have been created their sizes cannot be
 * changed.
 *
 * If a listening socket creates a new socket in response to an incoming
 * connect request then the new socket will inherit the buffers sizes of
 * the listening socket.
 */
    #ifndef ipconfigTCP_RX_BUFFER_LENGTH
        /* When MTU equals 1500, the buffer length defaults to 5840 bytes */
        #define ipconfigTCP_RX_BUFFER_LENGTH    ( 4U * ipconfigTCP_MSS )
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigTCP_TX_BUFFER_LENGTH
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigTCP_RX_BUFFER_LENGTH
 *
 * Each TCP socket has a buffer for reception and a separate buffer for
 * transmission.
 *
 * The default buffer size is (4 * ipconfigTCP_MSS).
 *
 * FreeRTOS_setsockopt() can be used with the FREERTOS_SO_RCVBUF and
 * FREERTOS_SO_SNDBUF parameters to set the receive and send buffer sizes
 * respectively - but this must be done between the time that the socket is
 * created and the buffers used by the socket are created. The receive
 * buffer is not created until data is actually received, and the transmit
 * buffer is not created until data is actually sent to the socket for
 * transmission. Once the buffers have been created their sizes cannot be
 * changed.
 *
 * If a listening socket creates a new socket in response to an incoming
 * connect request then the new socket will inherit the buffers sizes of
 * the listening socket.
 */
    #ifndef ipconfigTCP_TX_BUFFER_LENGTH
        #define ipconfigTCP_TX_BUFFER_LENGTH    ( 4U * ipconfigTCP_MSS )
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigTCP_TIME_TO_LIVE
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigTCP_TIME_TO_LIVE
 *
 * Defines the Time To Live TTL) values used in outgoing TCP packets.
 */
    #ifndef ipconfigTCP_TIME_TO_LIVE
        #define ipconfigTCP_TIME_TO_LIVE    128U
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigUSE_TCP_WIN
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_TCP_WIN
 *
 * Sliding Windows allows messages to arrive out-of-order.
 *
 * Set ipconfigUSE_TCP_WIN to 1 to include sliding window behavior in TCP
 * sockets. Set ipconfigUSE_TCP_WIN to 0 to exclude sliding window
 * behavior in TCP sockets.
 *
 * Sliding windows can increase throughput while minimizing network traffic
 * at the expense of consuming more RAM.
 *
 * The size of the sliding window can be changed from its default using the
 * FREERTOS_SO_WIN_PROPERTIES parameter to FreeRTOS_setsockopt(). The
 * sliding window size is specified in units of MSS (so if the MSS is set
 * to 200 bytes then a sliding window size of 2 is equal to 400 bytes) and
 * must always be smaller than or equal to the size of the internal buffers
 * in both directions.
 *
 * If a listening socket creates a new socket in response to an incoming
 * connect request then the new socket will inherit the sliding window
 * sizes of the listening socket.
 */
    #ifndef ipconfigUSE_TCP_WIN
        #define ipconfigUSE_TCP_WIN    1
    #endif

/*-----------------------------------------------------------------------*/

    #if ( ipconfigUSE_TCP_WIN != 0 )

/*-------------------------------------------------------------------*/

/*
 * ipconfigTCP_SRTT_MINIMUM_VALUE_MS
 *
 * when measuring the Smoothed Round Trip Time (SRTT),
 * the result will be rounded up to a minimum value.
 * The default has always been 50, but a value of 1000
 * is recommended ( see RFC6298 ) because hosts often delay the
 * sending of ACK packets with 200 ms.
 */
        #ifndef ipconfigTCP_SRTT_MINIMUM_VALUE_MS
            #define ipconfigTCP_SRTT_MINIMUM_VALUE_MS    50U
        #endif

/*-------------------------------------------------------------------*/

/*
 * ipconfigTCP_WIN_SEG_COUNT
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigTCP_WIN_SEG_COUNT
 *
 * If ipconfigUSE_TCP_WIN is set to 1 then each socket will use a
 * sliding window. Sliding windows allow messages to arrive out-of
 * order, and FreeRTOS-Plus-TCP uses window descriptors to track
 * information about the packets in a window.
 *
 * A pool of descriptors is allocated when the first TCP connection is
 * made. The descriptors are shared between all the sockets.
 * ipconfigTCP_WIN_SEG_COUNT sets the number of descriptors in the
 * pool, and each descriptor is approximately 64 bytes.
 *
 * As an example: If a system will have at most 16 simultaneous TCP
 * connections, and each connection will have an Rx and Tx window of at
 * most 8 segments, then the worst case maximum number of descriptors
 * that will be required is 256 ( 16 * 2 * 8 ). However, the practical
 * worst case is normally much lower than this as most packets will
 * arrive in order.
 */
        #ifndef ipconfigTCP_WIN_SEG_COUNT
            #define ipconfigTCP_WIN_SEG_COUNT    256U
        #endif

/*-------------------------------------------------------------------*/

    #endif /* if ( ipconfigUSE_TCP_WIN != 0 ) */

/*-----------------------------------------------------------------------*/

/*
 * pvPortMallocLarge
 *
 * Malloc functions.  Within most applications of FreeRTOS, the couple
 * pvPortMalloc()/vPortFree() will be used.
 * If there are different types of RAM, the user may decide to use a different
 * memory allocator for different purposes:
 * MallocLarge is used to allocate large TCP buffers (for Rx/Tx)
 */
    #ifndef pvPortMallocLarge
        #define pvPortMallocLarge( x )    pvPortMalloc( x )
    #endif

/*-----------------------------------------------------------------------*/

/*
 * vPortFreeLarge
 *
 * Malloc functions.  Within most applications of FreeRTOS, the couple
 * pvPortMalloc()/vPortFree() will be used.
 * If there are different types of RAM, the user may decide to use a different
 * memory allocator for different purposes:
 * MallocLarge is used to allocate large TCP buffers (for Rx/Tx)
 */
    #ifndef vPortFreeLarge
        #define vPortFreeLarge( ptr )    vPortFree( ptr )
    #endif

/*-----------------------------------------------------------------------*/

#endif /* ( ipconfigUSE_TCP != 0 ) */

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                                TCP CONFIG                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                                UDP CONFIG                                 */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUDP_MAX_RX_PACKETS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUDP_MAX_RX_PACKETS
 *
 * ipconfigUDP_MAX_RX_PACKETS defines the maximum number of packets that can
 * exist in the Rx queue of a UDP socket. For example, if
 * ipconfigUDP_MAX_RX_PACKETS is set to 5 and there are already 5 packets
 * queued on the UDP socket then subsequent packets received on that socket
 * will be dropped until the queue length is less than 5 again.
 */
#ifndef ipconfigUDP_MAX_RX_PACKETS
    #define ipconfigUDP_MAX_RX_PACKETS    0U
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS
 *
 * Sockets have a send block time attribute. If FreeRTOS_sendto() is called but
 * a network buffer cannot be obtained, then the calling RTOS task is held in
 * the Blocked state (so other tasks can continue to executed) until either a
 * network buffer becomes available or the send block time expires. If the send
 * block time expires then the send operation is aborted.
 *
 * The maximum allowable send block time is capped to the value set by
 * ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS. Capping the maximum allowable send
 * block time prevents prevents a deadlock occurring when all the network
 * buffers are in use and the tasks that process (and subsequently free) the
 * network buffers are themselves blocked waiting for a network buffer.
 *
 * ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS is specified in RTOS ticks. A time in
 * milliseconds can be converted to a time in ticks by dividing the time in
 * milliseconds by portTICK_PERIOD_MS.
 */
#ifndef ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS
    #define ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS    ( pdMS_TO_TICKS( 20U ) )
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS
 *
 * If ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS is set to 1 then FreeRTOS-Plus-TCP
 * will accept UDP packets that have their checksum value set to 0, which is in
 * compliance with the UDP specification.
 *
 * If ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS is set to 0 then FreeRTOS-Plus-TCP
 * will drop UDP packets that have their checksum value set to 0, which
 * deviates from the UDP specification, but is safer.
 *
 * Note: This configuration parameter defaults to 0.
 */
#ifndef ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS
    #define ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUDP_TIME_TO_LIVE
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUDP_TIME_TO_LIVE
 *
 * Defines the Time To Live (TTL) values used in outgoing UDP packets.
 */
#ifndef ipconfigUDP_TIME_TO_LIVE
    #define ipconfigUDP_TIME_TO_LIVE    128U
#endif

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                                UDP CONFIG                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              SOCKET CONFIG                                */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND
 *
 * The address of a socket is the combination of its IP address and its port
 * number. FreeRTOS_bind() is used to manually allocate a port number to a
 * socket (to 'bind' the socket to a port), but manual binding is not normally
 * necessary for client sockets (those sockets that initiate outgoing
 * connections rather than wait for incoming connections on a known port
 * number). If ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND is set to 1 then calling
 * FreeRTOS_sendto() on a socket that has not yet been bound will result in the
 * IP stack automatically binding the socket to a port number from the range
 * socketAUTO_PORT_ALLOCATION_START_NUMBER to 0xffff. If
 * ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND is set to 0 then calling
 * FreeRTOS_sendto() on a socket that has not yet been bound will result
 * in the send operation being aborted.
 */
#ifndef ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND
    #define ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND    1
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigSUPPORT_SELECT_FUNCTION
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigSUPPORT_SELECT_FUNCTION
 *
 * Set ipconfigSUPPORT_SELECT_FUNCTION to 1 to include support for the
 * FreeRTOS_select() and associated API functions, or 0 to exclude
 * FreeRTOS_select() and associated API functions from the build.
 */
#ifndef ipconfigSUPPORT_SELECT_FUNCTION
    #define ipconfigSUPPORT_SELECT_FUNCTION    0
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigSUPPORT_SELECT_FUNCTION != 0 )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigSELECT_USES_NOTIFY
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigSELECT_USES_NOTIFY
 *
 * This option is only used in case the socket-select functions are
 * activated (when ipconfigSUPPORT_SELECT_FUNCTION is non-zero). When
 * calling select() for a given socket from the same task, this macro is
 * not required. Only when there are multiple tasks using select on the
 * same sockets, this option may prevent a dead-lock. The problem is that
 * the event bit eSELECT_CALL_IP is waited for and cleared by multiple
 * tasks. The macro ipconfigSELECT_USES_NOTIFY defaults to zero, meaning
 * not active.
 */
    #ifndef ipconfigSELECT_USES_NOTIFY
        #define ipconfigSELECT_USES_NOTIFY    0
    #endif

/*-----------------------------------------------------------------------*/

#endif /* if ( ipconfigSUPPORT_SELECT_FUNCTION != 0 ) */

/*---------------------------------------------------------------------------*/

/*
 * ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME
 *
 * API functions used to read data from a socket can block to wait for data to
 * become available. ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME sets the default
 * block time defined in RTOS ticks. If ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME
 * is not defined then the default block time will be set to portMAX_DELAY -
 * meaning an RTOS task that is blocked on a socket read will not leave the
 * Blocked state until data is available. Note that tasks in the Blocked state
 * do not consume any CPU time.
 *
 * ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME is specified in ticks. The macros
 * pdMS_TO_TICKS() and portTICK_PERIOD_MS can both be used to convert a time
 * specified in milliseconds to a time specified in ticks.
 *
 * The timeout time can be changed at any time using the FREERTOS_SO_RCVTIMEO
 * parameter with FreeRTOS_setsockopt(). Note: Infinite block times should be
 * used with extreme care in order to avoid a situation where all tasks are
 * blocked indefinitely to wait for another RTOS task (which is also blocked
 * indefinitely) to free a network buffer.
 *
 * A socket can be set to non-blocking mode by setting both the send and
 * receive block time to 0. This might be desirable when an RTOS task is using
 * more than one socket - in which case blocking can instead by performed on
 * all the sockets at once using FreeRTOS_select(), or the RTOS task can
 * set ipconfigSOCKET_HAS_USER_SEMAPHORE to one, then block on its own
 * semaphore.
 */
#ifndef ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME
    #define ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME    portMAX_DELAY
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME
 *
 * When writing to a socket, the write may not be able to proceed immediately.
 * For example, depending on the configuration, a write might have to wait for
 * a network buffer to become available. API functions used to write data to a
 * socket can block to wait for the write to succeed.
 * ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME sets the default block time (defined in
 * RTOS ticks). If ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME is not defined, then
 * the default block time will be set to portMAX_DELAY - meaning an RTOS task
 * that is blocked on a socket read will not leave the Blocked state until data
 * is available. Note that tasks in the Blocked state do not consume any CPU
 * time.
 *
 * ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME is specified in ticks.
 * The macros pdMS_TO_TICKS() and portTICK_PERIOD_MS can both be used to
 * convert a time specified in milliseconds to a time specified in ticks.
 *
 * The timeout time can be changed at any time using the FREERTOS_SO_SNDTIMEO
 * parameter with FreeRTOS_setsockopt(). Note: Infinite block times should be
 * used with extreme care in order to avoid a situation where all tasks are
 * blocked indefinitely to wait for another RTOS task (which is also blocked
 * indefinitely) to free a network buffer.
 *
 * A socket can be set to non-blocking mode by setting both the send and
 * receive block time to 0. This might be desirable when an RTOS task is using
 * more than one socket - in which case blocking can instead by performed on
 * all the sockets at once using FreeRTOS_select(), or the RTOS task can set
 * ipconfigSOCKET_HAS_USER_SEMAPHORE to one, then block on its own semaphore.
 *
 * A socket can be set to non-blocking mode by setting both the send and
 * receive block time to 0.
 */
#ifndef ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME
    #define ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME    portMAX_DELAY
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigSOCKET_HAS_USER_SEMAPHORE
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigSOCKET_HAS_USER_SEMAPHORE
 *
 * By default, sockets will block on a send or receive that cannot complete
 * immediately. See the description of the
 * ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME and
 * ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME parameters.
 *
 * If an RTOS task is using multiple sockets and cannot block on one socket at
 * a time, then the sockets can be set into non-blocking mode, and the RTOS
 * task can block on all the sockets at once by either using the
 * FreeRTOS_select() function or by setting ipconfigSOCKET_HAS_USER_SEMAPHORE
 * to 1, using the FREERTOS_SO_SET_SEMAPHORE parameter with
 * FreeRTOS_setsockopt() to provide a semaphore to the socket, and then
 * blocking on the semaphore. The semaphore will be given when any of the
 * sockets are able to proceed - at which time the RTOS task can inspect all
 * the sockets individually using non blocking API calls to determine which
 * socket caused it to unblock.
 */
#ifndef ipconfigSOCKET_HAS_USER_SEMAPHORE
    #define ipconfigSOCKET_HAS_USER_SEMAPHORE    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigSOCKET_HAS_USER_WAKE_CALLBACK
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigSOCKET_HAS_USER_WAKE_CALLBACK
 *
 * It is possible to install an application hook that will be called after
 * every essential socket event. The hook has one parameter: the socket, and it
 * has no return value:
 * typedef void (* SocketWakeupCallback_t)( Socket_t pxSocket );
 * The reason for calling the hook can be one or more of these events:
 *
 * eSOCKET_RECEIVE = 0x0001, /* Reception of new data. *
 * eSOCKET_SEND    = 0x0002, /* Some data has been sent. *
 * eSOCKET_ACCEPT  = 0x0004, /* A new TCP client was detected, please call accept(). *
 * eSOCKET_CONNECT = 0x0008, /* A TCP connect has succeeded or timed-out. *
 * eSOCKET_BOUND   = 0x0010, /* A socket got bound. *
 * eSOCKET_CLOSED  = 0x0020, /* A TCP connection got closed. *
 * eSOCKET_INTR    = 0x0040, /* A blocking API call got interrupted, because
 *                            * the function FreeRTOS_SignalSocket() was called. *
 *
 * Normally the hook will only notify the task that owns the socket so that the
 * socket gets immediate attention.
 */
#ifndef ipconfigSOCKET_HAS_USER_WAKE_CALLBACK
    #define ipconfigSOCKET_HAS_USER_WAKE_CALLBACK    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigSUPPORT_SIGNALS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigSUPPORT_SIGNALS
 *
 * If ipconfigSUPPORT_SIGNALS is set to 1 then the FreeRTOS_SignalSocket() API
 * function is included in the build. FreeRTOS_SignalSocket() can be used to
 * send a signal to a socket, so that any task blocked on a read from the
 * socket will leave the Blocked state (abort the blocking read operation).
 */
#ifndef ipconfigSUPPORT_SIGNALS
    #define ipconfigSUPPORT_SIGNALS    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_CALLBACKS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_CALLBACKS
 *
 * When this macro is defined as non-zero, it is possible to bind specific
 * application hooks (callbacks) to a socket. There is a different application
 * hook for every type of event:
 *
 * FREERTOS_SO_TCP_CONN_HANDLER  * Callback for (dis) connection events.
 *                               * Supply pointer to 'F_TCP_UDP_Handler_t'
 * FREERTOS_SO_TCP_RECV_HANDLER  * Callback for receiving TCP data.
 *                               * Supply pointer to 'F_TCP_UDP_Handler_t'
 * FREERTOS_SO_TCP_SENT_HANDLER  * Callback for sending TCP data.
 *                               * Supply pointer to 'F_TCP_UDP_Handler_t'
 * FREERTOS_SO_UDP_RECV_HANDLER  * Callback for receiving UDP data.
 *                               * Supply pointer to 'F_TCP_UDP_Handler_t'
 * FREERTOS_SO_UDP_SENT_HANDLER  * Callback for sending UDP data.
 *                               * Supply pointer to 'F_TCP_UDP_Handler_t'
 */
#ifndef ipconfigUSE_CALLBACKS
    #define ipconfigUSE_CALLBACKS    0
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigUSE_CALLBACKS != 0 )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigIS_VALID_PROG_ADDRESS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigIS_VALID_PROG_ADDRESS
 *
 * In cases where installable application hooks are used, this macro is
 * called to check if a given address refers to valid (instruction) memory.
 * This is a small example taken from FreeRTOS_TCP_IP.c:
 *
 * if( ipconfigIS_VALID_PROG_ADDRESS( pxSocket->u.xTCP.pxHandleSent ) )
 * {
 *     pxSocket->u.xTCP.pxHandleSent( pxSocket, ulCount );
 * }
 */
    #ifndef ipconfigIS_VALID_PROG_ADDRESS
        #define ipconfigIS_VALID_PROG_ADDRESS( pxAddress )    ( ( pxAddress ) != NULL )
    #endif

/*-----------------------------------------------------------------------*/

#endif /* if ( ipconfigUSE_CALLBACKS != 0 ) */

/*---------------------------------------------------------------------------*/

/*
 * pvPortMallocSocket
 *
 * Malloc functions.  Within most applications of FreeRTOS, the couple
 * pvPortMalloc()/vPortFree() will be used.
 * If there are different types of RAM, the user may decide to use a different
 * memory allocator for different purposes:
 * MallocSocket is used to allocate the space for the sockets
 */
#ifndef pvPortMallocSocket
    #define pvPortMallocSocket( x )    pvPortMalloc( x )
#endif

/*---------------------------------------------------------------------------*/

/*
 * vPortFreeSocket
 *
 * Malloc functions.  Within most applications of FreeRTOS, the couple
 * pvPortMalloc()/vPortFree() will be used.
 * If there are different types of RAM, the user may decide to use a different
 * memory allocator for different purposes:
 * MallocSocket is used to allocate the space for the sockets
 */
#ifndef vPortFreeSocket
    #define vPortFreeSocket( ptr )    vPortFree( ptr )
#endif

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                              SOCKET CONFIG                                */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                               DHCP CONFIG                                 */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_DHCP
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_DHCP
 *
 * If ipconfigUSE_DHCP is 1 then FreeRTOS-Plus-TCP will attempt to retrieve an
 * IP address, netmask, DNS server address and gateway address from a DHCP
 * server - and revert to using the defined static address if an IP address
 * cannot be obtained.
 *
 * If ipconfigUSE_DHCP is 0 then FreeRTOS-Plus-TCP will not attempt to obtain
 * its address information from a DHCP server. Instead, it will immediately use
 * the defined static address information.
 */
#ifndef ipconfigUSE_DHCP
    #define ipconfigUSE_DHCP    1
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_DHCPv6
 *
 * Disable DHCPv6 by default.
 */
#ifndef ipconfigUSE_DHCPv6
    #define ipconfigUSE_DHCPv6    0
#endif

/*---------------------------------------------------------------------------*/

#if ( ( ipconfigUSE_DHCPv6 != 0 ) && ( ipconfigUSE_IPv6 == 0 ) )
    #error DHCPv6 Cannot be enabled without IPv6
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigUSE_DHCP != 0 )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigDHCP_REGISTER_HOSTNAME
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigDHCP_REGISTER_HOSTNAME
 *
 * Often DHCP servers can show the names of devices that have leased IP
 * addresses. When ipconfigDHCP_REGISTER_HOSTNAME is set to 1, the device
 * running FreeRTOS-Plus-TCP can identify itself to a DHCP server with a
 * human readable name by returning the name from an application provided
 * hook (or 'callback') function called pcApplicationHostnameHook().
 *
 * When ipconfigDHCP_REGISTER_HOSTNAME is set to 1 the application must
 * provide a hook (callback) function with the following name and
 * prototype:
 *
 * const char *pcApplicationHostnameHook( void );
 */
    #ifndef ipconfigDHCP_REGISTER_HOSTNAME
        #define ipconfigDHCP_REGISTER_HOSTNAME    0
    #endif

/*-----------------------------------------------------------------------*/

#endif /* if ( ipconfigUSE_DHCP != 0 ) */

/*---------------------------------------------------------------------------*/

#if ( ( ipconfigUSE_DHCP != 0 ) || ( ipconfigUSE_DHCPv6 != 0 ) )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigUSE_DHCP_HOOK
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_DHCP_HOOK
 *
 * A normal DHCP transaction involves the following sequence:
 *
 *     1. The client sends a DHCP discovery packet to request an IP address
 *     from the DHCP server.
 *
 *     2. The DHCP server responds with an offer packet that contains the
 *     offered IP address.
 *
 *     3. The client sends a DHCP request packet in order to claim the
 *     offered IP address
 *
 *     4. The DHCP server sends an acknowledgement packet to grant the
 *     client use of the offered IP address, and to send additional
 *     configuration information to the client. Additional configuration
 *     information typically includes the IP address of the gateway, the IP
 *     address of the DNS server, and the IP address lease length.
 *
 * If ipconfigUSE_DHCP_HOOK is set to 1 then FreeRTOS-Plus-TCP will call an
 * application provided hook (or 'callback') function called
 * xApplicationDHCPUserHook() both before the initial discovery packet is
 * sent, and after a DHCP offer has been received - the hook function can
 * be used to terminate the DHCP process at either one of these two phases
 * in the DHCP sequence. For example, the application writer can
 * effectively disable DHCP, even when ipconfigUSE_DHCP is set to 1, by
 * terminating the DHCP process before the initial discovery packet is
 * sent. As another example, the application writer can check a static IP
 * address is compatible with the network to which the device is connected
 * by receiving an IP address offer from a DHCP server, but then
 * terminating the DHCP process without sending a request packet to claim
 * the offered IP address.
 *
 * If ipconfigUSE_DHCP_HOOK is set to 1, then the application writer must
 * provide a hook (callback) function with the following name and
 * prototype:
 *
 * eDHCPCallbackAnswer_t xApplicationDHCPHook( eDHCPCallbackPhase_t eDHCPPhase,
 *                                             uint32_t ulIPAddress );
 *
 * Where eDHCPCallbackQuestion_t and eDHCPCallbackAnswer_t are defined as
 * follows
 *
 * typedef enum eDHCP_QUESTIONS
 * {
 *     /* About to send discover packet.
 *     eDHCPPhasePreDiscover,
 *     /* About to send a request packet.
 *     eDHCPPhasePreRequest,
 * } eDHCPCallbackQuestion_t;
 *
 * typedef enum eDHCP_ANSWERS
 * {
 *     /* Continue the DHCP process as normal.
 *     eDHCPContinue,
 *     /* Stop the DHCP process, and use the static defaults.
 *     eDHCPUseDefaults,
 *     /* Stop the DHCP process, and continue with current settings.
 *     eDHCPStopNoChanges,
 * } eDHCPCallbackAnswer_t;
 *
 * For example purposes only, below is a reference xApplicationDHCPHook
 * implementation that allows the DHCP sequence to proceed up to the point
 * where an IP address is offered, at which point the offered IP address is
 * compared to the statically configured IP address. If the offered and
 * statically configured IP addresses are on the same subnet, then the
 * statically configured IP address is used. If the offered and statically
 * configured IP addresses are not on the same subnet, then the IP address
 * offered by the DHCP server is used.
 *
 * eDHCPCallbackAnswer_t xApplicationDHCPHook( eDHCPCallbackPhase_t eDHCPPhase,
 *                                      uint32_t ulIPAddress )
 * {
 *     eDHCPCallbackAnswer_t eReturn;
 *     uint32_t ulStaticIPAddress, ulStaticNetMask;
 *
 *     /* This hook is called in a couple of places during the DHCP process, as
 *     identified by the eDHCPPhase parameter. *
 *     switch( eDHCPPhase )
 *     {
 *         case eDHCPPhasePreDiscover  :
 *             /* A DHCP discovery is about to be sent out.  eDHCPContinue is
 *             returned to allow the discovery to go out.
 *
 *             If eDHCPUseDefaults had been returned instead then the DHCP process
 *             would be stopped and the statically configured IP address would be
 *             used.
 *
 *             If eDHCPStopNoChanges had been returned instead then the DHCP
 *             process would be stopped and whatever the current network
 *             configuration was would continue to be used. *
 *             eReturn = eDHCPContinue;
 *         break;
 *
 *         case eDHCPPhasePreRequest  :
 *             /* An offer has been received from the DHCP server, and the
 *             offered IP address is passed in the ulIPAddress parameter.
 *             Convert the offered and statically allocated IP addresses to
 *             32-bit values. *
 *             ulStaticIPAddress = FreeRTOS_inet_addr_quick( configIP_ADDR0,
 *                                                           configIP_ADDR1,
 *                                                           configIP_ADDR2,
 *                                                           configIP_ADDR3 );
 *
 *             ulStaticNetMask = FreeRTOS_inet_addr_quick( configNET_MASK0,
 *                                                         configNET_MASK1,
 *                                                         configNET_MASK2,
 *                                                         configNET_MASK3 );
 *
 *             /* Mask the IP addresses to leave just the sub-domain
 *             octets. *
 *             ulStaticIPAddress &= ulStaticNetMask;
 *             ulIPAddress &= ulStaticNetMask;
 *
 *             /* Are the sub-domains the same? *
 *             if( ulStaticIPAddress == ulIPAddress )
 *             {
 *                 /* The sub-domains match, so the default IP address can be
 *                 used.  The DHCP process is stopped at this point. *
 *                 eReturn = eDHCPUseDefaults;
 *             }
 *             else
 *             {
 *                 /* The sub-domains don't match, so continue with the
 *                 DHCP process so the offered IP address is used. *
 *                 eReturn = eDHCPContinue;
 *             }
 *
 *             break;
 *
 *         default :
 *             /* Cannot be reached, but set eReturn to prevent compiler
 *             warnings where compilers are disposed to generating one. *
 *             eReturn = eDHCPContinue;
 *             break;
 *     }
 *
 *     return eReturn;
 * }
 *
 * When the eDHCPPhase parameter is set to eDHCPPhasePreDiscover, the
 * ulIPAddress parameter is set to the IP address already in use. When the
 * eDHCPPhase parameter is set to eDHCPPhasePreRequest, the ulIPAddress
 * parameter is set to the IP address offered by the DHCP server.
 */
    #ifndef ipconfigUSE_DHCP_HOOK
        #define ipconfigUSE_DHCP_HOOK    1
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigDHCP_FALL_BACK_AUTO_IP
 *
 * Only applicable when DHCP is in use. If no DHCP server responds, use
 * "Auto-IP"; the device will allocate a random LinkLayer IP address, and
 * test if it is still available.
 */
    #ifndef ipconfigDHCP_FALL_BACK_AUTO_IP
        #define ipconfigDHCP_FALL_BACK_AUTO_IP    0
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigMAXIMUM_DISCOVER_TX_PERIOD
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigMAXIMUM_DISCOVER_TX_PERIOD
 *
 * When ipconfigUSE_DHCP is set to 1, DHCP requests will be sent out at
 * increasing time intervals until either a reply is received from a DHCP
 * server and accepted, or the interval between transmissions reaches
 * ipconfigMAXIMUM_DISCOVER_TX_PERIOD. The TCP/IP stack will revert to
 * using the static IP address passed as a parameter to FreeRTOS_IPInit()
 * if the re-transmission time interval reaches
 * ipconfigMAXIMUM_DISCOVER_TX_PERIOD without a DHCP reply being received.
 */
    #ifndef ipconfigMAXIMUM_DISCOVER_TX_PERIOD
        #ifdef _WINDOWS_
            #define ipconfigMAXIMUM_DISCOVER_TX_PERIOD    ( pdMS_TO_TICKS( 999U ) )
        #else
            #define ipconfigMAXIMUM_DISCOVER_TX_PERIOD    ( pdMS_TO_TICKS( 30000U ) )
        #endif
    #endif

/*-----------------------------------------------------------------------*/

#endif /* if ( ( ipconfigUSE_DHCP != 0 ) || ( ipconfigUSE_DHCPv6 != 0 ) ) */

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                               DHCP CONFIG                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                                DNS CONFIG                                 */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_DNS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_DNS
 *
 * Set ipconfigUSE_DNS to 1 to include a basic DNS client/resolver. DNS is used
 * through the FreeRTOS_gethostbyname() API function.
 */
#ifndef ipconfigUSE_DNS
    #define ipconfigUSE_DNS    1
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigUSE_IPv4 == 0 ) && ( ipconfigUSE_DNS != 0 )
    #error "IPv4 (ipconfigUSE_IPv4) needs to be enabled to use DNS"
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigUSE_DNS != 0 )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY
 *
 * When looking up a URL, multiple answers (IP-addresses) may be received.
 * This macro determines how many answers will be stored per URL.
 */
    #ifndef ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY
        #define ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY    1U
    #endif

/*-----------------------------------------------------------------------*/

/*
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_DNS_CACHE
 *
 * ipconfigUSE_DNS_CACHE
 *
 * If ipconfigUSE_DNS_CACHE is set to 1, then the DNS cache will be
 * enabled. If ipconfigUSE_DNS_CACHE is set to 0, then the DNS cache will
 * be disabled.
 */
    #ifndef ipconfigUSE_DNS_CACHE
        #define ipconfigUSE_DNS_CACHE    1
    #endif

/*-----------------------------------------------------------------------*/

    #if ( ipconfigUSE_DNS_CACHE != 0 )

/*-------------------------------------------------------------------*/

/*
 * ipconfigDNS_CACHE_ENTRIES
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigDNS_CACHE_ENTRIES
 *
 * If ipconfigUSE_DNS_CACHE is set to 1 then ipconfigDNS_CACHE_ENTRIES
 * defines the number of entries in the DNS cache.
 */
        #ifndef ipconfigDNS_CACHE_ENTRIES
            #define ipconfigDNS_CACHE_ENTRIES    1U
        #endif

/*-------------------------------------------------------------------*/

/*
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigDNS_CACHE_NAME_LENGTH
 *
 * ipconfigDNS_CACHE_NAME_LENGTH
 *
 * The maximum number of characters a DNS host name can take, including
 * the NULL terminator.
 */
        #ifndef ipconfigDNS_CACHE_NAME_LENGTH
            #define ipconfigDNS_CACHE_NAME_LENGTH    254U
        #endif

/*-------------------------------------------------------------------*/

    #endif /* if ( ipconfigUSE_DNS_CACHE != 0 ) */

/*-----------------------------------------------------------------------*/

/*
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigDNS_REQUEST_ATTEMPTS
 *
 * ipconfigDNS_REQUEST_ATTEMPTS
 *
 *  When looking up a host, the library has to send a DNS request and wait
 *  for a result. This process will be repeated at most
 *  ipconfigDNS_REQUEST_ATTEMPTS times. The macro
 *  ipconfigDNS_SEND_BLOCK_TIME_TICKS determines how long the function
 *  FreeRTOS_sendto() may block.
 *
 *  When sending, by default, the function will block for at most 500
 *  milliseconds. When waiting for a reply, FreeRTOS_recvfrom() will wait
 *  for at most 5000 milliseconds.
 */
    #ifndef ipconfigDNS_REQUEST_ATTEMPTS
        #define ipconfigDNS_REQUEST_ATTEMPTS    5U
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigDNS_RECEIVE_BLOCK_TIME_TICKS
 *
 * When waiting for a reply, FreeRTOS_recvfrom() will wait for at most 5000
 * milliseconds.
 */
    #ifndef ipconfigDNS_RECEIVE_BLOCK_TIME_TICKS
        #define ipconfigDNS_RECEIVE_BLOCK_TIME_TICKS    pdMS_TO_TICKS( 5000U )
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigDNS_SEND_BLOCK_TIME_TICKS
 *
 * The macro ipconfigDNS_SEND_BLOCK_TIME_TICKS determines how long the
 * function FreeRTOS_sendto() may block. When sending, by default, the
 * function will block for at most 500 milliseconds.
 */
    #ifndef ipconfigDNS_SEND_BLOCK_TIME_TICKS
        #define ipconfigDNS_SEND_BLOCK_TIME_TICKS    pdMS_TO_TICKS( 500U )
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigDNS_USE_CALLBACKS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigDNS_USE_CALLBACKS
 *
 * When defined, the function FreeRTOS_gethostbyname_a() becomes available.
 * This function will start a DNS-lookup and set an application 'hook'.
 * This user function (or 'hook') will be called when either the URL has
 * been found, or when a time-out has been reached. Note that the function
 * FreeRTOS_gethostbyname_a() will not make use of the macros
 * ipconfigDNS_SEND_BLOCK_TIME_TICKS and
 * ipconfigDNS_RECEIVE_BLOCK_TIME_TICKS.
 */
    #ifndef ipconfigDNS_USE_CALLBACKS
        #define ipconfigDNS_USE_CALLBACKS    0
    #endif

/*-----------------------------------------------------------------------*/

/*
 * ipconfigINCLUDE_FULL_INET_ADDR
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigINCLUDE_FULL_INET_ADDR
 *
 * Implementing FreeRTOS_inet_addr() necessitates the use of string
 * handling routines, which are relatively large. To save code space, the
 * full FreeRTOS_inet_addr() implementation is made optional, and a smaller
 * and faster alternative called FreeRTOS_inet_addr_quick() is provided.
 * FreeRTOS_inet_addr() takes an IP in decimal dot format (for example,
 * "192.168.0.1") as its parameter. FreeRTOS_inet_addr_quick() takes an IP
 * address as four separate numerical octets (for example, 192, 168, 0, 1)
 * as its parameters. If ipconfigINCLUDE_FULL_INET_ADDR is set to 1, then
 * both FreeRTOS_inet_addr() and FreeRTOS_indet_addr_quick() are available.
 * If ipconfigINCLUDE_FULL_INET_ADDR is not set to 1, then only
 * FreeRTOS_indet_addr_quick() is available.
 */
    #ifndef ipconfigINCLUDE_FULL_INET_ADDR
        #define ipconfigINCLUDE_FULL_INET_ADDR    1
    #endif

/*-----------------------------------------------------------------------*/

#endif /* if ( ipconfigUSE_DNS != 0 ) */

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_LLMNR
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_LLMNR
 *
 * Set ipconfigUSE_LLMNR to 1 to include LLMNR.
 */
#ifndef ipconfigUSE_LLMNR
    #define ipconfigUSE_LLMNR    ( 0 )
#endif

#if ( ( ipconfigUSE_LLMNR != 0 ) && ( ipconfigUSE_DNS == 0 ) )
    #error When either LLMNR is used, ipconfigUSE_DNS must be defined
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_NBNS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_NBNS
 *
 * Set ipconfigUSE_NBNS to 1 to include NBNS.
 */
#ifndef ipconfigUSE_NBNS
    #define ipconfigUSE_NBNS    0
#endif

#if ( ( ipconfigUSE_NBNS != 0 ) && ( ipconfigUSE_DNS == 0 ) )
    #error When either NBNS is used, ipconfigUSE_DNS must be defined
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_MDNS
 *
 * Include support for MDNS: Multicast DNS.
 */
#ifndef ipconfigUSE_MDNS
    #define ipconfigUSE_MDNS    0
#endif

#if ( ( ipconfigUSE_MDNS != 0 ) && ( ipconfigUSE_DNS == 0 ) )
    #error When either MDNS is used, ipconfigUSE_DNS must be defined
#endif

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                                DNS CONFIG                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                                ARP CONFIG                                 */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigARP_CACHE_ENTRIES
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigARP_CACHE_ENTRIES
 *
 * The ARP cache is a table that maps IP addresses to MAC addresses.
 *
 * The IP stack can only send a UDP message to a remove IP address if it knowns
 * the MAC address associated with the IP address, or the MAC address of the
 * router used to contact the remote IP address. When a UDP message is received
 * from a remote IP address, the MAC address and IP address are added to the
 * ARP cache. When a UDP message is sent to a remote IP address that does not
 * already appear in the ARP cache, then the UDP message is replaced by a ARP
 * message that solicits the required MAC address information.
 *
 * ipconfigARP_CACHE_ENTRIES defines the maximum number of entries that can
 * exist in the ARP table at any one time.
 */
#ifndef ipconfigARP_CACHE_ENTRIES
    #define ipconfigARP_CACHE_ENTRIES    10U
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigARP_STORES_REMOTE_ADDRESSES
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigARP_STORES_REMOTE_ADDRESSES
 *
 * Advanced users only.
 *
 * ipconfigARP_STORES_REMOTE_ADDRESSES is provided for the case when a message
 * that requires a reply arrives from the Internet, but from a computer
 * attached to a LAN rather than via the defined gateway. Before replying to
 * the message, the TCP/IP stack RTOS task will loop up the message's IP
 * address in the ARP table - but if ipconfigARP_STORES_REMOTE_ADDRESSES is set
 * to 0, then ARP will return the MAC address of the defined gateway, because
 * the destination address is outside of the netmask. That might prevent the
 * reply reaching its intended destination.
 *
 * If ipconfigARP_STORES_REMOTE_ADDRESSES is set to 1, then remote addresses
 * will also be stored in the ARP table, along with the MAC address from which
 * the message was received. This can allow the message in the scenario above
 * to be routed and delivered correctly.
 */
#ifndef ipconfigARP_STORES_REMOTE_ADDRESSES
    #define ipconfigARP_STORES_REMOTE_ADDRESSES    0
#endif

/*---------------------------------------------------------------------------*/

#if ( defined( ipconfigDHCP_FALL_BACK_AUTO_IP ) && ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 ) )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigARP_USE_CLASH_DETECTION
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigARP_USE_CLASH_DETECTION
 *
 * When a link-layer address is assigned, the driver will test if it is
 * already taken by a different device by sending ARP requests. Therefore,
 * ipconfigARP_USE_CLASH_DETECTION must be defined as non-zero.
 */
    #ifndef ipconfigARP_USE_CLASH_DETECTION
        #define ipconfigARP_USE_CLASH_DETECTION    1
    #endif

    #if ( ipconfigARP_USE_CLASH_DETECTION == 0 )
        #error ipconfigARP_USE_CLASH_DETECTION should be defined as 1 when ipconfigDHCP_FALL_BACK_AUTO_IP is used.
    #endif

/*-----------------------------------------------------------------------*/

#else /* if ( defined( ipconfigDHCP_FALL_BACK_AUTO_IP ) && ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 ) ) */

/*-----------------------------------------------------------------------*/

    #ifndef ipconfigARP_USE_CLASH_DETECTION
        #define ipconfigARP_USE_CLASH_DETECTION    0
    #endif

/*-----------------------------------------------------------------------*/

#endif /* if ( defined( ipconfigDHCP_FALL_BACK_AUTO_IP ) && ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 ) ) */

/*---------------------------------------------------------------------------*/

/*
 * ipconfigMAX_ARP_AGE
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigMAX_ARP_AGE
 *
 * ipconfigMAX_ARP_AGE defines the maximum time between an entry in the ARP
 * table being created or refreshed and the entry being removed because it is
 * stale. New ARP requests are sent for ARP cache entries that are nearing
 * their maximum age.
 *
 * ipconfigMAX_ARP_AGE is specified in tens of seconds, so a value of 150 is
 * equal to 1500 seconds (or 25 minutes).
 */
#ifndef ipconfigMAX_ARP_AGE
    #define ipconfigMAX_ARP_AGE    150U
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigMAX_ARP_RETRANSMISSIONS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigMAX_ARP_RETRANSMISSIONS
 *
 * ARP requests that do not result in an ARP response will be re-transmitted a
 * maximum of ipconfigMAX_ARP_RETRANSMISSIONS times before the ARP request is
 * aborted.
 */
#ifndef ipconfigMAX_ARP_RETRANSMISSIONS
    #define ipconfigMAX_ARP_RETRANSMISSIONS    5U
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_ARP_REMOVE_ENTRY
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_ARP_REMOVE_ENTRY
 *
 * Advanced users only.
 *
 * If ipconfigUSE_ARP_REMOVE_ENTRY is set to 1 then
 * ulARPRemoveCacheEntryByMac() is included in the build.
 * ulARPRemoveCacheEntryByMac() uses a MAC address to look up, and then remove,
 * an entry from the ARP cache. If the MAC address is found in the ARP cache,
 * then the IP address associated with the MAC address is returned. If the MAC
 * address is not found in the ARP cache, then 0 is returned.
 *
 * uint32_t ulARPRemoveCacheEntryByMac( const MACAddress_t * pxMACAddress );
 *
 * ulARPRemoveCacheEntryByMac() function prototype
 */
#ifndef ipconfigUSE_ARP_REMOVE_ENTRY
    #define ipconfigUSE_ARP_REMOVE_ENTRY    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_ARP_REVERSED_LOOKUP
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_ARP_REVERSED_LOOKUP
 *
 * Advanced users only.
 *
 * Normally ARP will look up an IP address from a MAC address. If
 * ipconfigUSE_ARP_REVERSED_LOOKUP is set to 1 then a function that does the
 * reverse is also available. eARPGetCacheEntryByMac() looks up a MAC address
 * from an IP address.
 *
 * eARPLookupResult_t eARPGetCacheEntryByMac( MACAddress_t * const pxMACAddress,
 *                                            uint32_t *pulIPAddress );
 *
 * eARPGetCacheEntryByMac() function prototype
 */
#ifndef ipconfigUSE_ARP_REVERSED_LOOKUP
    #define ipconfigUSE_ARP_REVERSED_LOOKUP    0
#endif

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                                ARP CONFIG                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                               ICMP CONFIG                                 */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigREPLY_TO_INCOMING_PINGS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigREPLY_TO_INCOMING_PINGS
 *
 * If ipconfigREPLY_TO_INCOMING_PINGS is set to 1, then the TCP/IP stack will
 * generate replies to incoming ICMP echo (ping) requests.
 */
#ifndef ipconfigREPLY_TO_INCOMING_PINGS
    #define ipconfigREPLY_TO_INCOMING_PINGS    1
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigREPLY_TO_INCOMING_PINGS != 0 )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigICMP_TIME_TO_LIVE
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigICMP_TIME_TO_LIVE
 *
 * When replying to an ICMP packet, the TTL field will be set to the value
 * of this macro. The default value is 64 (as recommended by RFC 1700).
 * The minimum value is 1, the maximum value is 255.
 */
    #ifndef ipconfigICMP_TIME_TO_LIVE
        #define ipconfigICMP_TIME_TO_LIVE    64U
    #endif

/*-----------------------------------------------------------------------*/

#endif /* if ( ipconfigREPLY_TO_INCOMING_PINGS != 0 ) */

/*---------------------------------------------------------------------------*/

/*
 * ipconfigSUPPORT_OUTGOING_PINGS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigSUPPORT_OUTGOING_PINGS
 *
 * If ipconfigSUPPORT_OUTGOING_PINGS is set to 1 then the
 * FreeRTOS_SendPingRequest() API function is available.
 */
#ifndef ipconfigSUPPORT_OUTGOING_PINGS
    #define ipconfigSUPPORT_OUTGOING_PINGS    0
#endif

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                               ICMP CONFIG                                 */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                              ROUTING CONFIG                               */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigCOMPATIBLE_WITH_SINGLE
 */
#ifndef ipconfigCOMPATIBLE_WITH_SINGLE
    #define ipconfigCOMPATIBLE_WITH_SINGLE    0
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigHAS_ROUTING_STATISTICS
 */
    #ifndef ipconfigHAS_ROUTING_STATISTICS
        #define ipconfigHAS_ROUTING_STATISTICS    1
    #endif

/*-----------------------------------------------------------------------*/

#else /* if ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 ) */

/*-----------------------------------------------------------------------*/

/*
 * ipconfigMULTI_INTERFACE
 */
    #ifndef ipconfigMULTI_INTERFACE
        #define ipconfigMULTI_INTERFACE    1
    #endif

/*-----------------------------------------------------------------------*/

#endif /* if ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 ) */

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                              ROUTING CONFIG                               */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/
/*                        DEBUG/TRACE/LOGGING CONFIG                         */
/*===========================================================================*/

/*---------------------------------------------------------------------------*/

/*
 * ipconfigCHECK_IP_QUEUE_SPACE
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigCHECK_IP_QUEUE_SPACE
 *
 * A FreeRTOS queue is used to send events from application tasks to the IP
 * stack. ipconfigEVENT_QUEUE_LENGTH sets the maximum number of events that can
 * be queued for processing at any one time. If ipconfigCHECK_IP_QUEUE_SPACE is
 * set to 1 then the uxGetMinimumIPQueueSpace() function can be used to query
 * the minimum amount of free space that has existed in the queue since the
 * system booted.
 *
 * UBaseType_t uxGetMinimumIPQueueSpace( void );
 */
#ifndef ipconfigCHECK_IP_QUEUE_SPACE
    #define ipconfigCHECK_IP_QUEUE_SPACE    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigHAS_DEBUG_PRINTF & FreeRTOS_debug_printf
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigHAS_DEBUG_PRINTF
 *
 * The TCP/IP stack outputs debugging messages by calling the
 * FreeRTOS_debug_printf macro. To obtain debugging messages set
 * ipconfigHAS_DEBUG_PRINTF to 1, then define FreeRTOS_debug_printf() to a
 * function that takes a printf() style format string and variable number of
 * inputs, and sends the formatted messages to an output of your choice.
 *
 * Do not define FreeRTOS_debug_printf if ipconfigHAS_DEBUG_PRINTF is set to 0.
 *
 * The following code is taken from the FreeRTOS-Plus-TCP example for the
 * RTOS's Win32 simulator, which has the ability to output debugging messages
 * to a UDP port, standard out, and to a disk file:
 *
 * Prototype for the function function that actually performs the output.
 *
 * extern void vLoggingPrintf( const char *pcFormatString, ... );
 *
 * Set to 1 to print out debug messages.  If ipconfigHAS_DEBUG_PRINTF is set to
 * 1 then FreeRTOS_debug_printf should be defined to the function used to print
 * out the debugging messages.
 *
 * #define ipconfigHAS_DEBUG_PRINTF    0
 * #if( ipconfigHAS_DEBUG_PRINTF == 1 )
 *     #define FreeRTOS_debug_printf(X)    vLoggingPrintf X
 * #endif
 *
 * The function that performs the output (vLoggingPrintf() in the code above)
 * must be reentrant.
 */
#ifndef ipconfigHAS_DEBUG_PRINTF
    #define ipconfigHAS_DEBUG_PRINTF    0
#endif

#ifndef FreeRTOS_debug_printf
    #define FreeRTOS_debug_printf( MSG )    do {} while( ipFALSE_BOOL )
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigHAS_PRINTF & FreeRTOS_printf
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigHAS_PRINTF
 *
 * Some of the TCP/IP stack demo applications generate output messages.
 * The TCP/IP stack outputs these messages by calling the FreeRTOS_printf
 * macro. To obtain the demo application messages set ipconfigHAS_PRINTF to 1,
 * then define FreeRTOS_printf() to a function that takes a printf() style
 * format string and variable number of inputs, and sends the formatted
 * messages to an output of your choice.
 *
 * Do not define FreeRTOS_printf if ipconfigHAS_PRINTF is set to 0.
 *
 * The following code is taken from the FreeRTOS-Plus-TCP example for the
 * RTOS's Win32 simulator, which has the ability to output application messages
 * to a UDP port, standard out, and to a disk file:
 *
 * Prototype for the function function that actually performs the output.
 *
 * extern void vLoggingPrintf( const char *pcFormatString, ... );
 *
 * Set to 1 to print out application messages.  If ipconfigHAS_PRINTF is set to
 * 1 then FreeRTOS_printf should be defined to the function used to print out
 * the application messages.
 *
 * #define ipconfigHAS_PRINTF  0
 * #if( ipconfigHAS_PRINTF == 1 )
 *     #define FreeRTOS_printf(X)  vLoggingPrintf X
 * #endif
 *
 * The function that performs the output (vLoggingPrintf() in the code above)
 * must be reentrant.
 */
#ifndef ipconfigHAS_PRINTF
    #define ipconfigHAS_PRINTF    0
#endif

#ifndef FreeRTOS_printf
    #define FreeRTOS_printf( MSG )    do {} while( ipFALSE_BOOL )
#endif

/*---------------------------------------------------------------------------*/

/*
 * FreeRTOS_flush_logging
 *
 * In cases where a lot of logging is produced, this will be called to give the
 * logging module a chance to flush the data.
 */
#ifndef FreeRTOS_flush_logging
    #define FreeRTOS_flush_logging()    do {} while( ipFALSE_BOOL )
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS
 *
 * The macro configINCLUDE_TRACE_RELATED_CLI_COMMANDS can be defined in
 * FreeRTOSConfig.h. When defined, it will be assigned to
 * ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS. It allows the inclusion
 * of a CLI for tracing purposes.
 */
#ifndef configINCLUDE_TRACE_RELATED_CLI_COMMANDS
    #define ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS    0
#else
    #define ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS    configINCLUDE_TRACE_RELATED_CLI_COMMANDS
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigTCP_IP_SANITY
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigTCP_IP_SANITY
 *
 * The name of this macro is a bit misleading: it only checks the behavior of
 * the module BufferAllocation_1.c. It issues warnings when irregularities are
 * detected.
 */
#ifndef ipconfigTCP_IP_SANITY
    #define ipconfigTCP_IP_SANITY    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigTCP_MAY_LOG_PORT
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigTCP_MAY_LOG_PORT
 *
 * ipconfigTCP_MAY_LOG_PORT( x ) can be defined to specify which port numbers
 * should or should not be logged by FreeRTOS_lprintf(). For example, the
 * following definition will not generate log messages for ports 23 or 2402:
 * #define ipconfigTCP_MAY_LOG_PORT(xPort) ( ( ( xPort ) != 23 ) && ( ( xPort ) != 2402 ) )
 */
#ifndef ipconfigTCP_MAY_LOG_PORT
    #define ipconfigTCP_MAY_LOG_PORT( xPort )    ( xPort != 23U )
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigWATCHDOG_TIMER
 *
 * https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigWATCHDOG_TIMER
 *
 * ipconfigWATCHDOG_TIMER() is a macro that is called on each iteration of the
 * IP task and may be useful if the application included watchdog type
 * functionality that needs to know the IP task is still cycling
 * (although the fact that the IP task is cycling does not necessarily indicate
 * it is functioning correctly).
 *
 * ipconfigWATCHDOG_TIMER() can be defined to perform any action desired by the
 * application writer. If ipconfigWATCHDOG_TIMER() is left undefined then it
 * will be removed completely by the pre-processor (it will default to an empty
 * macro).
 */
#ifndef ipconfigWATCHDOG_TIMER
    #define ipconfigWATCHDOG_TIMER()
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_DUMP_PACKETS
 */
#ifndef ipconfigUSE_DUMP_PACKETS
    #define ipconfigUSE_DUMP_PACKETS    0
#endif

/*---------------------------------------------------------------------------*/

/*
 * ipconfigUSE_TCP_MEM_STATS
 */
#ifndef ipconfigUSE_TCP_MEM_STATS
    #define ipconfigUSE_TCP_MEM_STATS    0
#endif

/*---------------------------------------------------------------------------*/

#if ( ipconfigUSE_TCP_MEM_STATS != 0 )

/*-----------------------------------------------------------------------*/

/*
 * ipconfigTCP_MEM_STATS_MAX_ALLOCATION
 */
    #ifndef ipconfigTCP_MEM_STATS_MAX_ALLOCATION
        #define ipconfigTCP_MEM_STATS_MAX_ALLOCATION    128U
    #endif

/*-----------------------------------------------------------------------*/

#endif /* if ( ipconfigUSE_TCP_MEM_STATS != 0 ) */

/*---------------------------------------------------------------------------*/

/* Should only be included here, ensures trace config is set first */
#include "IPTraceMacroDefaults.h"

/*---------------------------------------------------------------------------*/

/*===========================================================================*/
/*                        DEBUG/TRACE/LOGGING CONFIG                         */
/*===========================================================================*/
/*---------------------------------------------------------------------------*/
/*===========================================================================*/

#endif /* FREERTOS_IP_CONFIG_DEFAULTS_H */
