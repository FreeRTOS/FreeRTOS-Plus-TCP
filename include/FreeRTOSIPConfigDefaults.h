/*
 * FreeRTOS+TCP V2.3.3
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

#ifndef FREERTOS_DEFAULT_IP_CONFIG_H
#define FREERTOS_DEFAULT_IP_CONFIG_H

#ifndef FREERTOS_IP_H
    #error Please FreeRTOS_IP.h include this header file.
#endif

/* The error numbers defined in this file will be moved to the core FreeRTOS
 * code in future versions of FreeRTOS - at which time the following header file
 * will be removed. */
#include "FreeRTOS_errno_TCP.h"

/* This file provides default values for configuration options that are missing
 * from the FreeRTOSIPConfig.h configuration header file. */

/* These macros are used to define away static keyword for CBMC proofs */
#ifndef _static
    #define _static    static
#endif

#ifndef configPRINTF
    #define configPRINTF( X )    do {} while( 0 )
#endif

/* Ensure defined configuration constants are using the most up to date naming. */
#ifdef tcpconfigIP_TIME_TO_LIVE
    #error now called: ipconfigTCP_TIME_TO_LIVE
#endif

#ifdef updconfigIP_TIME_TO_LIVE
    #error now called: ipconfigUDP_TIME_TO_LIVE
#endif

#ifdef ipFILLER_SIZE
    #error now called: ipconfigPACKET_FILLER_SIZE
#endif

#ifdef dnsMAX_REQUEST_ATTEMPTS
    #error now called: ipconfigDNS_REQUEST_ATTEMPTS
#endif

#ifdef ipconfigUDP_TASK_PRIORITY
    #error now called: ipconfigIP_TASK_PRIORITY
#endif

#ifdef ipconfigUDP_TASK_STACK_SIZE_WORDS
    #error now called: ipconfigIP_TASK_STACK_SIZE_WORDS
#endif

#ifdef ipconfigDRIVER_INCLUDED_RX_IP_FILTERING
    #error now called: ipconfigETHERNET_DRIVER_FILTERS_PACKETS
#endif

#ifdef ipconfigMAX_SEND_BLOCK_TIME_TICKS
    #error now called: ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS
#endif

#ifdef ipconfigUSE_RECEIVE_CONNECT_CALLBACKS
    #error now called: ipconfigUSE_CALLBACKS
#endif

#ifdef ipconfigNUM_NETWORK_BUFFERS
    #error now called: ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS
#endif

#ifdef ipconfigTCP_HANG_PROT
    #error now called: ipconfigTCP_HANG_PROTECTION
#endif

#ifdef ipconfigTCP_HANG_PROT_TIME
    #error now called: ipconfigTCP_HANG_PROTECTION_TIME
#endif

#ifdef FreeRTOS_lprintf
    #error now called: FreeRTOS_debug_printf
#endif

#ifdef  ipconfigBUFFER_ALLOC_FIXED_SIZE
    #error ipconfigBUFFER_ALLOC_FIXED_SIZE was dropped and replaced by a const value, declared in BufferAllocation[12].c
#endif

#ifdef  ipconfigNIC_SEND_PASSES_DMA
    #error now called: ipconfigZERO_COPY_TX_DRIVER
#endif

#ifdef  HAS_TX_CRC_OFFLOADING

/* _HT_ As these macro names have changed, throw an error
 * if they're still defined. */
    #error now called: ipconfigHAS_TX_CRC_OFFLOADING
#endif

#ifdef  HAS_RX_CRC_OFFLOADING
    #error now called: ipconfigHAS_RX_CRC_OFFLOADING
#endif

#ifdef ipconfigTCP_RX_BUF_LEN
    #error ipconfigTCP_RX_BUF_LEN is now called ipconfigTCP_RX_BUFFER_LENGTH
#endif

#ifdef ipconfigTCP_TX_BUF_LEN
    #error ipconfigTCP_TX_BUF_LEN is now called ipconfigTCP_TX_BUFFER_LENGTH
#endif

#ifdef ipconfigDHCP_USES_USER_HOOK
    #error ipconfigDHCP_USES_USER_HOOK and its associated callback have been superseded - see http: /*www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_DHCP_HOOK */
#endif

/* The IP stack executes it its own task (although any application task can make
 * use of its services through the published sockets API). ipconfigUDP_TASK_PRIORITY
 * sets the priority of the task that executes the IP stack.  The priority is a
 * standard FreeRTOS task priority so can take any value from 0 (the lowest
 * priority) to (configMAX_PRIORITIES - 1) (the highest priority).
 * configMAX_PRIORITIES is a standard FreeRTOS configuration parameter defined in
 * FreeRTOSConfig.h, not FreeRTOSIPConfig.h. Consideration needs to be given as to
 * the priority assigned to the task executing the IP stack relative to the
 * priority assigned to tasks that use the IP stack. */
#ifndef ipconfigIP_TASK_PRIORITY
    #define ipconfigIP_TASK_PRIORITY    ( configMAX_PRIORITIES - 2 )
#endif

/* The size, in words (not bytes), of the stack allocated to the FreeRTOS+TCP
 * task.  This setting is less important when the FreeRTOS Win32 simulator is used
 * as the Win32 simulator only stores a fixed amount of information on the task
 * stack.  FreeRTOS includes optional stack overflow detection, see:
 * http://www.freertos.org/Stacks-and-stack-overflow-checking.html */
#ifndef ipconfigIP_TASK_STACK_SIZE_WORDS
    #define ipconfigIP_TASK_STACK_SIZE_WORDS    ( configMINIMAL_STACK_SIZE * 5 )
#endif

#ifndef ipconfigUSE_TCP
    #define ipconfigUSE_TCP    ( 1 )
#endif

#ifndef ipconfigCOMPATIBLE_WITH_SINGLE
    #define ipconfigCOMPATIBLE_WITH_SINGLE    ( 0 )
#endif

#if ipconfigUSE_TCP

/* Disable IPv6 by default. */
    #ifndef ipconfigUSE_DHCPv6
        #define ipconfigUSE_DHCPv6    ( 0 )
    #endif

/* Include support for TCP scaling windows */
    #ifndef ipconfigUSE_TCP_WIN
        #define ipconfigUSE_TCP_WIN    ( 1 )
    #endif

    #ifndef ipconfigTCP_WIN_SEG_COUNT
        #define ipconfigTCP_WIN_SEG_COUNT    ( 256 )
    #endif

    #ifndef ipconfigIGNORE_UNKNOWN_PACKETS

/* When non-zero, TCP will not send RST packets in reply to
 * TCP packets which are unknown, or out-of-order. */
        #define ipconfigIGNORE_UNKNOWN_PACKETS    ( 0 )
    #endif
#endif /* if ipconfigUSE_TCP */

/*
 * For debugging/logging: check if the port number is used for telnet
 * Some events will not be logged for telnet connections
 * because it would produce logging about the transmission of the logging...
 * This macro will only be used if FreeRTOS_debug_printf() is defined for logging
 */
#ifndef ipconfigTCP_MAY_LOG_PORT
    #define ipconfigTCP_MAY_LOG_PORT( xPort )    ( ( xPort ) != 23U )
#endif


#ifndef ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME
    #define ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME    portMAX_DELAY
#endif

#ifndef ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME
    #define ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME    portMAX_DELAY
#endif


#ifndef ipconfigDNS_RECEIVE_BLOCK_TIME_TICKS
    #define ipconfigDNS_RECEIVE_BLOCK_TIME_TICKS    pdMS_TO_TICKS( 500U )
#endif

#ifndef ipconfigDNS_SEND_BLOCK_TIME_TICKS
    #define ipconfigDNS_SEND_BLOCK_TIME_TICKS    pdMS_TO_TICKS( 500U )
#endif

/*
 * FreeRTOS debug logging routine (proposal)
 * The macro will be called in the printf() style. Users can define
 * their own logging routine as:
 *
 *     #define FreeRTOS_debug_printf( MSG )			my_printf MSG
 *
 * The FreeRTOS_debug_printf() must be thread-safe but does not have to be
 * interrupt-safe.
 */
#ifdef ipconfigHAS_DEBUG_PRINTF
    #if ( ipconfigHAS_DEBUG_PRINTF == 0 )
        #ifdef FreeRTOS_debug_printf
            #error Do not define FreeRTOS_debug_print if ipconfigHAS_DEBUG_PRINTF is set to 0
        #endif /* ifdef FreeRTOS_debug_printf */
    #endif /* ( ipconfigHAS_DEBUG_PRINTF == 0 ) */
#endif /* ifdef ipconfigHAS_DEBUG_PRINTF */

#ifndef FreeRTOS_debug_printf
    #define FreeRTOS_debug_printf( MSG )    do {} while( ipFALSE_BOOL )
    #define ipconfigHAS_DEBUG_PRINTF    0
#endif

/*
 * FreeRTOS general logging routine (proposal)
 * Used in some utility functions such as FreeRTOS_netstat() and FreeRTOS_PrintARPCache()
 *
 *     #define FreeRTOS_printf( MSG )			my_printf MSG
 *
 * The FreeRTOS_printf() must be thread-safe but does not have to be interrupt-safe
 */
#ifdef ipconfigHAS_PRINTF
    #if ( ipconfigHAS_PRINTF == 0 )
        #ifdef FreeRTOS_printf
            #error Do not define FreeRTOS_print if ipconfigHAS_PRINTF is set to 0
        #endif /* ifdef FreeRTOS_debug_printf */
    #endif /* ( ipconfigHAS_PRINTF == 0 ) */
#endif /* ifdef ipconfigHAS_PRINTF */

#ifndef FreeRTOS_printf
    #define FreeRTOS_printf( MSG )    do {} while( ipFALSE_BOOL )
    #define ipconfigHAS_PRINTF    0
#endif

/*
 * In cases where a lot of logging is produced, FreeRTOS_flush_logging( )
 * will be called to give the logging module a chance to flush the data
 * An example of this is the netstat command, which produces many lines of logging
 */
#ifndef FreeRTOS_flush_logging
    #define FreeRTOS_flush_logging()    do {} while( ipFALSE_BOOL )
#endif

/* Malloc functions. Within most applications of FreeRTOS, the couple
 * pvPortMalloc()/vPortFree() will be used.
 * If there is also SDRAM, the user may decide to use a different memory
 * allocator:
 * MallocLarge is used to allocate large TCP buffers (for Rx/Tx)
 * MallocSocket is used to allocate the space for the sockets
 */
#ifndef pvPortMallocLarge
    #define pvPortMallocLarge( x )    pvPortMalloc( x )
#endif

#ifndef vPortFreeLarge
    #define vPortFreeLarge( ptr )    vPortFree( ptr )
#endif

#ifndef pvPortMallocSocket
    #define pvPortMallocSocket( x )    pvPortMalloc( x )
#endif

#ifndef vPortFreeSocket
    #define vPortFreeSocket( ptr )    vPortFree( ptr )
#endif

/* --------------------------------------------------------
 * End of: HT Added some macro defaults for the PLUS-UDP project
 * -------------------------------------------------------- */

#ifndef ipconfigUSE_NETWORK_EVENT_HOOK
    #define ipconfigUSE_NETWORK_EVENT_HOOK    0
#endif

#ifndef ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS
    #define ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS    ( pdMS_TO_TICKS( 20U ) )
#endif

#ifndef ipconfigARP_CACHE_ENTRIES
    #define ipconfigARP_CACHE_ENTRIES    10
#endif

#ifndef ipconfigND_CACHE_ENTRIES
    #define ipconfigND_CACHE_ENTRIES    24
#endif

#ifndef ipconfigMAX_ARP_RETRANSMISSIONS
    #define ipconfigMAX_ARP_RETRANSMISSIONS    ( 5U )
#endif

#ifndef ipconfigMAX_ARP_AGE
    #define ipconfigMAX_ARP_AGE    150U
#endif

#ifndef ipconfigUSE_ARP_REVERSED_LOOKUP
    #define ipconfigUSE_ARP_REVERSED_LOOKUP    0
#endif

#ifndef ipconfigUSE_ARP_REMOVE_ENTRY
    #define ipconfigUSE_ARP_REMOVE_ENTRY    0
#endif

#ifndef ipconfigINCLUDE_FULL_INET_ADDR
    #define ipconfigINCLUDE_FULL_INET_ADDR    1
#endif

#ifndef ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS
    #define ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS    45U
#endif

#ifndef ipconfigEVENT_QUEUE_LENGTH
    #define ipconfigEVENT_QUEUE_LENGTH    ( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS + 5U )
#endif

#if ( ipconfigEVENT_QUEUE_LENGTH < ( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS + 5U ) )
    #error The ipconfigEVENT_QUEUE_LENGTH parameter must be at least ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS + 5U
#endif

#ifndef ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND
    #define ipconfigALLOW_SOCKET_SEND_WITHOUT_BIND    1
#endif

/* Configuration to control whether packets with IP options,
 * received over the network, should be passed up to the
 * software stack OR should be dropped.
 * If set to 1, the stack accepts IP packets that contain IP options, but does
 * not process the options (IP options are not supported).
 * If set to 0, the stack will drop IP packets that contain IP options.
 */
#ifndef ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS
    #define ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS    1
#endif

/* Configuration to control whether all outgoing IP datagrams get their
 * "don't fragment" flag set.
 * If set to 1, the stack will set the "don't fragment" flag on all outgoing IP
 * packets. If a packet needs to be fragmented somewhere along it's path, it will get
 * discarded instead of fragmented.
 * If set to 0, the stack will clear the "don't fragment" flag an all outgoing IP
 * packets therefore allowing fragmentation if it is needed.
 */
#ifndef ipconfigFORCE_IP_DONT_FRAGMENT
    #define ipconfigFORCE_IP_DONT_FRAGMENT    0
#endif

/* Configuration to control whether UDP packets with
 * checksum value of zero should be passed up the software
 * stack OR should be dropped.
 * If set to 1, the stack will accept UDP packets that have their checksum
 * value set to 0.
 * If set to 0, the stack will drop UDP packets that have their checksum value
 * set to 0.
 */
#ifndef ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS
    #define ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS    0
#endif

#ifndef ipconfigUDP_TIME_TO_LIVE
    #define ipconfigUDP_TIME_TO_LIVE    128
#endif

#ifndef ipconfigTCP_TIME_TO_LIVE
    #define ipconfigTCP_TIME_TO_LIVE    128
#endif

#ifndef ipconfigICMP_TIME_TO_LIVE
    /* Set the default value suggested in RFC 1700. */
    #define ipconfigICMP_TIME_TO_LIVE    64
#endif

#ifndef ipconfigUDP_MAX_RX_PACKETS

/* Make positive to define the maximum number of packets which will be buffered
 * for each UDP socket.
 * Can be overridden with the socket option FREERTOS_SO_UDP_MAX_RX_PACKETS
 */
    #define ipconfigUDP_MAX_RX_PACKETS    0U
#endif

#ifndef ipconfigUSE_DHCP
    #define ipconfigUSE_DHCP    1
#endif

/* In earlier releases 'ipconfigUSE_DHCP_HOOK' was called
 * 'ipconfigDHCP_USES_USER_HOOK'. */
#ifndef ipconfigUSE_DHCP_HOOK
    #define ipconfigUSE_DHCP_HOOK    0
#endif

#ifndef ipconfigDHCP_FALL_BACK_AUTO_IP

/*
 * Only applicable when DHCP is in use:
 * If no DHCP server responds, use "Auto-IP" : the
 * device will allocate a random LinkLayer IP address.
 */
    #define ipconfigDHCP_FALL_BACK_AUTO_IP    ( 0 )
#endif

#if ( ipconfigDHCP_FALL_BACK_AUTO_IP != 0 )
    #ifndef ipconfigARP_USE_CLASH_DETECTION
        #define ipconfigARP_USE_CLASH_DETECTION    1
    #else
        #if ( ipconfigARP_USE_CLASH_DETECTION != 1 )
            #error ipconfigARP_USE_CLASH_DETECTION should be defined as 1 when AUTO_IP is used.
        #endif
    #endif
#elif !defined( ipconfigARP_USE_CLASH_DETECTION )
    #define ipconfigARP_USE_CLASH_DETECTION    0
#endif

/* RA or Router Advertisement/SLAAC: see end-point flag 'bWantRA'.
 * An Router Solicitation will be sent. It will wait for ipconfigRA_SEARCH_TIME_OUT_MSEC ms.
 * When there is no response, it will be repeated ipconfigRA_SEARCH_COUNT times.
 * Then it will be checked if the chosen IP-address already exists, repeating this
 * ipconfigRA_IP_TEST_COUNT times, each time with a timeout of ipconfigRA_IP_TEST_TIME_OUT_MSEC ms.
 * Finally the end-point will go in the UP state.
 */
#ifndef ipconfigRA_SEARCH_COUNT
    #define ipconfigRA_SEARCH_COUNT    ( 3U )
#endif

#ifndef ipconfigRA_SEARCH_TIME_OUT_MSEC
    #define ipconfigRA_SEARCH_TIME_OUT_MSEC    ( 10000U )
#endif

#ifndef ipconfigRA_IP_TEST_COUNT
    #define ipconfigRA_IP_TEST_COUNT    ( 3 )
#endif

#ifndef ipconfigRA_IP_TEST_TIME_OUT_MSEC
    #define ipconfigRA_IP_TEST_TIME_OUT_MSEC    ( 1500U )
#endif

#ifndef ipconfigNETWORK_MTU
    #define ipconfigNETWORK_MTU    1500U
#else
    #if ipconfigNETWORK_MTU > ( SIZE_MAX >> 1 )
        #undef ipconfigNETWORK_MTU
        #define ipconfigNETWORK_MTU    ( SIZE_MAX >> 1 )
    #endif
#endif

#if ( ipconfigNETWORK_MTU < 46 )
    #error ipconfigNETWORK_MTU must be at least 46.
#endif

#ifndef ipconfigTCP_MSS

/* The default value of ipconfigTCP_MSS depends
 * on the IP version in use: an IPv6 header is
 * 20 bytes longer than an IPv4 header. */
    #if ( ipconfigUSE_IPv6 != 0 )
        #define ipconfigTCP_MSS    ( ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_TCP_HEADER ) )
    #else
        #define ipconfigTCP_MSS    ( ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER ) )
    #endif
#endif

#if ( ipconfigUSE_IPv6 != 0 )
    /* Check if 'ipconfigTCP_MSS' is not too large. */
    #if ( ( ipconfigTCP_MSS + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_TCP_HEADER ) > ipconfigNETWORK_MTU )
        #error The ipconfigTCP_MSS setting in FreeRTOSIPConfig.h is too large.
    #endif
#endif

/* Each TCP socket has circular stream buffers for Rx and Tx, which
 * have a fixed maximum size.
 * The defaults for these size are defined here, although
 * they can be overridden at runtime by using the setsockopt() call */
#ifndef ipconfigTCP_RX_BUFFER_LENGTH
    #define ipconfigTCP_RX_BUFFER_LENGTH    ( 4U * ipconfigTCP_MSS )            /* defaults to 5840 bytes */
#endif

/* Define the size of Tx stream buffer for TCP sockets */
#ifndef ipconfigTCP_TX_BUFFER_LENGTH
    #define ipconfigTCP_TX_BUFFER_LENGTH    ( 4U * ipconfigTCP_MSS )        /* defaults to 5840 bytes */
#endif

#ifndef ipconfigMAXIMUM_DISCOVER_TX_PERIOD
    #ifdef _WINDOWS_
        #define ipconfigMAXIMUM_DISCOVER_TX_PERIOD    ( pdMS_TO_TICKS( 999U ) )
    #else
        #define ipconfigMAXIMUM_DISCOVER_TX_PERIOD    ( pdMS_TO_TICKS( 30000U ) )
    #endif /* _WINDOWS_ */
#endif /* ipconfigMAXIMUM_DISCOVER_TX_PERIOD */

#if ( ipconfigUSE_DNS == 0 )
    /* The DNS module will not be included. */
    #if ( ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) )
        /* LLMNR and NBNS depend on DNS because those protocols share a lot of code. */
        #error When either LLMNR or NBNS is used, ipconfigUSE_DNS must be defined
    #endif
#endif

#ifndef ipconfigUSE_DNS
    #define ipconfigUSE_DNS    1
#endif

#ifndef ipconfigDNS_REQUEST_ATTEMPTS
    #define ipconfigDNS_REQUEST_ATTEMPTS    5
#endif

#ifndef ipconfigUSE_DNS_CACHE
    #define ipconfigUSE_DNS_CACHE    0
#endif

#if ( ipconfigUSE_DNS_CACHE != 0 )
    #ifndef ipconfigDNS_CACHE_NAME_LENGTH

/* Per https://tools.ietf.org/html/rfc1035, 253 is the maximum string length
 * of a DNS name. The following default accounts for a null terminator. */
        #define ipconfigDNS_CACHE_NAME_LENGTH    254U
    #endif

    #ifndef ipconfigDNS_CACHE_ENTRIES
        #define ipconfigDNS_CACHE_ENTRIES    1
    #endif
#endif /* ipconfigUSE_DNS_CACHE != 0 */

/* When accessing services which have multiple IP addresses, setting this
 * greater than 1 can improve reliability by returning different IP address
 * answers on successive calls to FreeRTOS_gethostbyname(). */
#ifndef ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY
    #define ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY    1
#endif

#ifndef ipconfigCHECK_IP_QUEUE_SPACE
    #define ipconfigCHECK_IP_QUEUE_SPACE    0
#endif

#ifndef ipconfigUSE_LLMNR
    /* Include support for LLMNR: Link-local Multicast Name Resolution (non-Microsoft) */
    #define ipconfigUSE_LLMNR    ( 0 )
#endif

#ifndef ipconfigREPLY_TO_INCOMING_PINGS
    #define ipconfigREPLY_TO_INCOMING_PINGS    1
#endif

#ifndef ipconfigSUPPORT_OUTGOING_PINGS
    #define ipconfigSUPPORT_OUTGOING_PINGS    0
#endif

#ifndef ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES
    #define ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES    1
#endif

#ifndef ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES
    #define ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES    1
#endif

#ifndef configINCLUDE_TRACE_RELATED_CLI_COMMANDS
    #define ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS    0
#else
    #define ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS    configINCLUDE_TRACE_RELATED_CLI_COMMANDS
#endif

#ifndef ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM    ( 0 )
#endif

#ifndef ipconfigETHERNET_DRIVER_FILTERS_PACKETS

/*
 * MISRA: the macro 'ipconfigETHERNET_DRIVER_FILTERS_PACKETS'
 * may not be unique, as it is longer than 32 characters.
 * The first 31 characters are the same as in
 * 'ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES'.
 */
    #define ipconfigETHERNET_DRIVER_FILTERS_PACKETS    ( 0 )
#endif

#ifndef ipconfigWATCHDOG_TIMER

/* This macro will be called in every loop the IP-task makes.  It may be
 * replaced by user-code that triggers a watchdog */
    #define ipconfigWATCHDOG_TIMER()
#endif

#ifndef ipconfigUSE_CALLBACKS
    #define ipconfigUSE_CALLBACKS    ( 0 )
#endif

#if ( ipconfigUSE_CALLBACKS != 0 )
    #ifndef ipconfigIS_VALID_PROG_ADDRESS

/* Replace this macro with a test returning non-zero if the memory pointer to by x
 * is valid memory which can contain executable code
 * In fact this is an extra safety measure: if a handler points to invalid memory,
 * it will not be called
 */
        #define ipconfigIS_VALID_PROG_ADDRESS( x )    ( ( x ) != NULL )
    #endif
#endif

#ifndef ipconfigHAS_INLINE_FUNCTIONS
    #define ipconfigHAS_INLINE_FUNCTIONS    ( 1 )
#endif

#ifndef portINLINE
    #define portINLINE    inline
#endif

#ifndef ipconfigZERO_COPY_TX_DRIVER

/* When non-zero, the buffers passed to the SEND routine may be passed
 * to DMA. As soon as sending is ready, the buffers must be released by
 * calling vReleaseNetworkBufferAndDescriptor(), */
    #define ipconfigZERO_COPY_TX_DRIVER    ( 0 )
#endif

#ifndef ipconfigZERO_COPY_RX_DRIVER

/* This define doesn't mean much to the driver, except that it makes
 * sure that pxPacketBuffer_to_NetworkBuffer() will be included. */
    #define ipconfigZERO_COPY_RX_DRIVER    ( 0 )
#endif

#ifndef ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM    0
#endif

#ifndef ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM    0
#endif

#ifndef ipconfigDHCP_REGISTER_HOSTNAME
    #define ipconfigDHCP_REGISTER_HOSTNAME    0
#endif

#ifndef ipconfigSOCKET_HAS_USER_SEMAPHORE
    #define ipconfigSOCKET_HAS_USER_SEMAPHORE    0
#endif

#ifndef ipconfigSOCKET_HAS_USER_WAKE_CALLBACK
    #define ipconfigSOCKET_HAS_USER_WAKE_CALLBACK    0
#endif

#ifndef ipconfigSUPPORT_SELECT_FUNCTION
    #define ipconfigSUPPORT_SELECT_FUNCTION    0
#endif

#ifndef ipconfigSELECT_USES_NOTIFY
    #define ipconfigSELECT_USES_NOTIFY    0
#endif

#ifndef ipconfigTCP_KEEP_ALIVE
    #define ipconfigTCP_KEEP_ALIVE    0
#endif

#ifndef ipconfigDNS_USE_CALLBACKS
    #define ipconfigDNS_USE_CALLBACKS    0
#endif

#ifndef ipconfigSUPPORT_SIGNALS
    #define ipconfigSUPPORT_SIGNALS    0
#endif

#ifndef ipconfigUSE_IPv6
    #define ipconfigUSE_IPv6    0
#endif

#ifndef ipconfigUSE_RA
    #define ipconfigUSE_RA    0
#endif

#if ( ipconfigUSE_IPv6 == 0 ) && ( ipconfigUSE_RA == 1 )

/* ipconfigUSE_RA depends on ipconfigUSE_IPv6. When ipconfigUSE_IPv6 is disabled,
 * disable ipconfigUSE_RA as well. */
    #undef ipconfigUSE_RA
    #define ipconfigUSE_RA    0
#endif

#ifndef ipconfigUSE_NBNS
    #define ipconfigUSE_NBNS    0
#endif

/* As an attack surface reduction for ports that listen for inbound
 * connections, hang protection can help reduce the impact of SYN floods. */
#ifndef ipconfigTCP_HANG_PROTECTION
    #define ipconfigTCP_HANG_PROTECTION    1
#endif

/* Non-activity timeout is expressed in seconds. */
#ifndef ipconfigTCP_HANG_PROTECTION_TIME
    #define ipconfigTCP_HANG_PROTECTION_TIME    30
#endif

#ifndef ipconfigTCP_IP_SANITY
    #define ipconfigTCP_IP_SANITY    0
#endif

#ifndef ipconfigARP_STORES_REMOTE_ADDRESSES
    #define ipconfigARP_STORES_REMOTE_ADDRESSES    0
#endif

#ifndef ipconfigUSE_LINKED_RX_MESSAGES
    #define ipconfigUSE_LINKED_RX_MESSAGES    0
#endif

#ifndef ipconfigBUFFER_PADDING

/* Expert option: define a value for 'ipBUFFER_PADDING'.
 * When 'ipconfigBUFFER_PADDING' equals 0,
 * 'ipBUFFER_PADDING' will get a default value of 8 + 2 bytes. */
    #define ipconfigBUFFER_PADDING    0
#endif

#ifndef ipconfigPACKET_FILLER_SIZE
    #define ipconfigPACKET_FILLER_SIZE    2U
#endif

#ifndef ipconfigMULTI_INTERFACE
    #define ipconfigMULTI_INTERFACE    0
#endif

#ifndef ipconfigENDPOINT_DNS_ADDRESS_COUNT
    #define ipconfigENDPOINT_DNS_ADDRESS_COUNT    2U
#endif

#ifndef ipconfigUSE_LOOPBACK
    #define ipconfigUSE_LOOPBACK    0
#endif

#ifndef ipconfigUSE_TCP_TIMESTAMPS
    #define ipconfigUSE_TCP_TIMESTAMPS    0
#endif

#ifndef ipconfigNETWORK_BUFFER_DEBUGGING
    #define ipconfigNETWORK_BUFFER_DEBUGGING    0
#endif

#ifndef ipconfigHAS_ROUTING_STATISTICS
    #define ipconfigHAS_ROUTING_STATISTICS    0
#endif

#endif /* FREERTOS_DEFAULT_IP_CONFIG_H */
