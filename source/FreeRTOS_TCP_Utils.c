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
 * @file FreeRTOS_TCP_Utils.c
 * @brief Module contains utility functions used by FreeRTOS+TCP module.
 *
 * Endianness: in this module all ports and IP addresses are stored in
 * host byte-order, except fields in the IP-packets
 */
/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

#include "FreeRTOS_TCP_Utils.h"

/* Just make sure the contents doesn't get compiled if TCP is not enabled. */
#if ipconfigUSE_TCP == 1


/* For logging and debugging: make a string showing the TCP flags
 */
    #if ( ipconfigHAS_DEBUG_PRINTF != 0 )

/**
 * @brief Print out the value of flags in a human readable manner.
 *
 * @param[in] xFlags: The TCP flags.
 *
 * @return The string containing the flags.
 */

        static char retString[ 10 ];
        const char * prvTCPFlagMeaning( UBaseType_t xFlags )
        {
            size_t uxFlags = ( size_t ) xFlags;

            ( void ) snprintf( retString,
                               sizeof( retString ), "%c%c%c%c%c%c%c%c",
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_FIN ) != 0 ) ? 'F' : '.',   /* 0x0001: No more data from sender */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_SYN ) != 0 ) ? 'S' : '.',   /* 0x0002: Synchronize sequence numbers */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_RST ) != 0 ) ? 'R' : '.',   /* 0x0004: Reset the connection */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_PSH ) != 0 ) ? 'P' : '.',   /* 0x0008: Push function: please push buffered data to the recv application */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_ACK ) != 0 ) ? 'A' : '.',   /* 0x0010: Acknowledgment field is significant */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_URG ) != 0 ) ? 'U' : '.',   /* 0x0020: Urgent pointer field is significant */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_ECN ) != 0 ) ? 'E' : '.',   /* 0x0040: ECN-Echo */
                               ( ( uxFlags & ( size_t ) tcpTCP_FLAG_CWR ) != 0 ) ? 'C' : '.' ); /* 0x0080: Congestion Window Reduced */
            return retString;
        }
        /*-----------------------------------------------------------*/

    #endif /* ipconfigHAS_DEBUG_PRINTF */

/**
 * @brief Set the MSS (Maximum segment size) associated with the given socket.
 *
 * @param[in] pxSocket: The socket whose MSS is to be set.
 */
    void prvSocketSetMSS( FreeRTOS_Socket_t * pxSocket )
    {
        uint32_t ulMSS;

        /* Do not allow MSS smaller than tcpMINIMUM_SEGMENT_LENGTH. */
        #if ( ipconfigTCP_MSS >= tcpMINIMUM_SEGMENT_LENGTH )
            {
                ulMSS = ipconfigTCP_MSS;
            }
        #else
            {
                ulMSS = tcpMINIMUM_SEGMENT_LENGTH;
            }
        #endif

        if( ( ( FreeRTOS_ntohl( pxSocket->u.xTCP.ulRemoteIP ) ^ *ipLOCAL_IP_ADDRESS_POINTER ) & xNetworkAddressing.ulNetMask ) != 0U )
        {
            /* Data for this peer will pass through a router, and maybe through
             * the internet.  Limit the MSS to 1400 bytes or less. */
            ulMSS = FreeRTOS_min_uint32( ( uint32_t ) tcpREDUCED_MSS_THROUGH_INTERNET, ulMSS );
        }

        FreeRTOS_debug_printf( ( "prvSocketSetMSS: %u bytes for %xip:%u\n", ( unsigned ) ulMSS, ( unsigned ) pxSocket->u.xTCP.ulRemoteIP, pxSocket->u.xTCP.usRemotePort ) );

        pxSocket->u.xTCP.usMSS = ( uint16_t ) ulMSS;
    }
    /*-----------------------------------------------------------*/

#endif /* ipconfigUSE_TCP == 1 */
