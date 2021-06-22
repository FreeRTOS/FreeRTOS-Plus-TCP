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

 /* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"

#ifndef FREERTOS_TCP_IP_TIMERWORK_H
    #define FREERTOS_TCP_IP_TIMERWORK_H

    /* Just make sure the contents doesn't get compiled if TCP is not enabled. */
    #if ipconfigUSE_TCP == 1
    /*
     * Calculate when this socket needs to be checked to do (re-)transmissions.
     */
        TickType_t prvTCPNextTimeout( FreeRTOS_Socket_t * pxSocket );

    /*
     * prvTCPStatusAgeCheck() will see if the socket has been in a non-connected
     * state for too long.  If so, the socket will be closed, and -1 will be
     * returned.
     */
        #if ( ipconfigTCP_HANG_PROTECTION == 1 )
            BaseType_t prvTCPStatusAgeCheck( FreeRTOS_Socket_t * pxSocket );
        #endif

    /*
     * Either sends a SYN or calls prvTCPSendRepeated (for regular messages).
     */
         int32_t prvTCPSendPacket( FreeRTOS_Socket_t * pxSocket );


    /*
     * Let ARP look-up the MAC-address of the peer and initialise the first SYN
     * packet.
     */
        BaseType_t prvTCPPrepareConnect( FreeRTOS_Socket_t * pxSocket );
    #endif

#endif
