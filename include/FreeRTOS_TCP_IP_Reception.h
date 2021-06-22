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

#ifndef FREERTOS_TCP_IP_RECEPTION_H
    #define FREERTOS_TCP_IP_RECEPTION_H

/* Just make sure the contents doesn't get compiled if TCP is not enabled. */
    #if ipconfigUSE_TCP == 1

/*
 * Parse the TCP option(s) received, if present.
 */
        void prvCheckOptions( FreeRTOS_Socket_t * pxSocket,
                              const NetworkBufferDescriptor_t * pxNetworkBuffer );

/*
 * Identify and deal with a single TCP header option, advancing the pointer to
 * the header. This function returns pdTRUE or pdFALSE depending on whether the
 * caller should continue to parse more header options or break the loop.
 */
        size_t prvSingleStepTCPHeaderOptions( const uint8_t * const pucPtr,
                                              size_t uxTotalLength,
                                              FreeRTOS_Socket_t * const pxSocket,
                                              BaseType_t xHasSYNFlag );

/*
 * A "challenge ACK" is as per https://tools.ietf.org/html/rfc5961#section-3.2,
 * case #3. In summary, an RST was received with a sequence number that is
 * unexpected but still within the window.
 */
        BaseType_t prvTCPSendChallengeAck( NetworkBufferDescriptor_t * pxNetworkBuffer );

/*
 * Reply to a peer with the RST flag on, in case a packet can not be handled.
 */
        BaseType_t prvTCPSendReset( NetworkBufferDescriptor_t * pxNetworkBuffer );

/*
 * Return either a newly created socket, or the current socket in a connected
 * state (depends on the 'bReuseSocket' flag).
 */
        FreeRTOS_Socket_t * prvHandleListen( FreeRTOS_Socket_t * pxSocket,
                                             NetworkBufferDescriptor_t * pxNetworkBuffer );

/*
 * The heart of all: check incoming packet for valid data and acks and do what
 * is necessary in each state.
 */
        BaseType_t prvTCPHandleState( FreeRTOS_Socket_t * pxSocket,
                                      NetworkBufferDescriptor_t ** ppxNetworkBuffer );

/*
 * Try to send a series of messages.
 */
        int32_t prvTCPSendRepeated( FreeRTOS_Socket_t * pxSocket,
                                    NetworkBufferDescriptor_t ** ppxNetworkBuffer );

/*
 * Prepare an outgoing message, if anything has to be sent.
 */
        int32_t prvTCPPrepareSend( FreeRTOS_Socket_t * pxSocket,
                                   NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                                   UBaseType_t uxOptionsLength );

    #endif /* if ipconfigUSE_TCP == 1 */

#endif /* ifndef FREERTOS_TCP_IP_RECEPTION_H */
