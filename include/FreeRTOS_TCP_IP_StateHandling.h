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

#ifndef FREERTOS_TCP_IP_STATEHANDLING_H
    #define FREERTOS_TCP_IP_STATEHANDLING_H

/* Just make sure the contents doesn't get compiled if TCP is not enabled. */
    #if ipconfigUSE_TCP == 1

/*
 * Called from prvTCPHandleState().  Find the TCP payload data and check and
 * return its length.
 */
        BaseType_t prvCheckRxData( const NetworkBufferDescriptor_t * pxNetworkBuffer,
                                   uint8_t ** ppucRecvData );

/*
 * Called from prvTCPHandleState() as long as the TCP status is eESTABLISHED.
 */
        BaseType_t prvHandleEstablished( FreeRTOS_Socket_t * pxSocket,
                                         NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                                         uint32_t ulReceiveLength,
                                         UBaseType_t uxOptionsLength );

/*
 *  Called to handle the closure of a TCP connection.
 */
        BaseType_t prvTCPHandleFin( FreeRTOS_Socket_t * pxSocket,
                                    const NetworkBufferDescriptor_t * pxNetworkBuffer );

/*
 * Called from prvTCPHandleState() as long as the TCP status is eSYN_RECEIVED to
 * eCONNECT_SYN.
 */
        BaseType_t prvHandleSynReceived( FreeRTOS_Socket_t * pxSocket,
                                         const NetworkBufferDescriptor_t * pxNetworkBuffer,
                                         uint32_t ulReceiveLength,
                                         UBaseType_t uxOptionsLength );

/*
 * Set the TCP options (if any) for the outgoing packet.
 */
        UBaseType_t prvSetOptions( FreeRTOS_Socket_t * pxSocket,
                                   const NetworkBufferDescriptor_t * pxNetworkBuffer );

/*
 * Called from prvTCPHandleState().  There is data to be sent.
 * If ipconfigUSE_TCP_WIN is defined, and if only an ACK must be sent, it will
 * be checked if it would better be postponed for efficiency.
 */
        BaseType_t prvSendData( FreeRTOS_Socket_t * pxSocket,
                                NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                                uint32_t ulReceiveLength,
                                BaseType_t xByteCount );


/*
 * Called from prvTCPHandleState().  Check if the payload data may be accepted.
 * If so, it will be added to the socket's reception queue.
 */
        BaseType_t prvStoreRxData( FreeRTOS_Socket_t * pxSocket,
                                   const uint8_t * pucRecvData,
                                   NetworkBufferDescriptor_t * pxNetworkBuffer,
                                   uint32_t ulReceiveLength );

    #endif /* if ipconfigUSE_TCP == 1 */

#endif /* ifndef FREERTOS_TCP_IP_STATE_HANDLING_H */
