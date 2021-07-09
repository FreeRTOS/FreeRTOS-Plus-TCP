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

#ifndef FREERTOS_TCP_IP_UTILS_H
    #define FREERTOS_TCP_IP_UTILS_H

/* Just make sure the contents doesn't get compiled if TCP is not enabled. */
    #if ipconfigUSE_TCP == 1

/*
 * Set the initial value for MSS (Maximum Segment Size) to be used.
 */
        void prvSocketSetMSS( FreeRTOS_Socket_t * pxSocket );

/*
 * Initialise the data structures which keep track of the TCP windowing system.
 */
        void prvTCPCreateWindow( FreeRTOS_Socket_t * pxSocket );

/*
 * The API FreeRTOS_send() adds data to the TX stream.  Add
 * this data to the windowing system to it can be transmitted.
 */
        void prvTCPAddTxData( FreeRTOS_Socket_t * pxSocket );

        NetworkBufferDescriptor_t * prvTCPBufferResize( const FreeRTOS_Socket_t * pxSocket,
                                                        NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                        int32_t lDataLen,
                                                        UBaseType_t uxOptionsLength );

/*
 * Internal: Sets a new state for a TCP socket and performs the necessary
 * actions like calling a OnConnected handler to notify the socket owner.
 */
        #if ( ipconfigUSE_TCP == 1 )
            void vTCPStateChange( FreeRTOS_Socket_t * pxSocket,
                                  enum eTCP_STATE eTCPState );
        #endif /* ipconfigUSE_TCP */

/*
 * Returns true if the socket must be checked.  Non-active sockets are waiting
 * for user action, either connect() or close().
 */
        BaseType_t prvTCPSocketIsActive( eIPTCPState_t xStatus );

/*
 * For anti-hang protection and TCP keep-alive messages.  Called in two places:
 * after receiving a packet and after a state change.  The socket's alive timer
 * may be reset.
 */
        void prvTCPTouchSocket( FreeRTOS_Socket_t * pxSocket );

        #if ( ipconfigUSE_TCP_WIN != 0 )
            uint8_t prvWinScaleFactor( const FreeRTOS_Socket_t * pxSocket );
        #endif

/*
 * Common code for sending a TCP protocol control packet (i.e. no options, no
 * payload, just flags).
 */
        BaseType_t prvTCPSendSpecialPacketHelper( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                  uint8_t ucTCPFlags );

/*
 * Return or send a packet to the other party.
 */
        void prvTCPReturnPacket( FreeRTOS_Socket_t * pxSocket,
                                 NetworkBufferDescriptor_t * pxDescriptor,
                                 uint32_t ulLen,
                                 BaseType_t xReleaseAfterSend );

/*
 * After a listening socket receives a new connection, it may duplicate itself.
 * The copying takes place in prvTCPSocketCopy.
 */
        BaseType_t prvTCPSocketCopy( FreeRTOS_Socket_t * pxNewSocket,
                                     FreeRTOS_Socket_t * pxSocket );

        #if ( ipconfigUSE_TCP_WIN == 1 )

/*
 * Skip past TCP header options when doing Selective ACK, until there are no
 * more options left.
 */
            void prvReadSackOption( const uint8_t * const pucPtr,
                                    size_t uxIndex,
                                    FreeRTOS_Socket_t * const pxSocket );
        #endif /* ( ipconfigUSE_TCP_WIN == 1 ) */

/*
 * Set the initial properties in the options fields, like the preferred
 * value of MSS and whether SACK allowed.  Will be transmitted in the state
 * 'eCONNECT_SYN'.
 */
        UBaseType_t prvSetSynAckOptions( FreeRTOS_Socket_t * pxSocket,
                                         TCPHeader_t * pxTCPHeader );
    #endif /* if ipconfigUSE_TCP == 1 */

#endif /* ifndef FREERTOS_TCP_IP_UTILS_H */
