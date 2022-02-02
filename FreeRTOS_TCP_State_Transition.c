/*
 * FreeRTOS+TCP V2.3.4
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file FreeRTOS_TCP_IP.c
 * @brief Module which handles the TCP connections for FreeRTOS+TCP.
 * It depends on  FreeRTOS_TCP_WIN.c, which handles the TCP windowing
 * schemes.
 *
 * Endianness: in this module all ports and IP addresses are stored in
 * host byte-order, except fields in the IP-packets
 */


/*
 * The heart of all: check incoming packet for valid data and acks and do what
 * is necessary in each state.
 */
    static BaseType_t prvTCPHandleState( FreeRTOS_Socket_t * pxSocket,
                                         NetworkBufferDescriptor_t ** ppxNetworkBuffer );


/*
 * For anti-hang protection and TCP keep-alive messages.  Called in two places:
 * after receiving a packet and after a state change.  The socket's alive timer
 * may be reset.
 */
    static void prvTCPTouchSocket( FreeRTOS_Socket_t * pxSocket );

/*
 * Returns true if the socket must be checked.  Non-active sockets are waiting
 * for user action, either connect() or close().
 */
    static BaseType_t prvTCPSocketIsActive( uint8_t ucStatus );

/*
 * prvTCPStatusAgeCheck() will see if the socket has been in a non-connected
 * state for too long.  If so, the socket will be closed, and -1 will be
 * returned.
 */
    #if ( ipconfigTCP_HANG_PROTECTION == 1 )
        static BaseType_t prvTCPStatusAgeCheck( FreeRTOS_Socket_t * pxSocket );
    #endif

/*
 *  Called to handle the closure of a TCP connection.
 */
    static BaseType_t prvTCPHandleFin( FreeRTOS_Socket_t * pxSocket,
                                       const NetworkBufferDescriptor_t * pxNetworkBuffer );

/*
 * Called from prvTCPHandleState() as long as the TCP status is eSYN_RECEIVED to
 * eCONNECT_SYN.
 */
    static BaseType_t prvHandleSynReceived( FreeRTOS_Socket_t * pxSocket,
                                            const NetworkBufferDescriptor_t * pxNetworkBuffer,
                                            uint32_t ulReceiveLength,
                                            UBaseType_t uxOptionsLength );

/*
 * Called from prvTCPHandleState() as long as the TCP status is eESTABLISHED.
 */
    static BaseType_t prvHandleEstablished( FreeRTOS_Socket_t * pxSocket,
                                            NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                                            uint32_t ulReceiveLength,
                                            UBaseType_t uxOptionsLength );

/*
 * Return either a newly created socket, or the current socket in a connected
 * state (depends on the 'bReuseSocket' flag).
 */
    static FreeRTOS_Socket_t * prvHandleListen( FreeRTOS_Socket_t * pxSocket,
                                                NetworkBufferDescriptor_t * pxNetworkBuffer );

/**
 * @brief Check whether the socket is active or not.
 *
 * @param[in] ucStatus: The status of the socket.
 *
 * @return pdTRUE if the socket must be checked. Non-active sockets
 *         are waiting for user action, either connect() or close().
 */
    static BaseType_t prvTCPSocketIsActive( uint8_t ucStatus )
    {
        BaseType_t xResult;
        eIPTCPState_t eStatus = ucStatus;

        switch( eStatus )
        {
            case eCLOSED:
            case eCLOSE_WAIT:
            case eFIN_WAIT_2:
            case eCLOSING:
            case eTIME_WAIT:
                xResult = pdFALSE;
                break;

            case eTCP_LISTEN:
            case eCONNECT_SYN:
            case eSYN_FIRST:
            case eSYN_RECEIVED:
            case eESTABLISHED:
            case eFIN_WAIT_1:
            case eLAST_ACK:
            default:
                xResult = pdTRUE;
                break;
        }

        return xResult;
    }
/*-----------------------------------------------------------*/



    #if ( ipconfigTCP_HANG_PROTECTION == 1 )

/**
 * @brief Some of the TCP states may only last a certain amount of time.
 *        This function checks if the socket is 'hanging', i.e. staying
 *        too long in the same state.
 *
 * @param[in] The socket to be checked.
 *
 * @return pdFALSE if no checks are needed, pdTRUE if checks were done, or negative
 *         in case the socket has reached a critical time-out. The socket will go to
 *         the eCLOSE_WAIT state.
 */
        static BaseType_t prvTCPStatusAgeCheck( FreeRTOS_Socket_t * pxSocket )
        {
            BaseType_t xResult;
            eIPTCPState_t eState = pxSocket->u.xTCP.ucTCPState;

            switch( eState )
            {
                case eESTABLISHED:

                    /* If the 'ipconfigTCP_KEEP_ALIVE' option is enabled, sockets in
                     *  state ESTABLISHED can be protected using keep-alive messages. */
                    xResult = pdFALSE;
                    break;

                case eCLOSED:
                case eTCP_LISTEN:
                case eCLOSE_WAIT:
                    /* These 3 states may last for ever, up to the owner. */
                    xResult = pdFALSE;
                    break;

                case eCONNECT_SYN:
                case eSYN_FIRST:
                case eSYN_RECEIVED:
                case eFIN_WAIT_1:
                case eFIN_WAIT_2:
                case eCLOSING:
                case eLAST_ACK:
                case eTIME_WAIT:
                default:

                    /* All other (non-connected) states will get anti-hanging
                     * protection. */
                    xResult = pdTRUE;
                    break;
            }

            if( xResult != pdFALSE )
            {
                /* How much time has past since the last active moment which is
                 * defined as A) a state change or B) a packet has arrived. */
                TickType_t xAge = xTaskGetTickCount() - pxSocket->u.xTCP.xLastActTime;

                /* ipconfigTCP_HANG_PROTECTION_TIME is in units of seconds. */
                if( xAge > ( ( TickType_t ) ipconfigTCP_HANG_PROTECTION_TIME * ( TickType_t ) configTICK_RATE_HZ ) )
                {
                    #if ( ipconfigHAS_DEBUG_PRINTF == 1 )
                        {
                            FreeRTOS_debug_printf( ( "Inactive socket closed: port %u rem %xip:%u status %s\n",
                                                     pxSocket->usLocalPort,
                                                     ( unsigned ) pxSocket->u.xTCP.ulRemoteIP,
                                                     pxSocket->u.xTCP.usRemotePort,
                                                     FreeRTOS_GetTCPStateName( ( UBaseType_t ) pxSocket->u.xTCP.ucTCPState ) ) );
                        }
                    #endif /* ipconfigHAS_DEBUG_PRINTF */

                    /* Move to eCLOSE_WAIT, user may close the socket. */
                    vTCPStateChange( pxSocket, eCLOSE_WAIT );

                    /* When 'bPassQueued' true, this socket is an orphan until it
                     * gets connected. */
                    if( pxSocket->u.xTCP.bits.bPassQueued != pdFALSE_UNSIGNED )
                    {
                        /* vTCPStateChange() has called vSocketCloseNextTime()
                         * in case the socket is not yet owned by the application.
                         * Return a negative value to inform the caller that
                         * the socket will be closed in the next cycle. */
                        xResult = -1;
                    }
                }
            }

            return xResult;
        }
        /*-----------------------------------------------------------*/

    #endif /* if ( ipconfigTCP_HANG_PROTECTION == 1 ) */
