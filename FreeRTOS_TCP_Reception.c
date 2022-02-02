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
 * Parse the TCP option(s) received, if present.
 */
    static BaseType_t prvCheckOptions( FreeRTOS_Socket_t * pxSocket,
                                       const NetworkBufferDescriptor_t * pxNetworkBuffer );

/*
 * Identify and deal with a single TCP header option, advancing the pointer to
 * the header. This function returns pdTRUE or pdFALSE depending on whether the
 * caller should continue to parse more header options or break the loop.
 */
    static int32_t prvSingleStepTCPHeaderOptions( const uint8_t * const pucPtr,
                                                  size_t uxTotalLength,
                                                  FreeRTOS_Socket_t * const pxSocket,
                                                  BaseType_t xHasSYNFlag );

    #if ( ipconfigUSE_TCP_WIN == 1 )

/*
 * Skip past TCP header options when doing Selective ACK, until there are no
 * more options left.
 */
        _static void prvReadSackOption( const uint8_t * const pucPtr,
                                        size_t uxIndex,
                                        FreeRTOS_Socket_t * const pxSocket );
    #endif /* ( ipconfigUSE_TCP_WIN == 1 ) */


/*
 * Called from prvTCPHandleState().  Find the TCP payload data and check and
 * return its length.
 */
    static BaseType_t prvCheckRxData( const NetworkBufferDescriptor_t * pxNetworkBuffer,
                                      uint8_t ** ppucRecvData );

/*
 * Called from prvTCPHandleState().  Check if the payload data may be accepted.
 * If so, it will be added to the socket's reception queue.
 */
    static BaseType_t prvStoreRxData( FreeRTOS_Socket_t * pxSocket,
                                      const uint8_t * pucRecvData,
                                      NetworkBufferDescriptor_t * pxNetworkBuffer,
                                      uint32_t ulReceiveLength );



/**
 * @brief Parse the TCP option(s) received, if present.
 *
 * @param[in] pxSocket: The socket handling the connection.
 * @param[in] pxNetworkBuffer: The network buffer containing the TCP
 *                             packet.
 *
 * @return: If the options are well formed and processed successfully
 *          then pdPASS is returned; else a pdFAIL is returned.
 *
 * @note It has already been verified that:
 *       ((pxTCPHeader->ucTCPOffset & 0xf0) > 0x50), meaning that
 *       the TP header is longer than the usual 20 (5 x 4) bytes.
 */
    static BaseType_t prvCheckOptions( FreeRTOS_Socket_t * pxSocket,
                                       const NetworkBufferDescriptor_t * pxNetworkBuffer )
    {
        size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + xIPHeaderSize( pxNetworkBuffer );
        const ProtocolHeaders_t * pxProtocolHeaders = ipCAST_PTR_TO_TYPE_PTR( ProtocolHeaders_t,
                                                                              &( pxNetworkBuffer->pucEthernetBuffer[ uxTCPHeaderOffset ] ) );
        const TCPHeader_t * pxTCPHeader;
        const uint8_t * pucPtr;
        BaseType_t xHasSYNFlag;
        BaseType_t xReturn = pdPASS;
        /* Offset in the network packet where the first option byte is stored. */
        size_t uxOptionOffset = uxTCPHeaderOffset + ( sizeof( TCPHeader_t ) - sizeof( pxTCPHeader->ucOptdata ) );
        size_t uxOptionsLength;
        int32_t lResult;
        uint8_t ucLength;

        pxTCPHeader = &( pxProtocolHeaders->xTCPHeader );


        /* A character pointer to iterate through the option data */
        pucPtr = pxTCPHeader->ucOptdata;

        if( pxTCPHeader->ucTCPOffset <= ( 5U << 4U ) )
        {
            /* Avoid integer underflow in computation of ucLength. */
        }
        else
        {
            ucLength = ( ( ( pxTCPHeader->ucTCPOffset >> 4U ) - 5U ) << 2U );
            uxOptionsLength = ( size_t ) ucLength;

            if( pxNetworkBuffer->xDataLength > uxOptionOffset )
            {
                /* Validate options size calculation. */
                if( ( pxNetworkBuffer->xDataLength > uxOptionOffset ) &&
                    ( uxOptionsLength <= ( pxNetworkBuffer->xDataLength - uxOptionOffset ) ) )
                {
                    if( ( pxTCPHeader->ucTCPFlags & tcpTCP_FLAG_SYN ) != ( uint8_t ) 0U )
                    {
                        xHasSYNFlag = pdTRUE;
                    }
                    else
                    {
                        xHasSYNFlag = pdFALSE;
                    }

                    /* The length check is only necessary in case the option data are
                     *  corrupted, we don't like to run into invalid memory and crash. */
                    for( ; ; )
                    {
                        if( uxOptionsLength == 0U )
                        {
                            /* coverity[break_stmt] : Break statement terminating the loop */
                            break;
                        }

                        lResult = prvSingleStepTCPHeaderOptions( pucPtr, uxOptionsLength, pxSocket, xHasSYNFlag );

                        if( lResult < 0 )
                        {
                            xReturn = pdFAIL;
                            break;
                        }

                        if( lResult == 0 )
                        {
                            break;
                        }

                        uxOptionsLength -= ( size_t ) lResult;
                        pucPtr = &( pucPtr[ lResult ] );
                    }
                }
            }
        }

        return xReturn;
    }
    /*-----------------------------------------------------------*/

/**
 * @brief Identify and deal with a single TCP header option, advancing the pointer to
 *        the header.
 *
 * @param[in] pucPtr: Pointer to the TCP packet options.
 * @param[in] uxTotalLength: Length of the TCP packet options.
 * @param[in] pxSocket: Socket handling the connection.
 * @param[in] xHasSYNFlag: Whether the header has SYN flag or not.
 *
 * @return This function returns index of the next option if the current option is
 *         successfully processed and it is not the end of options whereafter the caller
 *         should continue to process more options.
 *         If the options have ended, this function will return a zero whereafter the
 *         caller should stop parsing options and continue further processing.
 *         If the current option has erroneous value, then the function returns a
 *         negative value wherein the calling function should not process this packet any
 *         further and drop it.
 */
    static int32_t prvSingleStepTCPHeaderOptions( const uint8_t * const pucPtr,
                                                  size_t uxTotalLength,
                                                  FreeRTOS_Socket_t * const pxSocket,
                                                  BaseType_t xHasSYNFlag )
    {
        UBaseType_t uxNewMSS;
        size_t uxRemainingOptionsBytes = uxTotalLength;
        uint8_t ucLen;
        int32_t lIndex;
        TCPWindow_t * pxTCPWindow = &( pxSocket->u.xTCP.xTCPWindow );
        BaseType_t xReturn = pdFALSE;

        if( pucPtr[ 0U ] == tcpTCP_OPT_END )
        {
            /* End of options. */
            lIndex = 0;
        }
        else if( pucPtr[ 0U ] == tcpTCP_OPT_NOOP )
        {
            /* NOP option, inserted to make the length a multiple of 4. */
            lIndex = 1;
        }
        else if( uxRemainingOptionsBytes < 2U )
        {
            /* Any other well-formed option must be at least two bytes: the option
             * type byte followed by a length byte. */
            lIndex = -1;
        }

        #if ( ipconfigUSE_TCP_WIN != 0 )
            else if( pucPtr[ 0 ] == tcpTCP_OPT_WSOPT )
            {
                /* The TCP Window Scale Option. */
                /* Confirm that the option fits in the remaining buffer space. */
                if( ( uxRemainingOptionsBytes < tcpTCP_OPT_WSOPT_LEN ) || ( pucPtr[ 1 ] != tcpTCP_OPT_WSOPT_LEN ) )
                {
                    lIndex = -1;
                }
                else
                {
                    /* Option is only valid in SYN phase. */
                    if( xHasSYNFlag != 0 )
                    {
                        pxSocket->u.xTCP.ucPeerWinScaleFactor = pucPtr[ 2 ];
                        pxSocket->u.xTCP.bits.bWinScaling = pdTRUE_UNSIGNED;
                    }

                    lIndex = ( int32_t ) tcpTCP_OPT_WSOPT_LEN;
                }
            }
        #endif /* ipconfigUSE_TCP_WIN */
        else if( pucPtr[ 0 ] == tcpTCP_OPT_MSS )
        {
            /* Confirm that the option fits in the remaining buffer space. */
            if( ( uxRemainingOptionsBytes < tcpTCP_OPT_MSS_LEN ) || ( pucPtr[ 1 ] != tcpTCP_OPT_MSS_LEN ) )
            {
                lIndex = -1;
            }
            else
            {
                /* An MSS option with the correct option length.  FreeRTOS_htons()
                 * is not needed here because usChar2u16() already returns a host
                 * endian number. */
                uxNewMSS = usChar2u16( &( pucPtr[ 2 ] ) );

                if( pxSocket->u.xTCP.usMSS != uxNewMSS )
                {
                    /* Perform a basic check on the the new MSS. */
                    if( uxNewMSS == 0U )
                    {
                        lIndex = -1;

                        /* Return Condition found. */
                        xReturn = pdTRUE;
                    }
                    else
                    {
                        FreeRTOS_debug_printf( ( "MSS change %u -> %u\n", pxSocket->u.xTCP.usMSS, ( unsigned ) uxNewMSS ) );
                    }
                }

                /* If a 'return' condition has not been found. */
                if( xReturn == pdFALSE )
                {
                    /* Restrict the minimum value of segment length to the ( Minimum IP MTU (576) - IP header(20) - TCP Header(20) ).
                     * See "RFC 791 section 3.1 Total Length" for more details. */
                    if( uxNewMSS < tcpMINIMUM_SEGMENT_LENGTH )
                    {
                        uxNewMSS = tcpMINIMUM_SEGMENT_LENGTH;
                    }

                    if( pxSocket->u.xTCP.usMSS > uxNewMSS )
                    {
                        /* our MSS was bigger than the MSS of the other party: adapt it. */
                        pxSocket->u.xTCP.bits.bMssChange = pdTRUE_UNSIGNED;

                        if( pxSocket->u.xTCP.usMSS > uxNewMSS )
                        {
                            /* The peer advertises a smaller MSS than this socket was
                             * using.  Use that as well. */
                            FreeRTOS_debug_printf( ( "Change mss %d => %u\n", pxSocket->u.xTCP.usMSS, ( unsigned ) uxNewMSS ) );
                            pxSocket->u.xTCP.usMSS = ( uint16_t ) uxNewMSS;
                        }

                        pxTCPWindow->xSize.ulRxWindowLength = ( ( uint32_t ) uxNewMSS ) * ( pxTCPWindow->xSize.ulRxWindowLength / ( ( uint32_t ) uxNewMSS ) );
                        pxTCPWindow->usMSSInit = ( uint16_t ) uxNewMSS;
                        pxTCPWindow->usMSS = ( uint16_t ) uxNewMSS;
                        pxSocket->u.xTCP.usMSS = ( uint16_t ) uxNewMSS;
                    }

                    lIndex = ( int32_t ) tcpTCP_OPT_MSS_LEN;
                }
            }
        }
        else
        {
            /* All other options have a length field, so that we easily
             * can skip past them. */
            ucLen = pucPtr[ 1 ];
            lIndex = 0;

            if( ( ucLen < ( uint8_t ) 2U ) || ( uxRemainingOptionsBytes < ( size_t ) ucLen ) )
            {
                /* If the length field is too small or too big, the options are
                 * malformed, don't process them further.
                 */
                lIndex = -1;
            }
            else
            {
                #if ( ipconfigUSE_TCP_WIN == 1 )
                    {
                        /* Selective ACK: the peer has received a packet but it is missing
                         * earlier packets. At least this packet does not need retransmission
                         * anymore. ulTCPWindowTxSack( ) takes care of this administration.
                         */
                        if( pucPtr[ 0U ] == tcpTCP_OPT_SACK_A )
                        {
                            ucLen -= 2U;
                            lIndex += 2;

                            while( ucLen >= ( uint8_t ) 8U )
                            {
                                prvReadSackOption( pucPtr, ( size_t ) lIndex, pxSocket );
                                lIndex += 8;
                                ucLen -= 8U;
                            }

                            /* ucLen should be 0 by now. */
                        }
                    }
                #endif /* ipconfigUSE_TCP_WIN == 1 */

                lIndex += ( int32_t ) ucLen;
            }
        }

        #if ( ipconfigUSE_TCP_WIN == 0 )
            /* Avoid compiler warnings when TCP window is not used. */
            ( void ) xHasSYNFlag;
        #endif

        return lIndex;
    }
    /*-----------------------------------------------------------*/

    #if ( ipconfigUSE_TCP_WIN == 1 )

/**
 * @brief Skip past TCP header options when doing Selective ACK, until there are no
 *        more options left.
 *
 * @param[in] pucPtr: Pointer to the TCP packet options.
 * @param[in] uxIndex: Index of options in the TCP packet options.
 * @param[in] pxSocket: Socket handling the TCP connection.
 */
        _static void prvReadSackOption( const uint8_t * const pucPtr,
                                        size_t uxIndex,
                                        FreeRTOS_Socket_t * const pxSocket )
        {
            uint32_t ulFirst = ulChar2u32( &( pucPtr[ uxIndex ] ) );
            uint32_t ulLast = ulChar2u32( &( pucPtr[ uxIndex + 4U ] ) );
            uint32_t ulCount = ulTCPWindowTxSack( &( pxSocket->u.xTCP.xTCPWindow ), ulFirst, ulLast );

            /* ulTCPWindowTxSack( ) returns the number of bytes which have been acked
             * starting from the head position.  Advance the tail pointer in txStream.
             */
            if( ( pxSocket->u.xTCP.txStream != NULL ) && ( ulCount > 0U ) )
            {
                /* Just advancing the tail index, 'ulCount' bytes have been confirmed. */
                ( void ) uxStreamBufferGet( pxSocket->u.xTCP.txStream, 0, NULL, ( size_t ) ulCount, pdFALSE );
                pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_SEND;

                #if ipconfigSUPPORT_SELECT_FUNCTION == 1
                    {
                        if( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_WRITE ) != 0U )
                        {
                            /* The field 'xEventBits' is used to store regular socket events
                             * (at most 8), as well as 'select events', which will be left-shifted.
                             */
                            pxSocket->xEventBits |= ( ( EventBits_t ) eSELECT_WRITE ) << SOCKET_EVENT_BIT_COUNT;
                        }
                    }
                #endif

                /* In case the socket owner has installed an OnSent handler,
                 * call it now. */
                #if ( ipconfigUSE_CALLBACKS == 1 )
                    {
                        if( ipconfigIS_VALID_PROG_ADDRESS( pxSocket->u.xTCP.pxHandleSent ) )
                        {
                            pxSocket->u.xTCP.pxHandleSent( pxSocket, ulCount );
                        }
                    }
                #endif /* ipconfigUSE_CALLBACKS == 1  */
            }
        }

    #endif /* ( ipconfigUSE_TCP_WIN != 0 ) */
    /*-----------------------------------------------------------*/

