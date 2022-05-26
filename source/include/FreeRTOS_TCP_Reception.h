/*
 * FreeRTOS+TCP V2.3.4
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifndef FREERTOS_TCP_RECEPTION_H
    #define FREERTOS_TCP_RECEPTION_H

    #ifdef __cplusplus
        extern "C" {
    #endif

/*
 * Identify and deal with a single TCP header option, advancing the pointer to
 * the header. This function returns pdTRUE or pdFALSE depending on whether the
 * caller should continue to parse more header options or break the loop.
 */
    int32_t prvSingleStepTCPHeaderOptions( const uint8_t * const pucPtr,
                                           size_t uxTotalLength,
                                           FreeRTOS_Socket_t * const pxSocket,
                                           BaseType_t xHasSYNFlag );

/*
 * Skip past TCP header options when doing Selective ACK, until there are no
 * more options left.
 */
    #if ( ipconfigUSE_TCP_WIN == 1 )
        void prvReadSackOption( const uint8_t * const pucPtr,
                                size_t uxIndex,
                                FreeRTOS_Socket_t * const pxSocket );
    #endif /* ( ipconfigUSE_TCP_WIN == 1 ) */

/*
 * Called from prvTCPHandleState().  Find the TCP payload data and check and
 * return its length.
 */
    BaseType_t prvCheckRxData( const NetworkBufferDescriptor_t * pxNetworkBuffer,
                               uint8_t ** ppucRecvData );

/*
 * Called from prvTCPHandleState().  Check if the payload data may be accepted.
 * If so, it will be added to the socket's reception queue.
 */
    BaseType_t prvStoreRxData( FreeRTOS_Socket_t * pxSocket,
                               const uint8_t * pucRecvData,
                               NetworkBufferDescriptor_t * pxNetworkBuffer,
                               uint32_t ulReceiveLength );

    #ifdef __cplusplus
        } /* extern "C" */
    #endif

#endif /* FREERTOS_TCP_RECEPTION_H */
