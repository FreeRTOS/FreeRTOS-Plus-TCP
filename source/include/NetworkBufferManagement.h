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

#ifndef NETWORK_BUFFER_MANAGEMENT_H
#define NETWORK_BUFFER_MANAGEMENT_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

#include "FreeRTOS_IP.h"

/* NOTE PUBLIC API FUNCTIONS. */

BaseType_t xNetworkBuffersInitialise( void );
NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks );
void vReleaseNetworkBufferAndDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer );

#if ( ipconfigBUFFER_ALLOC_STATIC != 0 )

    NetworkBufferDescriptor_t * pxNetworkBufferGetFromISR( size_t xRequestedSizeBytes );

    BaseType_t vNetworkBufferReleaseFromISR( NetworkBufferDescriptor_t * const pxNetworkBuffer );

    void vNetworkBufferAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] );

    extern const UBaseType_t uxBufferAllocFixedSize;

#else

/* Increase the size of a Network Buffer. */
    NetworkBufferDescriptor_t * pxResizeNetworkBufferWithDescriptor( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                                     size_t xNewSizeBytes );
#endif /* ipconfigIS_ENABLED( ipconfigBUFFER_ALLOC_STATIC ) */

/* Get the current number of free network buffers. */
UBaseType_t uxGetNumberOfFreeNetworkBuffers( void );

/* Get the lowest number of free network buffers. */
UBaseType_t uxGetMinimumFreeNetworkBuffers( void );

/* Copy a network buffer into a bigger buffer. */
NetworkBufferDescriptor_t * pxDuplicateNetworkBufferWithDescriptor( const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                    size_t uxNewLength );

/* *INDENT-OFF* */
#ifdef __cplusplus
    } /* extern "C" */
#endif
/* *INDENT-ON* */


#endif /* NETWORK_BUFFER_MANAGEMENT_H */
