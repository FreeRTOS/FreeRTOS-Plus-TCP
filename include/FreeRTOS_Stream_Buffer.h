/*
 * FreeRTOS+TCP V2.4.0
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

/*
 *  FreeRTOS_Stream_Buffer.h
 *
 *  A circular character buffer
 *  An implementation of a circular buffer without a length field
 *  If LENGTH defines the size of the buffer, a maximum of (LENGTH-1) bytes can be stored
 *  In order to add or read data from the buffer, memcpy() will be called at most 2 times
 */

#ifndef FREERTOS_STREAM_BUFFER_H

    #define FREERTOS_STREAM_BUFFER_H

    #ifdef __cplusplus
        extern "C" {
    #endif

/**
 * structure to store all the details of a stream buffer.
 */
    typedef struct xSTREAM_BUFFER
    {
        volatile size_t uxTail;              /**< next item to read */
        volatile size_t uxMid;               /**< iterator within the valid items */
        volatile size_t uxHead;              /**< next position store a new item */
        volatile size_t uxFront;             /**< iterator within the free space */
        size_t LENGTH;                       /**< const value: number of reserved elements */
        uint8_t ucArray[ sizeof( size_t ) ]; /**< array big enough to store any pointer address */
    } StreamBuffer_t;

    void vStreamBufferClear( StreamBuffer_t * pxBuffer );
/*-----------------------------------------------------------*/

    size_t uxStreamBufferSpace( const StreamBuffer_t * pxBuffer,
                                const size_t uxLower,
                                const size_t uxUpper );
/*-----------------------------------------------------------*/

    size_t uxStreamBufferDistance( const StreamBuffer_t * pxBuffer,
                                   const size_t uxLower,
                                   const size_t uxUpper );
/*-----------------------------------------------------------*/

    size_t uxStreamBufferGetSpace( const StreamBuffer_t * pxBuffer );
/*-----------------------------------------------------------*/

    size_t uxStreamBufferFrontSpace( const StreamBuffer_t * pxBuffer );
/*-----------------------------------------------------------*/

    size_t uxStreamBufferGetSize( const StreamBuffer_t * pxBuffer );
/*-----------------------------------------------------------*/

    size_t uxStreamBufferMidSpace( const StreamBuffer_t * pxBuffer );
/*-----------------------------------------------------------*/

    void vStreamBufferMoveMid( StreamBuffer_t * pxBuffer,
                               size_t uxCount );
/*-----------------------------------------------------------*/

    BaseType_t xStreamBufferLessThenEqual( const StreamBuffer_t * pxBuffer,
                                           const size_t uxLeft,
                                           const size_t uxRight );
/*-----------------------------------------------------------*/

    size_t uxStreamBufferGetPtr( StreamBuffer_t * pxBuffer,
                                 uint8_t ** ppucData );

/*
 * Add bytes to a stream buffer.
 *
 * pxBuffer -   The buffer to which the bytes will be added.
 * uxOffset -   If uxOffset > 0, data will be written at an offset from uxHead
 *              while uxHead will not be moved yet.
 * pucData -    A pointer to the data to be added.
 * uxCount -    The number of bytes to add.
 */
    size_t uxStreamBufferAdd( StreamBuffer_t * pxBuffer,
                              size_t uxOffset,
                              const uint8_t * pucData,
                              size_t uxByteCount );

/*
 * Read bytes from a stream buffer.
 *
 * pxBuffer -   The buffer from which the bytes will be read.
 * uxOffset -   Can be used to read data located at a certain offset from 'uxTail'.
 * pucData -    A pointer to the buffer into which data will be read.
 * uxMaxCount - The number of bytes to read.
 * xPeek -      If set to pdTRUE the data will remain in the buffer.
 */
    size_t uxStreamBufferGet( StreamBuffer_t * pxBuffer,
                              size_t uxOffset,
                              uint8_t * pucData,
                              size_t uxMaxCount,
                              BaseType_t xPeek );

    #ifdef __cplusplus
        } /* extern "C" */
    #endif

#endif /* !defined( FREERTOS_STREAM_BUFFER_H ) */
