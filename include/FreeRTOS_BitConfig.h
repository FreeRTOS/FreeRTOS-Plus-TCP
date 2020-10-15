/*
 * FreeRTOS+TCP V2.3.0
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

/*
 *	FreeRTOS_Stream_Buffer.h
 *
 *	A cicular character buffer
 *	An implementation of a circular buffer without a length field
 *	If LENGTH defines the size of the buffer, a maximum of (LENGT-1) bytes can be stored
 *	In order to add or read data from the buffer, memcpy() will be called at most 2 times
 */

#ifndef FREERTOS_BITCONFIG_H
#define	FREERTOS_BITCONFIG_H

#ifdef __cplusplus
extern "C" {
#endif

typedef struct xBitCOnfig
{
	uint8_t *ucContents;
	size_t uxIndex;
	size_t uxSize;
	BaseType_t xHasError;
} BitCOnfig_t;

BaseType_t xBitConfig_init( BitCOnfig_t *pxConfig, size_t uxSize, const uint8_t *pucData );

uint8_t ucBitConfig_read_8( BitCOnfig_t *pxConfig );
uint16_t usBitConfig_read_16( BitCOnfig_t *pxConfig );
uint32_t ulBitConfig_read_32( BitCOnfig_t *pxConfig );
BaseType_t xBitConfig_read_uc( BitCOnfig_t *pxConfig, uint8_t *pucData, size_t uxSize );

BaseType_t xBitConfig_write_8( BitCOnfig_t *pxConfig, uint8_t ucValue );
BaseType_t xBitConfig_write_16( BitCOnfig_t *pxConfig, uint16_t usValue );
BaseType_t xBitConfig_write_32( BitCOnfig_t *pxConfig, uint32_t ulValue );
BaseType_t xBitConfig_write_uc( BitCOnfig_t *pxConfig, uint8_t *pucData, size_t uxSize );

void vBitConfig_release( BitCOnfig_t *pxConfig );
void vBitConfig_show( BitCOnfig_t *pxConfig );


#ifdef __cplusplus
} /* extern "C" */
#endif

#endif	/* !defined( FREERTOS_STREAM_BUFFER_H ) */
