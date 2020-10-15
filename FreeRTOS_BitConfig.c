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

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_BitConfig.h"


BaseType_t xBitConfig_init( BitCOnfig_t *pxConfig, size_t uxSize, const uint8_t *pucData )
{
BaseType_t xResult = pdFALSE;

	( void ) memset( ( void * ) pxConfig, 0, sizeof( *pxConfig ) );
	pxConfig->ucContents = ( uint8_t * ) pvPortMalloc( uxSize );
	if( pxConfig->ucContents != NULL )
	{
		pxConfig->uxSize = uxSize;
		if( pucData != NULL )
		{
			( void ) memcpy( pxConfig->ucContents, pucData, uxSize );
		}
		else
		{
			( void ) memset( pxConfig->ucContents, 0, uxSize );
		}
		xResult = pdTRUE;
	}
	else
	{
		pxConfig->xHasError = pdTRUE;
	}

	return xResult;
}
/*-----------------------------------------------------------*/

BaseType_t xBitConfig_read_uc( BitCOnfig_t *pxConfig, uint8_t *pucData, size_t uxSize )
{
BaseType_t xResult = pdFALSE;
const size_t uxNeeded = uxSize;

	if( pxConfig->xHasError == pdFALSE )
	{
		if( pxConfig->uxIndex <= pxConfig->uxSize - uxNeeded )
		{
			if( pucData != NULL )
			{
				( void ) memcpy( pucData, &( pxConfig->ucContents[ pxConfig->uxIndex ] ), uxNeeded );
			}
			else
			{
				/* Caller just wants to skip some bytes. */
			}
			pxConfig->uxIndex += uxNeeded;
			xResult = pdTRUE;
		}
		else
		{
			pxConfig->xHasError = pdTRUE;
		}
	}
	return xResult;
}
/*-----------------------------------------------------------*/

uint8_t ucBitConfig_read_8( BitCOnfig_t *pxConfig )
{
uint8_t ucResult = 0xff;
const size_t uxNeeded = sizeof ucResult;
uint8_t pucData[ uxNeeded ];

	if( xBitConfig_read_uc( pxConfig, pucData, uxNeeded ) != pdFALSE )
	{
		ucResult = pucData[ 0 ];
	}

	return ucResult;
}
/*-----------------------------------------------------------*/

uint16_t usBitConfig_read_16( BitCOnfig_t *pxConfig )
{
uint16_t usResult = 0xffff;
const size_t uxNeeded = sizeof usResult;
uint8_t pucData[ uxNeeded ];

	if( xBitConfig_read_uc( pxConfig, pucData, uxNeeded ) != pdFALSE )
	{
		usResult = ( ( ( uint16_t ) pucData[ 0 ] ) <<  8 ) |
				   ( ( ( uint16_t ) pucData[ 1 ] )       );
	}

	return usResult;
}
/*-----------------------------------------------------------*/

uint32_t ulBitConfig_read_32( BitCOnfig_t *pxConfig )
{
uint32_t ulResult = 0xffffffff;
const size_t uxNeeded = sizeof ulResult;
uint8_t pucData[ uxNeeded ];

	if( xBitConfig_read_uc( pxConfig, pucData, uxNeeded ) != pdFALSE )
	{
		ulResult = ( ( ( uint32_t ) pucData[ 0 ] ) << 24 ) |
				   ( ( ( uint32_t ) pucData[ 1 ] ) << 16 ) |
				   ( ( ( uint32_t ) pucData[ 2 ] ) <<  8 ) |
				   ( ( ( uint32_t ) pucData[ 3 ] )       );
	}

	return ulResult;
}
/*-----------------------------------------------------------*/

BaseType_t xBitConfig_write_uc( BitCOnfig_t *pxConfig, uint8_t *pucData, size_t uxSize )
{
BaseType_t xResult = pdFALSE;
const size_t uxNeeded = uxSize;

	if( pxConfig->xHasError == pdFALSE )
	{
		if( pxConfig->uxIndex <= pxConfig->uxSize - uxNeeded )
		{
			( void ) memcpy( &( pxConfig->ucContents[ pxConfig->uxIndex ] ), pucData, uxNeeded );
			pxConfig->uxIndex += uxNeeded;
			xResult = pdTRUE;
		}
		else
		{
			pxConfig->xHasError = pdTRUE;
		}
	}
	return xResult;
}
/*-----------------------------------------------------------*/

BaseType_t xBitConfig_write_8( BitCOnfig_t *pxConfig, uint8_t ucValue )
{
BaseType_t xResult;
const size_t uxNeeded = sizeof ucValue;

	xResult = xBitConfig_write_uc( pxConfig, &( ucValue ), uxNeeded );

	return xResult;
}
/*-----------------------------------------------------------*/

BaseType_t xBitConfig_write_16( BitCOnfig_t *pxConfig, uint16_t usValue )
{
BaseType_t xResult;
const size_t uxNeeded = sizeof usValue;
uint8_t pucData[ uxNeeded ];

	pucData[ 0 ] = ( uint8_t ) ( ( usValue >>  8 ) & 0xFFU );
	pucData[ 1 ] = ( uint8_t ) ( usValue & 0xFFU );
	xResult = xBitConfig_write_uc( pxConfig, pucData, uxNeeded );

	return xResult;
}
/*-----------------------------------------------------------*/

BaseType_t xBitConfig_write_32( BitCOnfig_t *pxConfig, uint32_t ulValue )
{
BaseType_t xResult;
const size_t uxNeeded = sizeof ulValue;
uint8_t pucData[ uxNeeded ];

	pucData[ 0 ] = ( uint8_t ) ( ( ulValue >> 24 ) & 0xFFU );
	pucData[ 1 ] = ( uint8_t ) ( ( ulValue >> 16 ) & 0xFFU );
	pucData[ 2 ] = ( uint8_t ) ( ( ulValue >>  8 ) & 0xFFU );
	pucData[ 3 ] = ( uint8_t ) ( ulValue & 0xFFU );
	xResult = xBitConfig_write_uc( pxConfig, pucData, uxNeeded );

	return xResult;
}
/*-----------------------------------------------------------*/

void vBitConfig_release( BitCOnfig_t *pxConfig )
{
	if( pxConfig->ucContents != NULL )
	{
		vPortFree( pxConfig->ucContents );
	}
	memset( pxConfig, 0, sizeof *pxConfig );
}
/*-----------------------------------------------------------*/

//void vBitConfig_show( BitCOnfig_t *pxConfig )
//{
//	FreeRTOS_printf( ( "BitConfig: index %u size %u contents %s error %d\n",
//		( unsigned ) pxConfig->uxIndex,
//		( unsigned ) pxConfig->uxSize,
//		( pxConfig->ucContents != NULL ) ? "yes" : "no",
//		( int ) pxConfig->xHasError ) );
//}
///*-----------------------------------------------------------*/
