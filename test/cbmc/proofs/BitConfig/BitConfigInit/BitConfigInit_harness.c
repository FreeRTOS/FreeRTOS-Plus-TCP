/*
 * FreeRTOS memory safety proofs with CBMC.
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* Standard includes. */
#include <stdint.h>

/* cbmc.h pulls in FreeRTOS.h and the +TCP headers that define the base
 * types (BaseType_t, size_t, ...) that FreeRTOS_BitConfig.h relies on, so
 * it MUST be included first. */
#include "cbmc.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_BitConfig.h"

/****************************************************************
* Signature of function under test
****************************************************************/

BaseType_t xBitConfig_init( BitConfig_t * pxConfig,
                            const uint8_t * pucData,
                            size_t uxSize );

/****************************************************************
* Proof of xBitConfig_init memory safety.
*
* Minimal assumptions:
*  - pxConfig points to a valid (stack) BitConfig_t; the function
*    memset()s it fully before use.
*  - uxSize is nondeterministic, bounded only to keep the CBMC object
*    model finite.
*  - pucData is EITHER NULL (memset path) OR a buffer of EXACTLY uxSize
*    bytes (memcpy path). safeMalloc returns NULL or malloc(uxSize), so
*    both branches are explored and any over-read of pucData is genuine.
****************************************************************/

void harness()
{
    BitConfig_t xConfig;
    size_t uxSize;

    __CPROVER_assume( uxSize <= 32 );

    /* Source buffer is either NULL or allocated to EXACTLY uxSize bytes. */
    const uint8_t * pucData = ( const uint8_t * ) safeMalloc( uxSize );

    ( void ) xBitConfig_init( &xConfig, pucData, uxSize );
}
