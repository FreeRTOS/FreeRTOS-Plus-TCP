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

BaseType_t xBitConfig_read_uc( BitConfig_t * pxConfig,
                               uint8_t * pucData,
                               size_t uxSize );

/****************************************************************
* Proof of xBitConfig_read_uc memory safety.
*
* Minimal assumptions modelling any REACHABLE BitConfig_t:
*  - ucContents is allocated to EXACTLY uxSize bytes, so any read past
*    the end is a genuine over-read, not a harness artifact.
*  - uxIndex satisfies the invariant maintained by xBitConfig_init and
*    the read/write functions: 0 <= uxIndex <= uxSize. It is otherwise
*    nondeterministic so the read boundary (uxIndex + uxSize <= uxSize)
*    is fully exercised.
*  - xHasError is nondeterministic (both the error and non-error entry
*    states are explored).
*  - The read length and destination buffer are nondeterministic; the
*    destination is either NULL (skip path) or EXACTLY uxReadLen bytes.
****************************************************************/

void harness()
{
    BitConfig_t xConfig;
    size_t uxSize;

    __CPROVER_assume( uxSize <= 32 );

    xConfig.ucContents = ( uint8_t * ) malloc( uxSize );
    __CPROVER_assume( xConfig.ucContents != NULL );
    xConfig.uxSize = uxSize;
    xConfig.uxIndex = nondet_sizet();
    __CPROVER_assume( xConfig.uxIndex <= uxSize );
    xConfig.xHasError = nondet_basetype();

    size_t uxReadLen;
    __CPROVER_assume( uxReadLen <= 32 );

    /* Destination is either NULL (skip) or allocated to EXACTLY uxReadLen. */
    uint8_t * pucData = ( uint8_t * ) safeMalloc( uxReadLen );

    ( void ) xBitConfig_read_uc( &xConfig, pucData, uxReadLen );
}
