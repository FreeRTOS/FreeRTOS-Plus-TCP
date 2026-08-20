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

uint32_t ulBitConfig_read_32( BitConfig_t * pxConfig );

/****************************************************************
* Proof of ulBitConfig_read_32 memory safety.
*
* ulBitConfig_read_32 reads sizeof(uint32_t) bytes via xBitConfig_read_uc
* into a local stack buffer. We model any REACHABLE BitConfig_t:
*  - ucContents allocated to EXACTLY uxSize bytes (over-read => genuine).
*  - uxIndex nondeterministic but within the maintained invariant
*    0 <= uxIndex <= uxSize, so the read boundary is exercised.
*  - xHasError nondeterministic.
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

    ( void ) ulBitConfig_read_32( &xConfig );
}
