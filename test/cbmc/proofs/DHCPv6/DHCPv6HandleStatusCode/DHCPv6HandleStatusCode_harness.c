/*
 * FreeRTOS memory safety proofs with CBMC.
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 * http://www.FreeRTOS.org
 */

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "FreeRTOS_DHCPv6.h"
#include "FreeRTOS_BitConfig.h"

/* CBMC includes. */
#include "cbmc.h"

/* Bound the modeled receive buffer to keep the state space finite.
 * The real DHCPv6 payload is MTU-bounded; 100 matches DHCPv6Analyse. */
#define DHCPv6_PAYLOAD_LENGTH_MAX    ( 100 )

/* Target: file-local static in FreeRTOS_DHCPv6.c, reached via
 * --export-file-local-symbols. Reads a 16-bit status from the wire, then
 * copies up to sizeof(ucMessage)-1 bytes into a local ucMessage[50]. The
 * real BitConfig reader (bounds-checked) is linked, NOT stubbed. */
BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvDHCPv6_handleStatusCode( size_t uxLength,
                                                                              BitConfig_t * pxMessage );

void harness()
{
    BitConfig_t * pxMessage = safeMalloc( sizeof( BitConfig_t ) );
    size_t uxSize;
    size_t uxLength;

    __CPROVER_assume( pxMessage != NULL );

    /* Model the bit-stream: buffer allocated to EXACTLY uxSize so any
     * over-read is a genuine out-of-bounds access. Contents are the nondet
     * bytes returned by malloc (attacker-controlled). */
    __CPROVER_assume( ( uxSize > 0U ) && ( uxSize <= DHCPv6_PAYLOAD_LENGTH_MAX ) );
    pxMessage->ucContents = safeMalloc( uxSize );
    __CPROVER_assume( pxMessage->ucContents != NULL );
    pxMessage->uxSize = uxSize;

    /* The read cursor may sit anywhere within the buffer (mid-parse). */
    __CPROVER_assume( pxMessage->uxIndex <= uxSize );

    /* Parsing only continues while no prior read error occurred. */
    pxMessage->xHasError = pdFALSE;

    /* uxLength is the attacker-supplied option length. Leave it FULLY
     * non-deterministic (including < 2, which underflows uxLength - 2U in
     * the source) so the clamp arithmetic is exercised. */
    ( void ) __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvDHCPv6_handleStatusCode( uxLength, pxMessage );
}
