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

/* Bound the modeled receive buffer to keep the state space finite. */
#define DHCPv6_PAYLOAD_LENGTH_MAX    ( 100 )

/* Bound the attacker-supplied option length. The sub-option scan loop
 * consumes at least 4 bytes (option code + length) per iteration, so the
 * loop runs at most OPTION_LENGTH_MAX/4 times. Must be covered by the
 * --unwindset in Makefile.json for soundness. */
#define OPTION_LENGTH_MAX            ( 32 )

/* Target: file-local static in FreeRTOS_DHCPv6.c, reached via
 * --export-file-local-symbols. Real BitConfig readers are linked (not
 * stubbed) so the length-validation arithmetic runs against real memory. */
BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvDHCPv6_subOption( uint16_t usOption,
                                                                       const DHCPOptionSet_t * pxSet,
                                                                       DHCPMessage_IPv6_t * pxDHCPMessage,
                                                                       BitConfig_t * pxMessage );

void harness()
{
    uint16_t usOption;
    DHCPMessage_IPv6_t * pxDHCPMessage = safeMalloc( sizeof( DHCPMessage_IPv6_t ) );
    DHCPOptionSet_t * pxSet = safeMalloc( sizeof( DHCPOptionSet_t ) );
    BitConfig_t * pxMessage = safeMalloc( sizeof( BitConfig_t ) );
    size_t uxSize;

    __CPROVER_assume( pxDHCPMessage != NULL );
    __CPROVER_assume( pxSet != NULL );
    __CPROVER_assume( pxMessage != NULL );

    /* Model the bit-stream: buffer allocated to EXACTLY uxSize so any
    * over-read is a genuine out-of-bounds access. Contents nondet. */
    __CPROVER_assume( ( uxSize > 0U ) && ( uxSize <= DHCPv6_PAYLOAD_LENGTH_MAX ) );
    pxMessage->ucContents = safeMalloc( uxSize );
    __CPROVER_assume( pxMessage->ucContents != NULL );
    pxMessage->uxSize = uxSize;
    __CPROVER_assume( pxMessage->uxIndex <= uxSize );
    pxMessage->xHasError = pdFALSE;

    /* pxSet describes the current option. uxStart is left non-deterministic
     * (the source tolerates uxIndex < uxStart via the >= guard). Only
     * uxOptionLength is bounded, purely to keep the scan loop finite. */
    __CPROVER_assume( pxSet->uxOptionLength <= OPTION_LENGTH_MAX );

    /* Match the caller's option-code range so the switch default is reached. */
    __CPROVER_assume( ( usOption >= DHCPv6_Option_Client_Identifier ) &&
                      ( usOption <= DHCPv6_Option_IA_Prefix ) );

    ( void ) __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvDHCPv6_subOption( usOption,
                                                                         pxSet,
                                                                         pxDHCPMessage,
                                                                         pxMessage );
}
