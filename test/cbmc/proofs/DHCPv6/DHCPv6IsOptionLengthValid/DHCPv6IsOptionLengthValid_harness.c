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

/* Target: file-local static in FreeRTOS_DHCPv6.c. Exposed via
 * --export-file-local-symbols. This function is pure arithmetic on
 * attacker-controlled length fields; it performs NO pointer dereference.
 * Minimal assumptions: all three inputs are fully non-deterministic. */
BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvIsOptionLengthValid( uint16_t usOption,
                                                                          size_t uxOptionLength,
                                                                          size_t uxRemainingSize );

void harness()
{
    uint16_t usOption;
    size_t uxOptionLength;
    size_t uxRemainingSize;

    ( void ) __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvIsOptionLengthValid( usOption,
                                                                            uxOptionLength,
                                                                            uxRemainingSize );
}
