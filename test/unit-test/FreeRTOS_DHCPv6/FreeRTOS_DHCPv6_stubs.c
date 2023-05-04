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


/* Include Unity header */
#include <unity.h>

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Routing.h"

typedef enum eTestDHCPv6HookOperationType
{
    eTestDHCPv6HookOperationTypeNone = 0,
    eTestDHCPv6HookOperationTypeContinue,
} eTestDHCPv6HookOperationType_t;

/** @brief A list of all network end-points.  Each element has a next pointer. */
struct xNetworkEndPoint * pxNetworkEndPoints = NULL;

BaseType_t xARPHadIPClash = pdFALSE;

extern Socket_t xDHCPv6Socket;

eTestDHCPv6HookOperationType_t eTestDHCPv6HookOperationType = eTestDHCPv6HookOperationTypeContinue;

void InitializeUnitTest()
{
    pxNetworkEndPoints = NULL;
    xDHCPv6Socket = NULL;
    eTestDHCPv6HookOperationType = eTestDHCPv6HookOperationTypeContinue;
}

uint32_t ulApplicationTimeHook( void )
{
    /** @brief The function time() counts since 1-1-1970.  The DHCPv6 time-stamp however
     * uses a time stamp that had zero on 1-1-2000. */
    return 946684800U;
}

void vSetDHCPHookOperation( eTestDHCPv6HookOperationType_t eOperationType )
{
    eTestDHCPv6HookOperationType = eOperationType;
}

eDHCPCallbackAnswer_t xApplicationDHCPHook_Multi( eDHCPCallbackPhase_t eDHCPPhase,
                                                  struct xNetworkEndPoint * pxEndPoint,
                                                  IP_Address_t * pxIPAddress )
{
    eDHCPCallbackAnswer_t eReturn = eDHCPContinue;

    return eReturn;
}

void * pvPortMalloc( size_t xWantedSize )
{
    return malloc( xWantedSize );
}

void vPortFree( void * pv )
{
    free( pv );
}

void vPortEnterCritical( void )
{
}

void vPortExitCritical( void )
{
}
