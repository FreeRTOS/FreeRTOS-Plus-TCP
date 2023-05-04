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

typedef enum eTestStubsOperation
{
    eTestStubsOperationNone = 0,
    eTestStubsAllocateFail,
    eTestStubsHookFail,
    eTestStubsHookUseDefault,
} eTestStubsOperation_t;

/** @brief A list of all network end-points.  Each element has a next pointer. */
struct xNetworkEndPoint * pxNetworkEndPoints = NULL;

BaseType_t xARPHadIPClash = pdFALSE;

extern Socket_t xDHCPv6Socket;

eTestStubsOperation_t eTestStubsOperation = eTestStubsOperationNone;

void InitializeUnitTest()
{
    pxNetworkEndPoints = NULL;
    xDHCPv6Socket = NULL;
    eTestStubsOperation = eTestStubsOperationNone;
}

uint32_t ulApplicationTimeHook( void )
{
    /** @brief The function time() counts since 1-1-1970.  The DHCPv6 time-stamp however
     * uses a time stamp that had zero on 1-1-2000. */
    return 946684800U;
}

void vAddStubsOperation( eTestStubsOperation_t eOperation )
{
    eTestStubsOperation = eOperation;
}

eDHCPCallbackAnswer_t xApplicationDHCPHook_Multi( eDHCPCallbackPhase_t eDHCPPhase,
                                                  struct xNetworkEndPoint * pxEndPoint,
                                                  IP_Address_t * pxIPAddress )
{
    eDHCPCallbackAnswer_t eReturn = eDHCPContinue;

    if( eTestStubsOperation == eTestStubsHookFail )
    {
        eReturn = eDHCPStopNoChanges;
    }
    else if( eTestStubsOperation == eTestStubsHookUseDefault )
    {
        eReturn = eDHCPUseDefaults;
    }

    return eReturn;
}

void * pvPortMalloc( size_t xWantedSize )
{
    void * pvReturn = NULL;

    if( eTestStubsOperation != eTestStubsAllocateFail )
    {
        pvReturn = malloc( xWantedSize );
    }

    return pvReturn;
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
