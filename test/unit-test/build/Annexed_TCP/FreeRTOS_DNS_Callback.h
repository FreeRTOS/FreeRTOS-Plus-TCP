#ifndef FREERTOS_DNS_CALLBACK_H
#include "FreeRTOSIPConfig.h"
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
 * https://github.com/FreeRTOS
 * https://www.FreeRTOS.org
 */


#define FREERTOS_DNS_CALLBACK_H

/* *INDENT-OFF* */
/* *INDENT-ON* */

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"

#include "FreeRTOS_DNS_Globals.h"

/* Standard includes. */
#include <stdint.h>
/* Application level configuration options. */


    BaseType_t xDNSDoCallback( ParseSet_t * pxSet,
                               struct freertos_addrinfo * pxAddress );

    void vDNSSetCallBack( const char * pcHostName,
                          void * pvSearchID,
                          FOnDNSEvent pCallbackFunction,
                          TickType_t uxTimeout,
                          TickType_t uxIdentifier,
                          BaseType_t xIsIPv6 );

    void vDNSCheckCallBack( void * pvSearchID );

    void vDNSCallbackInitialise();


/* *INDENT-OFF* */
/* *INDENT-ON* */

#endif
