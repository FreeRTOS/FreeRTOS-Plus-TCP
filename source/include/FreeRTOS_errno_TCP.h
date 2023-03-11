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

#ifndef FREERTOS_ERRNO_TCP
#define FREERTOS_ERRNO_TCP

/* The following definitions will be included in the core FreeRTOS code in
 * future versions of FreeRTOS - hence the 'pd' (ProjDefs) prefix - at which time
 * this file will be removed. */

/* The following errno values are used by FreeRTOS+ components, not FreeRTOS
 * itself. */

/* For future compatibility (see comment above), check the definitions have not
 * already been made. */
#ifndef pdFREERTOS_ERRNO_EAFNOSUPPORT
    #define pdFREERTOS_ERRNO_EAFNOSUPPORT    97 /* Address family not supported by protocol */
#endif /* pdFREERTOS_ERRNO_EAFNOSUPPORT */

/* Translate a pdFREERTOS_ERRNO code to a human readable string. */
const char * FreeRTOS_strerror_r( BaseType_t xErrnum,
                                  char * pcBuffer,
                                  size_t uxLength );

#endif /* FREERTOS_ERRNO_TCP */
