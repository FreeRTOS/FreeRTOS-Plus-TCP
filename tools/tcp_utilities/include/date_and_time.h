/*
 * FreeRTOS+TCP V4.3.0
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

#ifndef DATE_AND_TIME_H
    #define DATE_AND_TIME_H

    #include <time.h>

    #ifdef __cplusplus
    extern "C" {
    #endif

    extern uint32_t ulSeconds, ulMsec;
    extern int iTimeZone;

    extern time_t FreeRTOS_get_secs_msec( time_t * pulMsec );
    extern void FreeRTOS_set_secs_msec( time_t * pulSeconds,
                                        time_t * pulMsec );

    extern time_t FreeRTOS_time( time_t * pxTime );
    extern void FreeRTOS_settime( time_t * pxTime );


    #ifdef __cplusplus
}         /* extern "C" */
    #endif

#endif /* DATE_AND_TIME_H */
