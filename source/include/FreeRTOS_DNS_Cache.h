/*
 * FreeRTOS+TCP V2.3.2
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifndef FREERTOS_DNS_CACHE_H
#define FREERTOS_DNS_CACHE_H

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"

#include "FreeRTOS_DNS_Globals.h"

/* Standard includes. */
#include <stdint.h>

#if ( ( ipconfigUSE_DNS_CACHE == 1 ) && ( ipconfigUSE_DNS != 0 ) )

/* Look for the indicated host name in the DNS cache. Returns the IPv4
 * address if present, or 0x0 otherwise. */
    uint32_t FreeRTOS_dnslookup( const char * pcHostName );

    #if ( ipconfigUSE_IPv6 != 0 )
        /* FreeRTOS_dnslookup6() returns pdTRUE when a host has been found. */
        uint32_t FreeRTOS_dnslookup6( const char * pcHostName,
                                      IPv6_Address_t * pxAddress_IPv6 );
    #endif /* ipconfigUSE_IPv6 != 0 */

    void FreeRTOS_dnsclear( void );

    BaseType_t FreeRTOS_ProcessDNSCache( const char * pcName,
                                         IPv46_Address_t * pxIP,
                                         uint32_t ulTTL,
                                         BaseType_t xLookUp,
                                         struct freertos_addrinfo ** ppxAddressInfo );

    uint32_t Prepare_CacheLookup( const char * pcHostName,
                                  BaseType_t xFamily,
                                  struct freertos_addrinfo ** ppxAddressInfo );

    void ParseDNS_StoreToCache( ParseSet_t * pxSet,
                                IPv46_Address_t * pxIP_Address,
                                uint32_t ulTTL );
#endif /* ( ipconfigUSE_DNS_CACHE == 1 ) && ( ipconfigUSE_DNS != 0 ) */

#endif /* ifndef FREERTOS_DNS_CACHE_H */
