#ifndef FREERTOS_DNS_H
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

#define FREERTOS_DNS_H

/* *INDENT-OFF* */
/* *INDENT-ON* */

/* Application level configuration options. */
#include "FreeRTOS_DNS_Globals.h"
#include "FreeRTOS_DNS_Callback.h"
#include "FreeRTOS_DNS_Cache.h"

/*
 * LLMNR is very similar to DNS, so is handled by the DNS routines.
 */
uint32_t ulDNSHandlePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer );

#if ( ipconfigUSE_LLMNR == 1 )
    /* The LLMNR MAC address is 01:00:5e:00:00:fc */
    extern const MACAddress_t xLLMNR_MacAdress;
#endif /* ipconfigUSE_LLMNR */

/** @brief While doing integration tests, it is necessary to influence the choice
 * between DNS/IPv4 and DNS/IPv4.  Depending on this, a DNS server will be
 * addressed via IPv4 or IPv6 messages. */
typedef enum xIPPreference
{
    xPreferenceNone,
    xPreferenceIPv4,
    #if ( ipconfigUSE_IPV6 != 0 )
        xPreferenceIPv6,
    #endif
} IPPreference_t;

/** @brief This variable determines he choice of DNS server, either IPv4 or IPv6. */
extern IPPreference_t xDNS_IP_Preference;

#if ( ipconfigUSE_NBNS != 0 )

/*
 * Inspect a NetBIOS Names-Service message.  If the name matches with ours
 * (xApplicationDNSQueryHook returns true) an answer will be sent back.
 * Note that LLMNR is a better protocol for name services on a LAN as it is
 * less polluted
 */
    uint32_t ulNBNSHandlePacket( NetworkBufferDescriptor_t * pxNetworkBuffer );

#endif /* ipconfigUSE_NBNS */



/*
 * Asynchronous version of gethostbyname()
 * xTimeout is in units of ms.
 */
    uint32_t FreeRTOS_gethostbyname_a( const char * pcHostName,
                                       FOnDNSEvent pCallback,
                                       void * pvSearchID,
                                       TickType_t uxTimeout );
    void FreeRTOS_gethostbyname_cancel( void * pvSearchID );



/*
 * Lookup a IPv4 node in a blocking-way.
 * It returns a 32-bit IP-address, 0 when not found.
 * gethostbyname() is already deprecated.
 */
uint32_t FreeRTOS_gethostbyname( const char * pcHostName );


/*
 * The function vDNSInitialise() initialises the DNS module.
 * It will be called "internally", by the IP-task.
 */
    void vDNSInitialise( void );

/* *INDENT-OFF* */
/* *INDENT-ON* */

#endif
