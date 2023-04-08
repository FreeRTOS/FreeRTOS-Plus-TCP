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

#ifndef NET_SETUP_H

#define NET_SETUP_H

typedef enum xSetupMethod
{
	eStatic,
	eDHCP,
	eRA,
} SetupMethod_t;

typedef struct xV4
{
	const char * pcMACAddress;
	const char * pcIPAddress;
    const char * pcMask;
	const char * pcGateway;
	SetupMethod_t eType;
	const char * pcDNS[ ipconfigENDPOINT_DNS_ADDRESS_COUNT ];
} SetupV4_t;

typedef struct xV6
{
	const char * pcMACAddress;
	const char * pcIPAddress;
    const char * pcPrefix;
	size_t   uxPrefixLength;
	const char * pcGateway;
	SetupMethod_t eType;
	const char * pcDNS[ ipconfigENDPOINT_DNS_ADDRESS_COUNT ];
} SetupV6_t;

BaseType_t xSetupEndpoint_v4( NetworkInterface_t * pxInterface, NetworkEndPoint_t * pxEndpoint, SetupV4_t * pxSetup );
BaseType_t xSetupEndpoint_v6( NetworkInterface_t * pxInterface, NetworkEndPoint_t * pxEndpoint, SetupV6_t * pxSetup  );

#endif /* NET_SETUP_H */
