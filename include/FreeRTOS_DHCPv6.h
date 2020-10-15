/*
 * FreeRTOS+TCP V2.3.0
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

#ifndef FREERTOS_DHCPv6_H
#define FREERTOS_DHCPv6_H

#ifdef __cplusplus
extern "C" {
#endif

/* Application level configuration options. */
#include "FreeRTOS_DHCP.h"
#include "FreeRTOSIPConfig.h"
#include "IPTraceMacroDefaults.h"

#define DHCPv6_MAX_CLIENT_SERVER_ID_LENGTH	128

typedef struct xClientServerID
{
	uint16_t usDUIDType;
	uint16_t usHardwareType;
	uint8_t pucID[ DHCPv6_MAX_CLIENT_SERVER_ID_LENGTH ];
	size_t uxLength;
} ClientServerID_t;

typedef struct xDHCPMessage_IPv6
{
	uint8_t uxMessageType;
	uint8_t ucTransactionID[ 3 ];
	uint32_t ulTransactionID;
	IPv6_Address_t ucDNSServer;
	uint32_t ulPreferredLifeTime;
	uint32_t ulValidLifeTime;
	uint32_t ulTimeStamp;
	uint8_t ucprefixLength;
	uint8_t ucHasUID;
	IPv6_Address_t xPrefixAddress;
	IPv6_Address_t xIPAddress;
	ClientServerID_t xClientID, xServerID;
} DHCPMessage_IPv6_t;

/* Returns the current state of a DHCP process. */
eDHCPState_t eGetDHCPv6State( struct xNetworkEndPoint *pxEndPoint );

struct xNetworkEndPoint;

/*
 * Send a message to the IP-task, which will call vDHCPProcess().
 */
BaseType_t xSendDHCPv6Event( struct xNetworkEndPoint *pxEndPoint );

/*
 * NOT A PUBLIC API FUNCTION.
 * It will be called when the DHCP timer expires, or when
 * data has been received on the DHCP socket.
 */
void vDHCPv6Process( BaseType_t xReset, struct xNetworkEndPoint *pxEndPoint );


/* Internal call: returns true if socket is the current DHCP socket */
BaseType_t xIsDHCPv6Socket( Socket_t xSocket );

/* Prototype of the hook (or callback) function that must be provided by the
application if ipconfigUSE_DHCP_HOOK is set to 1.  See the following URL for
usage information:
http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_DHCP_HOOK
*/
eDHCPCallbackAnswer_t xApplicationDHCPHook( eDHCPCallbackPhase_t eDHCPPhase, uint32_t ulIPAddress );

#ifdef __cplusplus
}	/* extern "C" */
#endif

#endif /* FREERTOS_DHCPv6_H */













