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
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

NetworkInterface_t xInterfaces[ 1 ];

/*
 * @brief Send a neighbour solicitation.
 * @param[in] pxIPAddress: A network buffer big enough to hold the ICMP packet.
 * @param[in,out] pxMACAddress: When found, the array of 6 bytes will be filled
 *                with the MAC-address.
 * @param[in,out] ppxEndPoint: The pointer to a pointer will point to an
 *                             end-point to which the device has responded.
 *
 * @note Look for ulIPAddress in the ND cache.  If the IP address exists, copy the
 * associated MAC address into pxMACAddress, refresh the ND cache entry's
 * age, and return eARPCacheHit.  If the IP address does not exist in the ND
 * cache return eARPCacheMiss.  If the packet cannot be sent for any reason
 * (maybe DHCP is still in process, or the addressing needs a gateway but there
 * isn't a gateway defined) then return eCantSendPacket.
 */
eARPLookupResult_t eNDGetCacheEntry( IPv6_Address_t * pxIPAddress,
                                     MACAddress_t * const pxMACAddress,
                                     struct xNetworkEndPoint ** ppxEndPoint )
{
}

/*
 * Find the end-point with given IP-address.
 */
NetworkEndPoint_t * FreeRTOS_FindEndPointOnIP_IPv4( uint32_t ulIPAddress,
                                                    uint32_t ulWhere )
{
}

/**
 * @brief Send a neighbour solicitation.
 * @param[in] pxNetworkBuffer: A network buffer big enough to hold the ICMP packet.
 * @param[in] pxIPAddress: The IPv6 address of the target device.
 *
 * @note Send out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 * add an entry into the ND table that indicates that an ND reply is
 * outstanding so re-transmissions can be generated.
 */
void vNDSendNeighbourSolicitation( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                   const IPv6_Address_t * pxIPAddress )
{
}

/**
 * @brief Process the generated UDP packet and do other checks before sending the
 *        packet such as ARP cache check and address resolution.
 *
 * @param[in] pxNetworkBuffer: The network buffer carrying the packet.
 */
void vProcessGeneratedUDPPacket_IPv6( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
}

/**
 * @brief Process the received UDP packet.
 *
 * @param[in] pxNetworkBuffer: The network buffer carrying the UDP packet.
 * @param[in] usPort: The port number on which this packet was received.
 * @param[out] pxIsWaitingForARPResolution: If the packet is awaiting ARP resolution,
 *             this pointer will be set to pdTRUE. pdFALSE otherwise.
 *
 * @return pdPASS in case the UDP packet could be processed. Else pdFAIL is returned.
 */
BaseType_t xProcessReceivedUDPPacket_IPv4( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                           uint16_t usPort,
                                           BaseType_t * pxIsWaitingForARPResolution )
{
}


/*
 * Find the best fitting end-point to reach a given IP-address.
 * Find an end-point whose IP-address is in the same network as the IP-address provided.
 * 'ulWhere' is temporary and or debugging only.
 */
NetworkEndPoint_t * FreeRTOS_FindEndPointOnNetMask( uint32_t ulIPAddress,
                                                    uint32_t ulWhere )
{
}

/**
 * @brief Process the generated UDP packet and do other checks before sending the
 *        packet such as ARP cache check and address resolution.
 *
 * @param[in] pxNetworkBuffer: The network buffer carrying the packet.
 */
void vProcessGeneratedUDPPacket_IPv4( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
}


/**
 * @brief Process the received UDP packet.
 *
 * @param[in] pxNetworkBuffer: The network buffer carrying the UDP packet.
 * @param[in] usPort: The port number on which this packet was received.
 * @param[out] pxIsWaitingForARPResolution: If the packet is awaiting ARP resolution,
 *             this pointer will be set to pdTRUE. pdFALSE otherwise.
 *
 * @return pdPASS in case the UDP packet could be processed. Else pdFAIL is returned.
 */
BaseType_t xProcessReceivedUDPPacket_IPv6( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                           uint16_t usPort,
                                           BaseType_t * pxIsWaitingForARPResolution )
{
}

void vPortEnterCritical( void )
{
}
void vPortExitCritical( void )
{
}
