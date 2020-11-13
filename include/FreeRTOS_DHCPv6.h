/*
 * FreeRTOS+TCP V2.3.1
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

    #define DHCPv6_MAX_CLIENT_SERVER_ID_LENGTH    128

/** @brief The ID of a client or a server. */
    typedef struct xClientServerID
    {
        uint16_t usDUIDType;                                 /**< A DHCP Unique Identifier ( DUID ). */
        uint16_t usHardwareType;                             /**< The hardware type: 1 = Ethernet. */
        uint8_t pucID[ DHCPv6_MAX_CLIENT_SERVER_ID_LENGTH ]; /**< Universally Unique IDentifier (UUID) format. */
        size_t uxLength;                                     /**< The number of valid bytes within 'pucID'. */
    } ClientServerID_t;

/** @brief DHCPMessage_IPv6_t holds all data of a DHCP client. */
    typedef struct xDHCPMessage_IPv6
    {
        uint8_t uxMessageType;         /**< The type of the last message received: Advertise / Confirm / Reply / Decline */
        uint8_t ucTransactionID[ 3 ];  /**< ID of a transaction, shall be renewed when the transaction is ready ( and a reply has been received ). */
        uint32_t ulTransactionID;      /**< The same as above but now as a long integer. */
        IPv6_Address_t ucDNSServer;    /**< The IP-address of the DHCP server. */
        uint32_t ulPreferredLifeTime;  /**< The preferred life time. */
        uint32_t ulValidLifeTime;      /**< The valid life time. */
        uint32_t ulTimeStamp;          /**< DUID Time: seconds since 1-1-2000. */
        uint8_t ucprefixLength;        /**< The length of the prefix offered. */
        uint8_t ucHasUID;              /**< When pdFALSE: a transaction ID must be created. */
        IPv6_Address_t xPrefixAddress; /**< The prefix offered. */
        IPv6_Address_t xIPAddress;     /**< The IP-address offered. */
        ClientServerID_t xClientID;    /**< The UUID of the client. */
        ClientServerID_t xServerID;    /**< The UUID of the server. */
    } DHCPMessage_IPv6_t;

/* Returns the current state of a DHCP process. */
    eDHCPState_t eGetDHCPv6State( struct xNetworkEndPoint * pxEndPoint );

    struct xNetworkEndPoint;

/*
 * Send a message to the IP-task, which will call vDHCPProcess().
 */
    BaseType_t xSendDHCPv6Event( struct xNetworkEndPoint * pxEndPoint );

/*
 * NOT A PUBLIC API FUNCTION.
 * It will be called when the DHCP timer expires, or when
 * data has been received on the DHCP socket.
 */
    void vDHCPv6Process( BaseType_t xReset,
                         struct xNetworkEndPoint * pxEndPoint );


/* Internal call: returns true if socket is the current DHCP socket */
    BaseType_t xIsDHCPv6Socket( Socket_t xSocket );

/* Prototype of the hook (or callback) function that must be provided by the
 * application if ipconfigUSE_DHCP_HOOK is set to 1.  See the following URL for
 * usage information:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html#ipconfigUSE_DHCP_HOOK
 */
    eDHCPCallbackAnswer_t xApplicationDHCPHook( eDHCPCallbackPhase_t eDHCPPhase,
                                                uint32_t ulIPAddress );

    #ifdef __cplusplus
        } /* extern "C" */
    #endif

#endif /* FREERTOS_DHCPv6_H */
