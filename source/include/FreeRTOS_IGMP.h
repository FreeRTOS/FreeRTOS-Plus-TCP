/*
 * FreeRTOS+TCP V2.4.0
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifndef FREERTOS_IGMP_H
    #define FREERTOS_IGMP_H

    #ifdef __cplusplus
    extern "C" {
    #endif

/* Application level configuration options. */
    #include "FreeRTOSIPConfig.h"
    #include "FreeRTOSIPConfigDefaults.h"
    #include "FreeRTOS_Sockets.h"
    #include "IPTraceMacroDefaults.h"
    #include "FreeRTOS_Stream_Buffer.h"
    #if ( ipconfigUSE_TCP == 1 )
        #include "FreeRTOS_TCP_WIN.h"
        #include "FreeRTOS_TCP_IP.h"
    #endif

    #include "semphr.h"

    #include "event_groups.h"


/** @brief IGMP times things in 100ms increments. https://www.rfc-editor.org/rfc/rfc2236#section-2.2 */
    #define igmpTIMING_PERIOD_MS             ( 100U )

/* IGMP protocol definitions. */
    #define igmpIGMP_MEMBERSHIP_QUERY        ( ( uint8_t ) 0x11U )      /**< IGMP membership query. */
    #define igmpIGMP_MEMBERSHIP_REPORT_V1    ( ( uint8_t ) 0x12U )      /**< IGMP v1 membership report. */
    #define igmpIGMP_MEMBERSHIP_REPORT_V2    ( ( uint8_t ) 0x16U )      /**< IGMP v2 membership report. */
    #define igmpIGMP_MEMBERSHIP_REPORT_V3    ( ( uint8_t ) 0x22U )      /**< IGMP v3 membership report. */
    #define igmpIGMP_LEAVE_GROUP             ( ( uint8_t ) 0x17U )      /**< IGMP leave group */

    #if ( ipconfigBYTE_ORDER == pdFREERTOS_BIG_ENDIAN )
        #define igmpIGMP_IP_ADDR             0xE0000001UL
    #else
        #define igmpIGMP_IP_ADDR             0x010000E0UL
    #endif /* ipconfigBYTE_ORDER == pdFREERTOS_BIG_ENDIAN */

    #include "pack_struct_start.h"
    struct xIGMP_HEADER
    {
        uint8_t ucMessageType;     /**< The IGMP type                     0 + 1 = 1 */
        uint8_t ucMaxResponseTime; /**< Maximum time (sec) for responses. 1 + 1 = 2 */
        uint16_t usChecksum;       /**< The checksum of whole IGMP packet 2 + 2 = 4 */
        uint32_t ulGroupAddress;   /**< The multicast group address       4 + 4 = 8 */
    }
    #include "pack_struct_end.h"
    typedef struct xIGMP_HEADER IGMPHeader_t;

    #include "pack_struct_start.h"
    struct xIGMP_PACKET
    {
        EthernetHeader_t xEthernetHeader; /**< The Ethernet header of an IGMP packet. */
        IPHeader_t xIPHeader;             /**< The IP header of an IGMP packet. */
        IGMPHeader_t xIGMPHeader;         /**< The IGMP header of an IGMP packet. */
    }
    #include "pack_struct_end.h"
    typedef struct xIGMP_PACKET IGMPPacket_t;



    #ifdef __cplusplus
}     /* extern "C" */
    #endif

#endif /* FREERTOS_IP_PRIVATE_H */
