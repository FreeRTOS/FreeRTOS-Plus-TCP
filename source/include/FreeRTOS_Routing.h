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

#ifndef FREERTOS_ROUTING_H
    #define FREERTOS_ROUTING_H

    #ifdef __cplusplus
        extern "C" {
    #endif

    #if ( ipconfigUSE_DHCP != 0 )
        #include "FreeRTOS_DHCP.h"
    #endif

/* Every NetworkInterface needs a set of access functions: */

/* Forward declaration of 'struct xNetworkInterface'. */
    struct xNetworkInterface;

/* Initialise the interface. */
    typedef BaseType_t ( * NetworkInterfaceInitialiseFunction_t ) ( struct xNetworkInterface * pxDescriptor );

/* Send out an Ethernet packet. */
    typedef BaseType_t ( * NetworkInterfaceOutputFunction_t ) ( struct xNetworkInterface * pxDescriptor,
                                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                BaseType_t xReleaseAfterSend );

/* Return true as long as the LinkStatus on the PHY is present. */
    typedef BaseType_t ( * GetPhyLinkStatusFunction_t ) ( struct xNetworkInterface * pxDescriptor );

/** @brief These NetworkInterface access functions are collected in a struct: */
    typedef struct xNetworkInterface
    {
        const char * pcName;                               /**< Just for logging, debugging. */
        void * pvArgument;                                 /**< Will be passed to the access functions. */
        NetworkInterfaceInitialiseFunction_t pfInitialise; /**< This function will be called upon initialisation and repeated until it returns pdPASS. */
        NetworkInterfaceOutputFunction_t pfOutput;         /**< This function is supposed to send out a packet. */
        GetPhyLinkStatusFunction_t pfGetPhyLinkStatus;     /**< This function will return pdTRUE as long as the PHY Link Status is high. */
        struct
        {
            uint32_t
                bInterfaceUp : 1,          /**< Non-zero as soon as the interface is up. */
                bCallDownEvent : 1;        /**< The down-event must be called. */
        } bits;                            /**< A collection of boolean flags. */

        MACAddress_t xMACAddress;          /**< The MAC-address assigned to this end-point. */

        struct xNetworkInterface * pxNext; /**< The next interface in a linked list. */
    } NetworkInterface_t;

/*
 *  // As an example:
 *  NetworkInterface_t xZynqDescriptor = {
 *      .pcName					= "Zynq-GEM",
 *      .pvArgument				= ( void * )1,
 *      .pfInitialise           = xZynqGEMInitialise,
 *      .pfOutput               = xZynqGEMOutput,
 *      .pfGetPhyLinkStatus     = xZynqGEMGetPhyLinkStatus,
 *  };
 */


/*
 * Add a new physical Network Interface.  The object pointed to by 'pxInterface'
 * must continue to exist.
 * Only the Network Interface function xx_FillInterfaceDescriptor() shall call this function.
 */
    NetworkInterface_t * FreeRTOS_AddNetworkInterface( NetworkInterface_t * pxInterface );

/*
 * Get the first Network Interface.
 */
    NetworkInterface_t * FreeRTOS_FirstNetworkInterface( void );

/*
 * Get the next Network Interface.
 */
    NetworkInterface_t * FreeRTOS_NextNetworkInterface( const NetworkInterface_t * pxInterface );

/* A ethernet packet has come in on a certain network interface.
 * Find the best matching end-point. */
    void FreeRTOS_MatchingEndpoint( const NetworkInterface_t * pxNetworkInterface,
                                    NetworkBufferDescriptor_t * pucEthernetBuffer );


    #include "FreeRTOS_Routing_IPv4.h"

    #if ( ipconfigUSE_IPv6 != 0 )
        #include "FreeRTOS_Routing_IPv6.h"
    #endif

    #ifdef __cplusplus
        } /* extern "C" */
    #endif

#endif /* FREERTOS_ROUTING_H */
