/* Copyright 2018 Espressif Systems (Shanghai) PTE LTD */
/* */
/* Licensed under the Apache License, Version 2.0 (the "License"); */
/* you may not use this file except in compliance with the License. */
/* You may obtain a copy of the License at */
/* */
/*     http://www.apache.org/licenses/LICENSE-2.0 */
/* */
/* Unless required by applicable law or agreed to in writing, software */
/* distributed under the License is distributed on an "AS IS" BASIS, */
/* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. */
/* See the License for the specific language governing permissions and */
/* limitations under the License. */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_DNS.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "esp_log.h"
#include "esp_wifi.h"
#include "esp_wifi_internal.h"
#include "tcpip_adapter.h"

static const char * TAG = "NetInterface";

static EthernetPhy_t xPhyObject;

static NetworkInterface_t * pxMyInterface;

static BaseType_t xESP32_Eth_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface );

static BaseType_t xESP32_Eth_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                     NetworkBufferDescriptor_t * const pxDescriptor,
                                                     BaseType_t xReleaseAfterSend );

static BaseType_t xESP32_Eth_GetPhyLinkStatus( NetworkInterface_t * pxInterface );

NetworkInterface_t * pxESP32_Eth_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                          NetworkInterface_t * pxInterface );

/*-----------------------------------------------------------*/

#if ( ipconfigIPv4_BACKWARD_COMPATIBLE == 1 )

/* Do not call the following function directly. It is there for downward compatibility.
 * The function FreeRTOS_IPInit() will call it to initialice the interface and end-point
 * objects.  See the description in FreeRTOS_Routing.h. */
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface )
    {
        pxESP32_Eth_FillInterfaceDescriptor( xEMACIndex, pxInterface );
    }

#endif
/*-----------------------------------------------------------*/


NetworkInterface_t * pxESP32_Eth_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                          NetworkInterface_t * pxInterface )
{
    static char pcName[ 8 ];

/* This function pxESP32_Eth_FillInterfaceDescriptor() adds a network-interface.
 * Make sure that the object pointed to by 'pxInterface'
 * is declared static or global, and that it will remain to exist. */

    snprintf( pcName, sizeof( pcName ), "eth%ld", xEMACIndex );

    memset( pxInterface, '\0', sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;                    /* Just for logging, debugging. */
    pxInterface->pvArgument = ( void * ) xEMACIndex; /* Has only meaning for the driver functions. */
    pxInterface->pfInitialise = xESP32_Eth_NetworkInterfaceInitialise;
    pxInterface->pfOutput = xESP32_Eth_NetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = xESP32_Eth_GetPhyLinkStatus;

    FreeRTOS_AddNetworkInterface( pxInterface );
    pxMyInterface = pxInterface;

    return pxInterface;
}
/*-----------------------------------------------------------*/

static BaseType_t xESP32_Eth_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    BaseType_t xResult = pdFALSE;
    static BaseType_t xMACAdrInitialized = pdFALSE;
    uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ];

    vPhyInitialise( &xPhyObject, NULL, NULL );

    if( xESP32_Eth_GetPhyLinkStatus( pxInterface ) != pdFALSE )
    {
        if( xMACAdrInitialized == pdFALSE )
        {
            esp_wifi_get_mac( ESP_IF_WIFI_STA, ucMACAddress );
            FreeRTOS_UpdateMACAddress( ucMACAddress );
            xMACAdrInitialized = pdTRUE;
        }

        xResult = pdTRUE;
    }

    return xResult;
}

static BaseType_t xESP32_Eth_GetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    ( void ) pxInterface;

    BaseType_t xResult = pdFALSE;

    if( xPhyObject.ulLinkStatusMask != 0U )
    {
        xResult = pdTRUE;
    }

    return xResult;
}

static BaseType_t xESP32_Eth_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                     NetworkBufferDescriptor_t * const pxDescriptor,
                                                     BaseType_t xReleaseAfterSend )
{
    BaseType_t xResult;

    if( ( pxNetworkBuffer == NULL ) || ( pxNetworkBuffer->pucEthernetBuffer == NULL ) || ( pxNetworkBuffer->xDataLength == 0 ) )
    {
        ESP_LOGE( TAG, "Invalid params" );
        xResult = pdFALSE;
    }
    else
    {
        esp_err_t ret;

        if( xESP32_Eth_GetPhyLinkStatus( pxInterface ) == pdFALSE )
        {
            ESP_LOGD( TAG, "Interface down" );
            ret = ESP_FAIL;
        }
        else
        {
            ret = esp_wifi_internal_tx( ESP_IF_WIFI_STA, pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength );

            if( ret != ESP_OK )
            {
                ESP_LOGE( TAG, "Failed to tx buffer %p, len %d, err %d", pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, ret );
            }
        }

        /* Call a function that monitors resources: the amount of free network
         * buffers and the amount of free space on the heap.  See FreeRTOS_IP.c
         * for more detailed comments. */
        vPrintResourceStats();

        if( xReleaseAfterSend == pdTRUE )
        {
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
        }

        xResult = (ret == ESP_OK ? pdTRUE : pdFALSE);
    }

    return xResult;
}

void vNetworkNotifyIFDown()
{
    if( xESP32_Eth_GetPhyLinkStatus( pxMyInterface ) != pdFALSE )
    {
        xPhyObject.ulLinkStatusMask = 0;
        #if ( ipconfigSUPPORT_NETWORK_DOWN_EVENT != 0 )
            FreeRTOS_NetworkDown( pxMyInterface );
        #endif
    }
}

void vNetworkNotifyIFUp()
{
    xPhyObject.ulLinkStatusMask = 1;
}

esp_err_t wlanif_input( void * netif,
                        void * buffer,
                        uint16_t len,
                        void * eb )
{
    esp_err_t xResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
    const TickType_t xDescriptorWaitTime = pdMS_TO_TICKS( 250 );

    vPrintResourceStats();

    if( eConsiderFrameForProcessing( buffer ) != eProcessBuffer )
    {
        ESP_LOGD( TAG, "Dropping packet" );
        esp_wifi_internal_free_rx_buffer( eb );
        xResult = ESP_OK;
    }
    else
    {
        pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( len, xDescriptorWaitTime );

        if( pxNetworkBuffer != NULL )
        {
            /* Set the packet size, in case a larger buffer was returned. */
            pxNetworkBuffer->xDataLength = len;
            pxNetworkBuffer->pxInterface = pxMyInterface;
            pxNetworkBuffer->pxEndPoint = FreeRTOS_MatchingEndpoint( pxMyInterface, pcBuffer );

            /* Copy the packet data. */
            memcpy( pxNetworkBuffer->pucEthernetBuffer, buffer, len );
            xRxEvent.pvData = ( void * ) pxNetworkBuffer;

            if( xSendEventStructToIPTask( &xRxEvent, xDescriptorWaitTime ) == pdFAIL )
            {
                ESP_LOGE( TAG, "Failed to enqueue packet to network stack %p, len %d", buffer, len );
                vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
                xResult = ESP_FAIL;
            }
            else
            {
                esp_wifi_internal_free_rx_buffer( eb );
                xResult = ESP_OK;
            }
        }
        else
        {
            ESP_LOGE( TAG, "Failed to get buffer descriptor" );
            xResult = ESP_FAIL;
        }
    }

    return xResult;
}
