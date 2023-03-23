/*
 * Some constants, hardware definitions and comments taken from ST's HAL driver
 * library, COPYRIGHT(c) 2015 STMicroelectronics.
 */

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
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"
#include "phyHandling.h"

/* ST includes. */
#include "main.h"
#if defined(STM32F7)
    #include "stm32f7xx_hal_eth.h"
#elif defined(STM32H7)
    #include "stm32h7xx_hal_eth.h"
#else
    #error Unknown STM32 Family for NetworkInterface
#endif

/*-----------------------------------------------------------*/

#define NETWORK_BUFFER_SIZE ( ( ( ETH_RX_BUF_SIZE + ipBUFFER_PADDING ) + 7 ) & ~0x7UL )

#define EMAC_IF_RX_EVENT 1UL
#define EMAC_IF_TX_EVENT 2UL
#define EMAC_IF_ERR_EVENT 4UL
#define EMAC_IF_ALL_EVENT ( EMAC_IF_RX_EVENT | EMAC_IF_TX_EVENT | EMAC_IF_ERR_EVENT )

typedef enum
{
    eMACInit,   /* Must initialise MAC. */
    eMACPass,   /* Initialisation was successful. */
    eMACFailed, /* Initialisation failed. */
} eMAC_INIT_STATUS_TYPE;

/*-----------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceInput( void );

static void prvEMACHandlerTask( void * pvParameters ) __attribute__((__noreturn__));

static BaseType_t prvAcceptPacket( const uint8_t * const pucEthernetBuffer );

static BaseType_t prvPhyReadReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t * pulValue );

static BaseType_t prvPhyWriteReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue );

static void prvEthernetUpdateConfig( void );

/*-----------------------------------------------------------*/

static ETH_HandleTypeDef xEthHandle;

static ETH_DMADescTypeDef DMARxDscrTab[ ETH_RX_DESC_CNT ] __attribute__( ( section( ".RxDescripSection" ) ) );

/*#if ( ipconfigZERO_COPY_RX_DRIVER == 0 )
    __ALIGN_BEGIN uint8_t Rx_Buff[ ETH_RXBUFNB ][ ETH_RX_BUF_SIZE ] __ALIGN_END;
#endif*/

static ETH_DMADescTypeDef DMATxDscrTab[ ETH_TX_DESC_CNT ] __attribute__( ( section( ".TxDescripSection" ) ) );

/*#if ( ipconfigZERO_COPY_TX_DRIVER == 0 )
    __ALIGN_BEGIN uint8_t Tx_Buff[ ETH_TXBUFNB ][ ETH_TX_BUF_SIZE ] __ALIGN_END;
#endif*/

static ETH_TxPacketConfig xTxConfig;

/*#if ( ipconfigUSE_LLMNR == 1 )
    static const uint8_t xLLMNR_MACAddress[] = { 0x01, 0x00, 0x5E, 0x00, 0x00, 0xFC };
#endif*/

static TaskHandle_t xEMACTaskHandle;

static SemaphoreHandle_t xTxMutex;

static SemaphoreHandle_t xTxDescSem;

static EthernetPhy_t xPhyObject;

static const PhyProperties_t xPHYProperties = {
    .ucSpeed = PHY_SPEED_AUTO,
    .ucDuplex = PHY_DUPLEX_AUTO,
    .ucMDI_X = PHY_MDIX_AUTO,
};

/* static const PhyProperties_t xPHYProperties =
{
    #if ( ipconfigETHERNET_AN_ENABLE != 0 )
        .ucSpeed      = PHY_SPEED_AUTO,
        .ucDuplex     = PHY_DUPLEX_AUTO,
    #else
        #if ( ipconfigETHERNET_USE_100MB != 0 )
            .ucSpeed  = PHY_SPEED_100,
        #else
            .ucSpeed  = PHY_SPEED_10,
        #endif

        #if ( ipconfigETHERNET_USE_FULL_DUPLEX != 0 )
            .ucDuplex = PHY_DUPLEX_FULL,
        #else
            .ucDuplex = PHY_DUPLEX_HALF,
        #endif
    #endif

    #if ( ipconfigETHERNET_AN_ENABLE != 0 ) && ( ipconfigETHERNET_AUTO_CROSS_ENABLE != 0 )
        .ucMDI_X      = PHY_MDIX_AUTO,
    #elif ( ipconfigETHERNET_CROSSED_LINK != 0 )
        .ucMDI_X      = PHY_MDIX_CROSSED,
    #else
        .ucMDI_X      = PHY_MDIX_DIRECT,
    #endif
}; */

/*-----------------------------------------------------------*/

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ NETWORK_BUFFER_SIZE ] __attribute__( ( aligned( 4 ), section( ".EthBuffersSection" ) ) );

    for( size_t ul = 0; ul < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ul++ )
    {
        pxNetworkBuffers[ ul ].pucEthernetBuffer = &( ucNetworkPackets[ ul ][ ipBUFFER_PADDING ] );
        *( ( uint32_t * ) &( ucNetworkPackets[ ul ][ 0 ] ) ) = ( uint32_t ) ( &( pxNetworkBuffers[ ul ] ) );
    }
}

/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceInitialise( void )
{
    BaseType_t xResult = pdFAIL;

    static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMACInit;

    if( xMacInitStatus == eMACInit )
    {
        if( xEMACTaskHandle == NULL )
        {
            static StaticSemaphore_t xTxMutexBuf;
            xTxMutex = xSemaphoreCreateMutexStatic( &xTxMutexBuf );
            configASSERT( xTxMutex );
            vQueueAddToRegistry( xTxMutex, "TXMutex" );

            static StaticSemaphore_t xTxDescSemBuf;
    		xTxDescSem = xSemaphoreCreateCountingStatic( ( UBaseType_t ) ETH_TX_DESC_CNT, ( UBaseType_t ) ETH_TX_DESC_CNT, &xTxDescSemBuf );
            configASSERT( xTxDescSem );
            vQueueAddToRegistry( xTxDescSem, "xTxDescSem" );

            static StackType_t uxEMACTaskStack[ ( 2 * configMINIMAL_STACK_SIZE ) ];
            static StaticTask_t xEMACTaskTCB;
            xEMACTaskHandle = xTaskCreateStatic(
                prvEMACHandlerTask,
                "EMAC",
                ( 2 * configMINIMAL_STACK_SIZE ),
                NULL,
                ( configMAX_PRIORITIES - 1 ),
                uxEMACTaskStack,
                &xEMACTaskTCB
            );
            configASSERT( xEMACTaskHandle );
        }

        if( xEthHandle.Instance == NULL )
        {
            xEthHandle.Instance = ETH;
            xEthHandle.Init.MACAddr = ( uint8_t * ) FreeRTOS_GetMACAddress();
            xEthHandle.Init.MediaInterface = HAL_ETH_RMII_MODE;
            /*#if ( ipconfigUSE_RMII != 0 )
                xEthHandle.Init.MediaInterface = ETH_MEDIA_INTERFACE_RMII;
            #else
                xEthHandle.Init.MediaInterface = ETH_MEDIA_INTERFACE_MII;
            #endif*/
            xEthHandle.Init.TxDesc = DMATxDscrTab;
            xEthHandle.Init.RxDesc = DMARxDscrTab;
            xEthHandle.Init.RxBuffLen = ETH_RX_BUF_SIZE;

            memset( &DMATxDscrTab, 0, sizeof( DMATxDscrTab ) );
            memset( &DMARxDscrTab, 0, sizeof( DMARxDscrTab ) );

            #ifdef STM32F7
                /* This function doesn't get called in Fxx driver */
                HAL_ETH_SetMDIOClockRange( &xEthHandle );
            #endif

            configASSERT( HAL_ETH_Init( &xEthHandle ) == HAL_OK );

            /*#if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_MDNS != 0 )
                BaseType_t xMACEntry = ETH_MAC_ADDRESS1;
                uint8_t pMACAddr[6];
                memset( &pMACAddr, 0, sizeof( pMACAddr ) );
                configASSERT( HAL_ETH_SetSourceMACAddrMatch( &xEthHandle, xMACEntry, pMACAddr ) );
            #endif

            #if ( ipconfigUSE_MDNS == 1 )
                HAL_ETH_SetSourceMACAddrMatch( &xEthHandle, xMACEntry, ( uint8_t * ) xMDNS_MACAddressIPv4 );
                xMACEntry += 8;
            #endif
            #if ( ipconfigUSE_LLMNR == 1 )
                HAL_ETH_SetSourceMACAddrMatch( &xEthHandle, xMACEntry, ( uint8_t * ) xLLMNR_MACAddress );
                xMACEntry += 8;
            #endif*/

            memset( &xTxConfig, 0, sizeof( xTxConfig ) );
            xTxConfig.Attributes = ETH_TX_PACKETS_FEATURES_CRCPAD;
            xTxConfig.CRCPadCtrl = ETH_CRC_PAD_INSERT;
            #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM != 0 )
                xTxConfig.Attributes |= ETH_TX_PACKETS_FEATURES_CSUM;
                xTxConfig.ChecksumCtrl = ETH_CHECKSUM_IPHDR_PAYLOAD_INSERT_PHDR_CALC;
            #else
                xTxConfig.ChecksumCtrl = ETH_CHECKSUM_DISABLE;
            #endif
            xMacInitStatus = eMACPass;
        }
    }

    if( xMacInitStatus == eMACPass )
    {
        vPhyInitialise( &xPhyObject, ( xApplicationPhyReadHook_t ) prvPhyReadReg, ( xApplicationPhyWriteHook_t ) prvPhyWriteReg );
        configASSERT( xPhyDiscover( &xPhyObject ) > 0 );
        configASSERT( xPhyConfigure( &xPhyObject, &xPHYProperties ) == 0 );
        configASSERT( xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) ) == 0 );
    }

    if ( xPhyObject.ulLinkStatusMask != 0U )
    {
        ETH_MACConfigTypeDef MACConf;
        configASSERT( HAL_ETH_GetMACConfig( &xEthHandle , &MACConf ) == HAL_OK );
        MACConf.DuplexMode = ( xPhyObject.xPhyProperties.ucDuplex == PHY_DUPLEX_FULL ) ? ETH_FULLDUPLEX_MODE : ETH_HALFDUPLEX_MODE;
        MACConf.Speed = ( xPhyObject.xPhyProperties.ucSpeed == PHY_SPEED_10 ) ? ETH_SPEED_10M : ETH_SPEED_100M;
        MACConf.ChecksumOffload = ( FunctionalState ) ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM != 0 );
        configASSERT( HAL_ETH_SetMACConfig( &xEthHandle, &MACConf ) == HAL_OK );
        configASSERT( HAL_ETH_Start_IT( &xEthHandle ) == HAL_OK );
        xResult = pdPASS;
    }

    return xResult;
}

/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend )
{
    BaseType_t xResult = pdFAIL;
    /* TODO: ipconfigZERO_COPY_TX_DRIVER */

    if( pxDescriptor != NULL )
    {
        if( xPhyObject.ulLinkStatusMask != 0 )
        {
            ETH_BufferTypeDef xTxBuffer = {
                .buffer = ( uint8_t * ) pxDescriptor->pucEthernetBuffer,
                .len = pxDescriptor->xDataLength,
                .next = NULL
            };

            xTxConfig.Length = xTxBuffer.len;
            xTxConfig.TxBuffer = &xTxBuffer;
            xTxConfig.pData = pxDescriptor;

            if( xTxConfig.Length <= ETH_TX_BUF_SIZE - ipBUFFER_PADDING )
            {
            	if( xSemaphoreTake( xTxDescSem, pdMS_TO_TICKS( 100U ) ) != pdFALSE )
            	{
					if( xSemaphoreTake( xTxMutex, pdMS_TO_TICKS( 20U ) ) != pdFALSE )
					{
						xReleaseAfterSend = pdFALSE;
						if( HAL_ETH_Transmit_IT( &xEthHandle, &xTxConfig ) == HAL_OK )
						{
							xResult = pdPASS;
						}
                        else
                        {
                            configASSERT( xEthHandle.ErrorCode != HAL_ETH_ERROR_PARAM );
                            configASSERT( xEthHandle.gState == HAL_ETH_STATE_STARTED );
                        }
						xSemaphoreGive( xTxMutex );
					}
            	}
            }
        }

        if( xReleaseAfterSend != pdFALSE )
    	{
        	vReleaseNetworkBufferAndDescriptor( pxDescriptor );
    	}
    }

    return xResult;
}

/*-----------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceInput( void )
{
    /* TODO: ipconfigZERO_COPY_RX_DRIVER */
	BaseType_t xResult = 0;
    NetworkBufferDescriptor_t * pStartDescriptor = NULL;
	while ( HAL_ETH_ReadData( &xEthHandle, ( void ** ) &pStartDescriptor ) == HAL_OK )
	{
		xResult++;
        if ( pStartDescriptor != NULL )
        {
            const IPStackEvent_t xRxEvent = {
                .eEventType = eNetworkRxEvent,
                .pvData = ( void * ) pStartDescriptor
            };

            if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0U ) != pdPASS )
            {
                iptraceETHERNET_RX_EVENT_LOST();
                NetworkBufferDescriptor_t * pxDescriptorToClear = pStartDescriptor;
                do
                {
                    #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
                        NetworkBufferDescriptor_t * pxNext = pxDescriptorToClear->pxNextBuffer;
                    #else
                        NetworkBufferDescriptor_t * pxNext = NULL;
                    #endif
                    vReleaseNetworkBufferAndDescriptor( pxDescriptorToClear );
                    pxDescriptorToClear = pxNext;
                } while( pxDescriptorToClear != NULL );
            }
        }
	}
    configASSERT( xEthHandle.ErrorCode != HAL_ETH_ERROR_PARAM );
    configASSERT( xEthHandle.gState == HAL_ETH_STATE_STARTED );
	return ( BaseType_t ) ( xResult > 0 );
}

/*-----------------------------------------------------------*/

static void prvEMACHandlerTask( void * pvParameters )
{
    ( void ) pvParameters;

    for( ;; )
    {
    	BaseType_t xResult = 0U;

        uint32_t ulISREvents = 0U;

        if ( xTaskNotifyWait( 0U, EMAC_IF_ALL_EVENT, &ulISREvents, pdMS_TO_TICKS( 500UL ) ) == pdTRUE )
        {
            if( ( ulISREvents & EMAC_IF_RX_EVENT ) != 0 )
            {
                iptraceNETWORK_INTERFACE_RECEIVE();
                xResult = prvNetworkInterfaceInput();
            }

            if( ( ulISREvents & EMAC_IF_TX_EVENT ) != 0 )
            {
                iptraceNETWORK_INTERFACE_TRANSMIT();
                configASSERT( HAL_ETH_ReleaseTxPacket( heth ) == HAL_OK );
            }

            if( ( ulISREvents & EMAC_IF_ERR_EVENT ) != 0 )
            {
                HAL_ETH_Stop_IT( &xEthHandle );
                /* FreeRTOS_NetworkDown()
                HAL_ETH_ReleaseTxPacket( &xEthHandle );*/
                HAL_ETH_Start_IT( &xEthHandle );
            }
        }

        if( xPhyCheckLinkStatus( &xPhyObject, xResult ) != 0 )
        {
            prvEthernetUpdateConfig();
        }
    }
}

/*-----------------------------------------------------------*/

static BaseType_t prvAcceptPacket( const uint8_t * const pucEthernetBuffer )
{
	uint32_t pErrorCode = 0;
	HAL_ETH_GetRxDataErrorCode( &xEthHandle, &pErrorCode );
	if ( pErrorCode != 0 )
	{
        return pdFALSE;
    }

    const ProtocolPacket_t * pxProtPacket = ( const ProtocolPacket_t * ) pucEthernetBuffer;

    #if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES != 0 )
        switch( pxProtPacket->xTCPPacket.xEthernetHeader.usFrameType )
        {
            case ipARP_FRAME_TYPE:
                return pdTRUE;

            case ipIPv4_FRAME_TYPE:
                break;

            default:
                return pdFALSE;
        }
    #endif

    #if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS != 0 )
        const IPHeader_t * pxIPHeader = &( pxProtPacket->xTCPPacket.xIPHeader );

        if( ( pxIPHeader->usFragmentOffset & ipFRAGMENT_OFFSET_BIT_MASK ) != 0U )
        {
            return pdFALSE;
        }

        if( ( pxIPHeader->ucVersionHeaderLength < 0x45 ) || ( pxIPHeader->ucVersionHeaderLength > 0x4F ) )
        {
            return pdFALSE;
        }

        const uint32_t ulDestinationIPAddress = pxIPHeader->ulDestinationIPAddress;

        if( ( ulDestinationIPAddress != *ipLOCAL_IP_ADDRESS_POINTER ) && ( ( FreeRTOS_ntohl( ulDestinationIPAddress ) & 0xff ) != 0xff ) && ( *ipLOCAL_IP_ADDRESS_POINTER != 0 ) )
        {
            return pdFALSE;
        }

        if( pxIPHeader->ucProtocol == ipPROTOCOL_UDP )
        {
            if( ( xPortHasUDPSocket( pxProtPacket->xUDPPacket.xUDPHeader.usDestinationPort ) == pdFALSE ))
            {
                return pdFALSE;
            }
            /*#if ipconfigUSE_LLMNR == 1
                && ( usDestinationPort != ipLLMNR_PORT ) &&
                ( usSourcePort != ipLLMNR_PORT )
            #endif
            #if ipconfigUSE_MDNS == 1
                && ( usDestinationPort != ipMDNS_PORT ) &&
                ( usSourcePort != ipMDNS_PORT )
            #endif
            #if ipconfigUSE_NBNS == 1
                && ( usDestinationPort != ipNBNS_PORT ) &&
                ( usSourcePort != ipNBNS_PORT )
            #endif
            #if ipconfigUSE_DNS == 1
                && ( usSourcePort != ipDNS_PORT )
            #endif
            )*/
        }
    #endif

    return pdTRUE;
}

/*-----------------------------------------------------------*/

static BaseType_t prvPhyReadReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t * pulValue )
{
	BaseType_t iResult = -1;
	if( HAL_ETH_ReadPHYRegister( &xEthHandle, ( uint32_t ) xAddress, ( uint32_t ) xRegister, pulValue ) == HAL_OK )
	{
		iResult = 0;
	}
	return iResult;
}

/*-----------------------------------------------------------*/

static BaseType_t prvPhyWriteReg( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue )
{
    BaseType_t iResult = -1;
    if( HAL_ETH_WritePHYRegister( &xEthHandle, ( uint32_t ) xAddress, ( uint32_t ) xRegister, ulValue ) == HAL_OK )
    {
        iResult = 0;
    }
    return iResult;
}

/*-----------------------------------------------------------*/

static void prvEthernetUpdateConfig( void )
{
    if( ( xPhyObject.ulLinkStatusMask != 0 ) )
    {
        /* TODO: if( xETH.Init.AutoNegotiation != ETH_AUTONEGOTIATION_DISABLE ) */
    	configASSERT( xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) ) == 0 );

    	ETH_MACConfigTypeDef MACConf;
		configASSERT( HAL_ETH_GetMACConfig( &xEthHandle , &MACConf ) == HAL_OK );

        if( xPhyObject.xPhyProperties.ucDuplex == PHY_DUPLEX_FULL )
        {
        	MACConf.DuplexMode = ETH_FULLDUPLEX_MODE;
        }
        else
        {
        	MACConf.DuplexMode = ETH_HALFDUPLEX_MODE;
        }

        if( xPhyObject.xPhyProperties.ucSpeed == PHY_SPEED_10 )
        {
        	MACConf.Speed = ETH_SPEED_10M;
        }
        else
        {
        	MACConf.Speed = ETH_SPEED_100M;
        }

		configASSERT( HAL_ETH_SetMACConfig( &xEthHandle, &MACConf ) == HAL_OK );
        if( ( xPhyObject.ulLinkStatusMask != 0 ) )
        {
            HAL_ETH_Start_IT( &xEthHandle );
        }
    }
    else
    {
        if( HAL_ETH_Stop_IT( &xEthHandle ) == HAL_OK )
        {
            configASSERT( HAL_ETH_ReleaseTxPacket( &xEthHandle ) == HAL_OK );
            memset( &DMATxDscrTab, 0, sizeof( DMATxDscrTab ) );
        }
    }
}

/*-----------------------------------------------------------*/

void ETH_IRQHandler( void )
{
    HAL_ETH_IRQHandler( &xEthHandle );
}

/*-----------------------------------------------------------*/

void HAL_ETH_RxCpltCallback( ETH_HandleTypeDef * heth )
{
    static size_t uxMostRXDescsUsed = 0U;

    const size_t uxRxUsed = heth->RxDescList.RxDescCnt;

    if( uxMostRXDescsUsed < uxRxUsed )
    {
        uxMostRXDescsUsed = uxRxUsed;
    }

    if( xEMACTaskHandle != NULL )
    {
        BaseType_t xHigherPriorityTaskWoken = pdFALSE;
        xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_RX_EVENT, eSetBits, &xHigherPriorityTaskWoken );
        portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
    }
}

/*-----------------------------------------------------------*/

void HAL_ETH_TxCpltCallback( ETH_HandleTypeDef * heth )
{
    static size_t uxMostTXDescsUsed = 0U;

    const size_t uxTxUsed = heth->TxDescList.BuffersInUse;

    if( uxMostTXDescsUsed < uxTxUsed )
	{
		uxMostTXDescsUsed = uxTxUsed;
	}

    /* configASSERT( HAL_ETH_ReleaseTxPacket( heth ) == HAL_OK ); */

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_TX_EVENT, eSetBits, &xHigherPriorityTaskWoken );
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}

/*-----------------------------------------------------------*/

void HAL_ETH_ErrorCallback( ETH_HandleTypeDef *heth )
{
    if( HAL_ETH_GetError( heth ) & HAL_ETH_ERROR_DMA )
    {
        if( HAL_ETH_GetDMAError( heth ) )
        {
            if( heth->gState == HAL_ETH_STATE_ERROR )
            {
                /* fatal bus error occurred */
                /* F7 - ETH_DMASR_FBES | ETH_DMASR_TPS | ETH_DMASR_RPS */
                /* H7 - ETH_DMACSR_FBE | ETH_DMACSR_TPS | ETH_DMACSR_RPS */
                BaseType_t xHigherPriorityTaskWoken = pdFALSE;
                xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_ERR_EVENT, eSetBits, &xHigherPriorityTaskWoken );
                portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
            }
            else
            {
                /* F7 - ETH_DMASR_ETS | ETH_DMASR_RWTS | ETH_DMASR_RBUS | ETH_DMASR_AIS */
                /* H7 - ETH_DMACSR_CDE | ETH_DMACSR_ETI | ETH_DMACSR_RWT | ETH_DMACSR_RBU | ETH_DMACSR_AIS */
                /*if( ( HAL_ETH_GetDMAError(heth) & ETH_DMACSR_RBU ) == ETH_DMACSR_RBU )
                {
                    xSemaphoreGiveFromISR( xTxMutex );
                }

                if( ( HAL_ETH_GetDMAError(heth) & ETH_DMACSR_TBU ) == ETH_DMACSR_TBU )
                {
                    xSemaphoreGiveFromISR( xTxMutex );
                }*/
            }
        }
    }

    #ifdef STM32H7
        if( HAL_ETH_GetError( heth ) & HAL_ETH_ERROR_MAC )
        {
            if( HAL_ETH_GetMACError( heth ) )
            {

            }
        }
    #endif
}

/*-----------------------------------------------------------*/

void HAL_ETH_RxAllocateCallback( uint8_t **buff )
{
	NetworkBufferDescriptor_t * pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( ETH_RX_BUF_SIZE, pdMS_TO_TICKS( 0 ) );
	if( pxBufferDescriptor != NULL )
	{
		*buff = pxBufferDescriptor->pucEthernetBuffer;
	}
}

/*-----------------------------------------------------------*/

void HAL_ETH_RxLinkCallback( void **pStart, void **pEnd, uint8_t *buff, uint16_t Length )
{
	NetworkBufferDescriptor_t * pxCurDescriptor = pxPacketBuffer_to_NetworkBuffer( ( const void * ) buff );
	if ( prvAcceptPacket( pxCurDescriptor->pucEthernetBuffer ) == pdTRUE )
	{
    	NetworkBufferDescriptor_t ** pStartDescriptor = ( NetworkBufferDescriptor_t ** ) pStart;
    	NetworkBufferDescriptor_t ** pEndDescriptor = ( NetworkBufferDescriptor_t ** ) pEnd;

        pxCurDescriptor->xDataLength = Length;
        #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
            pxCurDescriptor->pxNextBuffer = NULL;
        #endif
        if( *pStartDescriptor == NULL )
        {
        	*pStartDescriptor = pxCurDescriptor;
        }
        #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
            else if( pEndDescriptor != NULL )
            {
                ( *pEndDescriptor )->pxNextBuffer = pxCurDescriptor;
            }
        #endif
        *pEndDescriptor = pxCurDescriptor;
    }
    else
    {
        vReleaseNetworkBufferAndDescriptor( pxCurDescriptor );
    }
}

/*-----------------------------------------------------------*/

void HAL_ETH_TxFreeCallback( uint32_t *buff )
{
	NetworkBufferDescriptor_t * pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) buff;
	if( pxNetworkBuffer != NULL )
	{
		vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
	}
	BaseType_t xHigherPriorityTaskWoken = pdFALSE;
	xSemaphoreGiveFromISR( xTxDescSem, &xHigherPriorityTaskWoken );
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}

/*-----------------------------------------------------------*/
