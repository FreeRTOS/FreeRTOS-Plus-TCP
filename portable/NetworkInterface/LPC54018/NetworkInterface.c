/*
FreeRTOS+TCP V2.3.0
Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

 http://aws.amazon.com/freertos
 http://www.FreeRTOS.org
*/

/* FreeRTOS includes. */
#include "LPC54018.h"
#include "FreeRTOS.h"
#include "list.h"

#include <stdbool.h>

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"

#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"

#include "fsl_enet.h"
#include "fsl_phy.h"

#include "fsl_enet_mdio.h"
#include "fsl_phylan8720a.h"
#include "fsl_debug_console.h"


#define PHY_ADDRESS					   ( 0x00U )
/* MDIO operations. */
#define EXAMPLE_MDIO_OPS			   lpc_enet_ops
/* PHY operations. */
#define EXAMPLE_PHY_OPS				   phylan8720a_ops
#define ENET_RXBD_NUM				   ( 4 )
#define ENET_TXBD_NUM				   ( 4 )
#define ENET_RXBUFF_SIZE			   ( ENET_FRAME_MAX_FRAMELEN )
#define ENET_BuffSizeAlign( n )	   ENET_ALIGN( n, ENET_BUFF_ALIGNMENT )
#define ENET_ALIGN( x, align )	   ( ( unsigned int ) ( ( x ) + ( ( align ) - 1 ) ) & ( unsigned int ) ( ~( unsigned int ) ( ( align ) - 1 ) ) )
#define ENET_EXAMPLE_FRAME_HEADSIZE	   ( 14U )
#define ENET_EXAMPLE_DATA_LENGTH	   ( 1000U )
#define ENET_EXAMPLE_FRAME_SIZE		   ( ENET_EXAMPLE_DATA_LENGTH + ENET_EXAMPLE_FRAME_HEADSIZE )
#define ENET_EXAMPLE_PACKAGETYPE	   ( 4U )
#define ENET_EXAMPLE_LOOP_COUNT		   ( 20U )

#if defined( __GNUC__ )
	#ifndef __ALIGN_END
		#define __ALIGN_END    __attribute__( ( aligned( ENET_BUFF_ALIGNMENT ) ) )
	#endif
	#ifndef __ALIGN_BEGIN
		#define __ALIGN_BEGIN
	#endif
#else
	#ifndef __ALIGN_END
		#define __ALIGN_END
	#endif
	#ifndef __ALIGN_BEGIN
		#if defined( __CC_ARM ) || defined( __ARMCC_VERSION )
			#define __ALIGN_BEGIN    __attribute__( ( aligned( ENET_BUFF_ALIGNMENT ) ) )
		#elif defined( __ICCARM__ )
			#define __ALIGN_BEGIN
		#endif
	#endif
#endif /* if defined( __GNUC__ ) */

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
driver will filter incoming packets and only pass the stack those packets it
considers need processing. */
#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )	eProcessBuffer
#else
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )	eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/*******************************************************************************
 * Variables
 ******************************************************************************/
#if defined( __ICCARM__ )
	#pragma data_alignment = ENET_BUFF_ALIGNMENT
#endif
__ALIGN_BEGIN enet_rx_bd_struct_t g_rxBuffDescrip[ ENET_RXBD_NUM ] __ALIGN_END;
#if defined( __ICCARM__ )
	#pragma data_alignment = ENET_BUFF_ALIGNMENT
#endif
__ALIGN_BEGIN enet_tx_bd_struct_t g_txBuffDescrip[ ENET_TXBD_NUM ] __ALIGN_END;

enet_handle_t g_handle = { 0 };
/* The MAC address for ENET device. */
uint8_t g_macAddr[ 6 ] = { 0xd4, 0xbe, 0xd9, 0x45, 0x22, 0x60 };
uint8_t multicastAddr[ 6 ] = { 0x01, 0x00, 0x5e, 0x00, 0x01, 0x81 };
uint8_t g_frame[ ENET_EXAMPLE_PACKAGETYPE ][ ENET_EXAMPLE_FRAME_SIZE ];
uint8_t *g_txbuff[ ENET_TXBD_NUM ];
uint32_t g_txIdx = 0;
uint8_t g_txbuffIdx = 0;
uint8_t g_txCosumIdx = 0;
uint32_t g_testIdx = 0;
uint32_t g_rxIndex = 0;
uint32_t g_rxCheckIdx = 0;

/*! @brief Enet PHY and MDIO interface handler. */
static mdio_handle_t mdioHandle = { .ops = &EXAMPLE_MDIO_OPS };
static phy_handle_t phyHandle = { .phyAddr = PHY_ADDRESS, .mdioHandle = &mdioHandle, .ops = &EXAMPLE_PHY_OPS };

__ALIGN_BEGIN uint32_t receiveBuffer[ ENET_RXBD_NUM ][ ENET_RXBUFF_SIZE / sizeof( uint32_t ) + 1 ] __ALIGN_END;
uint32_t rxbuffer[ ENET_RXBD_NUM ];

TaskHandle_t receiveTaskHandle;

void ENET_IntCallback( ENET_Type *base,
					   enet_handle_t *handle,
					   enet_event_t event,
					   uint8_t channel,
					   void *param )
{
	switch( event )
	{
		case kENET_TxIntEvent:
			break;

		case kENET_RxIntEvent:
			vTaskNotifyGiveFromISR( receiveTaskHandle, NULL );
			break;

		default:
			break;
	}
}

static void rx_task( void *parameter )
{
uint32_t length;
NetworkBufferDescriptor_t *pxBufferDescriptor;
IPStackEvent_t xRxEvent;
status_t status;

	while( pdTRUE )
	{
		ulTaskNotifyTake( pdTRUE, portMAX_DELAY );

		BaseType_t receiving = pdTRUE;

		while( receiving == pdTRUE )
		{
			status = ENET_GetRxFrameSize( ENET, &g_handle, &length, 0 );

			switch( status )
			{
				case kStatus_Success: /* there is a frame.  process it */

					if( length )
					{
						pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( length, 0 );

						if( pxBufferDescriptor != NULL )
						{
							status = ENET_ReadFrame( ENET, &g_handle, pxBufferDescriptor->pucEthernetBuffer, length, 0 );
							pxBufferDescriptor->xDataLength = length;

							if( eConsiderFrameForProcessing( pxBufferDescriptor->pucEthernetBuffer ) == eProcessBuffer )
							{
								xRxEvent.eEventType = eNetworkRxEvent;
								xRxEvent.pvData = ( void * ) pxBufferDescriptor;

								if( xSendEventStructToIPTask( &xRxEvent, 0 ) == pdFALSE )
								{
									vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
									iptraceETHERNET_RX_EVENT_LOST();
								}
								else
								{
									/* Message successfully transfered to the stack */
								}
							}
							else
							{
								vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
								/* Not sure if a trace is required.  The stack did not want this message */
							}
						}
						else
						{
							/* No buffer available to receive this message */
							iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER();
						}
					}

					break;

				case kStatus_ENET_RxFrameEmpty: /* Received an empty frame.  Ignore it */
					receiving = pdFALSE;
					break;

				case kStatus_ENET_RxFrameError: /* Received an error frame.  Read & drop it */
					ENET_ReadFrame( ENET, &g_handle, NULL, 0, 0 );
					/* Not sure if a trace is required.  The MAC had an error and needed to dump bytes */
					break;
			}
		}
	}
}

BaseType_t xGetPhyLinkStatus( void )
{
bool link;

	PHY_GetLinkStatus( &phyHandle, &link );
	return link ? pdTRUE : pdFALSE;
}


BaseType_t xNetworkInterfaceInitialise( void )
{
enet_config_t config;
uint32_t refClock = 50000000;     /* 50MHZ for rmii reference clock. */
phy_speed_t speed;
phy_duplex_t duplex;
status_t status;
bool link = false;

phy_config_t phyConfig;

int bufferIndex;

	for( bufferIndex = 0; bufferIndex < ENET_RXBD_NUM; bufferIndex++ )
	{
		rxbuffer[ bufferIndex ] = ( uint32_t ) &receiveBuffer[ bufferIndex ];
	}

	phyConfig.phyAddr = PHY_ADDRESS;
	phyConfig.autoNeg = true;
	mdioHandle.resource.base = ENET;

	/* prepare the buffer configuration. */
	enet_buffer_config_t buffConfig[ 1 ] =
	{
		{
			ENET_RXBD_NUM, ENET_TXBD_NUM,
			&g_txBuffDescrip[ 0 ], &g_txBuffDescrip[ 0 ],
			&g_rxBuffDescrip[ 0 ], &g_rxBuffDescrip[ ENET_RXBD_NUM ],
			&rxbuffer[ 0 ], ENET_BuffSizeAlign( ENET_RXBUFF_SIZE ),
		}
	};

	while( !link )
	{
		status = PHY_Init( &phyHandle, &phyConfig );

		if( kStatus_Success == status )
		{
			PHY_GetLinkStatus( &phyHandle, &link );
		}
		else if( kStatus_PHY_AutoNegotiateFail == status )
		{
			PRINTF( "\r\nPHY Auto-negotiation failed. Please check the cable connection and link partner setting.\r\n" );
		}
		else
		{
			PRINTF( "\r\nUnknown PHY failure %d\r\n", status );
		}
	}

	PHY_GetLinkSpeedDuplex( &phyHandle, &speed, &duplex );

	/* Get default configuration 100M RMII. */
	ENET_GetDefaultConfig( &config );

	/* Use the actual speed and duplex when phy success to finish the autonegotiation. */
	config.miiSpeed = ( enet_mii_speed_t ) speed;
	config.miiDuplex = ( enet_mii_duplex_t ) duplex;

	/* Initialize ENET. */
	ENET_Init( ENET, &config, &g_macAddr[ 0 ], refClock );

	/* Enable the rx interrupt. */
	ENET_EnableInterrupts( ENET, ( kENET_DmaRx ) );

	/* Initialize Descriptor. */
	ENET_DescriptorInit( ENET, &config, &buffConfig[ 0 ] );

	/* Create the handler. */
	ENET_CreateHandler( ENET, &g_handle, &config, &buffConfig[ 0 ], ENET_IntCallback, NULL );
	NVIC_SetPriority( 65 - 16, 4 ); /* TODO this feels like a hack and I would expect a nice ENET API for priority. */

	/* Active TX/RX. */
	ENET_StartRxTx( ENET, 1, 1 );

	if( xTaskCreate( rx_task, "rx_task", 512, NULL, 5, &receiveTaskHandle ) != pdPASS )
	{
		PRINTF( "Network Receive Task creation failed!.\r\n" );

		while( 1 )
		{
		}
	}

	return pdTRUE;
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
									BaseType_t xReleaseAfterSend )
{
BaseType_t response = pdFALSE;
status_t status;

	if( xGetPhyLinkStatus() )
	{
		status = ENET_SendFrame( ENET, &g_handle, pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength );

		switch( status )
		{
			default: /* anything not Success will be a failure */
			case kStatus_ENET_TxFrameBusy:
				break;

			case kStatus_Success:
				iptraceNETWORK_INTERFACE_TRANSMIT();
				response = pdTRUE;
				break;
		}
	}

	if( xReleaseAfterSend != pdFALSE )
	{
		vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
	}

	return response;
}

/* statically allocate the buffers */
/* allocating them as uint32_t's to force them into word alignment, a requirement of the DMA. */
__ALIGN_BEGIN static uint32_t buffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ ( ipBUFFER_PADDING + ENET_RXBUFF_SIZE ) / sizeof( uint32_t ) + 1 ] __ALIGN_END;
void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
	for( int x = 0; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++ )
	{
		pxNetworkBuffers[ x ].pucEthernetBuffer = ( uint8_t * ) &buffers[ x ][ 0 ] + ipBUFFER_PADDING;
		buffers[ x ][ 0 ] = ( uint32_t ) &pxNetworkBuffers[ x ];
	}
}
