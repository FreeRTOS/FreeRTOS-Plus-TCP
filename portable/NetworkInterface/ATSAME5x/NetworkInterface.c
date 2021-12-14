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


/* This driver is made to work with Atmel START's ASF4 GMAC driver.
 * The START generated GMAC initialization code should be commented out,
 * since this driver will take care of initializing the GMAC peripheral itself.
 *
 * Optimal performance is obtained with:
 * - CRC offloading enabled for both RX and TX
 * - "Copy all frames" set to zero / off
 */

/* Atmel ASF includes */
#include "hal_mac_async.h"
#include "hpl_gmac_config.h"
/* Include MAC initialization function here: */
#include "driver_init.h"

/* FreeRTOS includes */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"
#include "phyHandling.h"



/***********************************************/
/*           Configuration variables           */
/***********************************************/

/* Check for optimal performance parameters */
#if ( CONF_GMAC_NCFGR_RXCOEN == 0 )
    #warning This driver works best with RX CRC offloading enabled.
#endif

#if ( CONF_GMAC_DCFGR_TXCOEN == 0 )
    #warning This driver works best with TX CRC offloading enabled.
#endif

#if ( CONF_GMAC_NCFGR_CAF != 0 )
    #warning This driver includes GMAC hardware frame filtering for better performance.
#endif


/* Make sure someone takes care of the CRC calculation */
#if ( ( CONF_GMAC_NCFGR_RXCOEN == 0 ) && ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 1 ) )
    #error Receive CRC offloading should be enabled.
#endif
#if ( ( CONF_GMAC_DCFGR_TXCOEN == 0 ) && ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 1 ) )
    #error Transmit CRC offloading should be enabled.
#endif

/* Setup LLMNR specific multicast address. */
#if ( defined( ipconfigUSE_LLMNR ) && ( ipconfigUSE_LLMNR == 1 ) )
    static const uint8_t ucLLMNR_MAC_address[] = { 0x01, 0x00, 0x5E, 0x00, 0x00, 0xFC };
#endif

/* Receive task refresh time */
#define RECEIVE_BLOCK_TIME_MS    100

/***********************************************/
/*              FreeRTOS variables             */
/***********************************************/

/* Copied from FreeRTOS_IP.c. Used for ICMP CRC calculation */
#define ipCORRECT_CRC    0xffffU

/* Also copied from FreeRTOS_IP.c */

/** @brief If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
 * driver will filter incoming packets and only pass the stack those packets it
 * considers need processing.  In this case ipCONSIDER_FRAME_FOR_PROCESSING() can
 * be #-defined away.  If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 0
 * then the Ethernet driver will pass all received packets to the stack, and the
 * stack must do the filtering itself.  In this case ipCONSIDER_FRAME_FOR_PROCESSING
 * needs to call eConsiderFrameForProcessing.
 */
#if ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#endif

/* Ethernet buffers for BufferAllocation_1.c scheme.
 * Set ipUSE_STATIC_ALLOCATION to 1 if using BufferAllocation_1.c,
 * otherwise to 0, to save RAM. From Iperf testing, there is no point in using
 * static allocation with a non zero-copy driver.
 */
#define ipUSE_STATIC_ALLOCATION    0
#if ( defined( ipUSE_STATIC_ALLOCATION ) && ( ipUSE_STATIC_ALLOCATION == 1 ) )

/* 1536 bytes is more than needed, 1524 would be enough.
 * But 1536 is a multiple of 32, which gives a great alignment for cached memories. */
    #define NETWORK_BUFFER_SIZE    1536
    static uint8_t ucBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ NETWORK_BUFFER_SIZE ];
#endif /* ( defined( ipUSE_STATIC_ALLOCATION ) && ( ipUSE_STATIC_ALLOCATION == 1 )) */


/* Holds the handle of the task used as a deferred interrupt processor.  The
 * handle is used so direct notifications can be sent to the task for all EMAC/DMA
 * related interrupts. */
TaskHandle_t xEMACTaskHandle = NULL;

/* The PING response queue */
#if ( defined( ipconfigSUPPORT_OUTGOING_PINGS ) && ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) )
    QueueHandle_t xPingReplyQueue = NULL;
#endif

/* GMAC interrupt callbacks. */
void xRxCallback( void );
static void prvEMACDeferredInterruptHandlerTask( void * pvParameters );

/***********************************************/
/*                GMAC variables               */
/***********************************************/

/* The Ethernet MAC instance created by ASF4 */
extern struct mac_async_descriptor ETH_MAC;

static void prvGMACInit( void );

/* Enable/Disable MDC and MDIO ports for PHY register management. */
static inline void prvGMACEnablePHYManagementPort( bool enable );

/* GMAC registers configuration functions. */
static inline void prvGMACEnable100Mbps( bool enable );
static inline void prvGMACEnableFullDuplex( bool enable );


/***********************************************/
/*                PHY variables                */
/***********************************************/

/* All PHY handling code has now been separated from the NetworkInterface.c,
 * see "../Common/phyHandling.c". */
static EthernetPhy_t xPhyObject;

/* PHY link preferences. */
/* Set both speed and Duplex to AUTO, or give them BOTH manual values. */
const PhyProperties_t xPHYProperties =
{
    .ucSpeed  = PHY_SPEED_AUTO,
    .ucDuplex = PHY_DUPLEX_AUTO,
    .ucMDI_X  = PHY_MDIX_AUTO,
};

static void prvPHYLinkReset( void );
static void prvPHYInit( void );
static inline bool bPHYGetLinkStatus( void );

/* PHY read and write functions. */
static BaseType_t xPHYRead( BaseType_t xAddress,
                            BaseType_t xRegister,
                            uint32_t * pulValue );
static BaseType_t xPHYWrite( BaseType_t xAddress,
                             BaseType_t xRegister,
                             uint32_t pulValue );


/*********************************************************************/
/*                      FreeRTOS+TCP functions                       */
/*********************************************************************/

BaseType_t xNetworkInterfaceInitialise( void )
{
    /*
     * Perform the hardware specific network initialization here.  Typically
     * that will involve using the Ethernet driver library to initialize the
     * Ethernet (or other network) hardware, initialize DMA descriptors, and
     * perform a PHY auto-negotiation to obtain a network link. */

    if( xEMACTaskHandle == NULL )
    {
        /* Initialize MAC and PHY */
        prvGMACInit();
        prvPHYInit();

        /* (Re)set PHY link */
        prvPHYLinkReset();

        /* Initialize PING capability */
        #if ( defined( ipconfigSUPPORT_OUTGOING_PINGS ) && ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) )
            xPingReplyQueue = xQueueCreate( ipconfigPING_QUEUE_SIZE, sizeof( uint16_t ) );
        #endif

        /* Create event handler task */
        xTaskCreate( prvEMACDeferredInterruptHandlerTask, /* Function that implements the task. */
                     "EMACInt",                           /* Text name for the task. */
                     256,                                 /* Stack size in words, not bytes. */
                     ( void * ) 1,                        /* Parameter passed into the task. */
                     configMAX_PRIORITIES - 1,            /* Priority at which the task is created. */
                     &xEMACTaskHandle );                  /* Used to pass out the created task's handle. */

        configASSERT( xEMACTaskHandle );
    }

    return bPHYGetLinkStatus();
}


static void prvEMACDeferredInterruptHandlerTask( void * pvParameters )
{
    NetworkBufferDescriptor_t * pxBufferDescriptor;
    size_t xBytesReceived = 0, xBytesRead = 0;

    uint16_t xICMPChecksumResult = ipCORRECT_CRC;
    const IPPacket_t * pxIPPacket;


    /* Used to indicate that xSendEventStructToIPTask() is being called because
     * of an Ethernet receive event. */
    IPStackEvent_t xRxEvent;

    for( ; ; )
    {
        /* Wait for the Ethernet MAC interrupt to indicate that another packet
         * has been received.  The task notification is used in a similar way to a
         * counting semaphore to count Rx events, but is a lot more efficient than
         * a semaphore. */
        ulTaskNotifyTake( pdFALSE, pdMS_TO_TICKS( RECEIVE_BLOCK_TIME_MS ) );

        /* See how much data was received.  Here it is assumed ReceiveSize() is
         * a peripheral driver function that returns the number of bytes in the
         * received Ethernet frame. */
        xBytesReceived = mac_async_read_len( &ETH_MAC );

        if( xBytesReceived > 0 )
        {
            /* Allocate a network buffer descriptor that points to a buffer
             * large enough to hold the received frame.  As this is the simple
             * rather than efficient example the received data will just be copied
             * into this buffer. */
            pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( xBytesReceived, 0 );

            if( pxBufferDescriptor != NULL )
            {
                /* pxBufferDescriptor->pucEthernetBuffer now points to an Ethernet
                 * buffer large enough to hold the received data.  Copy the
                 * received data into pcNetworkBuffer->pucEthernetBuffer.  Here it
                 * is assumed ReceiveData() is a peripheral driver function that
                 * copies the received data into a buffer passed in as the function's
                 * parameter.  Remember! While is is a simple robust technique -
                 * it is not efficient.  An example that uses a zero copy technique
                 * is provided further down this page. */
                xBytesRead = mac_async_read( &ETH_MAC, pxBufferDescriptor->pucEthernetBuffer, xBytesReceived );
                pxBufferDescriptor->xDataLength = xBytesRead;


                #if ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 1 )
                    {
                        /* the Atmel SAM GMAC peripheral does not support hardware CRC offloading for ICMP packets.
                         * It must therefore be implemented in software. */
                        pxIPPacket = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( IPPacket_t, pxBufferDescriptor->pucEthernetBuffer );

                        if( pxIPPacket->xIPHeader.ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP )
                        {
                            xICMPChecksumResult = usGenerateProtocolChecksum( pxBufferDescriptor->pucEthernetBuffer, pxBufferDescriptor->xDataLength, pdFALSE );
                        }
                        else
                        {
                            xICMPChecksumResult = ipCORRECT_CRC; /* Reset the result value in case this is not an ICMP packet. */
                        }
                    }
                #endif /* if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 1 ) */

                /* See if the data contained in the received Ethernet frame needs
                * to be processed.  NOTE! It is preferable to do this in
                * the interrupt service routine itself, which would remove the need
                * to unblock this task for packets that don't need processing. */
                if( ( ipCONSIDER_FRAME_FOR_PROCESSING( pxBufferDescriptor->pucEthernetBuffer ) == eProcessBuffer ) &&
                    ( xICMPChecksumResult == ipCORRECT_CRC ) )
                {
                    /* The event about to be sent to the TCP/IP is an Rx event. */
                    xRxEvent.eEventType = eNetworkRxEvent;

                    /* pvData is used to point to the network buffer descriptor that
                     * now references the received data. */
                    xRxEvent.pvData = ( void * ) pxBufferDescriptor;

                    /* Send the data to the TCP/IP stack. */
                    if( xSendEventStructToIPTask( &xRxEvent, 0 ) == pdFALSE )
                    {
                        /* The buffer could not be sent to the IP task so the buffer
                         * must be released. */
                        vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );

                        /* Make a call to the standard trace macro to log the
                         * occurrence. */
                        iptraceETHERNET_RX_EVENT_LOST();
                    }
                    else
                    {
                        /* The message was successfully sent to the TCP/IP stack.
                        * Call the standard trace macro to log the occurrence. */
                        iptraceNETWORK_INTERFACE_RECEIVE();
                    }
                }
                else
                {
                    /* The Ethernet frame can be dropped, but the Ethernet buffer
                     * must be released. */
                    vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
                }
            }
            else
            {
                /* The event was lost because a network buffer was not available.
                 * Call the standard trace macro to log the occurrence. */
                iptraceETHERNET_RX_EVENT_LOST();
            }
        }

        prvGMACEnablePHYManagementPort( true );

        if( xPhyCheckLinkStatus( &xPhyObject, xBytesReceived ) )
        {
            prvPHYLinkReset();
        }

        prvGMACEnablePHYManagementPort( false );
    }
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor,
                                    BaseType_t xReleaseAfterSend )
{
    /* Simple network interfaces (as opposed to more efficient zero copy network
     * interfaces) just use Ethernet peripheral driver library functions to copy
     * data from the FreeRTOS+TCP buffer into the peripheral driver's own buffer.
     * This example assumes SendData() is a peripheral driver library function that
     * takes a pointer to the start of the data to be sent and the length of the
     * data to be sent as two separate parameters.  The start of the data is located
     * by pxDescriptor->pucEthernetBuffer.  The length of the data is located
     * by pxDescriptor->xDataLength. */

    if( bPHYGetLinkStatus() )
    {
        #if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 1 )
            {
                /* the Atmel SAM GMAC peripheral does not support hardware CRC offloading for ICMP packets.
                 * It must therefore be implemented in software. */
                const IPPacket_t * pxIPPacket = ipCAST_CONST_PTR_TO_CONST_TYPE_PTR( IPPacket_t, pxDescriptor->pucEthernetBuffer );

                if( pxIPPacket->xIPHeader.ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP )
                {
                    ( void ) usGenerateProtocolChecksum( pxDescriptor->pucEthernetBuffer, pxDescriptor->xDataLength, pdTRUE );
                }
            }
        #endif

        mac_async_write( &ETH_MAC, pxDescriptor->pucEthernetBuffer, pxDescriptor->xDataLength );

        /* Call the standard trace macro to log the send event. */
        iptraceNETWORK_INTERFACE_TRANSMIT();
    }

    if( xReleaseAfterSend != pdFALSE )
    {
        /* It is assumed SendData() copies the data out of the FreeRTOS+TCP Ethernet
         * buffer.  The Ethernet buffer is therefore no longer needed, and must be
         * freed for re-use. */
        vReleaseNetworkBufferAndDescriptor( pxDescriptor );
    }

    return pdTRUE;
}

void xRxCallback( void )
{
    vTaskNotifyGiveFromISR( xEMACTaskHandle, 0 );
}

#if ( defined( ipUSE_STATIC_ALLOCATION ) && ( ipUSE_STATIC_ALLOCATION == 1 ) )

/* Next provide the vNetworkInterfaceAllocateRAMToBuffers() function, which
 * simply fills in the pucEthernetBuffer member of each descriptor. */
    void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
    {
        BaseType_t x;

        for( x = 0; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++ )
        {
            /* pucEthernetBuffer is set to point ipBUFFER_PADDING bytes in from the
             * beginning of the allocated buffer. */
            pxNetworkBuffers[ x ].pucEthernetBuffer = &( ucBuffers[ x ][ ipBUFFER_PADDING ] );

            /* The following line is also required, but will not be required in
             * future versions. */
            *( ( uint32_t * ) &ucBuffers[ x ][ 0 ] ) = ( uint32_t ) &( pxNetworkBuffers[ x ] );
        }
    }
#endif /* ( defined( ipUSE_STATIC_ALLOCATION ) && ( ipUSE_STATIC_ALLOCATION == 1 )) */


/*********************************************************************/
/*                          GMAC functions                           */
/*********************************************************************/

/* Initializes the GMAC peripheral. This function is based on ASF4 GMAC initialization
 * and uses the Atmel START- generated code, typically located in "driver_init.h".
 * Make sure the initialization function is not called twice, e.g. comment out the call in "driver_init.c".
 * It is compatible with modifications made in Atmel START afterwards because the
 * configuration is saved in "hpl_gmac_config.h". */
static void prvGMACInit()
{
    /* Call MAC initialization function here: */
    vGMACInit();
    prvGMACEnablePHYManagementPort( false );
    mac_async_disable_irq( &ETH_MAC );

    /* Set GMAC Filtering for own MAC address */
    struct mac_async_filter mac_filter;
    memcpy( mac_filter.mac, ipLOCAL_MAC_ADDRESS, ipMAC_ADDRESS_LENGTH_BYTES );
    mac_filter.tid_enable = false;
    mac_async_set_filter( &ETH_MAC, 0, &mac_filter );

    /* Set GMAC filtering for LLMNR, if defined. */
    #if ( defined( ipconfigUSE_LLMNR ) && ( ipconfigUSE_LLMNR == 1 ) )
        {
            memcpy( mac_filter.mac, ucLLMNR_MAC_address, ipMAC_ADDRESS_LENGTH_BYTES );
            /* LLMNR requires responders to listen to both TCP and UDP protocols. */
            mac_filter.tid_enable = false;
            mac_async_set_filter( &ETH_MAC, 1, &mac_filter );
        }
    #endif

    /* Set GMAC interrupt priority to be compatible with FreeRTOS API */
    NVIC_SetPriority( GMAC_IRQn, configMAX_SYSCALL_INTERRUPT_PRIORITY >> ( 8 - configPRIO_BITS ) );

    /* Register callback(s). Currently only RX callback is implemented, but TX callback can be added the same way. */
    mac_async_register_callback( &ETH_MAC, MAC_ASYNC_RECEIVE_CB, ( FUNC_PTR ) xRxCallback );

    /* Start the GMAC. */
    mac_async_enable( &ETH_MAC );
    mac_async_enable_irq( &ETH_MAC );
}

static inline void prvGMACEnablePHYManagementPort( bool enable )
{
    if( enable )
    {
        ( ( Gmac * ) ETH_MAC.dev.hw )->NCR.reg |= GMAC_NCR_MPE;
    }
    else
    {
        ( ( Gmac * ) ETH_MAC.dev.hw )->NCR.reg &= ~GMAC_NCR_MPE;
    }
}

static inline void prvGMACEnable100Mbps( bool enable )
{
    if( enable )
    {
        ( ( Gmac * ) ETH_MAC.dev.hw )->NCFGR.reg |= GMAC_NCFGR_SPD;
    }
    else
    {
        ( ( Gmac * ) ETH_MAC.dev.hw )->NCFGR.reg &= ~GMAC_NCFGR_SPD;
    }
}

static inline void prvGMACEnableFullDuplex( bool enable )
{
    if( enable )
    {
        ( ( Gmac * ) ETH_MAC.dev.hw )->NCFGR.reg |= GMAC_NCFGR_FD;
    }
    else
    {
        ( ( Gmac * ) ETH_MAC.dev.hw )->NCFGR.reg &= ~GMAC_NCFGR_FD;
    }
}


/*********************************************************************/
/*                           PHY functions                           */
/*********************************************************************/

/* Initializes the PHY hardware. Based on ASF4 generated code. */
static void prvPHYInit()
{
    prvGMACEnablePHYManagementPort( true );

    vPhyInitialise( &xPhyObject, &xPHYRead, &xPHYWrite );
    xPhyDiscover( &xPhyObject );
    xPhyConfigure( &xPhyObject, &xPHYProperties );

    prvGMACEnablePHYManagementPort( false );
}

/* Start a new link negotiation on the PHY and wait until link is up. */
static void prvPHYLinkReset()
{
    /* Restart an auto-negotiation */
    prvGMACEnablePHYManagementPort( true );

    if( ( xPHYProperties.ucDuplex == PHY_DUPLEX_AUTO ) && ( xPHYProperties.ucSpeed == PHY_SPEED_AUTO ) && ( xPHYProperties.ucMDI_X == PHY_MDIX_AUTO ) )
    {
        /* Auto-negotiation */
        xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) );

        /* Update the MAC with the auto-negotiation result parameters. */
        prvGMACEnableFullDuplex( xPhyObject.xPhyProperties.ucDuplex == PHY_DUPLEX_FULL );
        prvGMACEnable100Mbps( xPhyObject.xPhyProperties.ucSpeed == PHY_SPEED_100 );
    }
    else
    {
        /* Fixed values */
        xPhyObject.xPhyPreferences.ucDuplex = xPHYProperties.ucDuplex;
        xPhyObject.xPhyPreferences.ucSpeed = xPHYProperties.ucSpeed;
        xPhyObject.xPhyPreferences.ucMDI_X = xPHYProperties.ucMDI_X;
        xPhyFixedValue( &xPhyObject, xPhyGetMask( &xPhyObject ) );

        /* Update the MAC with the auto-negotiation result parameters. */
        prvGMACEnableFullDuplex( xPHYProperties.ucDuplex == PHY_DUPLEX_FULL );
        prvGMACEnable100Mbps( xPHYProperties.ucSpeed == PHY_SPEED_100 );
    }

    prvGMACEnablePHYManagementPort( false );
}

static BaseType_t xPHYRead( BaseType_t xAddress,
                            BaseType_t xRegister,
                            uint32_t * pulValue )
{
    prvGMACEnablePHYManagementPort( true );
    BaseType_t readStatus = mac_async_read_phy_reg( &ETH_MAC, xAddress, xRegister, ( ( uint16_t * ) pulValue ) );
    prvGMACEnablePHYManagementPort( false );
    return readStatus;
}

static BaseType_t xPHYWrite( BaseType_t xAddress,
                             BaseType_t xRegister,
                             uint32_t pulValue )
{
    prvGMACEnablePHYManagementPort( true );
    BaseType_t writeStatus = mac_async_write_phy_reg( &ETH_MAC, xAddress, xRegister, pulValue );
    prvGMACEnablePHYManagementPort( false );
    return writeStatus;
}

static inline bool bPHYGetLinkStatus( void )
{
    return( xPhyObject.ulLinkStatusMask != 0 );
}
