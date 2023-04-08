/*
 * FreeRTOS V202012.00
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/*
 * This project is a cut down version of the project described on the following
 * link.  Only the simple UDP client and server and the TCP echo clients are
 * included in the build:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html
 */

/* Standard includes. */
#include <stdio.h>
#include <time.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_Routing.h"
#if ( ipconfigMULTI_INTERFACE == 1 )
    #include "FreeRTOS_ND.h"
#endif

/* Define a name that will be used for LLMNR and NBNS searches. */
#define mainHOST_NAME                   "TCPDemo"
#define mainDEVICE_NICK_NAME            "windows_multi_interface_demo"

/* Second set of IP address to be used by this demo. */
#define configIP2_ADDR0                 10
#define configIP2_ADDR1                 0
#define configIP2_ADDR2                 1
#define configIP2_ADDR3                 6

#define democonfigCLASS_A_IP_ADDRESS    "10.0.1.10"
#define democonfigCLASS_C_IP_ADDRESS    "192.168.0.1"

#define democonfigPING_COUNT            10

/*
 * Just seeds the simple pseudo random number generator.
 */
static void prvSRand( UBaseType_t ulSeed );

/*
 * Miscellaneous initialisation including preparing the logging and seeding the
 * random number generator.
 */
static void prvMiscInitialisation( void );

/* Two sets of default IP and MAC address used by the demo. The address configuration
 * defined here will be used if ipconfigUSE_DHCP is 0, or if ipconfigUSE_DHCP is
 * 1 but a DHCP server could not be contacted.  See the online documentation for
 * more information. */
/* First set of the IP configuration. */
static const uint8_t ucIPAddress[ 4 ] = { configIP1_ADDR0, configIP1_ADDR1, configIP1_ADDR2, configIP1_ADDR3 };
static const uint8_t ucNetMask[ 4 ] = { configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3 };
static const uint8_t ucGatewayAddress[ 4 ] = { configGATEWAY_ADDR0, configGATEWAY_ADDR1, configGATEWAY_ADDR2, configGATEWAY_ADDR3 };
static const uint8_t ucDNSServerAddress[ 4 ] = { configDNS_SERVER_ADDR0, configDNS_SERVER_ADDR1, configDNS_SERVER_ADDR2, configDNS_SERVER_ADDR3 };

/* Second set of the IP configuration. */
static const uint8_t ucIPAddress2[ 4 ] = { configIP2_ADDR0, configIP2_ADDR1, configIP2_ADDR2, configIP2_ADDR3 };
static const uint8_t ucNetMask2[ 4 ] = { configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3 };
/* No gateway on this network. */
static const uint8_t ucGatewayAddress2[ 4 ] = { 0, 0, 0, 0 };
/* No DNS server on this network. */
static const uint8_t ucDNSServerAddress2[ 4 ] = { 0, 0, 0, 0 };

/* Set the following constant to pdTRUE to log using the method indicated by the
 * name of the constant, or pdFALSE to not log using the method indicated by the
 * name of the constant.  Options include to standard out (xLogToStdout), to a disk
 * file (xLogToFile), and to a UDP port (xLogToUDP).  If xLogToUDP is set to pdTRUE
 * then UDP messages are sent to the IP address configured as the echo server
 * address (see the configECHO_SERVER_ADDR0 definitions in FreeRTOSConfig.h) and
 * the port number set by configPRINT_PORT in FreeRTOSConfig.h. */
const BaseType_t xLogToStdout = pdTRUE, xLogToFile = pdFALSE, xLogToUDP = pdFALSE;


/* Default MAC address configuration. The demo creates a virtual network
 * connection that uses this MAC address by accessing the raw Ethernet data
 * to and from a real network connection on the host PC. See the
 * configNETWORK_INTERFACE_TO_USE definition for information on how to configure
 * the real network connection to use. */
const uint8_t ucMACAddress[ 6 ] = { configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5 };

/* Use by the pseudo random number generator. */
static UBaseType_t ulNextRand;

/*-----------------------------------------------------------*/

#if ( ipconfigMULTI_INTERFACE == 1 ) && ( ipconfigCOMPATIBLE_WITH_SINGLE == 0 )

/* In case multiple interfaces are used, define them statically as they must
 * continue to exist throughout the code execution. */

/* With WinPCap there is only 1 physical interface. */
    static NetworkInterface_t xInterfaces[ 1 ];

/* The demo will have two end-points. */
    static NetworkEndPoint_t xEndPoints[ 2 ];

/* A function from NetworkInterface.c to initialise the interface descriptor
 * of type 'NetworkInterface_t'. */
    NetworkInterface_t * xWinPcap_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                           NetworkInterface_t * pxInterface );
#endif /* ipconfigMULTI_INTERFACE */
/*-----------------------------------------------------------*/

TaskHandle_t xDemoTaskHandleA, xDemoTaskHandleC;
BaseType_t xTotalIterations = 0, xTotalFailures = 0, xTotalSuccess = 0;
SemaphoreHandle_t xDemoSemphr;


void vDemoTask_PingClassA( void * pvParameters )
{
    uint32_t ulClassAIPAddr;
    uint32_t xPingCounter = 0;

    /* Just to avoid compiler warning about unused parameter. */
    ( void ) pvParameters;

    FreeRTOS_inet_pton( FREERTOS_AF_INET, democonfigCLASS_A_IP_ADDRESS, &ulClassAIPAddr );

    for( ; ; )
    {
        /* Send a ping to Class-A IP address. */
        FreeRTOS_SendPingRequest( ulClassAIPAddr, 32, 5000 );

        /* Sleep for half second. */
        vTaskDelay( pdMS_TO_TICKS( 500 ) );

        /* Increment the number of pings sent. */
        xPingCounter++;

        /* Send only democonfigPING_COUNT number of pings. */
        if( xPingCounter > democonfigPING_COUNT )
        {
            break;
        }
    }

    xSemaphoreGive( xDemoSemphr );

    /* Delete the demo task. */
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

void vDemoTask_PingClassC( void * pvParameters )
{
    uint32_t ulClassCIPAddr;
    uint32_t xPingCounter = 0;

    /* Just to avoid compiler warning about unused parameter. */
    ( void ) pvParameters;

    FreeRTOS_inet_pton( FREERTOS_AF_INET, democonfigCLASS_C_IP_ADDRESS, &ulClassCIPAddr );

    for( ; ; )
    {
        /* Send a ping to Class-C IP address. */
        FreeRTOS_SendPingRequest( ulClassCIPAddr, 32, 5000 );

        /* Sleep for half second. */
        vTaskDelay( pdMS_TO_TICKS( 500 ) );

        /* Increment the number of pings sent. */
        xPingCounter++;

        /* Send only democonfigPING_COUNT number of pings. */
        if( xPingCounter > democonfigPING_COUNT )
        {
            break;
        }
    }

    xSemaphoreGive( xDemoSemphr );

    /* Delete the demo task. */
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/
void vCreateDemoTasks( BaseType_t xIsClassA )
{
    static BaseType_t xClassADemoTaskCreated = pdFALSE, xClassCDemoTaskCreated = pdFALSE;

    if( ( xIsClassA == pdTRUE ) && ( xClassADemoTaskCreated == pdFALSE ) )
    {
        xTaskCreate( vDemoTask_PingClassA, "DemoTaskA", configMINIMAL_STACK_SIZE * 2, NULL, configMAX_PRIORITIES - 3, &xDemoTaskHandleA );
        xClassADemoTaskCreated = pdTRUE;
    }
    else if( ( xIsClassA != pdTRUE ) && ( xClassCDemoTaskCreated == pdFALSE ) )
    {
        xTaskCreate( vDemoTask_PingClassC, "DemoTaskC", configMINIMAL_STACK_SIZE * 2, NULL, configMAX_PRIORITIES - 3, &xDemoTaskHandleC );
        xClassCDemoTaskCreated = pdTRUE;
    }
}


void vDemoStatusTask( void * pvParameters )
{
    /* Task to print demo status. */

    xSemaphoreTake( xDemoSemphr, portMAX_DELAY );
    xSemaphoreTake( xDemoSemphr, portMAX_DELAY );

    /* Wait for any pending ping reply. */
    vTaskDelay( pdMS_TO_TICKS( 2000 ) );

    if( democonfigPING_COUNT * 2 <= xTotalSuccess )
    {
        FreeRTOS_printf( ( "=================== Demo completed successfully ====================\r\n" ) );
        FreeRTOS_printf( ( "%d Pings sent ---> %d Received\r\n", democonfigPING_COUNT * 2, xTotalSuccess ) );
    }
    else
    {
        FreeRTOS_printf( ( "=================== Demo failed ===================\r\n" ) );
        FreeRTOS_printf( ( "%d Pings sent ---> %d Received\r\n", democonfigPING_COUNT * 2, xTotalSuccess ) );
    }

    vTaskDelete( NULL );
}

int main( void )
{
    /* Variable to declare 'sleep time' in worst case. */
    const uint32_t ulLongTime_ms = pdMS_TO_TICKS( 1000UL );
    NetworkInterface_t * pxWinPCapInterface = &( xInterfaces[ 0 ] );
    BaseType_t xIPTaskStarted;

    /*
     * Instructions for using this project are provided on:
     * TODO: add link.
     */

    /* Miscellaneous initialisation including seeding the random number
     * generator, creating a semaphore for the demo and creating the demo
     * status task. */
    prvMiscInitialisation();

    /* Initialise the interface descriptor for WinPCap. 'xInterfaces[ 0 ]' will
     * now hold all the information for WinPCap driver. */
    pxWinPCapInterface = xWinPcap_FillInterfaceDescriptor( 0, pxWinPCapInterface );


    /* Fill in the details of the first endpoint. */
    FreeRTOS_FillEndPoint( pxWinPCapInterface,
                           &( xEndPoints[ 0 ] ),
                           ucIPAddress,
                           ucNetMask,
                           ucGatewayAddress,
                           ucDNSServerAddress,
                           ucMACAddress );

    /* Fill in the details of the second endpoint. */
    FreeRTOS_FillEndPoint( pxWinPCapInterface,
                           &( xEndPoints[ 1 ] ),
                           ucIPAddress2,
                           ucNetMask2,
                           ucGatewayAddress2,
                           ucDNSServerAddress2,
                           ucMACAddress );

    /* Initialise the network interface.
     *
     ***NOTE*** Tasks that use the network are created in the network event hook
     * when the network is connected and ready for use (see the definition of
     * vApplicationIPNetworkEventHook() below).  The address values passed in here
     * are used if ipconfigUSE_DHCP is set to 0, or if ipconfigUSE_DHCP is set to 1
     * but a DHCP server cannot be	contacted. */
    FreeRTOS_debug_printf( ( "FreeRTOS_IPInit\r\n" ) );
    xIPTaskStarted = FreeRTOS_IPStart();

    if( xIPTaskStarted != pdTRUE )
    {
        FreeRTOS_printf( ( "IP Task not created\r\n" ) );
    }

    /* Start the RTOS scheduler. */
    FreeRTOS_debug_printf( ( "vTaskStartScheduler\r\n" ) );
    vTaskStartScheduler();

    /* If all is well, the scheduler will now be running, and the following
     * line will never be reached.  If the following line does execute, then
     * there was insufficient FreeRTOS heap memory available for the idle and/or
     * timer tasks	to be created.  See the memory management section on the
     * FreeRTOS web site for more details (this is standard text that is not not
     * really applicable to the Win32 simulator port). */
    for( ; ; )
    {
        Sleep( ulLongTime_ms );
    }
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
    const uint32_t ulMSToSleep = 1;

    /* This is just a trivial example of an idle hook.  It is called on each
     * cycle of the idle task if configUSE_IDLE_HOOK is set to 1 in
     * FreeRTOSConfig.h.  It must *NOT* attempt to block.  In this case the
     * idle task just sleeps to lower the CPU usage. */
    Sleep( ulMSToSleep );
}
/*-----------------------------------------------------------*/

void vAssertCalled( const char * pcFile,
                    uint32_t ulLine )
{
    const uint32_t ulLongSleep = 1000UL;
    volatile uint32_t ulBlockVariable = 0UL;
    volatile char * pcFileName = ( volatile char * ) pcFile;
    volatile uint32_t ulLineNumber = ulLine;

    ( void ) pcFileName;
    ( void ) ulLineNumber;

    FreeRTOS_debug_printf( ( "vAssertCalled( %s, %ld\r\n", pcFile, ulLine ) );

    /* Setting ulBlockVariable to a non-zero value in the debugger will allow
     * this function to be exited. */
    taskDISABLE_INTERRUPTS();
    {
        while( ulBlockVariable == 0UL )
        {
            Sleep( ulLongSleep );
        }
    }
    taskENABLE_INTERRUPTS();
}
/*-----------------------------------------------------------*/

/* Called by FreeRTOS+TCP when the network connects or disconnects. Disconnect
 * events are only received if implemented in the MAC driver. */
void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent,
                                     NetworkEndPoint_t * pxEndPoint )
{
    uint32_t ulIPAddress, ulNetMask, ulGatewayAddress, ulDNSServerAddress;
    char cBuffer[ 16 ];
    BaseType_t xIsClassA;

    /* If the network has just come up...*/
    if( eNetworkEvent == eNetworkUp )
    {
        if( memcmp( &( pxEndPoint->ipv4_defaults.ulIPAddress ), ucIPAddress, sizeof( ucIPAddress ) ) == 0 )
        {
            xIsClassA = pdTRUE;
        }
        else
        {
            xIsClassA = pdFALSE;
        }

        vCreateDemoTasks( xIsClassA );

        /* Print out the network configuration, which may have come from a DHCP
         * server. */
        FreeRTOS_GetEndPointConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress, pxEndPoint );
        FreeRTOS_inet_ntoa( ulIPAddress, cBuffer );
        FreeRTOS_printf( ( "\r\n\r\nIP Address: %s\r\n", cBuffer ) );

        FreeRTOS_inet_ntoa( ulNetMask, cBuffer );
        FreeRTOS_printf( ( "Subnet Mask: %s\r\n", cBuffer ) );

        FreeRTOS_inet_ntoa( ulGatewayAddress, cBuffer );
        FreeRTOS_printf( ( "Gateway Address: %s\r\n", cBuffer ) );

        FreeRTOS_inet_ntoa( ulDNSServerAddress, cBuffer );
        FreeRTOS_printf( ( "DNS Server Address: %s\r\n\r\n\r\n", cBuffer ) );
    }
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
    /* Called if a call to pvPortMalloc() fails because there is insufficient
     * free memory available in the FreeRTOS heap.  pvPortMalloc() is called
     * internally by FreeRTOS API functions that create tasks, queues, software
     * timers, and semaphores.  The size of the FreeRTOS heap is set by the
     * configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */
    vAssertCalled( __FILE__, __LINE__ );
}
/*-----------------------------------------------------------*/

UBaseType_t uxRand( void )
{
    const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL;

    /* Utility function to generate a pseudo random number. */

    ulNextRand = ( ulMultiplier * ulNextRand ) + ulIncrement;
    return( ( int ) ( ulNextRand >> 16UL ) & 0x7fffUL );
}
/*-----------------------------------------------------------*/

static void prvSRand( UBaseType_t ulSeed )
{
    /* Utility function to seed the pseudo random number generator. */
    ulNextRand = ulSeed;
}
/*-----------------------------------------------------------*/

static void prvMiscInitialisation( void )
{
    time_t xTimeNow;
    uint32_t ulLoggingIPAddress;

    ulLoggingIPAddress = FreeRTOS_inet_addr_quick( configECHO_SERVER_ADDR0, configECHO_SERVER_ADDR1, configECHO_SERVER_ADDR2, configECHO_SERVER_ADDR3 );
    /* Initialise the logging. */
    vLoggingInit( xLogToStdout, xLogToFile, xLogToUDP, ulLoggingIPAddress, configPRINT_PORT );

    /* Seed the random number generator. */
    time( &xTimeNow );
    FreeRTOS_debug_printf( ( "Seed for randomiser: %lu\r\n", xTimeNow ) );
    prvSRand( ( uint32_t ) xTimeNow );
    FreeRTOS_debug_printf( ( "First four random numbers: %08X %08X %08X %08X\r\n", ipconfigRAND32(), ipconfigRAND32(), ipconfigRAND32(), ipconfigRAND32() ) );

    /* Create a counting semaphore. Max count = 2. */
    xDemoSemphr = xSemaphoreCreateCounting( 2, 0 );

    /* Create the demo status task. */
    xTaskCreate( vDemoStatusTask, "DemoStatusTask", 5000, NULL, tskIDLE_PRIORITY + 1, &xDemoTaskHandleC );
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) || ( ipconfigDHCP_REGISTER_HOSTNAME == 1 )

    const char * pcApplicationHostnameHook( void )
    {
        /* Assign the name "FreeRTOS" to this network node.  This function will
         * be called during the DHCP: the machine will be registered with an IP
         * address plus this name. */
        return mainHOST_NAME;
    }

#endif
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 )

    BaseType_t xApplicationDNSQueryHook( const char * pcName )
    {
        BaseType_t xReturn;

        /* Determine if a name lookup is for this node.  Two names are given
         * to this node: that returned by pcApplicationHostnameHook() and that set
         * by mainDEVICE_NICK_NAME. */
        if( _stricmp( pcName, pcApplicationHostnameHook() ) == 0 )
        {
            xReturn = pdPASS;
        }
        else if( _stricmp( pcName, mainDEVICE_NICK_NAME ) == 0 )
        {
            xReturn = pdPASS;
        }
        else
        {
            xReturn = pdFAIL;
        }

        return xReturn;
    }

#endif /* if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) */

/*
 * Callback that provides the inputs necessary to generate a randomized TCP
 * Initial Sequence Number per RFC 6528.  THIS IS ONLY A DUMMY IMPLEMENTATION
 * THAT RETURNS A PSEUDO RANDOM NUMBER SO IS NOT INTENDED FOR USE IN PRODUCTION
 * SYSTEMS.
 */
extern uint32_t ulApplicationGetNextSequenceNumber( uint32_t ulSourceAddress,
                                                    uint16_t usSourcePort,
                                                    uint32_t ulDestinationAddress,
                                                    uint16_t usDestinationPort )
{
    ( void ) ulSourceAddress;
    ( void ) usSourcePort;
    ( void ) ulDestinationAddress;
    ( void ) usDestinationPort;

    return uxRand();
}

/*
 * Supply a random number to FreeRTOS+TCP stack.
 * THIS IS ONLY A DUMMY IMPLEMENTATION THAT RETURNS A PSEUDO RANDOM NUMBER
 * SO IS NOT INTENDED FOR USE IN PRODUCTION SYSTEMS.
 */
BaseType_t xApplicationGetRandomNumber( uint32_t * pulNumber )
{
    *( pulNumber ) = uxRand();
    return pdTRUE;
}


void vApplicationPingReplyHook( ePingReplyStatus_t eStatus,
                                uint16_t usIdentifier )
{
    if( eStatus == eSuccess )
    {
        FreeRTOS_printf( ( "Ping response received. ID: %d\r\n", usIdentifier ) );

        /* Increment successful ping replies. */
        xTotalSuccess++;
    }
}
