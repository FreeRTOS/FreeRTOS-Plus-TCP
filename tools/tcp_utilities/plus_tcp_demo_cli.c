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

/**
 * @file plus_tcp_demo_cli.c
 * @brief This module will handle a set of commands that help with integration testing.
 *        It is used for integration tests, both IPv4 and IPv6.
 */

/* Standard includes. */
#include <stdio.h>
#include <time.h>
#include <ctype.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "timers.h"
#include "queue.h"
#include "semphr.h"
#include "message_buffer.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DHCP.h"
#include "FreeRTOS_DNS.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_IP_Private.h"

#if ( ipconfigMULTI_INTERFACE != 0 )
    #include "FreeRTOS_Routing.h"
    #if ( ipconfigUSE_IPv6 != 0 )
        #include "FreeRTOS_ND.h"
    #endif
#endif

#include "plus_tcp_demo_cli.h"
#include "http_client_test.h"

#if ( ipconfigUSE_NTP_DEMO != 0 )
    #include "NTPDemo.h"
#endif

#if ( USE_IPERF != 0 )
    #include "iperf_task.h"
#endif

int verboseLevel;

#define PING_TIMEOUT    100U

typedef struct xCommandOptions
{
    BaseType_t xDoClear;
    BaseType_t xIPVersion; /* Zero means: do not change version, otherwise 4 or 6. */
    BaseType_t xAsynchronous;
    BaseType_t xLogging;
} CommandOptions_t;

size_t uxGetOptions( CommandOptions_t * pxOptions,
                     const char ** ppcCommand );

int PING_COUNT_MAX = 10;

static TaskHandle_t xServerWorkTaskHandle = NULL;

extern void vApplicationPingReplyHook( ePingReplyStatus_t eStatus,
                                       uint16_t usIdentifier );
#if ( ipconfigUSE_IPv6 != 0 )
    static IPv6_Address_t xPing6IPAddress;
    volatile BaseType_t xPing6Count = -1;
#endif
uint32_t ulPingIPAddress;
size_t uxPingSize = 42U;
volatile BaseType_t xPing4Count = -1;
volatile BaseType_t xPingReady;
static int pingLogging = pdFALSE;

static void handle_dnsq( char * pcBuffer );
static void handle_ping( char * pcBuffer );
#if ( ipconfigUSE_NTP_DEMO != 0 )
    static void handle_ntp( char * pcBuffer );
#endif
static void handle_rand( char * pcBuffer );

static void handle_http( char * pcBuffer );

#if ( ipconfigUSE_IPv6 != 0 )
    static void handle_whatismyipaddress( char * pcBuffer );
#endif

#if ( ipconfigMULTI_INTERFACE != 0 )
    static void handle_ifconfig( char * pcBuffer );
#endif

#if ( ipconfigMULTI_INTERFACE != 0 )
    static void handle_gw( char * pcBuffer );
#endif

static void clear_caches( void );

static volatile BaseType_t xDNSCount = 0;

static struct freertos_addrinfo * pxDNSLookup( char * pcHost,
                                               BaseType_t xIPVersion,
                                               BaseType_t xAsynchronous,
                                               BaseType_t xDoClear );

#if ( ipconfigUSE_IPv6 == 0 )
    /* In the old days, an IP-address was just a number. */
    void onDNSEvent( const char * pcName,
                     void * pvSearchID,
                     uint32_t ulIPAddress );
#else
    /* freertos_addrinfo can contain either an IPv4 or an IPv6 address. */
    void onDNSEvent( const char * pcName,
                     void * pvSearchID,
                     struct freertos_addrinfo * pxAddrInfo );
#endif

#if ( ipconfigMULTI_INTERFACE != 0 )
    /* Defined in FreeRTOS_DNS.c */
    void show_addressinfo( struct freertos_addrinfo * pxAddress );
#endif

/*-----------------------------------------------------------*/

typedef void ( * pfhandler ) ( char * /*pcBuffer */ );

static BaseType_t can_handle( char * pcBuffer,
                              char * pcCommand,
                              size_t uxLength,
                              pfhandler phandler )
{
    BaseType_t xReturn = pdFALSE;

    if( strncmp( pcBuffer, pcCommand, uxLength ) == 0 )
    {
        phandler( pcBuffer + uxLength );
        xReturn = pdTRUE;
    }

    return xReturn;
}

/**
 *
 * @brief Create a task that runs the CLI.
 * @return zero when the command was recognised and handled.
 */
BaseType_t xHandleTestingCommand( char * pcBuffer,
                                  size_t uxBufferSize )
{
    BaseType_t xReturn = pdTRUE;

    ( void ) uxBufferSize;

/*	FreeRTOS_printf( ( "Command '%s'\n", pcBuffer ) ); */
    if( xServerWorkTaskHandle == NULL )
    {
        xServerWorkTaskHandle = xTaskGetCurrentTaskHandle();
    }

    if( strncmp( pcBuffer, "ver", 3 ) == 0 )
    {
        int level;

        if( sscanf( pcBuffer + 3, "%d", &level ) == 1 )
        {
            verboseLevel = level;
        }

        FreeRTOS_printf( ( "Verbose level %d\n", verboseLevel ) );
    }

    else if( can_handle( pcBuffer, "ping", 4U, handle_ping ) == pdTRUE )
    {
    }

    else if( can_handle( pcBuffer, "dnsq", 4U, handle_dnsq ) == pdTRUE )
    {
    }

    else if( can_handle( pcBuffer, "rand", 4U, handle_rand ) == pdTRUE )
    {
    }
    else if( can_handle( pcBuffer, "http", 4U, handle_http ) == pdTRUE )
    {
    }

    #if ( ipconfigUSE_NTP_DEMO != 0 )
        else if( can_handle( pcBuffer, "ntp", 3U, handle_ntp ) == pdTRUE )
        {
        }
    #endif /* ( ipconfigUSE_NTP_DEMO != 0 ) */

    #if ( ipconfigUSE_IPv6 != 0 )
        else if( can_handle( pcBuffer, "whatismyip", 10U, handle_whatismyipaddress ) == pdTRUE )
        {
        }
    #endif

    #if ( ipconfigMULTI_INTERFACE != 0 )
        else if( can_handle( pcBuffer, "gw", 2U, handle_gw ) == pdTRUE )
        {
        }
    #endif

    #if ( ipconfigMULTI_INTERFACE != 0 )
        else if( can_handle( pcBuffer, "ifconfig", 8U, handle_ifconfig ) == pdTRUE )
        {
        }
    #endif /* ipconfigMULTI_INTERFACE */

    else
    {
        xReturn = pdFALSE;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigMULTI_INTERFACE != 0 )
    static void handle_ifconfig( char * pcBuffer )
    {
        NetworkInterface_t * pxInterface;
        NetworkEndPoint_t * pxEndPoint;

        ( void ) pcBuffer;

        for( pxInterface = FreeRTOS_FirstNetworkInterface();
             pxInterface != NULL;
             pxInterface = FreeRTOS_NextNetworkInterface( pxInterface ) )
        {
            FreeRTOS_printf( ( "Interface %s\n", pxInterface->pcName ) );

            for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
                 pxEndPoint != NULL;
                 pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
            {
                showEndPoint( pxEndPoint );
            }
        }
    }
#endif /* ( ipconfigMULTI_INTERFACE != 0 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigMULTI_INTERFACE != 0 )
    static void handle_dnsq( char * pcBuffer )
    {
        CommandOptions_t xOptions;
        char * ptr = pcBuffer;

        uxGetOptions( &( xOptions ), &( ptr ) );

        while( isspace( ( ( uint8_t ) *ptr ) ) )
        {
            ptr++;
        }

        if( *ptr )
        {
            struct freertos_addrinfo * pxResult;

            pxResult = pxDNSLookup( ptr, xOptions.xIPVersion, xOptions.xAsynchronous, xOptions.xDoClear );

            if( pxResult != NULL )
            {
                FreeRTOS_freeaddrinfo( pxResult );
            }
        }
        else
        {
            FreeRTOS_printf( ( "Usage: dnsq <name>\n" ) );
        }
    }
/*-----------------------------------------------------------*/

#else /* if ( ipconfigMULTI_INTERFACE != 0 ) */

    #if ( ipconfigMULTI_INTERFACE == 0 )
        void dnsFound( const char * pcName,
                       void * pvSearchID,
                       uint32_t aIp )
        {
            ( void ) pvSearchID;
            FreeRTOS_printf( ( "DNS-callback: '%s' found at %lxip\n", pcName, FreeRTOS_ntohl( aIp ) ) );
        }
    #endif

    static void handle_dnsq( char * pcBuffer )
    {
        char * ptr = pcBuffer;

        while( *ptr && !isspace( *ptr ) )
        {
            ptr++;
        }

        while( isspace( ( ( uint8_t ) *ptr ) ) )
        {
            ptr++;
        }

        unsigned tmout = 4000;
        static unsigned searchID;

        if( *ptr )
        {
            for( char * target = ptr; *target; target++ )
            {
                if( isspace( *target ) )
                {
                    *target = '\0';
                    break;
                }
            }

            FreeRTOS_printf( ( "DNS query: '%s'\n", ptr ) );
            #if ( ipconfigDNS_USE_CALLBACKS != 0 )
                uint32_t ip = FreeRTOS_gethostbyname_a( ptr, dnsFound, ( void * ) ++searchID, tmout );
            #else
                uint32_t ip;
                int count;
                #if ( ipconfigUSE_DNS_CACHE != 0 )
                    {
                        FreeRTOS_dnsclear();
                    }
                #endif

                for( count = 0; count < 5; count++ )
                {
                    ip = FreeRTOS_gethostbyname( ptr );
                    FreeRTOS_printf( ( "Lookup: %lxip\n", ip ) );

                    if( ip == 0U )
                    {
                        break;
                    }
                }
            #endif /* if ( ipconfigDNS_USE_CALLBACKS != 0 ) */

            if( ip )
            {
                FreeRTOS_printf( ( "%s : %lxip\n", ptr, FreeRTOS_ntohl( ip ) ) );
            }
        }
        else
        {
            FreeRTOS_printf( ( "Usage: dnsquery <name>\n" ) );
        }
    }
#endif /* ( ipconfigMULTI_INTERFACE != 0 ) */
/*-----------------------------------------------------------*/

static void handle_rand( char * pcBuffer )
{
    uint32_t ulNumber = 0x5a5a5a5a;
    BaseType_t rc = xApplicationGetRandomNumber( &ulNumber );

    ( void ) pcBuffer;

    if( rc == pdPASS )
    {
        char buffer[ 33 ];
        int index;
        uint32_t ulMask = 0x80000000uL;

        for( index = 0; index < 32; index++ )
        {
            buffer[ index ] = ( ( ulNumber & ulMask ) != 0 ) ? '1' : '0';
            ulMask >>= 1;
        }

        buffer[ index ] = '\0';
        FreeRTOS_printf( ( "Random %08lx (%s)\n", ulNumber, buffer ) );
    }
    else
    {
        FreeRTOS_printf( ( "Random failed\n" ) );
    }
}
/*-----------------------------------------------------------*/

size_t uxGetOptions( CommandOptions_t * pxOptions,
                     const char ** ppcCommand )
{
    size_t uxLength = 0U;
    const char * pcCommand = *ppcCommand;

    memset( pxOptions, 0, sizeof( *pxOptions ) );

    while( ( pcCommand[ uxLength ] != 0 ) && ( !isspace( ( uint8_t ) pcCommand[ uxLength ] ) ) )
    {
        switch( pcCommand[ uxLength ] )
        {
            case 'a':
                pxOptions->xAsynchronous = pdTRUE;
                break;

            case 'c':
                pxOptions->xDoClear = pdTRUE;
                break;

            case 'v':
                pxOptions->xLogging = pdTRUE;
                break;

            case '4':
                pxOptions->xIPVersion = 4;
                break;

            case '6':
                pxOptions->xIPVersion = 6;
                break;
        }

        uxLength++;
    }

    if( uxLength > 0U )
    {
        *ppcCommand = &( pcCommand[ uxLength ] );
    }

    return uxLength;
}

#if ( ipconfigUSE_NTP_DEMO != 0 )
    static void handle_ntp( char * pcBuffer )
    {
        CommandOptions_t xOptions;
        char * ptr = pcBuffer;

        uxGetOptions( &( xOptions ), &( ptr ) );

        ( void ) pcBuffer;

        if( xOptions.xDoClear )
        {
            clear_caches();
            vNTPClearCache();
        }

        vNTPSetNTPType( xOptions.xIPVersion, xOptions.xAsynchronous, xOptions.xLogging );
        /* vStartNTPTask() may be called multiple times. */
        vStartNTPTask( configMINIMAL_STACK_SIZE * 8, tskIDLE_PRIORITY + 1 );
    }
#endif /* if ( ipconfigUSE_NTP_DEMO != 0 ) */

#if ( ipconfigUSE_IPv6 != 0 )
    static void handle_whatismyipaddress( char * pcBuffer )
    {
        NetworkEndPoint_t * pxEndPoint;

        ( void ) pcBuffer;
        FreeRTOS_printf( ( "Showing all end-points\n" ) );

        for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
             pxEndPoint != NULL;
             pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                if( pxEndPoint->bits.bIPv6 )
                {
                    FreeRTOS_printf( ( "IPv6: %pip on '%s'\n", pxEndPoint->ipv6_settings.xIPAddress.ucBytes, pxEndPoint->pxNetworkInterface->pcName ) );
                }
                else
            #endif
            {
                FreeRTOS_printf( ( "IPv4: %lxip on '%s'\n", FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulIPAddress ), pxEndPoint->pxNetworkInterface->pcName ) );
            }
        }
    }
#endif /* if ( ipconfigUSE_IPv6 != 0 ) */

#if ( ipconfigMULTI_INTERFACE != 0 )
    static void handle_gw( char * pcBuffer )
    {
        NetworkEndPoint_t * pxEndPoint;

        ( void ) pcBuffer;
        FreeRTOS_printf( ( "Showing all gateways\n" ) );

        for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
             pxEndPoint != NULL;
             pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                if( pxEndPoint->bits.bIPv6 )
                {
                    if( memcmp( pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, in6addr_any.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) != 0 )
                    {
                        FreeRTOS_printf( ( "IPv6: %pip on '%s'\n", pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, pxEndPoint->pxNetworkInterface->pcName ) );
                    }
                }
                else
            #endif
            {
                if( pxEndPoint->ipv4_settings.ulGatewayAddress != 0U )
                {
                    FreeRTOS_printf( ( "IPv4: %lxip on '%s'\n", FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulGatewayAddress ), pxEndPoint->pxNetworkInterface->pcName ) );
                }
            }
        }
    }
#endif /* if ( ipconfigMULTI_INTERFACE != 0 ) */

#if ( ipconfigMULTI_INTERFACE != 0 )
    static void handle_ping( char * pcBuffer )
    {
        struct freertos_addrinfo * pxDNSResult = NULL;
        char * ptr = pcBuffer;
        CommandOptions_t xOptions;

        pingLogging = pdFALSE;

        uxGetOptions( &( xOptions ), &( ptr ) );

        while( isspace( ( ( uint8_t ) *ptr ) ) )
        {
            ptr++;
        }

        char * pcHostname = ptr;

        if( *pcHostname == '\0' )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                if( xOptions.xIPVersion == 6 )
                {
                    pcHostname = "fe80::6816:5e9b:80a0:9edb";
                }
                else
            #endif
            {
                pcHostname = "192.168.2.1";
            }
        }

        #if ( ipconfigUSE_IPv6 != 0 )
            if( strchr( pcHostname, ':' ) != NULL )
            {
                IPv6_Address_t xAddress_IPv6; /*lint !e9018 declaration of symbol 'xAddress_IPv6' with union based type 'const IPv6_Address_t' [MISRA 2012 Rule 19.2, advisory]. */

                /* ulIPAddress does not represent an IPv4 address here. It becomes non-zero when the look-up succeeds. */
                if( FreeRTOS_inet_pton6( pcHostname, xAddress_IPv6.ucBytes ) != 0 )
                {
                    xOptions.xIPVersion = 6;
                }
            }
            else if( strchr( pcHostname, '.' ) != NULL )
            {
                uint32_t ulIPAddress;

                ulIPAddress = FreeRTOS_inet_addr( pcHostname );

                if( ( ulIPAddress != 0 ) && ( ulIPAddress != ~0uL ) )
                {
                    xOptions.xIPVersion = 4;
                }
            }
        #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
        FreeRTOS_printf( ( "ping%d: looking up name '%s'\n", ( int ) xOptions.xIPVersion, pcHostname ) );

        if( xOptions.xDoClear )
        {
            clear_caches();
        }

        FreeRTOS_printf( ( "Calling pxDNSLookup\n" ) );
        pxDNSResult = pxDNSLookup( pcHostname, xOptions.xIPVersion, xOptions.xAsynchronous, xOptions.xDoClear );

        if( pxDNSResult != NULL )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                if( xOptions.xIPVersion == 6 )
                {
                    FreeRTOS_printf( ( "ping6 to '%s' (%pip)\n", pcHostname, pxDNSResult->xPrivateStorage.sockaddr6.sin_addrv6.ucBytes ) );
                    xPing4Count = -1;
                    xPing6Count = 0;
                    memcpy( xPing6IPAddress.ucBytes, pxDNSResult->xPrivateStorage.sockaddr6.sin_addrv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                    FreeRTOS_SendPingRequestIPv6( &xPing6IPAddress, uxPingSize, PING_TIMEOUT );
                }
                else
            #endif
            {
                FreeRTOS_printf( ( "ping4 to '%s' (%lxip)\n", pcHostname, FreeRTOS_ntohl( pxDNSResult->ai_addr->sin_addr ) ) );
                xPing4Count = 0;
                #if ( ipconfigUSE_IPv6 != 0 )
                    xPing6Count = -1;
                #endif
                ulPingIPAddress = pxDNSResult->ai_addr->sin_addr;
                xARPWaitResolution( ulPingIPAddress, pdMS_TO_TICKS( 5000U ) );
                FreeRTOS_SendPingRequest( ulPingIPAddress, uxPingSize, PING_TIMEOUT );
            }
        }
        else
        {
            FreeRTOS_printf( ( "ping -%d: '%s' not found\n", ( int ) xOptions.xIPVersion, ptr ) );
        }
    }
/*-----------------------------------------------------------*/

#else /* ipconfigMULTI_INTERFACE != 0 */

    static void handle_ping( char * pcBuffer )
    {
        uint32_t ulIPAddress;
        char * ptr = pcBuffer;

        pingLogging = pdFALSE;

        PING_COUNT_MAX = 10;

        CommandOptions_t xOptions;

        pingLogging = pdFALSE;

        uxGetOptions( &( xOptions ), &( ptr ) );

        while( isspace( *ptr ) )
        {
            ptr++;
        }

        #if ( ipconfigMULTI_INTERFACE != 0 )
            {
                ulIPAddress = FreeRTOS_inet_addr_quick( ucIPAddress[ 0 ], ucIPAddress[ 1 ], ucIPAddress[ 2 ], ucIPAddress[ 3 ] );
            }
        #else
            {
                FreeRTOS_GetAddressConfiguration( &ulIPAddress, NULL, NULL, NULL );
            }
        #endif

        if( *ptr != 0 )
        {
            char * rest = strchr( ptr, ' ' );

            if( rest )
            {
                *( rest++ ) = '\0';
            }

            ulIPAddress = FreeRTOS_inet_addr( ptr );

            while( *ptr && !isspace( *ptr ) )
            {
                ptr++;
            }

            unsigned count;

            if( ( rest != NULL ) && ( sscanf( rest, "%u", &count ) > 0 ) )
            {
                PING_COUNT_MAX = count;
            }
        }

        FreeRTOS_printf( ( "ping to %lxip\n", FreeRTOS_htonl( ulIPAddress ) ) );

        ulPingIPAddress = ulIPAddress;
        xPing4Count = 0;
        #if ( ipconfigUSE_IPv6 != 0 )
            xPing6Count = -1;
        #endif /* ( ipconfigUSE_IPv6 != 0 ) */
        xPingReady = pdFALSE;

        if( xOptions.xDoClear )
        {
            #if ( ipconfigMULTI_INTERFACE != 0 )
                FreeRTOS_ClearARP( NULL );
            #else
                FreeRTOS_ClearARP();
            #endif
            FreeRTOS_printf( ( "Clearing ARP cache\n" ) );
        }

        FreeRTOS_SendPingRequest( ulIPAddress, uxPingSize, PING_TIMEOUT );
    }
#endif /* ( ipconfigMULTI_INTERFACE != 0 ) */
/*-----------------------------------------------------------*/

static void handle_http( char * pcBuffer )
{
    char * ptr = pcBuffer;
    CommandOptions_t xOptions;

    pingLogging = pdFALSE;

    uxGetOptions( &( xOptions ), &( ptr ) );

    while( isspace( ( uint8_t ) *ptr ) )
    {
        ptr++;
    }

    if( *ptr != 0 )
    {
        char * pcHost = ptr;
        char * pcFileName;

        while( ( *ptr != 0 ) && ( !isspace( ( uint8_t ) *ptr ) ) )
        {
            ptr++;
        }

        if( isspace( ( uint8_t ) *ptr ) )
        {
            ptr[ 0 ] = 0;
            ptr++;
        }

        while( isspace( ( uint8_t ) *ptr ) )
        {
            ptr++;
        }

        pcFileName = ptr;

        if( xOptions.xDoClear )
        {
            clear_caches();
        }

        vStartHTTPClientTest( configMINIMAL_STACK_SIZE * 8, tskIDLE_PRIORITY + 1 );
        wakeupHTTPClient( 0U, pcHost, pcFileName, xOptions.xIPVersion );
    }
    else
    {
        FreeRTOS_printf( ( "Usage: tcp <hostname>\n" ) );
    }
}
/*-----------------------------------------------------------*/

void vApplicationPingReplyHook( ePingReplyStatus_t eStatus,
                                uint16_t usIdentifier )
{
    if( ( xPing4Count >= 0 ) && ( xPing4Count < PING_COUNT_MAX ) )
    {
        xPing4Count++;

        if( pingLogging || ( xPing4Count == PING_COUNT_MAX ) )
        {
            FreeRTOS_printf( ( "Received reply %d: status %d ID %04x\n", ( int ) xPing4Count, ( int ) eStatus, usIdentifier ) );
        }
    }

    #if ( ipconfigUSE_IPv6 != 0 )
        if( ( xPing6Count >= 0 ) && ( xPing6Count < PING_COUNT_MAX ) )
        {
            xPing6Count++;
            /*if (xPing6Count == PING_COUNT_MAX || xPing6Count == 1) */
            FreeRTOS_printf( ( "Received reply %d: status %d ID %04x\n", ( int ) xPing6Count, ( int ) eStatus, usIdentifier ) );
        }
    #endif
    xPingReady = pdTRUE;

    /*
     * if( xServerSemaphore != NULL )
     * {
     *  xSemaphoreGive( xServerSemaphore );
     * }
     */
}
/*-----------------------------------------------------------*/

void xHandleTesting()
{
    if( xPingReady )
    {
        #if ( ipconfigUSE_IPv6 != 0 )
            FreeRTOS_printf( ( "xPingReady %d xPing4 %d xPing6 %d\n", ( int ) xPingReady, ( int ) xPing4Count, ( int ) xPing6Count ) );
        #else
            FreeRTOS_printf( ( "xPingReady %d xPing4 %d\n", ( int ) xPingReady, ( int ) xPing4Count ) );
        #endif
        xPingReady = pdFALSE;

        if( ( xPing4Count >= 0 ) && ( xPing4Count < PING_COUNT_MAX ) )
        {
            /* 10 bytes, 100 clock ticks. */
            FreeRTOS_SendPingRequest( ulPingIPAddress, uxPingSize, PING_TIMEOUT );
        }

        #if ( ipconfigUSE_IPv6 != 0 )
            if( ( xPing6Count >= 0 ) && ( xPing6Count < PING_COUNT_MAX ) )
            {
                FreeRTOS_SendPingRequestIPv6( &xPing6IPAddress, uxPingSize, PING_TIMEOUT );
            }
        #endif
    }
}
/*-----------------------------------------------------------*/

static struct freertos_addrinfo * pxDNSLookup( char * pcHost,
                                               BaseType_t xIPVersion,
                                               BaseType_t xAsynchronous,
                                               BaseType_t xDoClear )
{
    #if ( ipconfigMULTI_INTERFACE != 0 )
        struct freertos_addrinfo * pxResult = NULL;
        struct freertos_addrinfo xHints;

        if( xIPVersion == 4 )
        {
            xHints.ai_family = FREERTOS_AF_INET;
        }
        else
        {
            xHints.ai_family = FREERTOS_AF_INET6;
        }
    #endif /* if ( ipconfigMULTI_INTERFACE != 0 ) */
    FreeRTOS_printf( ( "pxDNSLookup: '%s' IPv%d %s DNS-clear = %s\n",
                       pcHost, ( int ) xIPVersion, ( xAsynchronous != 0 ) ? " Async" : "Sync", ( xDoClear != 0 ) ? "true" : "false" ) );

    if( xDoClear )
    {
        #if ( ipconfigUSE_DNS_CACHE != 0 )
            {
                FreeRTOS_dnsclear();
            }
        #endif /* ipconfigUSE_DNS_CACHE */
        #if ( ipconfigMULTI_INTERFACE != 0 )
            FreeRTOS_ClearARP( NULL );
        #else
            FreeRTOS_ClearARP();
        #endif
    }

    xDNSCount = 0;
    #if ( ipconfigMULTI_INTERFACE != 0 )
        #if ( ipconfigDNS_USE_CALLBACKS != 0 )
            if( xAsynchronous != 0 )
            {
                void * pvSearchID = ( void * ) ipconfigRAND32();
                BaseType_t rc = FreeRTOS_getaddrinfo_a(
                    pcHost,    /* The node. */
                    NULL,      /* const char *pcService: ignored for now. */
                    &xHints,   /* If not NULL: preferences. */
                    &pxResult, /* An allocated struct, containing the results. */
                    onDNSEvent,
                    pvSearchID,
                    5000 );

                FreeRTOS_printf( ( "dns query%d: '%s' = %d\n", ( int ) xIPVersion, pcHost, ( int ) rc ) );

                if( pxResult != NULL )
                {
                    show_addressinfo( pxResult );
                }
            }
            else
        #endif /* if ( ipconfigDNS_USE_CALLBACKS != 0 ) */
        {
            BaseType_t rc = FreeRTOS_getaddrinfo(
                pcHost,      /* The node. */
                NULL,        /* const char *pcService: ignored for now. */
                &xHints,     /* If not NULL: preferences. */
                &pxResult ); /* An allocated struct, containing the results. */
            FreeRTOS_printf( ( "FreeRTOS_getaddrinfo: rc %d\n", ( int ) rc ) );

            if( pxResult != NULL )
            {
                show_addressinfo( pxResult );
            }

            if( rc != 0 )
            {
                FreeRTOS_printf( ( "dns query%d: '%s' No results\n", ( int ) xIPVersion, pcHost ) );
            }
            else
            {
                #if ( ipconfigUSE_IPv6 != 0 )
                    if( xIPVersion == 6 )
                    {
                        struct freertos_sockaddr6 * pxAddr6;
                        pxAddr6 = ( struct freertos_sockaddr6 * ) pxResult->ai_addr;

                        FreeRTOS_printf( ( "dns query%d: '%s' = %pip rc = %d\n", ( int ) xIPVersion, pcHost, pxAddr6->sin_addrv6.ucBytes, ( int ) rc ) );
                    }
                    else
                #endif /* ipconfigUSE_IPv6 */
                {
                    uint32_t luIPAddress = pxResult->ai_addr->sin_addr;
                    FreeRTOS_printf( ( "dns query%d: '%s' = %lxip rc = %d\n", ( int ) xIPVersion, pcHost, FreeRTOS_ntohl( luIPAddress ), ( int ) rc ) );
                }
            }
        }
    #endif /* ipconfigMULTI_INTERFACE */

    #if ( ipconfigDNS_USE_CALLBACKS != 0 ) && ( ipconfigMULTI_INTERFACE != 0 )
        if( pxResult == NULL )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                IPv6_Address_t xAddress_IPv6;
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */
            uint32_t ulIpAddress;
            int iCount;

            for( iCount = 0; iCount < 10; iCount++ )
            {
                ulTaskNotifyTake( pdTRUE, 1000 );

                if( xDNSCount != 0 )
                {
                    break;
                }
            }

            vTaskDelay( 333 );
            pxResult = ipPOINTER_CAST( struct freertos_addrinfo *, pvPortMalloc( sizeof( *pxResult ) ) );

            if( pxResult != NULL )
            {
                memset( pxResult, '\0', sizeof( *pxResult ) );
                pxResult->ai_canonname = pxResult->xPrivateStorage.ucName;
                strncpy( pxResult->xPrivateStorage.ucName, pcHost, sizeof( pxResult->xPrivateStorage.ucName ) );

                #if ( ipconfigUSE_IPv6 != 0 )
                    {
                        pxResult->ai_addr = ipPOINTER_CAST( struct freertos_sockaddr *, & ( pxResult->xPrivateStorage.sockaddr6 ) );
                    }
                #else
                    {
                        pxResult->ai_addr = &( pxResult->xPrivateStorage.sockaddr4 );
                    }
                #endif

                #if ( ipconfigUSE_IPv6 != 0 )
                    memset( xAddress_IPv6.ucBytes, '\0', sizeof( xAddress_IPv6.ucBytes ) );

                    if( xIPVersion == 6 )
                    {
                        FreeRTOS_dnslookup6( pcHost, &( xAddress_IPv6 ) );
                        FreeRTOS_printf( ( "Lookup6 '%s' = %pip\n", pcHost, xAddress_IPv6.ucBytes ) );
                        pxResult->ai_family = FREERTOS_AF_INET6;
                        pxResult->ai_addrlen = ipSIZE_OF_IPv6_ADDRESS;
                        memcpy( pxResult->xPrivateStorage.sockaddr6.sin_addrv6.ucBytes, xAddress_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                    }
                    else
                #endif /* ( ipconfigUSE_IPv6 != 0 ) */
                {
                    #if ( ipconfigUSE_DNS_CACHE != 0 )
                        ulIpAddress = FreeRTOS_dnslookup( pcHost );
                        FreeRTOS_printf( ( "Lookup4 '%s' = %lxip\n", pcHost, FreeRTOS_ntohl( ulIpAddress ) ) );
                        pxResult->ai_addr->sin_addr = ulIpAddress;
                        pxResult->ai_family = FREERTOS_AF_INET4;
                        pxResult->ai_addrlen = ipSIZE_OF_IPv4_ADDRESS;
                    #endif
                }
            }
        }
    #endif /* if ( ipconfigDNS_USE_CALLBACKS != 0 ) && ( ipconfigMULTI_INTERFACE != 0 ) */
    #if ( ipconfigMULTI_INTERFACE != 0 )
        /* Don't forget to call FreeRTOS_freeaddrinfo() */
        return pxResult;
    #else
        return 0;
    #endif
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )
    void onDNSEvent( const char * pcName,
                     void * pvSearchID,
                     struct freertos_addrinfo * pxAddrInfo )
    {
        ( void ) pvSearchID;
        const struct freertos_sockaddr6 * pxAddress6 = ( const struct freertos_sockaddr6 * ) pxAddrInfo->ai_addr;

        if( pxAddress6->sin_family == FREERTOS_AF_INET6 )
        {
            BaseType_t xIsEmpty = pdTRUE, xIndex;

            for( xIndex = 0; xIndex < ( BaseType_t ) ARRAY_SIZE( pxAddress6->sin_addrv6.ucBytes ); xIndex++ )
            {
                if( pxAddress6->sin_addrv6.ucBytes[ xIndex ] != ( uint8_t ) 0u )
                {
                    xIsEmpty = pdFALSE;
                    break;
                }
            }

            if( xIsEmpty )
            {
                FreeRTOS_printf( ( "onDNSEvent/v6: '%s' timed out\n", pcName ) );
            }
            else
            {
                FreeRTOS_printf( ( "onDNSEvent/v6: found '%s' on %pip\n", pcName, pxAddress6->sin_addrv6.ucBytes ) );
            }
        }
        else
        {
            struct freertos_sockaddr * pxAddress4 = ( struct freertos_sockaddr * ) pxAddress6;

            if( pxAddress4->sin_addr == 0uL )
            {
                FreeRTOS_printf( ( "onDNSEvent/v4: '%s' timed out\n", pcName ) );
            }
            else
            {
                FreeRTOS_printf( ( "onDNSEvent/v4: found '%s' on %lxip\n", pcName, FreeRTOS_ntohl( pxAddress4->sin_addr ) ) );
            }
        }

        if( xServerWorkTaskHandle != NULL )
        {
            xDNSCount++;
            xTaskNotifyGive( xServerWorkTaskHandle );
        }
    }
#else /* if ( ipconfigUSE_IPv6 != 0 ) */
    void onDNSEvent( const char * pcName,
                     void * pvSearchID,
                     uint32_t ulIPAddress )
    {
        ( void ) pvSearchID;

        FreeRTOS_printf( ( "onDNSEvent: found '%s' on %lxip\n", pcName, FreeRTOS_ntohl( ulIPAddress ) ) );

        if( xServerWorkTaskHandle != NULL )
        {
            xDNSCount++;
            xTaskNotifyGive( xServerWorkTaskHandle );
        }
    }
#endif /* if ( ipconfigUSE_IPv6 != 0 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigMULTI_INTERFACE != 0 )
    void showEndPoint( NetworkEndPoint_t * pxEndPoint )
    {
        #if ( ipconfigUSE_IPv6 != 0 )
            if( pxEndPoint->bits.bIPv6 )
            {
                IPv6_Address_t xPrefix;
/*			pxEndPoint->ipv6_settings.xIPAddress;			/ * The actual IPv4 address. Will be 0 as long as end-point is still down. * / */
/*			pxEndPoint->ipv6_settings.uxPrefixLength; */
/*			pxEndPoint->ipv6_defaults.xIPAddress; */
/*			pxEndPoint->ipv6_settings.xGatewayAddress; */
/*			pxEndPoint->ipv6_settings.xDNSServerAddresses[ 2 ];	/ * Not yet in use. * / */

                /* Extract the prefix from the IP-address */
                FreeRTOS_CreateIPv6Address( &( xPrefix ), &( pxEndPoint->ipv6_settings.xIPAddress ), pxEndPoint->ipv6_settings.uxPrefixLength, pdFALSE );

                FreeRTOS_printf( ( "IP-address : %pip\n", pxEndPoint->ipv6_settings.xIPAddress.ucBytes ) );

                if( memcmp( pxEndPoint->ipv6_defaults.xIPAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) != 0 )
                {
                    FreeRTOS_printf( ( "Default IP : %pip\n", pxEndPoint->ipv6_defaults.xIPAddress.ucBytes ) );
                }

                FreeRTOS_printf( ( "End-point  : up = %s\n", pxEndPoint->bits.bEndPointUp ? "yes" : "no" ) );
                FreeRTOS_printf( ( "Prefix     : %pip/%d\n", xPrefix.ucBytes, ( int ) pxEndPoint->ipv6_settings.uxPrefixLength ) );
                FreeRTOS_printf( ( "GW         : %pip\n", pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes ) );
                FreeRTOS_printf( ( "DNS        : %pip\n", pxEndPoint->ipv6_settings.xDNSServerAddresses[ 0 ].ucBytes ) );
            }
            else
        #endif /* ( ipconfigUSE_IPv6 != 0 ) */
        {
            FreeRTOS_printf( ( "IP-address : %lxip\n",
                               FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulIPAddress ) ) );

            if( pxEndPoint->ipv4_settings.ulIPAddress != pxEndPoint->ipv4_defaults.ulIPAddress )
            {
                FreeRTOS_printf( ( "Default IP : %lxip\n", FreeRTOS_ntohl( pxEndPoint->ipv4_defaults.ulIPAddress ) ) );
            }

            int bWantDHCP;
            #if ( ipconfigUSE_DHCP != 0 )
                bWantDHCP = pxEndPoint->bits.bWantDHCP;
            #else
                bWantDHCP = 0;
            #endif

            FreeRTOS_printf( ( "End-point  : up = %s dhcp = %d\n",
                               pxEndPoint->bits.bEndPointUp ? "yes" : "no",
                               bWantDHCP ) );
            FreeRTOS_printf( ( "Net mask   : %lxip\n", FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulNetMask ) ) );
            FreeRTOS_printf( ( "GW         : %lxip\n", FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulGatewayAddress ) ) );
            FreeRTOS_printf( ( "DNS        : %lxip\n", FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulDNSServerAddresses[ 0 ] ) ) );
            FreeRTOS_printf( ( "Broadcast  : %lxip\n", FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulBroadcastAddress ) ) );
        }

        FreeRTOS_printf( ( "MAC address: %02x-%02x-%02x-%02x-%02x-%02x\n",
                           pxEndPoint->xMACAddress.ucBytes[ 0 ],
                           pxEndPoint->xMACAddress.ucBytes[ 1 ],
                           pxEndPoint->xMACAddress.ucBytes[ 2 ],
                           pxEndPoint->xMACAddress.ucBytes[ 3 ],
                           pxEndPoint->xMACAddress.ucBytes[ 4 ],
                           pxEndPoint->xMACAddress.ucBytes[ 5 ] ) );
        FreeRTOS_printf( ( " \n" ) );
    }
#endif /* ipconfigMULTI_INTERFACE */
/*-----------------------------------------------------------*/

static void clear_caches()
{
    #if ( ipconfigUSE_DNS_CACHE != 0 )
        {
            FreeRTOS_dnsclear();
        }
    #endif /* ipconfigUSE_DNS_CACHE */
    #if ( ipconfigMULTI_INTERFACE != 0 )
        FreeRTOS_ClearARP( NULL );
    #else
        FreeRTOS_ClearARP();
    #endif
    FreeRTOS_printf( ( "Cleared caches.\n" ) );
}
/*-----------------------------------------------------------*/
