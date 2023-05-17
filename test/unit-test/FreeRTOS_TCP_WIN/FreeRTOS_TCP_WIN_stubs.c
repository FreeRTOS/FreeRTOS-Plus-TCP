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

volatile BaseType_t xInsideInterrupt = pdFALSE;

/** @brief The expected IP version and header length coded into the IP header itself. */
#define ipIP_VERSION_AND_HEADER_LENGTH_BYTE    ( ( uint8_t ) 0x45 )

UDPPacketHeader_t xDefaultPartUDPPacketHeader =
{
    /* .ucBytes : */
    {
        0x11, 0x22, 0x33, 0x44, 0x55, 0x66,  /* Ethernet source MAC address. */
        0x08, 0x00,                          /* Ethernet frame type. */
        ipIP_VERSION_AND_HEADER_LENGTH_BYTE, /* ucVersionHeaderLength. */
        0x00,                                /* ucDifferentiatedServicesCode. */
        0x00, 0x00,                          /* usLength. */
        0x00, 0x00,                          /* usIdentification. */
        0x00, 0x00,                          /* usFragmentOffset. */
        ipconfigUDP_TIME_TO_LIVE,            /* ucTimeToLive */
        ipPROTOCOL_UDP,                      /* ucProtocol. */
        0x00, 0x00,                          /* usHeaderChecksum. */
        0x00, 0x00, 0x00, 0x00               /* Source IP address. */
    }
};


/*
 * IP-clash detection is currently only used internally. When DHCP doesn't respond, the
 * driver can try out a random LinkLayer IP address (169.254.x.x).  It will send out a
 * gratuitous ARP message and, after a period of time, check the variables here below:
 */
#if ( ipconfigARP_USE_CLASH_DETECTION != 0 )
    /* Becomes non-zero if another device responded to a gratuitous ARP message. */
    BaseType_t xARPHadIPClash;
    /* MAC-address of the other device containing the same IP-address. */
    MACAddress_t xARPClashMacAddress;
#endif /* ipconfigARP_USE_CLASH_DETECTION */


/** @brief For convenience, a MAC address of all 0xffs is defined const for quick
 * reference. */
const MACAddress_t xBroadcastMACAddress = { { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff } };

/** @brief Structure that stores the netmask, gateway address and DNS server addresses. */
NetworkAddressingParameters_t xNetworkAddressing =
{
    0xC0C0C0C0, /* 192.192.192.192 - Default IP address. */
    0xFFFFFF00, /* 255.255.255.0 - Netmask. */
    0xC0C0C001, /* 192.192.192.1 - Gateway Address. */
    0x01020304, /* 1.2.3.4 - DNS server address. */
    0xC0C0C0FF
};              /* 192.192.192.255 - Broadcast address. */

/** @brief Structure that stores the netmask, gateway address and DNS server addresses. */
NetworkAddressingParameters_t xDefaultAddressing =
{
    0xC0C0C0C0, /* 192.192.192.192 - Default IP address. */
    0xFFFFFF00, /* 255.255.255.0 - Netmask. */
    0xC0C0C001, /* 192.192.192.1 - Gateway Address. */
    0x01020304, /* 1.2.3.4 - DNS server address. */
    0xC0C0C0FF
};

size_t xPortGetMinimumEverFreeHeapSize( void )
{
    return 0;
}

BaseType_t xApplicationDNSQueryHook_Multi( struct xNetworkEndPoint * pxEndPoint,
                                           const char * pcName )
{
    return 0;
}

StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     StackType_t * pxEndOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters )
{
    return 0;
}

uint32_t ulApplicationGetNextSequenceNumber( uint32_t ulSourceAddress,
                                             uint16_t usSourcePort,
                                             uint32_t ulDestinationAddress,
                                             uint16_t usDestinationPort )
{
    return 0;
}

BaseType_t xNetworkInterfaceInitialise( void )
{
    return 0;
}

/* This function shall be defined by the application. */
void vApplicationIPNetworkEventHook_Multi( eIPCallbackEvent_t eNetworkEvent,
                                           struct xNetworkEndPoint * pxEndPoint )
{
}

void vApplicationDaemonTaskStartupHook( void )
{
}

void vApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
                                     StackType_t ** ppxTimerTaskStackBuffer,
                                     uint32_t * pulTimerTaskStackSize )
{
}

void vPortDeleteThread( void * pvTaskToDelete )
{
}

void vApplicationIdleHook( void )
{
}

void vApplicationTickHook( void )
{
}

unsigned long ulGetRunTimeCounterValue( void )
{
    return 0;
}

void vPortEndScheduler( void )
{
}

BaseType_t xPortStartScheduler( void )
{
    return 0;
}

void vPortEnterCritical( void )
{
}

void vPortExitCritical( void )
{
}

void vPortGenerateSimulatedInterrupt( uint32_t ulInterruptNumber )
{
}

void vPortCloseRunningThread( void * pvTaskToDelete,
                              volatile BaseType_t * pxPendYield )
{
}

void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                    StackType_t ** ppxIdleTaskStackBuffer,
                                    uint32_t * pulIdleTaskStackSize )
{
}

void vConfigureTimerForRunTimeStats( void )
{
}

/*-----------------------------------------------------------*/
