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

/* ===========================  EXTERN VARIABLES  =========================== */

/** @brief The pointer to buffer with packet waiting for ARP resolution. This variable
 *  is defined in FreeRTOS_IP.c.
 *  This pointer is for internal use only. */
NetworkBufferDescriptor_t * pxARPWaitingNetworkBuffer;

BaseType_t NetworkInterfaceOutputFunction_Stub_Called = 0;

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

/* ======================== Stub Callback Functions ========================= */

BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    NetworkInterfaceOutputFunction_Stub_Called++;
    return pdFALSE;
}

/**
 * @brief Receive and analyse a RA ( Router Advertisement ) message.
 *        If the reply is satisfactory, the end-point will do SLAAC: choose an IP-address using the
 *        prefix offered, and completed with random bits.  It will start testing if another device
 *        already exists that uses the same IP-address.
 *
 * @param[in] pxNetworkBuffer The buffer that contains the message.
 */
void vReceiveRA( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
}


/**
 * @brief Receive a NA ( Neighbour Advertisement ) message to see if a chosen IP-address is already in use.
 *
 * @param[in] pxNetworkBuffer The buffer that contains the message.
 */
void vReceiveNA( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
}

/*-----------------------------------------------------------*/
