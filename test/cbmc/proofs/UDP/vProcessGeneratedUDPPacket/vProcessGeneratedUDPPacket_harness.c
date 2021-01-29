/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "list.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Routing.h"

/* Include the stubs for APIs. */
#include "memory_assignments.c"
#include "freertos_api.c"

/* We do not need to calculate the actual checksum for the proof to be complete.
 * Neither does the checksum matter for completeness. */
uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
    __CPROVER_assert( pucNextData != NULL, "Next data in GenerateChecksum cannot be NULL" );

    uint16_t usChecksum;

    /* Return any random value of checksum since it does not matter for CBMC checks. */
    return usChecksum;
}


/* We do not need to calculate the actual checksum for the proof to be complete.
 * Neither does the checksum matter for completeness. */
uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    __CPROVER_assert( pucEthernetBuffer != NULL, "The Ethernet buffer cannot be NULL while generating Protocol Checksum" );
    uint16_t usProtocolChecksum;

    /* Return random value of checksum since it does not matter for CBMC checks. */
    return usProtocolChecksum;
}


/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                            const uint32_t ulIPAddress )
{
    /* pxMACAddress can be NULL or Non-NULL, no need to assert. */
}


/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void vARPGenerateRequestPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer cannot be NULL." );
}


/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
eARPLookupResult_t eARPGetCacheEntry( uint32_t * pulIPAddress,
                                      MACAddress_t * const pxMACAddress )
{
    __CPROVER_assert( pulIPAddress != NULL, "pulIPAddress cannot be NULL" );
    __CPROVER_assert( pxMACAddress != NULL, "pxMACAddress cannot be NULL" );

    eARPLookupResult_t eResult;

    return eResult;
}

/* Network Interface Output function is a portable low level function
 * which actually sends the data. We have assumed a correct
 * implementation of this function in this proof. */
BaseType_t NetworkInterfaceOutput( struct xNetworkInterface * pxDescriptor,
                                   NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                   BaseType_t xReleaseAfterSend )
{
    BaseType_t xReturn;

    /* Assert some basic conditions. */
    __CPROVER_assert( pxDescriptor != NULL, "Descriptor cannot be NULL" );
    __CPROVER_assert( pxNetworkBuffer != NULL, "NetworkBuffer cannot be NULL" );

    /* Return an arbitrary value. */
    return xReturn;
}

/* Global variables accessible throughout the program. Used in adding
 * Network interface/endpoint. */
NetworkInterface_t xNetworkInterface1;
NetworkEndPoint_t xEndPoint1;

const uint8_t ucIPAddress2[ 4 ];
const uint8_t ucNetMask2[ 4 ];
const uint8_t ucGatewayAddress2[ 4 ];
const uint8_t ucDNSServerAddress2[ 4 ];
const uint8_t ucMACAddress[ 6 ];

void harness()
{
    size_t xRequestedSizeBytes;

    /* Define and allocate members of an endpoint to be used later. */
    struct xNetworkEndPoint xLocalEndPoint;

    xLocalEndPoint.pxNetworkInterface = nondet_bool() ? NULL : malloc( sizeof( *( xLocalEndPoint.pxNetworkInterface ) ) );

    /* Network Interface cannot be NULL. */
    __CPROVER_assume( xLocalEndPoint.pxNetworkInterface != NULL );

    /* Assign the Network output function to the endpoint. This cannot be NULL. */
    xLocalEndPoint.pxNetworkInterface->pfOutput = NetworkInterfaceOutput;

    /* Assume that the size of packet must be greater than that of UDP-Packet and less than
     * that of the Ethernet Frame Size. */
    __CPROVER_assume( xRequestedSizeBytes >= sizeof( UDPPacket_t ) && xRequestedSizeBytes <= ipTOTAL_ETHERNET_FRAME_SIZE );

    /* Second parameter is not used from CBMC's perspective. */
    NetworkBufferDescriptor_t * const pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( xRequestedSizeBytes, 0 );

    /* The buffer cannot be NULL for the function call. */
    __CPROVER_assume( pxNetworkBuffer != NULL );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Arbitrarily add endpoint to the network buffer. This can be NULL or
     * a proper end point. */
    pxNetworkBuffer->pxEndPoint = nondet_bool() ? NULL : &xLocalEndPoint;

    /* Assume that the list of interfaces/endpoints is not initialized.
     * These are defined in the FreeRTOS_Routing.c file and used as a
     * list by the TCP stack. */
    __CPROVER_assume( pxNetworkInterfaces == NULL );
    __CPROVER_assume( pxNetworkEndPoints == NULL );

    /* Non-deterministically add a network-interface. */
    if( nondet_bool() )
    {
        /* Add the network interfaces to the list. */
        FreeRTOS_AddNetworkInterface( &xNetworkInterface1 );

        /* Non-deterministically add an end-point to the network-interface. */
        if( nondet_bool() )
        {
            /* Fill the endpoints and put them in the network interface. */
            FreeRTOS_FillEndPoint( &xNetworkInterface1,
                                   &xEndPoint1,
                                   ucIPAddress2,
                                   ucNetMask2,
                                   ucGatewayAddress2,
                                   ucDNSServerAddress2,
                                   ucMACAddress );

            /* Add the output function to the endpoint. */
            xEndPoint1.pxNetworkInterface = nondet_bool() ? NULL : malloc( sizeof( *( xEndPoint1.pxNetworkInterface ) ) );

            /* If a network interface has an endpoint, then it must have an output function. */
            __CPROVER_assume( xEndPoint1.pxNetworkInterface != NULL );
            xEndPoint1.pxNetworkInterface->pfOutput = NetworkInterfaceOutput;
        }
    }

    /* The network buffer passed to the vProcessGeneratedUDPPacket
     * cannot be NULL. */
    vProcessGeneratedUDPPacket( pxNetworkBuffer );
}
