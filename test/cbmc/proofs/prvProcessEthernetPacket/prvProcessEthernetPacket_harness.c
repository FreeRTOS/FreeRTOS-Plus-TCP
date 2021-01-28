/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_Routing.h"

#include "memory_assignments.c"
#include "freertos_api.c"

/****************************************************************
* Signature of function under test
****************************************************************/
void __CPROVER_file_local_FreeRTOS_IP_c_prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );


/* This function has been proved to be memory safe in another proof (in ARP/ARPRefreshCacheEntry). Hence we assume it to be correct here. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                            const uint32_t ulIPAddress )
{
    /* pxMACAddress can be NULL or non-NULL. No need to assert. */
}

/* This function has been proved to be memory safe in another proof (in ARP/ARPProcessPacket). Hence we assume it to be correct here. */
eFrameProcessingResult_t eARPProcessPacket( ARPPacket_t * const pxARPFrame )
{
    __CPROVER_assert( pxARPFrame != NULL, "pxARPFrame cannot be NULL" );

    eFrameProcessingResult_t eReturn;

    return eReturn;
}

/* This function has been proved to be memory safe in another proof (in parsing/ProcessIPPacket). Hence we assume it to be correct here. */
eFrameProcessingResult_t __CPROVER_file_local_FreeRTOS_IP_c_prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                                                                NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    __CPROVER_assert( pxIPPacket != NULL, "pxIPPacket cannot be NULL" );
    __CPROVER_assert( pxNetworkBuffer != NULL, "pxNetworkBuffer cannot be NULL" );

    eFrameProcessingResult_t result;

    return result;
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
    __CPROVER_assert( pxDescriptor, "Descriptor cannot be NULL" );
    __CPROVER_assert( pxNetworkBuffer, "NetworkBuffer cannot be NULL" );

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

        /* Fill the endpoints and put them in the network interface. */
        FreeRTOS_FillEndPoint( &xNetworkInterface1,
                               &xEndPoint1,
                               ucIPAddress2,
                               ucNetMask2,
                               ucGatewayAddress2,
                               ucDNSServerAddress2,
                               ucMACAddress );

        /* Add the output function to the endpoint. It will be called
         * if this endpoint is found. */
        xEndPoint1.pxNetworkInterface->pfOutput = NetworkInterfaceOutput;
    }

    /* Define and allocate members of an endpoint to be used later. */
    struct xNetworkEndPoint xLocalEndPoint;

    xLocalEndPoint.pxNetworkInterface = nondet_bool() ? NULL : malloc( sizeof( *( xLocalEndPoint.pxNetworkInterface ) ) );

    /* The network interface of the endpoint cannot be NULL. */
    __CPROVER_assume( xLocalEndPoint.pxNetworkInterface != NULL );

    /* The output function should also not be NULL */
    xLocalEndPoint.pxNetworkInterface->pfOutput = NetworkInterfaceOutput;

    NetworkBufferDescriptor_t * const pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( ipTOTAL_ETHERNET_FRAME_SIZE, 0 );

    __CPROVER_assume( pxNetworkBuffer != NULL );
    pxNetworkBuffer->pxEndPoint = nondet_bool() ? NULL : &xLocalEndPoint;

    /* The network buffer cannot be NULL for this function call. If it is, it will hit an assert in the function. */
    __CPROVER_assume( pxNetworkBuffer != NULL );

    __CPROVER_file_local_FreeRTOS_IP_c_prvProcessEthernetPacket( pxNetworkBuffer );
}
