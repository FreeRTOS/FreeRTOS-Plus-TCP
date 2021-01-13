/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_Routing.h"

/* Provide a stub for the interface output function. This is the low
 * level output function which is plaform dependent. */
BaseType_t xLocalNetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                         NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                         BaseType_t bReleaseAfterSend )
{
    BaseType_t xReturn;

    return xReturn;
}

/*We assume that the pxGetNetworkBufferWithDescriptor function is implemented correctly and returns a valid data structure. */
/*This is the mock to mimic the correct expected behavior. If this allocation fails, this might invalidate the proof. */
NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) malloc( sizeof( NetworkBufferDescriptor_t ) );

    __CPROVER_assume( pxNetworkBuffer != NULL );

    pxNetworkBuffer->pucEthernetBuffer = malloc( xRequestedSizeBytes );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    pxNetworkBuffer->xDataLength = xRequestedSizeBytes;
    return pxNetworkBuffer;
}

void harness()
{
    NetworkInterface_t xNetworkInterface1, xNetworkInterface2;
    NetworkEndPoint_t xEndPoint1, xEndPoint2;

    const uint8_t ucIPAddress2[ 4 ];
    const uint8_t ucNetMask2[ 4 ];
    const uint8_t ucGatewayAddress2[ 4 ];
    const uint8_t ucDNSServerAddress2[ 4 ];
    const uint8_t ucMACAddress[ 6 ];

    /* Assume that the list of interfaces/endpoints is not initialized. */
    __CPROVER_assume( pxNetworkInterfaces == NULL );
    __CPROVER_assume( pxNetworkEndPoints == NULL );

    /* Add the network interfaces to the list. */
    FreeRTOS_AddNetworkInterface( &xNetworkInterface1 );
    FreeRTOS_AddNetworkInterface( &xNetworkInterface2 );

    /* Fill the endpoints and put them in the network interface. */
    FreeRTOS_FillEndPoint( &xNetworkInterface1,
                           &xEndPoint1,
                           ucIPAddress2,
                           ucNetMask2,
                           ucGatewayAddress2,
                           ucDNSServerAddress2,
                           ucMACAddress );
    FreeRTOS_FillEndPoint( &xNetworkInterface2,
                           &xEndPoint2,
                           ucIPAddress2,
                           ucNetMask2,
                           ucGatewayAddress2,
                           ucDNSServerAddress2,
                           ucMACAddress );

    /* Add in the output function. */
    xNetworkInterface1.pfOutput = xLocalNetworkInterfaceOutput;
    xNetworkInterface2.pfOutput = xLocalNetworkInterfaceOutput;

    /* Call the function. */
    vARPAgeCache();
}
