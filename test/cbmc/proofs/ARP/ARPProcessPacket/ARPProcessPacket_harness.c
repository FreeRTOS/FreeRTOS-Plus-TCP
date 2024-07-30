/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_Routing.h"

/* CBMC includes. */
#include "cbmc.h"

/* This pointer is maintained by the IP-task. Defined in FreeRTOS_IP.c */
extern NetworkBufferDescriptor_t * pxARPWaitingNetworkBuffer;
NetworkEndPoint_t * pxNetworkEndPoint_Temp;

/* Stub FreeRTOS_FindEndPointOnNetMask_IPv6 as its not relevant to the
 * correctness of the proof */
NetworkEndPoint_t * FreeRTOS_FindEndPointOnNetMask_IPv6( const IPv6_Address_t * pxIPv6Address )
{
    __CPROVER_assert( pxIPv6Address != NULL, "Precondition: pxIPv6Address != NULL" );

    /* Assume at least one end-point is available */
    return pxNetworkEndPoint_Temp;
}

/* Stub FreeRTOS_FindEndPointOnNetMask_IPv6 as its not relevant to the
 * correctness of the proof */
NetworkEndPoint_t * FreeRTOS_FindEndPointOnNetMask( uint32_t ulIPAddress,
                                                    uint32_t ulWhere )
{
    /* Assume at least one end-point is available */
    return pxNetworkEndPoint_Temp;
}

/* Get rid of configASSERT in FreeRTOS_TCP_IP.c */
BaseType_t xIsCallingFromIPTask( void )
{
    return pdTRUE;
}

/* This is an output function and need not be tested with this proof. */
void FreeRTOS_OutputARPRequest_Multi( NetworkEndPoint_t * pxEndPoint,
                                      uint32_t ulIPAddress )
{
}

/* This function is proved elsewhere hence stubbing it out */
eARPLookupResult_t eARPGetCacheEntry( uint32_t * pulIPAddress,
                                      MACAddress_t * const pxMACAddress,
                                      struct xNetworkEndPoint ** ppxEndPoint )
{
    eARPLookupResult_t eReturn;

    __CPROVER_assert( pulIPAddress != NULL, "pulIPAddress cannot be NULL." );
    __CPROVER_assert( pxMACAddress != NULL, "pxMACAddress cannot be NULL." );
    __CPROVER_assert( ppxEndPoint != NULL, "ppxEndPoint cannot be NULL." );

    /* Return random value */
    return eReturn;
}

void harness()
{
    NetworkBufferDescriptor_t * pxLocalBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer2;
    TickType_t xBlockTimeTicks;
    uint16_t usEthernetBufferSize;

    /*
     * The assumption made here is that the buffer pointed by pucEthernetBuffer
     * is at least allocated to sizeof(ARPPacket_t) size but eventually an even larger buffer.
     * This is not checked inside eARPProcessPacket.
     */
    uint8_t ucBUFFER_SIZE;


    /* Non deterministically determine whether the pxARPWaitingNetworkBuffer will
     * point to some valid data or will it be NULL. */
    if( nondet_bool() )
    {
        /* The packet must at least be as big as an IP Packet. The size is not
         * checked in the function as the pointer is stored by the IP-task itself
         * and therefore it will always be of the required size. */
        __CPROVER_assume( usEthernetBufferSize >= sizeof( IPPacket_t ) );
        pxLocalBuffer = pxGetNetworkBufferWithDescriptor( usEthernetBufferSize, xBlockTimeTicks );

        /* Since this pointer is maintained by the IP-task, either the pointer
         * pxARPWaitingNetworkBuffer will be NULL or pxLocalBuffer->pucEthernetBuffer
         * will be non-NULL. */
        __CPROVER_assume( pxLocalBuffer != NULL );
        __CPROVER_assume( pxLocalBuffer->pucEthernetBuffer != NULL );
        __CPROVER_assume( pxLocalBuffer->xDataLength == usEthernetBufferSize );

        pxARPWaitingNetworkBuffer = pxLocalBuffer;
    }
    else
    {
        pxARPWaitingNetworkBuffer = NULL;
    }

    pxNetworkBuffer2 = pxGetNetworkBufferWithDescriptor( ucBUFFER_SIZE + sizeof( ARPPacket_t ), xBlockTimeTicks );
    __CPROVER_assume( pxNetworkBuffer2 != NULL );
    __CPROVER_assume( pxNetworkBuffer2->pucEthernetBuffer != NULL );

    /*
     * This proof assumes one end point is present.
     */
    pxNetworkBuffer2->pxEndPoint = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkBuffer2->pxEndPoint != NULL );
    pxNetworkBuffer2->pxEndPoint->pxNext = NULL;

    /* eARPProcessPacket will be called in the source code only after checking if
     * pxNetworkBuffer2->pucEthernetBuffer is not NULL, hence, __CPROVER_assume( xBuffer != NULL );   */
    eARPProcessPacket( pxNetworkBuffer2 );
}
