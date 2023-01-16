/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"

/* This pointer is maintained by the IP-task. Defined in FreeRTOS_IP.c */
extern NetworkBufferDescriptor_t * pxARPWaitingNetworkBuffer;

/* This is an output function and need not be tested with this proof. */
void FreeRTOS_OutputARPRequest( uint32_t ulIPAddress )
{
}

void harness()
{
    ARPPacket_t xARPFrame;
    NetworkBufferDescriptor_t xLocalBuffer;
    uint16_t usEthernetBufferSize;

    /* Non deterministically determine whether the pxARPWaitingNetworkBuffer will
     * point to some valid data or will it be NULL. */
    if( nondet_bool() )
    {
        /* The packet must at least be as big as an IP Packet. The size is not
         * checked in the function as the pointer is stored by the IP-task itself
         * and therefore it will always be of the required size. */
        __CPROVER_assume( usEthernetBufferSize >= sizeof( IPPacket_t ) );

        /* Add matching data length to the network buffer descriptor. */
        __CPROVER_assume( xLocalBuffer.xDataLength == usEthernetBufferSize );

        xLocalBuffer.pucEthernetBuffer = malloc( usEthernetBufferSize );

        /* Since this pointer is maintained by the IP-task, either the pointer
         * pxARPWaitingNetworkBuffer will be NULL or xLocalBuffer.pucEthernetBuffer
         * will be non-NULL. */
        __CPROVER_assume( xLocalBuffer.pucEthernetBuffer != NULL );

        pxARPWaitingNetworkBuffer = &xLocalBuffer;
    }
    else
    {
        pxARPWaitingNetworkBuffer = NULL;
    }

    eARPProcessPacket( &xARPFrame );
}
