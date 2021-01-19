/* CBMC includes */
#include "cbmc.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_Routing.h"

void harness()
{
    /*
     * The assumption made here is that the buffer pointed by pucEthernetBuffer
     * is at least allocated to sizeof(ARPPacket_t) size but eventually a even larger buffer.
     * This is not checked inside vARPGenerateRequestPacket.
     */
    uint8_t ucBUFFER_SIZE;

    __CPROVER_assume( ucBUFFER_SIZE >= sizeof( ARPPacket_t ) && ucBUFFER_SIZE < 2 * sizeof( ARPPacket_t ) );

    NetworkBufferDescriptor_t xNetworkBuffer2;
    xNetworkBuffer2.xDataLength = ucBUFFER_SIZE;
    xNetworkBuffer2.pucEthernetBuffer = safeMalloc( xNetworkBuffer2.xDataLength );
    __CPROVER_assume( xNetworkBuffer2.pucEthernetBuffer != NULL );

    /* Non-deterministically allocate some memory or return a NULL. */
    xNetworkBuffer2.pxEndPoint = safeMalloc( sizeof( *xNetworkBuffer2.pxEndPoint ) );
    /* vARPGenerateRequestPacket asserts that endpoint cannot be NULL. */
    __CPROVER_assume( xNetworkBuffer2.pxEndPoint != NULL );

    vARPGenerateRequestPacket( &xNetworkBuffer2 );
}
