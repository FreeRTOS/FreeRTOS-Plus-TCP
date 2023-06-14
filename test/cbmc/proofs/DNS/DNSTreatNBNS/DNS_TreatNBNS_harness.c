/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DNS_Parser.h"
#include "FreeRTOS_IP_Private.h"

#include "cbmc.h"

NetworkBufferDescriptor_t xNetworkBuffer;

NetworkBufferDescriptor_t * pxUDPPayloadBuffer_to_NetworkBuffer( const void * pvBuffer )
{
    __CPROVER_assert(pvBuffer != NULL, "Precondition: pvBuffer != NULL");
    NetworkBufferDescriptor_t * pxRBuf;

    if(nondet_bool())
    {
        pxRBuf = NULL;
    }
    else
    {   
        pxRBuf = &xNetworkBuffer;
    }

    return pxRBuf;
}

NetworkBufferDescriptor_t * pxResizeNetworkBufferWithDescriptor( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                                 size_t xNewSizeBytes )
{
    NetworkBufferDescriptor_t * pxRBuf;

    __CPROVER_assert(pxNetworkBuffer != NULL, "pxNetworkBuffer: pvBuffer != NULL");

    uint8_t *pucNewBuffer = malloc(xNewSizeBytes);
    __CPROVER_assume( pucNewBuffer != NULL );

    pxNetworkBuffer->pucEthernetBuffer = pucNewBuffer;

    if(nondet_bool())
    {
        pxRBuf = NULL;
    }
    else
    {   
        pxRBuf = pxNetworkBuffer;
    }
    
    return pxRBuf;

}

/* prepareReplyDNSMessage is proved separately */
void prepareReplyDNSMessage( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                     BaseType_t lNetLength )
{
    __CPROVER_assert(pxNetworkBuffer != NULL, "pxNetworkBuffer: pvBuffer != NULL");
}

void harness()
{

    
    uint32_t ulIPAddress;

    NetworkEndPoint_t * pxNetworkEndPoint_Temp = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

    BaseType_t xDataSize;
    __CPROVER_assume( (xDataSize != 0)  && (xDataSize < (ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER - (sizeof( NBNSAnswer_t ) - 2 * sizeof( uint16_t )))));
    xNetworkBuffer.pucEthernetBuffer = safeMalloc( xDataSize );
    xNetworkBuffer.xDataLength = xDataSize;

    if(nondet_bool())
    {
        xNetworkBuffer.pxEndPoint = pxNetworkEndPoint_Temp;
    }
    else
    {
        xNetworkBuffer.pxEndPoint = NULL;
    }

    //DNS_TreatNBNS(xNetworkBuffer.pucEthernetBuffer, xNetworkBuffer.xDataLength, ulIPAddress);
    ulNBNSHandlePacket(&xNetworkBuffer);

}
