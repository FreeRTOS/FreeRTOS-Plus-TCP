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

/* DNS_TreatNBNS is proved separately */
void DNS_TreatNBNS( uint8_t * pucPayload,
                            size_t uxBufferLength,
                            uint32_t ulIPAddress )
{
    __CPROVER_assert(pucPayload != NULL, "Precondition: pucPayload != NULL");
}

void harness()
{

    
    uint32_t ulIPAddress;

    NetworkEndPoint_t * pxNetworkEndPoint_Temp = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

    BaseType_t xDataSize;

    /* Assume an upper limit on max memory that can be allocated */
    __CPROVER_assume( (xDataSize < (ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER )));
    xNetworkBuffer.xDataLength = xDataSize;


    xNetworkBuffer.pucEthernetBuffer = safeMalloc( xDataSize );

    /* pucEthernetBuffer being not NULL is pre validated before the call to ulNBNSHandlePacket */
    __CPROVER_assume(xNetworkBuffer.pucEthernetBuffer != NULL);
    

    if(nondet_bool())
    {
        xNetworkBuffer.pxEndPoint = pxNetworkEndPoint_Temp;
    }
    else
    {
        xNetworkBuffer.pxEndPoint = NULL;
    }

    ulNBNSHandlePacket(&xNetworkBuffer);

}
