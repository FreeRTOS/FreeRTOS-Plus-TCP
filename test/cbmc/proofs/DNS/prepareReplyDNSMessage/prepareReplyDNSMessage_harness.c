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
NetworkEndPoint_t * pxNetworkEndPoint_Temp;

/* Stub FreeRTOS_FindEndPointOnNetMask_IPv6 as its not relevant to the 
correctness of the proof */
NetworkEndPoint_t * FreeRTOS_FindEndPointOnNetMask_IPv6( const IPv6_Address_t * pxIPv6Address )
{
    __CPROVER_assert(pxIPv6Address != NULL, "Precondition: pxIPv6Address != NULL");

    /* Assume atleast one end-point is available */
    return pxNetworkEndPoint_Temp;
}

/* Stub FreeRTOS_FindEndPointOnNetMask_IPv6 as its not relevant to the 
correctness of the proof */
NetworkEndPoint_t * FreeRTOS_FindEndPointOnNetMask( uint32_t ulIPAddress,
                                                        uint32_t ulWhere )
{

    /* Assume atleast one end-point is available */
    return pxNetworkEndPoint_Temp;

}

/* The checksum generation is stubbed out since the actual checksum
* does not matter. The stub will return an indeterminate value each time. */
uint16_t usGenerateChecksum( uint16_t usSum,
                                const uint8_t * pucNextData,
                                size_t uxByteCount )
{
    uint16_t usReturn;

    __CPROVER_assert( pucNextData != NULL, "Next data cannot be NULL" );

    /* Return an indeterminate value. */
    return usReturn;
}

/* The checksum generation is stubbed out since the actual checksum
* does not matter. The stub will return an indeterminate value each time. */
uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                        size_t uxBufferLength,
                                        BaseType_t xOutgoingPacket )
{
    uint16_t usReturn;

    __CPROVER_assert( pucEthernetBuffer != NULL, "Ethernet buffer cannot be NULL" );

    /* Return an indeterminate value. */
    return usReturn;
}

void harness()
{

    
    uint32_t ulIPAddress;
    uint16_t usLength;

    /* Assume atleast 1 valid endpoint */
    pxNetworkEndPoint_Temp = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume(pxNetworkEndPoint_Temp != NULL);

    BaseType_t xDataSize;
    /* The pucEthernetBuffer is re adjusted to the following size before the
    call to prepareReplyDNSMessage by pxResizeNetworkBufferWithDescriptor. If buffer allocation
    scheme #1 (BufferAllocation_1.c) is used we assert if the needed size is actually present
    in the buffer.  */
    __CPROVER_assume( (xDataSize > (sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t ) + sizeof( NBNSAnswer_t ) - 2 * sizeof( uint16_t ))) );
    
    xNetworkBuffer.pucEthernetBuffer = malloc( xDataSize );
    /* xNetworkBuffer.pucEthernetBuffer is checked if its valid before the call to
    prepareReplyDNSMessage() */
    __CPROVER_assume(xNetworkBuffer.pucEthernetBuffer != NULL);

    xNetworkBuffer.xDataLength = xDataSize;

    prepareReplyDNSMessage(&xNetworkBuffer, usLength);

}
