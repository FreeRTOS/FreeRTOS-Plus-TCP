/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"

/* CBMC includes. */
#include "cbmc.h"

/* Function DNS_ParseDNSReply is proven to be correct separately. */
uint32_t DNS_ParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                            size_t uxBufferLength,
                            struct freertos_addrinfo ** ppxAddressInfo,
                            BaseType_t xExpected,
                            uint16_t usPort )
{
    __CPROVER_assert( pucUDPPayloadBuffer != NULL, "pucUDPPayloadBuffer cannot be NULL" );
    return nondet_uint32();
}

void harness()
{
    NetworkBufferDescriptor_t xNetworkBuffer;

    xNetworkBuffer.pucEthernetBuffer = malloc( sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) );
    __CPROVER_assume( xNetworkBuffer.pucEthernetBuffer != NULL );

    ulDNSHandlePacket( &xNetworkBuffer );
}
