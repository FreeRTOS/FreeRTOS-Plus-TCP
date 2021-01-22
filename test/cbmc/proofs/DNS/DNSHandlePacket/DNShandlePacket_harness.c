/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"

/* Function Abstraction:
 * Function prvParseDNSReply is proven to be correct separately.
 * The proof can be found here: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/tree/labs/ipv6_multi/test/cbmc/proofs/ParseDNSReply */
uint32_t __CPROVER_file_local_FreeRTOS_DNS_c_prvParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                                                               size_t uxBufferLength,
                                                               struct freertos_addrinfo ** ppxAddressInfo,
                                                               BaseType_t xExpected )
{
    uint32_t ulReturn;

    /* Return an arbitrary value. */
    return ulReturn;
}

struct xDNSMessage
{
    uint16_t usIdentifier;
    uint16_t usFlags;
    uint16_t usQuestions;
    uint16_t usAnswers;
    uint16_t usAuthorityRRs;
    uint16_t usAdditionalRRs;
};

typedef struct xDNSMessage DNSMessage_t;

void harness()
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    size_t xEthernetBufferSize;

    /* Allocate arbitrary number of bytes. The packet should be processed
     * only when:
     * number of bytes >= ( sizeof( DNSMessage_t ) + sizeof( UDPPacket_t ) )
     */
    xNetworkBuffer.pucEthernetBuffer = malloc( xEthernetBufferSize );
    xNetworkBuffer.xDataLength = xEthernetBufferSize;

    /* The parameter to the function cannot be NULL. This function is called
     * by the +TCP stack internally and is not an API. */
    ulDNSHandlePacket( &xNetworkBuffer );
}
