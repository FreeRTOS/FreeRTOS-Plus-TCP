/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"

/* Function prvParseDNSReply is proven to be correct separately.
 * The proof can be found here: https://github.com/aws/amazon-freertos/tree/master/tools/cbmc/proofs/ParseDNSReply */
uint32_t prvParseDNSReply( uint8_t * pucUDPPayloadBuffer,
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

    xNetworkBuffer.pucEthernetBuffer = malloc( sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) );

    /* The parameter to the function cannot be NULL. */
    ulDNSHandlePacket( &xNetworkBuffer );
}
