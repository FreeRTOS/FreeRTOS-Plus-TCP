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
 * The proof can be found here: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/tree/labs/ipv6_multi/test/cbmc/proofs/ParseDNSReply.
 * Note: this function is defined as static in FreeRTOS_DNS.c.
 * To access this function outside of that file, we have used
 * a CBMC flag (--export-file-local-symbols). Using that flag
 * mangles the names of static functions. Thus, the below
 * function name is also mangled. */
uint32_t __CPROVER_file_local_FreeRTOS_DNS_c_prvParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                                                               size_t uxBufferLength,
                                                               struct freertos_addrinfo ** ppxAddressInfo,
                                                               BaseType_t xExpected )
{
    uint32_t ulReturn;

    /* Return an arbitrary value. */
    return ulReturn;
}

void harness()
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    size_t xEthernetBufferSize;

    /* Allocate arbitrary number of bytes. */
    xNetworkBuffer.pucEthernetBuffer = malloc( xEthernetBufferSize );
    xNetworkBuffer.xDataLength = xEthernetBufferSize;

    /* The parameter to the function cannot be NULL. This function is called
     * by the +TCP stack internally and is not an API. */
    ulDNSHandlePacket( &xNetworkBuffer );
}
