/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"

#include "cbmc.h"

size_t prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                            const char * pcHostName,
                            TickType_t uxIdentifier,
                            UBaseType_t uxHostType );

void harness()
{
    size_t uxExpectedPayloadLength;
    TickType_t uxIdentifier;
    UBaseType_t uxHostType;
    size_t len;

    /* Make sure the string has a valid but bounded length */
    __CPROVER_assume( len > 0 && len <= MAX_HOSTNAME_LEN );

    /* pcHostName is tested to be valid prior */
    char * pcHostName = malloc( len );

    if( len && pcHostName )
    {
        /* Make sure the string ends with a NULL, this is expected */
        pcHostName[ len - 1 ] = NULL;
    }

    /* prvCreateDNSMessage() is expected to be called with a ethernet buffer of
     * the following size */
    uxExpectedPayloadLength = sizeof( DNSMessage_t ) +
                              strlen( pcHostName ) +
                              sizeof( uint16_t ) +
                              sizeof( uint16_t ) + 2U;

    /* Add header size */
    if( nondet_bool() )
    {
        uxExpectedPayloadLength += ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_UDP_HEADER;
    }
    else
    {
        uxExpectedPayloadLength += ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER;
    }

    /* pucUDPPayloadBuffer is tested to be valid prior */
    uint8_t * pucUDPPayloadBuffer = malloc( uxExpectedPayloadLength );

    prvCreateDNSMessage( pucUDPPayloadBuffer, pcHostName, uxIdentifier, uxHostType );
}
