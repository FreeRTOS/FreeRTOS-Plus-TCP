/*
 * FreeRTOS memory safety proof for parseDNSAnswer().
 *
 * parseDNSAnswer() walks the "answer" records of a DNS response.  Every byte
 * it reads originates from an attacker-controlled UDP payload, so this proof
 * models the message with fully nondeterministic contents and allocates it to
 * EXACTLY the modeled payload length: any read outside
 * pxSet->pucUDPPayloadBuffer[ 0 .. pxSet->uxBufferLength ) is therefore a
 * genuine out-of-bounds bug, not a proof artifact.  pxSet->pucByte points at a
 * nondeterministic offset within that message, which is what makes the
 * compression-pointer path of the answer-name validation reachable.
 *
 * The unparsed tail deliberately is NOT modeled as an object of its own: the
 * function resolves compression pointers against the start of the message, so
 * every byte of the message -- not just the tail -- is legal for it to read,
 * exactly as it is for the real caller in DNS_ParseDNSReply().
 */

/* Standard includes. */
#include <stdint.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "list.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DNS_Parser.h"
#include "FreeRTOS_DNS_Globals.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"
#include "IPTraceMacroDefaults.h"

#include "cbmc.h"

/****************************************************************
* Signature of the function under test
****************************************************************/

uint32_t parseDNSAnswer( ParseSet_t * pxSet,
                         struct freertos_addrinfo ** ppxAddressInfo,
                         size_t * uxBytesRead );

/****************************************************************
* Stubs for callees that live OUTSIDE FreeRTOS_DNS_Parser.c.
* DNS_SkipNameField (which advances pucByte over a name field) and the
* owner-name decoder both live in the same translation unit and are linked
* in for real, so they are NOT stubbed here.
****************************************************************/

/* usChar2u16 reads two bytes from the packet in host order.  The exact value
 * is irrelevant to memory safety, but the read itself must be in-bounds. */
uint16_t usChar2u16( const uint8_t * pucPtr )
{
    uint16_t ret;

    __CPROVER_assert( __CPROVER_r_ok( pucPtr, 2 ), "usChar2u16: 2 bytes must be legal to read" );
    return ret;
}

/* Allocate a fresh addrinfo (or fail).  The real function copies pcName and
 * the address bytes; those copies are proved elsewhere.  Returning nondet
 * NULL / non-NULL exercises both linked-list insertion branches. */
struct freertos_addrinfo * pxNew_AddrInfo( const char * pcName,
                                           BaseType_t xFamily,
                                           const uint8_t * pucAddress )
{
    struct freertos_addrinfo * pxAddr;

    if( nondet_bool() )
    {
        pxAddr = NULL;
    }
    else
    {
        pxAddr = safeMalloc( sizeof( struct freertos_addrinfo ) );
        __CPROVER_assume( pxAddr != NULL );
        pxAddr->ai_next = NULL;
    }

    return pxAddr;
}

/****************************************************************
* Proof harness
****************************************************************/

void harness()
{
    ParseSet_t xSet;
    struct freertos_addrinfo * pxAddressInfo = NULL;
    struct freertos_addrinfo ** ppxAddressInfo;
    size_t uxBytesRead;
    size_t uxPayloadLength;
    size_t uxParsed;

    /* The modeled message has to be allocatable as a single CBMC object.
     * Checked against the proof parameter rather than assumed of the modeled
     * length, so that raising NETWORK_BUFFER_SIZE past the limit fails the
     * proof instead of silently shrinking what it covers. */
    __CPROVER_assert( NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE,
                      "NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE" );

    /* Bound the modeled payload length just enough to keep the name-parse and
     * answer-record loops finite (mirrors the small payload bounds used by the
     * DNS_ParseDNSReply proof).  It is otherwise nondeterministic so the
     * parser's length arithmetic is fully exercised. */
    __CPROVER_assume( uxPayloadLength <= NETWORK_BUFFER_SIZE );

    /* Number of payload bytes the caller has already consumed, i.e. how far
     * into the message pucByte points.  Nondeterministic so that both the
     * "answer name is inline" and "answer name is a compression pointer back
     * into the question section" cases are reachable. */
    __CPROVER_assume( uxParsed <= uxPayloadLength );

    /* Start from a clean ParseSet_t, then set only the fields parseDNSAnswer
     * reads.  memset mirrors DNS_ParseDNSReply, which zero-inits the struct. */
    ( void ) memset( &xSet, 0, sizeof( xSet ) );

    /* Allocate the DNS message to EXACTLY the modeled payload length, so any
     * read outside it is a genuine out-of-bounds access.  parseDNSAnswer
     * resolves compression pointers relative to pucUDPPayloadBuffer, so the
     * whole message must be modeled, not just the unparsed tail. */
    xSet.pucUDPPayloadBuffer = safeMalloc( uxPayloadLength );
    __CPROVER_assume( xSet.pucUDPPayloadBuffer != NULL );
    xSet.uxBufferLength = uxPayloadLength;

    /* Establish the caller's invariant: pucByte points at the first unparsed
     * byte within the message and uxSourceBytesRemaining is the count of bytes
     * that are legal to read from there onward. */
    xSet.pucByte = &( xSet.pucUDPPayloadBuffer[ uxParsed ] );
    xSet.uxSourceBytesRemaining = uxPayloadLength - uxParsed;

    /* Number of answer records claimed by the (attacker-controlled) header. */
    xSet.usAnswers = nondet_uint16();

    /* Records already stored is bounded by its natural range. */
    xSet.usNumARecordsStored = nondet_uint16();

    /* The linked-list tail pointer is wired to the local as the real caller
     * does. */
    xSet.ppxLastAddress = &( xSet.pxLastAddress );

    /* pxDNSMessageHeader is only dereferenced on the logging / cache path
     * (usIdentifier).  Give it a valid backing object. */
    xSet.pxDNSMessageHeader = safeMalloc( sizeof( DNSMessage_t ) );
    __CPROVER_assume( xSet.pxDNSMessageHeader != NULL );

    ppxAddressInfo = &pxAddressInfo;

    ( void ) parseDNSAnswer( &xSet, ppxAddressInfo, &uxBytesRead );
}
