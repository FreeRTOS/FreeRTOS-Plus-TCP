/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* CBMC includes. */
#include "cbmc.h"

/* prvProcessICMPEchoReply() is file-local (static); exported for verification
 * via --export-file-local-symbols. */
void __CPROVER_file_local_FreeRTOS_ICMP_c_prvProcessICMPEchoReply( const NetworkBufferDescriptor_t * const pxNetworkBuffer );

/* Application hook invoked with the ping-reply result. Body does not matter. */
void vApplicationPingReplyHook( ePingReplyStatus_t eStatus,
                                uint16_t usIdentifier )
{
}

void harness()
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    size_t xDataLength;

    /* Minimal assumptions: the caller (ProcessICMPPacket) guarantees the frame
     * is at least an ICMPPacket_t. Beyond that the length is nondeterministic.
     * The data-scan loop is bounded by (xDataLength - headers), so capping the
     * upper bound keeps the loop finite while leaving the wire-derived length
     * field (usLength) fully nondeterministic. */
    __CPROVER_assume( ( xDataLength >= sizeof( ICMPPacket_t ) ) &&
                      ( xDataLength <= ( sizeof( ICMPPacket_t ) + 20U ) ) );

    /* Allocate exactly xDataLength bytes so any read past the reported length
     * is a genuine out-of-bounds access, not a harness artifact. */
    uint8_t * pucEthernetBuffer = ( uint8_t * ) safeMalloc( xDataLength );
    __CPROVER_assume( pucEthernetBuffer != NULL );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = xDataLength;

    __CPROVER_file_local_FreeRTOS_ICMP_c_prvProcessICMPEchoReply( &xNetworkBuffer );
}
