/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_Stream_Buffer.h"

/* CBMC includes. */
#include "cbmc.h"
#include "../../utility/memory_assignments.c"

/* This proof assumes pxTCPSocketLookup and pxGetNetworkBufferWithDescriptor
 * are implemented correctly.
 *
 * It also assumes prvSingleStepTCPHeaderOptions, prvCheckOptions, prvTCPPrepareSend,
 * prvTCPHandleState, prvHandleListen_IPV4 and prvTCPReturnPacket are correct. These functions are
 * proved to be correct separately. */

/* Abstraction of xTaskGetCurrentTaskHandle */
TaskHandle_t xTaskGetCurrentTaskHandle( void )
{
    static int xIsInit = 0;
    static TaskHandle_t pxCurrentTCB;
    TaskHandle_t xRandomTaskHandle; /* not initialized on purpose */

    if( xIsInit == 0 )
    {
        pxCurrentTCB = xRandomTaskHandle;
        xIsInit = 1;
    }

    return pxCurrentTCB;
}

/* Abstraction of vTCPStateChange */
void vTCPStateChange( FreeRTOS_Socket_t * pxSocket,
                      enum eTCP_STATE eTCPState )
{
}

/* prvTCPReturnPacket is proven separately */
void prvTCPReturnPacket( FreeRTOS_Socket_t * pxSocket,
                         NetworkBufferDescriptor_t * pxDescriptor,
                         uint32_t ulLen,
                         BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxSocket != NULL || pxDescriptor != NULL, "Either pxSocket or pxDescriptor must be non-NULL" );
    __CPROVER_assert( pxDescriptor->pucEthernetBuffer != NULL, "pucEthernetBuffer should not be NULL" );
}

/* prvTCPPrepareSend is proven separately. */
int32_t prvTCPPrepareSend( FreeRTOS_Socket_t * pxSocket,
                           NetworkBufferDescriptor_t ** ppxNetworkBuffer,
                           UBaseType_t uxOptionsLength )
{
    int32_t ret = nondet_int32();

    __CPROVER_assert( pxSocket != NULL, "pxSocket cannot be NULL" );
    __CPROVER_assert( *ppxNetworkBuffer != NULL, "*ppxNetworkBuffer cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( ( *ppxNetworkBuffer )->pucEthernetBuffer, ( *ppxNetworkBuffer )->xDataLength ), "Data in *ppxNetworkBuffer must be readable" );

    __CPROVER_assume( ret >= 0 && ret <= ipconfigNETWORK_MTU );
    return ret;
}

/* prvTCPHandleState is proven separately. */
BaseType_t prvTCPHandleState( FreeRTOS_Socket_t * pxSocket,
                              NetworkBufferDescriptor_t ** ppxNetworkBuffer )
{
    __CPROVER_assert( pxSocket != NULL, "pxSocket cannot be NULL" );
    __CPROVER_assert( *ppxNetworkBuffer != NULL, "*ppxNetworkBuffer cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( ( *ppxNetworkBuffer )->pucEthernetBuffer, ( *ppxNetworkBuffer )->xDataLength ), "Data in *ppxNetworkBuffer must be readable" );

    return nondet_basetype();
}

/* prvCheckOptions is proven separately. */
BaseType_t prvCheckOptions( FreeRTOS_Socket_t * pxSocket,
                            const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    __CPROVER_assert( pxSocket != NULL, "pxSocket cannot be NULL" );
    __CPROVER_assert( pxNetworkBuffer != NULL, "*ppxNetworkBuffer cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength ), "Data in *ppxNetworkBuffer must be readable" );

    return nondet_basetype();
}

BaseType_t xTCPWindowTxHasData( TCPWindow_t const * pxWindow,
                                uint32_t ulWindowSize,
                                TickType_t * pulDelay )
{
    __CPROVER_assert( pxWindow != NULL, "pxWindow cannot be NULL" );
    __CPROVER_assert( pulDelay != NULL, "pulDelay cannot be NULL" );

    return nondet_basetype();
}

/* Abstraction of xSequenceLessThan */
BaseType_t xSequenceLessThan( uint32_t a,
                              uint32_t b )
{
    return nondet_basetype();
}

/* Abstraction of xSequenceGreaterThan */
BaseType_t xSequenceGreaterThan( uint32_t a,
                                 uint32_t b )
{
    return nondet_basetype();
}

/* Abstraction of prvHandleListen_IPV4 */
FreeRTOS_Socket_t * prvHandleListen_IPV4( FreeRTOS_Socket_t * pxSocket,
                                          NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    FreeRTOS_Socket_t * xRetSocket = ensure_FreeRTOS_Socket_t_is_allocated();

    if( xRetSocket )
    {
        /* This test case is for IPv4. */
        __CPROVER_assume( xRetSocket->bits.bIsIPv6 == pdFALSE );
    }

    return xRetSocket;
}

/* Abstraction of pxTCPSocketLookup */
FreeRTOS_Socket_t * pxTCPSocketLookup( uint32_t ulLocalIP,
                                       UBaseType_t uxLocalPort,
                                       IPv46_Address_t xRemoteIP,
                                       UBaseType_t uxRemotePort )
{
    FreeRTOS_Socket_t * xRetSocket = ensure_FreeRTOS_Socket_t_is_allocated();

    if( xRetSocket )
    {
        /* This test case is for IPv4. */
        __CPROVER_assume( xRetSocket->bits.bIsIPv6 == pdFALSE );
        __CPROVER_assume( xRetSocket->u.xTCP.ucPeerWinScaleFactor <= tcpTCP_OPT_WSOPT_MAXIMUM_VALUE );
    }

    return xRetSocket;
}

/* Abstraction of pxGetNetworkBufferWithDescriptor */
NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );

    if( pxNetworkBuffer )
    {
        pxNetworkBuffer->pucEthernetBuffer = safeMalloc( xRequestedSizeBytes );
        pxNetworkBuffer->xDataLength = xRequestedSizeBytes;
    }

    return pxNetworkBuffer;
}

/* Abstraction of uxIPHeaderSizePacket. Because we're testing IPv4 in this test case, the network buffer is
 * guaranteed to be IPv4 packet. Thus returns IPv4 header size here directly. */
size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    return ipSIZE_OF_IPv4_HEADER;
}

/* Abstraction of uxIPHeaderSizePacket. Because we're testing IPv4 in this test case, all socket handlers returned
 * by functions are for IPv4. Thus returns IPv4 header size here directly. */
size_t uxIPHeaderSizeSocket( const FreeRTOS_Socket_t * pxSocket )
{
    return ipSIZE_OF_IPv4_HEADER;
}

void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    size_t tcpPacketSize;

    __CPROVER_assume( tcpPacketSize >= ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + sizeof( TCPHeader_t ) ) );

    pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( tcpPacketSize, 0 );


    /* To avoid asserting on the network buffer being NULL. */
    __CPROVER_assume( pxNetworkBuffer != NULL );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    xProcessReceivedTCPPacket( pxNetworkBuffer );
}
