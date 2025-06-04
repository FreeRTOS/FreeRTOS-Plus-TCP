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

/* This proof assumes pxTCPSocketLookup, vTCPStateChange, prvTCPSocketIsActive, xIsCallingFromIPTask,
 * xSequenceGreaterThan, xSequenceLessThan, xTaskGetTickCount, vReleaseNetworkBufferAndDescriptor, xTCPWindowTxHasData and
 * pxGetNetworkBufferWithDescriptor are implemented correctly.
 *
 * It also assumes prvSingleStepTCPHeaderOptions, prvCheckOptions, prvTCPPrepareSend,
 * prvTCPHandleState, prvHandleListen_IPV6 and prvTCPReturnPacket are correct. These functions are
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

/* Abstraction of prvHandleListen */
FreeRTOS_Socket_t * prvHandleListen( FreeRTOS_Socket_t * pxSocket,
                                     NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    FreeRTOS_Socket_t * xRetSocket = ensure_FreeRTOS_Socket_t_is_allocated();

    if( xRetSocket )
    {
        /* This test case is for IPv6. */
        __CPROVER_assume( xRetSocket->bits.bIsIPv6 == pdTRUE );
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
        /* This test case is for IPv6. */
        __CPROVER_assume( xRetSocket->bits.bIsIPv6 == pdTRUE );
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
        __CPROVER_assume( pxNetworkBuffer->xDataLength == ipSIZE_OF_ETH_HEADER + sizeof( int32_t ) );
    }

    return pxNetworkBuffer;
}

/* Abstraction of uxIPHeaderSizePacket. Because we're testing IPv6 in this test case, the network buffer is
 * guaranteed to be IPv6 packet. Thus returns IPv6 header size here directly. */
size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    return ipSIZE_OF_IPv6_HEADER;
}

/* Abstraction of uxIPHeaderSizePacket. Because we're testing IPv6 in this test case, all socket handlers returned
 * by functions are for IPv6. Thus returns IPv6 header size here directly. */
size_t uxIPHeaderSizeSocket( const FreeRTOS_Socket_t * pxSocket )
{
    return ipSIZE_OF_IPv6_HEADER;
}

void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    EthernetHeader_t * pxEthernetHeader;
    size_t tcpPacketSize;

    __CPROVER_assume( tcpPacketSize >= ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( TCPHeader_t ) ) );

    pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( tcpPacketSize, 0 );

    /* To avoid asserting on the ethernet buffer being NULL. */
    __CPROVER_assume( pxNetworkBuffer != NULL );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* In this test case, we focus on IPv6 packets. */
    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    __CPROVER_assume( pxEthernetHeader->usFrameType == ipIPv6_FRAME_TYPE );

    xProcessReceivedTCPPacket( pxNetworkBuffer );
}
