/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_Stream_Buffer.h"
#include "FreeRTOS_Routing.h"

/* This proof assumes FreeRTOS_socket, pxTCPSocketLookup and
 * pxGetNetworkBufferWithDescriptor are implemented correctly.
 *
 * It also assumes prvSingleStepTCPHeaderOptions, prvCheckOptions, prvTCPPrepareSend,
 * prvTCPHandleState and prvTCPReturnPacket are correct. These functions are
 * proved to be correct separately. */

/* Abstraction of FreeRTOS_socket */
Socket_t FreeRTOS_socket( BaseType_t xDomain,
                          BaseType_t xType,
                          BaseType_t xProtocol )
{
    return nondet_bool() ? NULL : malloc( sizeof( FreeRTOS_Socket_t ) );
}

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

/* Abstraction of pxTCPSocketLookup */
FreeRTOS_Socket_t * pxTCPSocketLookup( UBaseType_t uxLocalPort,
                                       uint32_t ulRemoteIP,
                                       UBaseType_t uxRemotePort )
{
    FreeRTOS_Socket_t * xRetSocket = nondet_bool() ? NULL : malloc( sizeof( FreeRTOS_Socket_t ) );

    if( xRetSocket )
    {
        xRetSocket->u.xTCP.txStream = nondet_bool() ? NULL : malloc( sizeof( StreamBuffer_t ) );
        xRetSocket->u.xTCP.pxPeerSocket = nondet_bool() ? NULL : malloc( sizeof( StreamBuffer_t ) );
        xRetSocket->pxEndPoint = nondet_bool() ? NULL : malloc( sizeof( *( xRetSocket->pxEndPoint ) ) );

        /* Since the socket is bound, it must have an endpoint. */
        __CPROVER_assume( xRetSocket->pxEndPoint != NULL );

        if( xIsCallingFromIPTask() == pdFALSE )
        {
            xRetSocket->u.xTCP.bits.bPassQueued = pdFALSE_UNSIGNED;
            xRetSocket->u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;
        }
    }

    return xRetSocket;
}

/* Abstraction of pxGetNetworkBufferWithDescriptor */
NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = nondet_bool() ? NULL : malloc( sizeof( NetworkBufferDescriptor_t ) );

    if( pxNetworkBuffer )
    {
        pxNetworkBuffer->pucEthernetBuffer = nondet_bool() ? NULL : malloc( xRequestedSizeBytes );
        __CPROVER_assume( pxNetworkBuffer->xDataLength == ipSIZE_OF_ETH_HEADER + sizeof( int32_t ) );
    }

    return pxNetworkBuffer;
}

BaseType_t vSocketBind( FreeRTOS_Socket_t * pxSocket,
                        struct freertos_sockaddr * pxBindAddress,
                        size_t uxAddressLength,
                        BaseType_t xInternal )
{
    __CPROVER_assert( pxSocket != NULL, "The socket cannot be NULL" );
    __CPROVER_assert( pxBindAddress != NULL, "The bind address cannot be NULL" );

    /* Called from socket copying function. Since there is an existing socket
     * which is receiving the TCP data, it must be bound to an endpoint. Thus,
     * bind the copied socket to an endpoint to which the parent socket is
     * bound. */
    pxSocket->pxEndPoint = nondet_bool() ? NULL : malloc( sizeof( *( pxSocket->pxEndPoint ) ) );

    __CPROVER_assume( pxSocket->pxEndPoint != NULL );
}

/* Abstraction of xSocketValid. Used to determine whether a socket is valid or not. */
BaseType_t xSocketValid( ConstSocket_t xSocket )
{
    BaseType_t xReturn = pdFALSE;

    if( ( xSocket != NULL ) && ( xSocket != FREERTOS_INVALID_SOCKET ) )
    {
        xReturn = pdTRUE;
    }

    return xReturn;
}

void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = nondet_bool() ? NULL : malloc( sizeof( NetworkBufferDescriptor_t ) );

    __CPROVER_assume( pxNetworkBuffer != NULL );

    size_t xLocalSize;
    __CPROVER_assume( xLocalSize >= sizeof( TCPPacket_t ) &&
                      xLocalSize <= ipTOTAL_ETHERNET_FRAME_SIZE );

    pxNetworkBuffer->pucEthernetBuffer = nondet_bool() ? NULL : malloc( xLocalSize );

    /* Since this function is only called when there is a TCP packet (implying
     * there is an ethernet buffer), assume that the buffer is non-NULL. */
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Arbitrarily assign an endpoint or NULL. */
    pxNetworkBuffer->pxEndPoint = nondet_bool() ? NULL : malloc( sizeof( *( pxNetworkBuffer->pxEndPoint ) ) );

    xProcessReceivedTCPPacket( pxNetworkBuffer );
}
