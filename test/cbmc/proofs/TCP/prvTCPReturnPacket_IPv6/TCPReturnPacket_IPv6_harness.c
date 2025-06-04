/*
 * FreeRTOS memory safety proofs with CBMC.
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_TCP_Transmission.h"
#include "FreeRTOS_ND.h"

/* CBMC includes. */
#include "cbmc.h"

/*
 * This function is implemented by a third party.
 * After looking through a couple of samples in the demos folder, it seems
 * like the only shared contract is that you want to add the if statement
 * for releasing the buffer to the end. Apart from that, it is up to the vendor,
 * how to write this code out to the network.
 */
BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxDescriptor != NULL, "The network interface cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer descriptor cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer->pucEthernetBuffer != NULL, "The ethernet buffer cannot be NULL." );

    if( xReleaseAfterSend != pdFALSE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

    return 0;
}

/* Memory assignment for FreeRTOS_Socket_t */
FreeRTOS_Socket_t * ensure_FreeRTOS_Socket_t_is_allocated()
{
    size_t buf_size; /* Give buffer_size an unconstrained value */
    FreeRTOS_Socket_t * pxSocket = safeMalloc( sizeof( FreeRTOS_Socket_t ) + sizeof( IPTCPSocket_t ) );

    __CPROVER_assume( pxSocket != NULL );
    pxSocket->u.xTCP.rxStream = safeMalloc( sizeof( StreamBuffer_t ) );
    pxSocket->u.xTCP.txStream = safeMalloc( sizeof( StreamBuffer_t ) );
    pxSocket->u.xTCP.pxPeerSocket = safeMalloc( sizeof( FreeRTOS_Socket_t ) );
    pxSocket->pxEndPoint = safeMalloc( sizeof( NetworkEndPoint_t ) );
    pxSocket->u.xTCP.pxAckMessage = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );

    if( pxSocket->u.xTCP.pxAckMessage != NULL )
    {
        __CPROVER_assume( ( buf_size > ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( TCPHeader_t ) ) ) && ( buf_size < ipconfigNETWORK_MTU ) );
        pxSocket->u.xTCP.pxAckMessage->pucEthernetBuffer = safeMalloc( buf_size );
        __CPROVER_assume( pxSocket->u.xTCP.pxAckMessage->pucEthernetBuffer != NULL );
    }

    return pxSocket;
}

void prvTCPReturnPacket_IPV4( FreeRTOS_Socket_t * pxSocket,
                              NetworkBufferDescriptor_t * pxDescriptor,
                              uint32_t ulLen,
                              BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxSocket != NULL, "pxSocket cannot be NULL" );
    __CPROVER_assert( pxDescriptor != NULL, "pxDescriptor cannot be NULL" );
}

/* Abstraction of eNDGetCacheEntry. */
eARPLookupResult_t eNDGetCacheEntry( IPv6_Address_t * pxIPAddress,
                                     MACAddress_t * const pxMACAddress,
                                     struct xNetworkEndPoint ** ppxEndPoint )
{
    eARPLookupResult_t xReturn;

    __CPROVER_assert( __CPROVER_r_ok( pxIPAddress, sizeof( IPv6_Address_t ) ), "pxIPAddress must be readable" );
    __CPROVER_assert( __CPROVER_w_ok( pxMACAddress, sizeof( MACAddress_t ) ), "pxMACAddress must be writeable" );

    return xReturn;
}

/* Abstraction of this functions creates an endpoint and assign it to network interface
 * endpoint, real endpoint doesn't matter in this test. */
void prvTCPReturn_SetEndPoint( const FreeRTOS_Socket_t * pxSocket,
                               NetworkBufferDescriptor_t * pxNetworkBuffer,
                               size_t uxIPHeaderSize )
{
    NetworkEndPoint_t * pxEndPoint = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

    __CPROVER_assume( pxEndPoint != NULL );

    /* Add an interface */
    pxEndPoint->pxNetworkInterface = ( NetworkInterface_t * ) safeMalloc( sizeof( NetworkInterface_t ) );
    __CPROVER_assume( pxEndPoint->pxNetworkInterface != NULL );

    pxEndPoint->pxNetworkInterface->pfOutput = NetworkInterfaceOutputFunction_Stub;

    pxNetworkBuffer->pxEndPoint = pxEndPoint;
}

/* Abstraction of pxDuplicateNetworkBufferWithDescriptor*/
NetworkBufferDescriptor_t * pxDuplicateNetworkBufferWithDescriptor( const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                    size_t xNewLength )
{
    NetworkBufferDescriptor_t * pxLocalNetworkBuffer;
    EthernetHeader_t * pxHeader;

    pxLocalNetworkBuffer = pxGetNetworkBufferWithDescriptor( xNewLength, 0 );

    if( pxLocalNetworkBuffer != NULL )
    {
        /* In this test case, we only focus on IPv6. */
        pxHeader = ( ( const EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );
        __CPROVER_assume( pxHeader->usFrameType == ipIPv6_FRAME_TYPE );

        /* Add an end point to the network buffer present. Its assumed that the
         * network interface layer correctly assigns the end point to the generated buffer. */
        pxLocalNetworkBuffer->pxEndPoint = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
        __CPROVER_assume( pxLocalNetworkBuffer->pxEndPoint != NULL );
        pxLocalNetworkBuffer->pxEndPoint->pxNext = NULL;

        /* Add an interface */
        pxLocalNetworkBuffer->pxEndPoint->pxNetworkInterface = ( NetworkInterface_t * ) safeMalloc( sizeof( NetworkInterface_t ) );
        __CPROVER_assume( pxLocalNetworkBuffer->pxEndPoint->pxNetworkInterface != NULL );

        pxLocalNetworkBuffer->pxEndPoint->pxNetworkInterface->pfOutput = NetworkInterfaceOutputFunction_Stub;
    }

    return pxLocalNetworkBuffer;
}

uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    uint16_t usReturn;

    __CPROVER_assert( pucEthernetBuffer != NULL, "The ethernet buffer cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pucEthernetBuffer, uxBufferLength ), "pucEthernetBuffer should be readable." );

    return usReturn;
}

uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
    uint16_t usReturn;

    __CPROVER_assert( pucNextData != NULL, "The next data pointer cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pucNextData, uxByteCount ), "The pucNextData should be readable." );

    return usReturn;
}

void harness()
{
    FreeRTOS_Socket_t * pxSocket;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    BaseType_t xReleaseAfterSend;
    uint32_t ulLen;
    EthernetHeader_t * pxHeader;

    pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();

    if( pxSocket != NULL )
    {
        /* In this test case, we only focus on IPv6. */
        __CPROVER_assume( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED );
    }

    __CPROVER_assume( ( ulLen >= sizeof( TCPPacket_IPv6_t ) ) && ( ulLen < ipconfigNETWORK_MTU - ipSIZE_OF_ETH_HEADER ) );
    pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( ulLen + ipSIZE_OF_ETH_HEADER, 0 );

    /* The code does not expect both of these to be equal to NULL at the same time. */
    __CPROVER_assume( pxSocket != NULL || pxNetworkBuffer != NULL );
    /* ucPeerWinScaleFactor is limited in range [0,14]. */
    __CPROVER_assume( pxSocket->u.xTCP.ucMyWinScaleFactor <= tcpTCP_OPT_WSOPT_MAXIMUM_VALUE );

    /* If network buffer is properly created. */
    if( pxNetworkBuffer != NULL )
    {
        /* In this test case, we only focus on IPv6. */
        pxHeader = ( ( const EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer );
        __CPROVER_assume( pxHeader->usFrameType == ipIPv6_FRAME_TYPE );

        /* Add an end point to the network buffer present. Its assumed that the
         * network interface layer correctly assigns the end point to the generated buffer. */
        pxNetworkBuffer->pxEndPoint = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

        if( pxNetworkBuffer->pxEndPoint != NULL )
        {
            /* Add an interface */
            pxNetworkBuffer->pxEndPoint->pxNetworkInterface = ( NetworkInterface_t * ) safeMalloc( sizeof( NetworkInterface_t ) );
            __CPROVER_assume( pxNetworkBuffer->pxEndPoint->pxNetworkInterface != NULL );
            pxNetworkBuffer->pxEndPoint->pxNetworkInterface->pfOutput = NetworkInterfaceOutputFunction_Stub;
        }
    }
    /* If not. */
    else
    {
        /* Assume that the length is proper. The length should be between this range. It
         * is made so by the functions up the call tree. Essentially, this is equal to a
         * TCP packet header with and without TCP options. */
        __CPROVER_assume( ( ulLen >= ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_TCP_HEADER ) &&
                          ( ulLen <= ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_TCP_HEADER + 40 /* Maximum option bytes. */ ) );
    }

    prvTCPReturnPacket( pxSocket, pxNetworkBuffer, ulLen, xReleaseAfterSend );
}
