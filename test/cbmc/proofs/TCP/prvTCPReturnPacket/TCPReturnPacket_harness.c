/*
 * FreeRTOS memory safety proofs with CBMC.
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
#include "FreeRTOS_Routing.h"

#include "../../utility/memory_assignments.c"

/* This proof assumes that pxDuplicateNetworkBufferWithDescriptor is implemented correctly. */

void __CPROVER_file_local_FreeRTOS_TCP_IP_c_prvTCPReturnPacket( FreeRTOS_Socket_t * pxSocket,
                                                                NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                                uint32_t ulLen,
                                                                BaseType_t xReleaseAfterSend );

/* Abstraction of pxDuplicateNetworkBufferWithDescriptor*/
NetworkBufferDescriptor_t * pxDuplicateNetworkBufferWithDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                    BaseType_t xNewLength )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = ensure_FreeRTOS_NetworkBuffer_is_allocated();

    /* Ensure that the memory is non-NULL and writable. This Macro is
     * defined in memory_assignments.c. */
    if( ensure_memory_is_valid( pxNetworkBuffer, sizeof( *pxNetworkBuffer ) ) )
    {
        pxNetworkBuffer->pucEthernetBuffer = safeMalloc( sizeof( TCPPacket_t ) );
        __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer );
    }

    return pxNetworkBuffer;
}

/* Network Interface Output function is a portable low level function
 * which actually sends the data. We have assumed a correct
 * implementation of this function in this proof. */
BaseType_t NetworkInterfaceOutput( struct xNetworkInterface * pxDescriptor,
                                   NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                   BaseType_t xReleaseAfterSend )
{
    BaseType_t xReturn;

    /* Assert some basic conditions. */
    __CPROVER_assert( pxDescriptor != NULL, "Descriptor cannot be NULL" );
    __CPROVER_assert( pxNetworkBuffer != NULL, "NetworkBuffer cannot be NULL" );

    /* Return an arbitrary value. */
    return xReturn;
}


/* Global variables accessible throughout the program. Used in adding
 * Network interface/endpoint. */
NetworkInterface_t xNetworkInterface1;
NetworkEndPoint_t xEndPoint1;

const uint8_t ucIPAddress2[ 4 ];
const uint8_t ucNetMask2[ 4 ];
const uint8_t ucGatewayAddress2[ 4 ];
const uint8_t ucDNSServerAddress2[ 4 ];
const uint8_t ucMACAddress[ 6 ];

void harness()
{
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
    NetworkBufferDescriptor_t * pxNetworkBuffer = ensure_FreeRTOS_NetworkBuffer_is_allocated();

    /* Define and allocate members of an endpoint to be used later. */
    struct xNetworkEndPoint xLocalEndPoint;

    xLocalEndPoint.pxNetworkInterface = nondet_bool() ? NULL : malloc( sizeof( *( xLocalEndPoint.pxNetworkInterface ) ) );

    /* This cannot be NULL. */
    __CPROVER_assume( xLocalEndPoint.pxNetworkInterface != NULL );

    /* Assign the Network output function to the endpoint. This cannot be NULL. */
    xLocalEndPoint.pxNetworkInterface->pfOutput = NetworkInterfaceOutput;

    /* Assume that the list of interfaces/endpoints is not initialized.
     * These are defined in the FreeRTOS_Routing.c file and used as a
     * list by the TCP stack. */
    __CPROVER_assume( pxNetworkInterfaces == NULL );
    __CPROVER_assume( pxNetworkEndPoints == NULL );

    /* Ensure that the memory is non-NULL and writable. This Macro is
     * defined in memory_assignments.c. */
    if( ensure_memory_is_valid( pxNetworkBuffer, sizeof( *pxNetworkBuffer ) ) )
    {
        pxNetworkBuffer->pucEthernetBuffer = malloc( sizeof( TCPPacket_t ) );
        __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

        pxNetworkBuffer->pxEndPoint = &xLocalEndPoint;
    }

    /* Ensure that the memory is non-NULL and writable. This Macro is
     * defined in memory_assignments.c. */
    if( ensure_memory_is_valid( pxSocket, sizeof( *pxSocket ) ) )
    {
        pxSocket->pxEndPoint = &xLocalEndPoint;
    }

    /* Non-deterministically add a network-interface. */
    if( nondet_bool() )
    {
        /* Add the network interfaces to the list. */
        FreeRTOS_AddNetworkInterface( &xNetworkInterface1 );

        /* Non-deterministically add an end-point to the network-interface. */
        if( nondet_bool() )
        {
            /* Fill the endpoints and put them in the network interface. */
            FreeRTOS_FillEndPoint( &xNetworkInterface1,
                                   &xEndPoint1,
                                   ucIPAddress2,
                                   ucNetMask2,
                                   ucGatewayAddress2,
                                   ucDNSServerAddress2,
                                   ucMACAddress );
        }
    }

    uint32_t ulLen;
    BaseType_t xReleaseAfterSend;

    /* The code does not expect both of these to be equal to NULL at the same time. */
    __CPROVER_assume( pxSocket != NULL || pxNetworkBuffer != NULL );

    __CPROVER_file_local_FreeRTOS_TCP_IP_c_prvTCPReturnPacket( pxSocket, pxNetworkBuffer, ulLen, xReleaseAfterSend );
}
