/*
 * FreeRTOS memory safety proofs with CBMC.
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_Routing.h"

ARPPacket_t xARPPacket;
NetworkBufferDescriptor_t xNetworkBuffer;

/* STUB!
 * We assume that the pxGetNetworkBufferWithDescriptor function is
 * implemented correctly and returns a valid data structure.
 * This is the mock to mimic the expected behavior.
 * If this allocation fails, this might invalidate the proof.
 * FreeRTOS_OutputARPRequest calls pxGetNetworkBufferWithDescriptor
 * to get a NetworkBufferDescriptor. Then it calls vARPGenerateRequestPacket
 * passing this buffer along in the function call. vARPGenerateRequestPacket
 * casts the pointer xNetworkBuffer.pucEthernetBuffer into an ARPPacket_t pointer
 * and writes a complete ARPPacket to it. Therefore the buffer has to be at least of the size
 * of an ARPPacket to guarantee memory safety.
 */
NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    #ifdef CBMC_PROOF_ASSUMPTION_HOLDS
        #ifdef ipconfigETHERNET_MINIMUM_PACKET_BYTES
            xNetworkBuffer.pucEthernetBuffer = malloc( ipconfigETHERNET_MINIMUM_PACKET_BYTES );
        #else
            xNetworkBuffer.pucEthernetBuffer = malloc( xRequestedSizeBytes );
        #endif
    #else
        uint32_t malloc_size;
        __CPROVER_assert( !__CPROVER_overflow_mult( 2, xRequestedSizeBytes ) );
        __CPROVER_assume( malloc_size > 0 && malloc_size < 2 * xRequestedSizeBytes );
        xNetworkBuffer.pucEthernetBuffer = malloc( malloc_size );
    #endif
    __CPROVER_assume( xNetworkBuffer.pucEthernetBuffer != NULL );

    xNetworkBuffer.xDataLength = xRequestedSizeBytes;
    return &xNetworkBuffer;
}


/* Provide a stub for the interface output function. This is the low
 * level output function which is platform dependent. */
BaseType_t xLocalNetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                         NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                         BaseType_t bReleaseAfterSend )
{
    BaseType_t xReturn;

    /* Assert that these parameters are non NULL. */
    __CPROVER_assert( pxInterface != NULL, "pxInterface cannot be NULL here" );
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer cannot be NULL" );

    /* Return a random value. */
    return xReturn;
}


void harness()
{
    uint32_t ulIPAddress;

    NetworkInterface_t xNetworkInterface1;
    NetworkEndPoint_t xEndPoint1;

    const uint8_t ucIPAddress2[ 4 ];
    const uint8_t ucNetMask2[ 4 ];
    const uint8_t ucGatewayAddress2[ 4 ];
    const uint8_t ucDNSServerAddress2[ 4 ];
    const uint8_t ucMACAddress[ 6 ];

    /* Assume that the list of interfaces/endpoints is not initialized. */
    __CPROVER_assume( pxNetworkInterfaces == NULL );
    __CPROVER_assume( pxNetworkEndPoints == NULL );

    /* Non-deterministically add a network-interface and its endpoint. */
    if( nondet_bool() )
    {
        /* Add the network interfaces to the list. */
        FreeRTOS_AddNetworkInterface( &xNetworkInterface1 );

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

        /* Add in the output function. */
        xNetworkInterface1.pfOutput = xLocalNetworkInterfaceOutput;
    }

    FreeRTOS_OutputARPRequest( ulIPAddress );
}
