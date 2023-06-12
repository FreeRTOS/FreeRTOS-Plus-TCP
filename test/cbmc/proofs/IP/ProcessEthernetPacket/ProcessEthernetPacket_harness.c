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

#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* eARPProcessPacket() is proved separately */
eFrameProcessingResult_t eARPProcessPacket( ARPPacket_t * const pxARPFrame )
{
    __CPROVER_assert(pxARPFrame != NULL, "pxARPFrame != NULL");
    eFrameProcessingResult_t retVal;
    return retVal;
}

/* vReturnEthernetFrame() is proved separately */
void vReturnEthernetFrame( NetworkBufferDescriptor_t * pxNetworkBuffer,
                           BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert(pxNetworkBuffer != NULL, "xNetworkBuffer != NULL");
}

void __CPROVER_file_local_FreeRTOS_IP_c_prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

/* The harness test proceeds to call prvProcessEthernetPacket with an unconstrained value */
void harness()
{

    NetworkBufferDescriptor_t * const pxNetworkBuffer = malloc( sizeof( NetworkBufferDescriptor_t ) );

    __CPROVER_assume( pxNetworkBuffer != NULL );

    /* Points to ethernet buffer offset by ipIP_TYPE_OFFSET, this make sure the buffer allocation is similar
     * to the pxGetNetworkBufferWithDescriptor */
    pxNetworkBuffer->pucEthernetBuffer = ( ( ( uint8_t * ) malloc( ipTOTAL_ETHERNET_FRAME_SIZE ) ) + ipIP_TYPE_OFFSET );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Minimum length of the pxNetworkBuffer->xDataLength is at least the size of the IPPacket_t. */
    __CPROVER_assume( pxNetworkBuffer->xDataLength >= sizeof( IPPacket_t ) && pxNetworkBuffer->xDataLength <= ipTOTAL_ETHERNET_FRAME_SIZE );

    __CPROVER_file_local_FreeRTOS_IP_c_prvProcessEthernetPacket( pxNetworkBuffer );

}
