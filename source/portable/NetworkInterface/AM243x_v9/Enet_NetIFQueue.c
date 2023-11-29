/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

#include <assert.h>
#include "Enet_NetIFQueue.h"
#include <networking/enet/core/include/core/enet_utils.h>
#include <kernel/dpl/HwiP.h>
/*
 * Free queue from which buffer pointers are allocated
 */
NetBufQueue xNetBuffreeQ;
static bool gNetBuf_initialized = false;

static inline void NetBufQueue_assert(uint8_t cond)
{
    assert(cond);
}

/*
 * Initializes the freeQ.
 * MUST BE CALLED BEFORE INITIALIZING THE FIRST BUFFER QUEUE
 * Needs to be called only once as early in the program as possible
 */
void NetBufQueue_init_freeQ(NetBufNode *pfree, uint32_t maxSize)
{
    int fQ_iter;
    NetBufQueue_assert(NULL != pfree);

	if (!gNetBuf_initialized)
    {
        for(fQ_iter=0; fQ_iter<maxSize-1; fQ_iter++)
        {
            pfree[fQ_iter].pxNext = &pfree[fQ_iter+1];
            pfree[fQ_iter].pxNetworkBuffer = NULL;
        }

        pfree[fQ_iter].pxNext = NULL;
        pfree[fQ_iter].pxNetworkBuffer = NULL;

        xNetBuffreeQ.pxHead = &pfree[0];
        xNetBuffreeQ.pxTail = &pfree[maxSize - 1];
        xNetBuffreeQ.uCount = maxSize;

        gNetBuf_initialized = true;
    }
}

/*
 * Allocates memory from the freeQ to be used by other queues
 */
NetBufNode* mempQ_malloc()
{
    NetBufNode* p = xNetBuffreeQ.pxHead;
    xNetBuffreeQ.pxHead = xNetBuffreeQ.pxHead->pxNext;
    xNetBuffreeQ.uCount--;
    return p;
}

/*
 * Returns buffer pointers used by other queues back to freeQ
 */
void mempQ_free(NetBufNode* p)
{
    p->pxNext = NULL;
    p->pxNetworkBuffer = NULL;
    xNetBuffreeQ.pxTail->pxNext = p;
    xNetBuffreeQ.pxTail = p;
    xNetBuffreeQ.uCount++;
}

/*
 * Initializes a queue. Must be called after declaring a queue
 */
void NetBufQueue_init(NetBufQueue *pxNetBufQueue)
{
    uint32_t key = HwiP_disable();
    pxNetBufQueue->pxHead = NULL;
    pxNetBufQueue->pxTail = NULL;
    pxNetBufQueue->uCount = 0;
    HwiP_restore(key);
}

/*
 * Enqueues a buffer to the pxTail of the queue
 */
void NetBufQueue_enQ(NetBufQueue *pxNetBufQueue, NetworkBufferDescriptor_t *p)
{
    NetBufNode* temp = NULL;

    uint32_t key = HwiP_disable();

    temp = mempQ_malloc();
    NetBufQueue_assert(NULL != temp);

    temp->pxNetworkBuffer = p;
    temp->pxNext = NULL;

    if(pxNetBufQueue->uCount == 0)
    {
        pxNetBufQueue->pxHead = temp;
        pxNetBufQueue->pxTail = temp;
    }
    else if(pxNetBufQueue->uCount == 1)
    {
        pxNetBufQueue->pxHead->pxNext = temp;
        pxNetBufQueue->pxTail = temp;
    }
    else
    {
        pxNetBufQueue->pxTail->pxNext = temp;
        pxNetBufQueue->pxTail = pxNetBufQueue->pxTail->pxNext;
    }
    pxNetBufQueue->uCount++;

    HwiP_restore(key);

}

/*
 * Enqueues a packet to the pxHead of the queue.
 * NOT USED ANYWHERE. Can be removed
 */
void NetBufQueue_enQHead(NetBufQueue *pxNetBufQueue, NetworkBufferDescriptor_t *p)
{
    NetBufNode* temp = NULL;
    NetBufQueue_assert(p != NULL);

    temp = mempQ_malloc();
    NetBufQueue_assert(NULL != temp);

    uint32_t key = HwiP_disable();
    temp->pxNetworkBuffer = p;
    temp->pxNext = NULL;
    if(pxNetBufQueue->uCount == 0)
    {
        pxNetBufQueue->pxHead = temp;
        pxNetBufQueue->pxTail = temp;
    }
    else
    {
        temp->pxNext = pxNetBufQueue->pxHead;
        pxNetBufQueue->pxHead = temp;
    }
    HwiP_restore(key);

}

/*
 * Dequeues from the queue
 */
NetworkBufferDescriptor_t* NetBufQueue_deQ(NetBufQueue *pxNetBufQueue)
{
    NetworkBufferDescriptor_t *rtnNetBuf = NULL;
    NetBufNode *temp = NULL;
    uint32_t key = HwiP_disable();

    if(pxNetBufQueue->uCount != 0)
    {
        rtnNetBuf = pxNetBufQueue->pxHead->pxNetworkBuffer;
        temp = pxNetBufQueue->pxHead;
        pxNetBufQueue->pxHead = pxNetBufQueue->pxHead->pxNext;
        if(pxNetBufQueue->uCount == 1)
        {
            pxNetBufQueue->pxTail = NULL;
        }
        pxNetBufQueue->uCount--;

        NetBufQueue_assert(rtnNetBuf != NULL);
        NetBufQueue_assert(rtnNetBuf->pucEthernetBuffer != NULL);
        mempQ_free(temp);
    }

    HwiP_restore(key);

    return rtnNetBuf;
}
