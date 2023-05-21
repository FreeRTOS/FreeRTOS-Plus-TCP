/*
 *  Copyright (C) 2018-2021 Texas Instruments Incorporated
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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
