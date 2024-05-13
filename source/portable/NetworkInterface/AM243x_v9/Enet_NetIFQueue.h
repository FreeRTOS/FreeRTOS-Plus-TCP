#ifndef ENET_NETIF_NETBUFQ_H_
#define ENET_NETIF_NETBUFQ_H_

#include "FreeRTOS_IP.h"

#define uNetworkBufferDescriptorQueue_count( nQ )    ( ( nQ )->uCount )

/* Buffer pointer structure definition */
struct Enet_NetIF_NetBufNode
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    struct Enet_NetIF_NetBufNode * pxNext;
};
typedef struct Enet_NetIF_NetBufNode NetBufNode;

/* Queue structure definition */
struct Enet_NetIF_NetBufQueue
{
    NetBufNode * pxHead, * pxTail;
    uint32_t uCount;
};
typedef struct Enet_NetIF_NetBufQueue NetBufQueue;

void NetBufQueue_init_freeQ( NetBufNode * pfree,
                             uint32_t maxSize );
void NetBufQueue_init( NetBufQueue * pxNetBufQueue );
void NetBufQueue_enQ( NetBufQueue * pxNetBufQueue,
                      NetworkBufferDescriptor_t * pxNetworkBuffer );
void NetBufQueue_enQHead( NetBufQueue * pxNetBufQueue,
                          NetworkBufferDescriptor_t * pxNetworkBuffer );
NetworkBufferDescriptor_t * NetBufQueue_deQ( NetBufQueue * pxNetBufQueue );

#endif /* ENET_NETIF_NETBUFQ_H_ */
