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

/**
 * @file FreeRTOS_UDP_Sockets.c
 * @brief Implements the UDP Sockets API based on Berkeley sockets for the FreeRTOS+TCP network
 *        stack. Sockets are used by the application processes to interact with the IP-task
 *        which in turn interacts with the hardware.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "event_groups.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_UDP_Sockets.h"
#include "FreeRTOS_Sockets_Private.h"
#if ( ipconfigUSE_IPv4 != 0 )
    #include "FreeRTOS_IPv4_Sockets.h"
#endif
#if ( ipconfigUSE_IPv6 != 0 )
    #include "FreeRTOS_IPv6_Sockets.h"
#endif

/*-----------------------------------------------------------*/

/** @brief Check if a socket is already bound to a 'random' port number,
 * if not, try bind it to port 0.
 */
static BaseType_t prvMakeSureSocketIsBound( FreeRTOS_Socket_t * pxSocket );

static int32_t prvRecvFrom_CopyPacket( uint8_t * pucEthernetBuffer,
                                       void * pvBuffer,
                                       size_t uxBufferLength,
                                       BaseType_t xFlags,
                                       int32_t lDataLength );

static NetworkBufferDescriptor_t * prvRecvFromWaitForPacket( FreeRTOS_Socket_t const * pxSocket,
                                                             BaseType_t xFlags,
                                                             EventBits_t * pxEventBits );

static int32_t prvSendTo_ActualSend( const FreeRTOS_Socket_t * pxSocket,
                                     const void * pvBuffer,
                                     size_t uxTotalDataLength,
                                     BaseType_t xFlags,
                                     const struct freertos_sockaddr * pxDestinationAddress,
                                     size_t uxPayloadOffset );

static int32_t prvSendUDPPacket( const FreeRTOS_Socket_t * pxSocket,
                                 NetworkBufferDescriptor_t * pxNetworkBuffer,
                                 size_t uxTotalDataLength,
                                 BaseType_t xFlags,
                                 const struct freertos_sockaddr * pxDestinationAddress,
                                 TickType_t xTicksToWait,
                                 size_t uxPayloadOffset );

/*-----------------------------------------------------------*/

extern List_t xBoundUDPSocketsList;

/*-----------------------------------------------------------*/

/**
 * @brief Check if a socket is a valid UDP socket. In case it is not
 *        yet bound, bind it to port 0 ( random port ).
 * @param[in] pxSocket: The socket that must be bound to a port number.
 * @return Returns pdTRUE if the socket was already bound, or if the
 *         socket has been bound successfully.
 */
static BaseType_t prvMakeSureSocketIsBound( FreeRTOS_Socket_t * pxSocket )
{
    /* Check if this is a valid UDP socket, does not have to be bound yet. */
    BaseType_t xReturn = vSocketValid( pxSocket, FREERTOS_IPPROTO_UDP, pdFALSE );

    if( ( xReturn == pdTRUE ) && ( !socketSOCKET_IS_BOUND( pxSocket ) ) )
    {
        /* The socket is valid but it is not yet bound. */
        if( FreeRTOS_bind( pxSocket, NULL, 0U ) != 0 )
        {
            /* The socket was not yet bound, and binding it has failed. */
            xReturn = pdFALSE;
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Called by FreeRTOS_recvfrom(). it will copy the received data
 *        or just a pointer to the received data in case of zero-copy,
 *        to the buffer provided by the caller.
 * @param[in] pucEthernetBuffer: The packet that was received.
 * @param[in] pvBuffer: The user-supplied buffer.
 * @param[in] uxBufferLength: The size of the user-supplied buffer.
 * @param[in] xFlags: Only 'FREERTOS_ZERO_COPY' will be tested.
 * @param[in] lDataLength: The number of bytes in the UDP payload.
 * @return The number of bytes copied to the use buffer.
 */
static int32_t prvRecvFrom_CopyPacket( uint8_t * pucEthernetBuffer,
                                       void * pvBuffer,
                                       size_t uxBufferLength,
                                       BaseType_t xFlags,
                                       int32_t lDataLength )
{
    int32_t lReturn = lDataLength;
    const void * pvCopySource;

    if( ( ( UBaseType_t ) xFlags & ( UBaseType_t ) FREERTOS_ZERO_COPY ) == 0U )
    {
        /* The zero copy flag is not set.  Truncate the length if it won't
         * fit in the provided buffer. */
        if( lReturn > ( int32_t ) uxBufferLength )
        {
            iptraceRECVFROM_DISCARDING_BYTES( ( uxBufferLength - lReturn ) );
            lReturn = ( int32_t ) uxBufferLength;
        }

        /* Copy the received data into the provided buffer, then release the
         * network buffer. */
        pvCopySource = ( const void * ) pucEthernetBuffer;
        ( void ) memcpy( pvBuffer, pvCopySource, ( size_t ) lReturn );
    }
    else
    {
        /* The zero copy flag was set.  pvBuffer is not a buffer into which
         * the received data can be copied, but a pointer that must be set to
         * point to the buffer in which the received data has already been
         * placed. */
        *( ( void ** ) pvBuffer ) = ( void * ) pucEthernetBuffer;
    }

    return lReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief : called from FreeRTOS_recvfrom(). This function waits for an incoming
 *          UDP packet, or until a time-out occurs.
 * @param[in] pxSocket : The socket that receives UDP packets.
 * @param[in] xFlags : The flags as passed to FreeRTOS_recvfrom().
 * @param[in,out] pxEventBits : The last even received in this function,
 *                              either eSOCKET_INTR or eSOCKET_RECEIVE.
 */
static NetworkBufferDescriptor_t * prvRecvFromWaitForPacket( FreeRTOS_Socket_t const * pxSocket,
                                                             BaseType_t xFlags,
                                                             EventBits_t * pxEventBits )
{
    BaseType_t xTimed = pdFALSE;
    TickType_t xRemainingTime = pxSocket->xReceiveBlockTime;
    BaseType_t lPacketCount;
    TimeOut_t xTimeOut;
    EventBits_t xEventBits = ( EventBits_t ) 0;
    NetworkBufferDescriptor_t * pxNetworkBuffer = NULL;

    lPacketCount = ( BaseType_t ) listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) );

    while( lPacketCount == 0 )
    {
        if( xTimed == pdFALSE )
        {
            /* Check to see if the socket is non blocking on the first
             * iteration.  */
            if( xRemainingTime == ( TickType_t ) 0 )
            {
                #if ( ipconfigSUPPORT_SIGNALS != 0 )
                    {
                        /* Just check for the interrupt flag. */
                        xEventBits = xEventGroupWaitBits( pxSocket->xEventGroup, ( EventBits_t ) eSOCKET_INTR,
                                                          pdTRUE /*xClearOnExit*/, pdFALSE /*xWaitAllBits*/, socketDONT_BLOCK );
                    }
                #endif /* ipconfigSUPPORT_SIGNALS */
                break;
            }

            if( ( ( ( UBaseType_t ) xFlags ) & ( ( UBaseType_t ) FREERTOS_MSG_DONTWAIT ) ) != 0U )
            {
                break;
            }

            /* To ensure this part only executes once. */
            xTimed = pdTRUE;

            /* Fetch the current time. */
            vTaskSetTimeOutState( &xTimeOut );
        }

        /* Wait for arrival of data.  While waiting, the IP-task may set the
         * 'eSOCKET_RECEIVE' bit in 'xEventGroup', if it receives data for this
         * socket, thus unblocking this API call. */
        xEventBits = xEventGroupWaitBits( pxSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ),
                                          pdTRUE /*xClearOnExit*/, pdFALSE /*xWaitAllBits*/, xRemainingTime );

        #if ( ipconfigSUPPORT_SIGNALS != 0 )
            {
                if( ( xEventBits & ( EventBits_t ) eSOCKET_INTR ) != 0U )
                {
                    if( ( xEventBits & ( EventBits_t ) eSOCKET_RECEIVE ) != 0U )
                    {
                        /* Shouldn't have cleared the eSOCKET_RECEIVE flag. */
                        ( void ) xEventGroupSetBits( pxSocket->xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE );
                    }

                    break;
                }
            }
        #else /* if ( ipconfigSUPPORT_SIGNALS != 0 ) */
            {
                ( void ) xEventBits;
            }
        #endif /* ipconfigSUPPORT_SIGNALS */

        lPacketCount = ( BaseType_t ) listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) );

        if( lPacketCount != 0 )
        {
            break;
        }

        /* Has the timeout been reached ? */
        if( xTaskCheckForTimeOut( &xTimeOut, &xRemainingTime ) != pdFALSE )
        {
            break;
        }
    } /* while( lPacketCount == 0 ) */

    if( lPacketCount > 0 )
    {
        taskENTER_CRITICAL();
        {
            /* The owner of the list item is the network buffer. */
            pxNetworkBuffer = ( ( NetworkBufferDescriptor_t * ) listGET_OWNER_OF_HEAD_ENTRY( &( pxSocket->u.xUDP.xWaitingPacketsList ) ) );

            if( ( ( UBaseType_t ) xFlags & ( UBaseType_t ) FREERTOS_MSG_PEEK ) == 0U )
            {
                /* Remove the network buffer from the list of buffers waiting to
                 * be processed by the socket. */
                ( void ) uxListRemove( &( pxNetworkBuffer->xBufferListItem ) );
            }
        }
        taskEXIT_CRITICAL();
    }

    *pxEventBits = xEventBits;

    return pxNetworkBuffer;
}
/*-----------------------------------------------------------*/

/**
 * @brief Called by FreeRTOS_sendto(), it will actually send a UDP packet.
 * @param[in] pxSocket: The socket used for sending.
 * @param[in] pvBuffer: The character buffer as provided by the caller.
 * @param[in] uxTotalDataLength: The number of byte in the buffer.
 * @param[in] xFlags: The flags that were passed to FreeRTOS_sendto()
 *                    It will test for FREERTOS_MSG_DONTWAIT and for
 *                    FREERTOS_ZERO_COPY.
 * @param[in] pxDestinationAddress: The IP-address to which the packet must be sent.
 * @param[in] uxPayloadOffset: The calculated UDP payload offset, which depends
 *                             on the IP type: IPv4 or IPv6.
 * @return The number of bytes stored in the socket for transmission.
 */
static int32_t prvSendTo_ActualSend( const FreeRTOS_Socket_t * pxSocket,
                                     const void * pvBuffer,
                                     size_t uxTotalDataLength,
                                     BaseType_t xFlags,
                                     const struct freertos_sockaddr * pxDestinationAddress,
                                     size_t uxPayloadOffset )
{
    int32_t lReturn = 0;
    TickType_t xTicksToWait = pxSocket->xSendBlockTime;
    TimeOut_t xTimeOut;
    NetworkBufferDescriptor_t * pxNetworkBuffer;

    if( ( ( ( UBaseType_t ) xFlags & ( UBaseType_t ) FREERTOS_MSG_DONTWAIT ) != 0U ) ||
        ( xIsCallingFromIPTask() != pdFALSE ) )
    {
        /* The caller wants a non-blocking operation. When called by the IP-task,
         * the operation should always be non-blocking. */
        xTicksToWait = ( TickType_t ) 0U;
    }

    if( ( ( UBaseType_t ) xFlags & ( UBaseType_t ) FREERTOS_ZERO_COPY ) == 0U )
    {
        /* Zero copy is not set, so obtain a network buffer into
         * which the payload will be copied. */
        vTaskSetTimeOutState( &xTimeOut );

        /* Block until a buffer becomes available, or until a
         * timeout has been reached */
        pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxPayloadOffset + uxTotalDataLength, xTicksToWait );

        if( pxNetworkBuffer != NULL )
        {
            void * pvCopyDest = ( void * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxPayloadOffset ] );
            ( void ) memcpy( pvCopyDest, pvBuffer, uxTotalDataLength );

            if( xTaskCheckForTimeOut( &xTimeOut, &xTicksToWait ) == pdTRUE )
            {
                /* The entire block time has been used up. */
                xTicksToWait = ( TickType_t ) 0;
            }
        }
    }
    else
    {
        /* When zero copy is used, pvBuffer is a pointer to the
         * payload of a buffer that has already been obtained from the
         * stack.  Obtain the network buffer pointer from the buffer. */
        pxNetworkBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pvBuffer );
    }

    if( pxNetworkBuffer != NULL )
    {
        pxNetworkBuffer->pxEndPoint = pxSocket->pxEndPoint;
        lReturn = prvSendUDPPacket( pxSocket,
                                    pxNetworkBuffer,
                                    uxTotalDataLength,
                                    xFlags,
                                    pxDestinationAddress,
                                    xTicksToWait,
                                    uxPayloadOffset );
    }
    else
    {
        /* If errno was available, errno would be set to
         * FREERTOS_ENOPKTS.  As it is, the function must return the
         * number of transmitted bytes, so the calling function knows
         * how  much data was actually sent. */
        iptraceNO_BUFFER_FOR_SENDTO();
    }

    return lReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Forward a UDP packet to the IP-task, so it will be sent.
 * @param[in] pxSocket : The socket on which a packet is sent.
 * @param[in] pxNetworkBuffer : The packet to be sent.
 * @param[in] uxTotalDataLength : The total number of payload bytes in the packet.
 * @param[in] xFlags : The flag 'FREERTOS_ZERO_COPY' will be checked.
 * @param[in] pxDestinationAddress : The address of the destination.
 * @param[in] xTicksToWait : Number of ticks to wait, in case the IP-queue is full.
 * @param[in] uxPayloadOffset : The number of bytes in the packet before the payload.
 * @return The number of bytes sent on success, otherwise zero.
 */
static int32_t prvSendUDPPacket( const FreeRTOS_Socket_t * pxSocket,
                                 NetworkBufferDescriptor_t * pxNetworkBuffer,
                                 size_t uxTotalDataLength,
                                 BaseType_t xFlags,
                                 const struct freertos_sockaddr * pxDestinationAddress,
                                 TickType_t xTicksToWait,
                                 size_t uxPayloadOffset )
{
    int32_t lReturn = 0;
    IPStackEvent_t xStackTxEvent = { eStackTxEvent, NULL };

    if( pxDestinationAddress->sin_family == ( uint8_t ) FREERTOS_AF_INET6 )
    {
        #if ( ipconfigUSE_IPv6 != 0 )
            ( void ) xSend_UDP_Update_IPv6( pxNetworkBuffer, pxDestinationAddress );
        #endif
    }
    else
    {
        #if ( ipconfigUSE_IPv4 != 0 )
            ( void ) xSend_UDP_Update_IPv4( pxNetworkBuffer, pxDestinationAddress );
        #endif
    }

    pxNetworkBuffer->xDataLength = uxTotalDataLength + uxPayloadOffset;
    pxNetworkBuffer->usPort = pxDestinationAddress->sin_port;
    pxNetworkBuffer->usBoundPort = ( uint16_t ) socketGET_SOCKET_PORT( pxSocket );

    /* The socket options are passed to the IP layer in the
     * space that will eventually get used by the Ethernet header. */
    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] = pxSocket->ucSocketOptions;

    /* Tell the networking task that the packet needs sending. */
    xStackTxEvent.pvData = pxNetworkBuffer;

    /* Ask the IP-task to send this packet */
    if( xSendEventStructToIPTask( &xStackTxEvent, xTicksToWait ) == pdPASS )
    {
        /* The packet was successfully sent to the IP task. */
        lReturn = ( int32_t ) uxTotalDataLength;
        #if ( ipconfigUSE_CALLBACKS == 1 )
            {
                if( ipconfigIS_VALID_PROG_ADDRESS( pxSocket->u.xUDP.pxHandleSent ) )
                {
                    pxSocket->u.xUDP.pxHandleSent( pxSocket, uxTotalDataLength );
                }
            }
        #endif /* ipconfigUSE_CALLBACKS */
    }
    else
    {
        /* If the buffer was allocated in this function, release
         * it. */
        if( ( ( UBaseType_t ) xFlags & ( UBaseType_t ) FREERTOS_ZERO_COPY ) == 0U )
        {
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
        }

        iptraceSTACK_TX_EVENT_LOST( ipSTACK_TX_EVENT );
    }

    return lReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Find the UDP socket corresponding to the port number.
 *
 * @param[in] uxLocalPort: The port whose corresponding bound UDP socket
 *                         is to be found.
 *
 * @return The socket owning the port if found or else NULL.
 */
FreeRTOS_Socket_t * pxUDPSocketLookup( UBaseType_t uxLocalPort )
{
    const ListItem_t * pxListItem;
    FreeRTOS_Socket_t * pxSocket = NULL;

    /* Looking up a socket is quite simple, find a match with the local port.
     *
     * See if there is a list item associated with the port number on the
     * list of bound sockets. */
    pxListItem = pxListFindListItemWithValue( &xBoundUDPSocketsList, ( TickType_t ) uxLocalPort );

    if( pxListItem != NULL )
    {
        /* The owner of the list item is the socket itself. */
        pxSocket = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxListItem ) );
        configASSERT( pxSocket != NULL );
    }

    return pxSocket;
}
/*-----------------------------------------------------------*/

#if ( ( ipconfigHAS_PRINTF != 0 ) )

/**
 * @brief Print a summary of all sockets and their connections.
 */
    BaseType_t vUDPNetStat( void )
    {
        /* Show a simple listing of all created sockets and their connections */
        const ListItem_t * pxIterator;
        BaseType_t count = 0;

        if( !listLIST_IS_INITIALISED( &xBoundUDPSocketsList ) )
        {
            FreeRTOS_printf( ( "PLUS-TCP UDP not initialized\n" ) );
        }
        else
        {
            /* Casting a "MiniListItem_t" to a "ListItem_t".
             * This is safe because only its address is being accessed, not its fields. */
            const ListItem_t * pxEndUDP = listGET_END_MARKER( &xBoundUDPSocketsList );

            for( pxIterator = listGET_HEAD_ENTRY( &xBoundUDPSocketsList );
                 pxIterator != pxEndUDP;
                 pxIterator = listGET_NEXT( pxIterator ) )
            {
                /* Local port on this machine */
                FreeRTOS_printf( ( "UDP Port %5u\n",
                                   FreeRTOS_ntohs( listGET_LIST_ITEM_VALUE( pxIterator ) ) ) );
                count++;
            }
        }

        return count;
    }
#endif /* ( ipconfigHAS_PRINTF != 0 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 1 )

/**
 * @brief This define makes it possible for network interfaces to inspect
 *        UDP messages and see if there is any UDP socket bound to a given port
 *        number.  This is probably only useful in systems with a minimum of
 *        RAM and when lots of anonymous broadcast messages come in.
 *
 * @param[in] usPortNr: the port number to look for.
 *
 * @return xFound if a socket with the port number is found.
 */
    BaseType_t xPortHasUDPSocket( uint16_t usPortNr )
    {
        BaseType_t xFound = pdFALSE;

        vTaskSuspendAll();
        {
            if( ( pxListFindListItemWithValue( &xBoundUDPSocketsList, ( TickType_t ) usPortNr ) != NULL ) )
            {
                xFound = pdTRUE;
            }
        }
        ( void ) xTaskResumeAll();

        return xFound;
    }

#endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */
/*-----------------------------------------------------------*/

/**
 * @brief Receive data from a bound socket. In this library, the function
 *        can only be used with connection-less sockets (UDP). For TCP sockets,
 *        please use FreeRTOS_recv().
 *
 * @param[in] xSocket: The socket to which the data is sent i.e. the
 *                     listening socket.
 * @param[out] pvBuffer: The buffer in which the data being received is to
 *                      be stored.
 * @param[in] uxBufferLength: The length of the buffer.
 * @param[in] xFlags: The flags to indicate preferences while calling this function.
 * @param[out] pxSourceAddress: The source address from which the data is being sent.
 * @param[out] pxSourceAddressLength: The length of the source address structure.
 *                  This would always be a constant - 24 (in case of no error) as
 *                  FreeRTOS+TCP makes the sizes of IPv4 and IPv6 structures equal
 *                  (24-bytes) for compatibility.
 *
 * @return The number of bytes received. Or else, an error code is returned. When it
 *         returns a negative value, the cause can be looked-up in
 *         'FreeRTOS_errno_TCP.h'.
 */
int32_t FreeRTOS_recvfrom( const ConstSocket_t xSocket,
                           void * pvBuffer,
                           size_t uxBufferLength,
                           BaseType_t xFlags,
                           struct freertos_sockaddr * pxSourceAddress,
                           socklen_t * pxSourceAddressLength )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    FreeRTOS_Socket_t const * pxSocket = xSocket;
    int32_t lReturn;
    EventBits_t xEventBits = ( EventBits_t ) 0;
    size_t uxPayloadOffset;
    size_t uxPayloadLength;
    socklen_t xAddressLength;

    if( vSocketValid( pxSocket, FREERTOS_IPPROTO_UDP, pdTRUE ) == pdFALSE )
    {
        lReturn = -pdFREERTOS_ERRNO_EINVAL;
    }
    else
    {
        /* The function prototype is designed to maintain the expected Berkeley
         * sockets standard, but this implementation does not use all the parameters. */
        ( void ) pxSourceAddressLength;

        pxNetworkBuffer = prvRecvFromWaitForPacket( pxSocket, xFlags, &( xEventBits ) );

        if( pxNetworkBuffer != NULL )
        {
            if( uxIPHeaderSizePacket( pxNetworkBuffer ) == ipSIZE_OF_IPv6_HEADER )
            {
                #if ( ipconfigUSE_IPv6 != 0 )
                    uxPayloadOffset = xRecv_Update_IPv6( pxNetworkBuffer, pxSourceAddress );
                #endif
            }
            else
            {
                #if ( ipconfigUSE_IPv4 != 0 )
                    uxPayloadOffset = xRecv_Update_IPv4( pxNetworkBuffer, pxSourceAddress );
                #endif
            }

            xAddressLength = sizeof( struct freertos_sockaddr );

            if( pxSourceAddressLength != NULL )
            {
                *pxSourceAddressLength = xAddressLength;
            }

            /* The returned value is the length of the payload data, which is
             * calculated at the total packet size minus the headers.
             * The validity of `xDataLength` prvProcessIPPacket has been confirmed
             * in 'prvProcessIPPacket()'. */
            uxPayloadLength = pxNetworkBuffer->xDataLength - uxPayloadOffset;
            lReturn = ( int32_t ) uxPayloadLength;

            lReturn = prvRecvFrom_CopyPacket( &( pxNetworkBuffer->pucEthernetBuffer[ uxPayloadOffset ] ), pvBuffer, uxBufferLength, xFlags, lReturn );

            if( ( ( UBaseType_t ) xFlags & ( ( ( UBaseType_t ) FREERTOS_MSG_PEEK ) | ( ( UBaseType_t ) FREERTOS_ZERO_COPY ) ) ) == 0U )
            {
                vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
            }
        }

        #if ( ipconfigSUPPORT_SIGNALS != 0 )
            else if( ( xEventBits & ( EventBits_t ) eSOCKET_INTR ) != 0U )
            {
                lReturn = -pdFREERTOS_ERRNO_EINTR;
                iptraceRECVFROM_INTERRUPTED();
            }
        #endif /* ipconfigSUPPORT_SIGNALS */
        else
        {
            lReturn = -pdFREERTOS_ERRNO_EWOULDBLOCK;
            iptraceRECVFROM_TIMEOUT();
        }
    }

    return lReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief Send data to a socket. The socket must have already been created by a
 *        successful call to FreeRTOS_socket(). It works for UDP-sockets only.
 *
 * @param[in] xSocket: The socket being sent to.
 * @param[in] pvBuffer: Pointer to the data being sent.
 * @param[in] uxTotalDataLength: Length (in bytes) of the data being sent.
 * @param[in] xFlags: Flags used to communicate preferences to the function.
 *                    Possibly FREERTOS_MSG_DONTWAIT and/or FREERTOS_ZERO_COPY.
 * @param[in] pxDestinationAddress: The address to which the data is to be sent.
 * @param[in] xDestinationAddressLength: This parameter is present to adhere to the
 *                  Berkeley sockets standard. Else, it is not used.
 *
 * @return When positive: the total number of bytes sent, when negative an error
 *         has occurred: it can be looked-up in 'FreeRTOS_errno_TCP.h'.
 */
int32_t FreeRTOS_sendto( Socket_t xSocket,
                         const void * pvBuffer,
                         size_t uxTotalDataLength,
                         BaseType_t xFlags,
                         const struct freertos_sockaddr * pxDestinationAddress,
                         socklen_t xDestinationAddressLength )
{
    int32_t lReturn = 0;
    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
    size_t uxMaxPayloadLength;
    size_t uxPayloadOffset;

    /* The function prototype is designed to maintain the expected Berkeley
     * sockets standard, but this implementation does not use all the
     * parameters. */
    ( void ) xDestinationAddressLength;
    configASSERT( pxDestinationAddress != NULL );
    configASSERT( pvBuffer != NULL );

    if( pxDestinationAddress->sin_family == ( uint8_t ) FREERTOS_AF_INET6 )
    {
        uxMaxPayloadLength = ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_UDP_HEADER );
        uxPayloadOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_UDP_HEADER;
    }
    else
    {
        uxMaxPayloadLength = ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER );
        uxPayloadOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER;
    }

    if( uxTotalDataLength <= ( size_t ) uxMaxPayloadLength )
    {
        /* If the socket is not already bound to an address, bind it now.
         * Passing NULL as the address parameter tells FreeRTOS_bind() to select
         * the address to bind to. */
        if( prvMakeSureSocketIsBound( pxSocket ) == pdTRUE )
        {
            lReturn = prvSendTo_ActualSend( pxSocket, pvBuffer, uxTotalDataLength, xFlags, pxDestinationAddress, uxPayloadOffset );
        }
        else
        {
            /* No comment. */
            iptraceSENDTO_SOCKET_NOT_BOUND();
        }
    }
    else
    {
        /* The data is longer than the available buffer space. */
        iptraceSENDTO_DATA_TOO_LONG();
    }

    return lReturn;
} /* Tested */
/*-----------------------------------------------------------*/

#if 0

/**
 * @brief Returns the number of packets that are stored in a UDP socket.
 *
 * @param[in] xSocket: the socket to get the number of bytes from.
 *
 * @return Returns the number of packets that are stored.  Use FreeRTOS_recvfrom()
 *         to retrieve those packets.
 */
    BaseType_t FreeRTOS_udp_rx_size( Socket_t xSocket )
    {
        BaseType_t xReturn = 0;
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;

        if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_UDP )
        {
            xReturn = ( BaseType_t ) listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) );
        }
        else
        {
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }

        return xReturn;
    }
#endif /* 0 */
/*-----------------------------------------------------------*/
