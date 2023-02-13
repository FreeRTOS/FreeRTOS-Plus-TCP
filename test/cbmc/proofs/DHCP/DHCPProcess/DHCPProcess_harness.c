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

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "FreeRTOS_ARP.h"

#include "NetworkBufferManagement.h"

#include "cbmc.h"

/* Static members defined in FreeRTOS_DHCP.c */
extern DHCPData_t xDHCPData;
extern Socket_t xDHCPv4Socket;
void prvCreateDHCPSocket( NetworkEndPoint_t * pxEndPoint );

/* Static member defined in freertos_api.c */
#ifdef CBMC_GETNETWORKBUFFER_FAILURE_BOUND
    extern uint32_t GetNetworkBuffer_failure_count;
#endif















/****************************************************************
* This is a collection of abstractions of methods in the FreeRTOS TCP
* API.  The abstractions simply perform minimal validation of
* function arguments, and return unconstrained values of the
* appropriate type.
****************************************************************/

/****************************************************************
* Abstract FreeRTOS_socket.
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/socket.html
*
* We stub out this function to do nothing but allocate space for a
* socket containing unconstrained data or return an error.
****************************************************************/

Socket_t FreeRTOS_socket( BaseType_t xDomain,
                          BaseType_t xType,
                          BaseType_t xProtocol )
{
    // if( nondet_bool() )
    // {
    //     return FREERTOS_INVALID_SOCKET;
    // }
    // else
    // {
        void * ptr = malloc( sizeof( struct xSOCKET ) );
        __CPROVER_assume( ptr != NULL );
        return ptr;
    // }
}

/****************************************************************
* Abstract FreeRTOS_setsockopt.
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/setsockopt.html
****************************************************************/

BaseType_t FreeRTOS_setsockopt( Socket_t xSocket,
                                int32_t lLevel,
                                int32_t lOptionName,
                                const void * pvOptionValue,
                                size_t uxOptionLength )
{
    __CPROVER_assert( xSocket != NULL,
                      "FreeRTOS precondition: xSocket != NULL" );
    __CPROVER_assert( pvOptionValue != NULL,
                      "FreeRTOS precondition: pvOptionValue != NULL" );
    return nondet_BaseType();
}

/****************************************************************
* Abstract FreeRTOS_closesocket.
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/close.html
****************************************************************/

BaseType_t FreeRTOS_closesocket( Socket_t xSocket )
{
    __CPROVER_assert( xSocket != NULL,
                      "FreeRTOS precondition: xSocket != NULL" );
    return nondet_BaseType();
}

/****************************************************************
* Abstract FreeRTOS_bind.
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/bind.html
****************************************************************/

BaseType_t FreeRTOS_bind( Socket_t xSocket,
                          struct freertos_sockaddr * pxAddress,
                          socklen_t xAddressLength )
{
    __CPROVER_assert( xSocket != NULL,
                      "FreeRTOS precondition: xSocket != NULL" );
    __CPROVER_assert( pxAddress != NULL,
                      "FreeRTOS precondition: pxAddress != NULL" );
    return nondet_BaseType();
}

/****************************************************************
* Abstract FreeRTOS_inet_addr.
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/inet_addr.html
****************************************************************/

uint32_t FreeRTOS_inet_addr( const char * pcIPAddress )
{
    __CPROVER_assert( pcIPAddress != NULL,
                      "FreeRTOS precondition: pcIPAddress != NULL" );
    return nondet_uint32();
}

/****************************************************************
* Abstract FreeRTOS_recvfrom.
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/recvfrom.html
*
* We stub out this function to do nothing but allocate a buffer of
* unconstrained size containing unconstrained data and return the
* size (or return the size 0 if the allocation fails).
****************************************************************/

int32_t FreeRTOS_recvfrom( Socket_t xSocket,
                           void * pvBuffer,
                           size_t uxBufferLength,
                           BaseType_t xFlags,
                           struct freertos_sockaddr * pxSourceAddress,
                           socklen_t * pxSourceAddressLength )

{
    /****************************************************************
    * "If the zero copy calling semantics are used (the ulFlags
    * parameter does not have the FREERTOS_ZERO_COPY bit set) then
    * pvBuffer does not point to a buffer and xBufferLength is not
    * used."  This is from the documentation.
    ****************************************************************/
    __CPROVER_assert( xFlags & FREERTOS_ZERO_COPY, "I can only do ZERO_COPY" );

    __CPROVER_assert( pvBuffer != NULL,
                      "FreeRTOS precondition: pvBuffer != NULL" );

    /****************************************************************
    * TODO: We need to check this out.
    *
    * The code calls recvfrom with these parameters NULL, it is not
    * clear from the documentation that this is allowed.
    ****************************************************************/
    #if 0
        __CPROVER_assert( pxSourceAddress != NULL,
                          "FreeRTOS precondition: pxSourceAddress != NULL" );
        __CPROVER_assert( pxSourceAddressLength != NULL,
                          "FreeRTOS precondition: pxSourceAddress != NULL" );
    #endif

    size_t payload_size;
    __CPROVER_assume( payload_size + sizeof( UDPPacket_t )
                      < CBMC_MAX_OBJECT_SIZE );

    /****************************************************************
    * TODO: We need to make this lower bound explicit in the Makefile.json
    *
    * DNSMessage_t is a typedef in FreeRTOS_DNS.c
    * sizeof(DNSMessage_t) = 6 * sizeof(uint16_t)
    ****************************************************************/
    __CPROVER_assume( payload_size >= 6 * sizeof( uint16_t ) );

    #ifdef CBMC_FREERTOS_RECVFROM_BUFFER_BOUND
        __CPROVER_assume( payload_size <= CBMC_FREERTOS_RECVFROM_BUFFER_BOUND );
    #endif

    uint32_t buffer_size = payload_size + sizeof( UDPPacket_t );
    uint8_t * buffer = safeMalloc( buffer_size );

    if( buffer == NULL )
    {
        buffer_size = 0;
    }
    else
    {
        buffer = buffer + sizeof( UDPPacket_t );
        buffer_size = buffer_size - sizeof( UDPPacket_t );
    }

    *( ( uint8_t ** ) pvBuffer ) = buffer;
    return buffer_size;
}

/****************************************************************
* Abstract FreeRTOS_recvfrom.
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/sendto.html
****************************************************************/

int32_t FreeRTOS_sendto( Socket_t xSocket,
                         const void * pvBuffer,
                         size_t uxTotalDataLength,
                         BaseType_t xFlags,
                         const struct freertos_sockaddr * pxDestinationAddress,
                         socklen_t xDestinationAddressLength )
{
    __CPROVER_assert( xSocket != NULL,
                      "FreeRTOS precondition: xSocket != NULL" );
    __CPROVER_assert( pvBuffer != NULL,
                      "FreeRTOS precondition: pvBuffer != NULL" );
    __CPROVER_assert( pxDestinationAddress != NULL,
                      "FreeRTOS precondition: pxDestinationAddress != NULL" );
    return nondet_int32();
}

/****************************************************************
* Abstract FreeRTOS_GetUDPPayloadBuffer
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/API/FreeRTOS_GetUDPPayloadBuffer.html
*
* We stub out this function to do nothing but allocate a buffer of
* unconstrained size containing unconstrained data and return a
* pointer to the buffer (or NULL).
****************************************************************/

void * FreeRTOS_GetUDPPayloadBuffer( size_t xRequestedSizeBytes,
                                     TickType_t xBlockTimeTicks,
                                     uint8_t ucIPType )
{
    size_t size;

    __CPROVER_assume( size < CBMC_MAX_OBJECT_SIZE );
    __CPROVER_assume( size >= sizeof( UDPPacket_t ) );

    uint8_t * buffer = safeMalloc( size );

    return buffer == NULL ? buffer : buffer + sizeof( UDPPacket_t );
}

/****************************************************************
* Abstract FreeRTOS_GetUDPPayloadBuffer
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/FreeRTOS_ReleaseUDPPayloadBuffer.html
****************************************************************/

void FreeRTOS_ReleaseUDPPayloadBuffer( void * pvBuffer )
{
    __CPROVER_assert( pvBuffer != NULL,
                      "FreeRTOS precondition: pvBuffer != NULL" );
    __CPROVER_assert( __CPROVER_POINTER_OFFSET( pvBuffer )
                      == sizeof( UDPPacket_t ),
                      "FreeRTOS precondition: pvBuffer offset" );

    free( pvBuffer - sizeof( UDPPacket_t ) );
}

/*We assume that the pxGetNetworkBufferWithDescriptor function is implemented correctly and returns a valid data structure. */
/*This is the mock to mimic the correct expected behavior. If this allocation fails, this might invalidate the proof. */
NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) malloc( sizeof( NetworkBufferDescriptor_t ) );

    __CPROVER_assume( pxNetworkBuffer != NULL );

    pxNetworkBuffer->pucEthernetBuffer = ( malloc( ( ( uint8_t * ) xRequestedSizeBytes + ipUDP_PAYLOAD_IP_TYPE_OFFSET ) ) + ipIP_TYPE_OFFSET );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    pxNetworkBuffer->xDataLength = xRequestedSizeBytes;
    return pxNetworkBuffer;
}

/****************************************************************
* Abstract pxGetNetworkBufferWithDescriptor.
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/vReleaseNetworkBufferAndDescriptor.html
****************************************************************/

void vReleaseNetworkBufferAndDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    __CPROVER_assert( pxNetworkBuffer != NULL,
                      "Precondition: pxNetworkBuffer != NULL" );

    if( pxNetworkBuffer->pucEthernetBuffer != NULL )
    {
        free( pxNetworkBuffer->pucEthernetBuffer );
    }

    free( pxNetworkBuffer );
}

/****************************************************************
* Abstract FreeRTOS_GetAddressConfiguration
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/FreeRTOS_GetAddressConfiguration.html
****************************************************************/

void FreeRTOS_GetAddressConfiguration( uint32_t * pulIPAddress,
                                       uint32_t * pulNetMask,
                                       uint32_t * pulGatewayAddress,
                                       uint32_t * pulDNSServerAddress )
{
    if( pulIPAddress != NULL )
    {
        *pulIPAddress = nondet_unint32();
    }

    if( pulNetMask != NULL )
    {
        *pulNetMask = nondet_unint32();
    }

    if( pulGatewayAddress != NULL )
    {
        *pulGatewayAddress = nondet_unint32();
    }

    if( pulDNSServerAddress != NULL )
    {
        *pulDNSServerAddress = nondet_unint32();
    }
}

/****************************************************************/

/****************************************************************
* This is a collection of methods that are defined by the user
* application but are invoked by the FreeRTOS API.
****************************************************************/

/****************************************************************
* Abstract FreeRTOS_GetAddressConfiguration
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/API/vApplicationIPNetworkEventHook.html
****************************************************************/

void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
{
}

/****************************************************************
* Abstract pcApplicationHostnameHook
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/TCP_IP_Configuration.html
****************************************************************/

const char * pcApplicationHostnameHook( void )
{
    return "hostname";
}

/****************************************************************/


/****************************************************************
* Abstract xNetworkInterfaceOutput
* https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/Embedded_Ethernet_Porting.html#xNetworkInterfaceOutput
****************************************************************/
BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t bReleaseAfterSend )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "The networkbuffer cannot be NULL" );

    BaseType_t xReturn;

    /* Return some random value. */
    return xReturn;
}

/****************************************************************/

/**
 * @brief Internal version of bind() that should not be called directly.
 *        'xInternal' is used for TCP sockets only: it allows to have several
 *        (connected) child sockets bound to the same server port.
 *
 * @param[in] pxSocket: The socket is to be bound.
 * @param[in] pxBindAddress: The port to which this socket should be bound.
 * @param[in] uxAddressLength: The address length.
 * @param[in] xInternal: pdTRUE is calling internally, else pdFALSE.
 *
 * @return If the socket was bound to a port successfully, then a 0 is returned.
 *         Or else, an error code is returned.
 */
BaseType_t vSocketBind( FreeRTOS_Socket_t * pxSocket,
                        struct freertos_sockaddr * pxBindAddress,
                        size_t uxAddressLength,
                        BaseType_t xInternal ) 
{

    BaseType_t ret;
    __CPROVER_assume( ret == 0 );
    return ret;

}























/****************************************************************
* The signature of the function under test.
****************************************************************/

void vDHCPProcess( BaseType_t xReset,
                   eDHCPState_t eExpectedState );

/****************************************************************
* Abstract prvProcessDHCPReplies proved memory safe in ProcessDHCPReplies.
****************************************************************/

BaseType_t prvProcessDHCPReplies( BaseType_t xExpectedMessageType )
{
    return nondet_BaseType();
}

/****************************************************************
* The proof of vDHCPProcess
****************************************************************/

void harness()
{
    BaseType_t xReset;
    BaseType_t xDoCheck;
    //eDHCPState_t eExpectedState;

    pxNetworkEndPoints = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );
    __CPROVER_assume( pxNetworkEndPoints->pxNext == NULL );

    /* Interface init. */
    pxNetworkEndPoints->pxNetworkInterface = ( NetworkInterface_t * ) malloc( sizeof( NetworkInterface_t ) );
    __CPROVER_assume( pxNetworkEndPoints->pxNetworkInterface != NULL );

    NetworkEndPoint_t * pxNetworkEndPoint_Temp = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoint_Temp != NULL );
    __CPROVER_assume( pxNetworkEndPoint_Temp->pxNext == NULL );
    //pxNetworkEndPoint_Temp->xDHCPData.eExpectedState = eExpectedState;

    /****************************************************************
    * Initialize the counter used to bound the number of times
    * GetNetworkBufferWithDescriptor can fail.
    ****************************************************************/

    #ifdef CBMC_GETNETWORKBUFFER_FAILURE_BOUND
        GetNetworkBuffer_failure_count = 0;
    #endif

    /****************************************************************
    * Assume a valid socket in most states of the DHCP state machine.
    *
    * The socket is created in the eWaitingSendFirstDiscover state.
    * xReset==True resets the state to eWaitingSendFirstDiscover.
    ****************************************************************/

    if( !( ( pxNetworkEndPoint_Temp->xDHCPData.eDHCPState == eInitialWait ) ||
           ( xReset != pdFALSE ) ) )
    {
        prvCreateDHCPSocket( pxNetworkEndPoint_Temp );
        
    }

    __CPROVER_assume( xDHCPv4Socket != NULL );
    //vDHCPProcess( xReset, pxNetworkEndPoint_Temp );

    vDHCPProcessEndPoint( xReset, xDoCheck, pxNetworkEndPoint_Temp );
    
}
