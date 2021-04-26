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
#include "FreeRTOS_Routing.h"

/* Static members defined in FreeRTOS_DHCP.c */
extern DHCPData_t xDHCPData;
extern Socket_t xDHCPSocket;
void prvCreateDHCPSocket( NetworkEndPoint_t * pxEndPoint );

/* Signature of function under test (vDHCPProcessEndPoint).
 * This function is defined as static and thus needs to be
 * taken out of the file using a CBMC flag
 * (--export-file-local-symbols). Using this flag results
 * in mangling of the name.  */
void __CPROVER_file_local_FreeRTOS_DHCP_c_vDHCPProcessEndPoint( BaseType_t xReset,
                                                                BaseType_t xDoCheck,
                                                                NetworkEndPoint_t * pxEndPoint );

/* Static member defined in freertos_api.c */
#ifdef CBMC_GETNETWORKBUFFER_FAILURE_BOUND
    extern uint32_t GetNetworkBuffer_failure_count;
#endif

/****************************************************************
* Abstract vSocketBind function to always return a 0 (meaning pass
* in Berkeley sockets).
* The function under test asserts the return to be 0 further down
* the call graph.
****************************************************************/
BaseType_t vSocketBind( FreeRTOS_Socket_t * pxSocket,
                        struct freertos_sockaddr * pxBindAddress,
                        size_t uxAddressLength,
                        BaseType_t xInternal )
{
    return ( BaseType_t ) 0;
}


/****************************************************************
* Abstract FreeRTOS_socket call to allocate a socket sized chunk.
* The socket cannot be NULL when DHCP is in process and is asserted
* by the function under test.
****************************************************************/
Socket_t FreeRTOS_socket( BaseType_t xDomain,
                          BaseType_t xType,
                          BaseType_t xProtocol )
{
    void * ptr = malloc( sizeof( Socket_t ) );

    __CPROVER_assume( ptr != NULL );

    return ptr;
}

/****************************************************************
* Function Abstraction:
* prvProcessDHCPReplies has been proved memory safe in ProcessDHCPReplies.
****************************************************************/
BaseType_t __CPROVER_file_local_FreeRTOS_DHCP_c_prvProcessDHCPReplies( BaseType_t xExpectedMessageType,
                                                                       NetworkEndPoint_t * pxEndPoint )
{
    return nondet_BaseType();
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
    BaseType_t xReset, xDoCheck;
    NetworkEndPoint_t xLocalEndPoint;
    NetworkEndPoint_t * pxLocalPointerEndPoint;

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
    * The socket is created in the eInitialWait state.
    * xReset==True resets the state to eInitialWait.
    ****************************************************************/
    if( ( xDHCPData.eDHCPState != eInitialWait ) ||
        ( xReset == pdFALSE ) )
    {
        prvCreateDHCPSocket( &xLocalEndPoint );
        __CPROVER_assume( xDHCPSocket != NULL );
    }

    /* The pointer to the endpoint must be non-NULL. The function under
     * test asserts that. */
    pxLocalPointerEndPoint = &xLocalEndPoint;

    /* Call the function under test. */
    __CPROVER_file_local_FreeRTOS_DHCP_c_vDHCPProcessEndPoint( xReset, xDoCheck, pxLocalPointerEndPoint );
}
