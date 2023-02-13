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
* The signature of the function under test.
****************************************************************/

void vDHCPProcess( BaseType_t xReset,
                    struct xNetworkEndPoint * pxEndPoint );

/****************************************************************
* Abstract prvProcessDHCPReplies proved memory safe in ProcessDHCPReplies.
****************************************************************/

BaseType_t prvProcessDHCPReplies( BaseType_t xExpectedMessageType,
                                             NetworkEndPoint_t * pxEndPoint )
{
    return nondet_BaseType();
}

BaseType_t xSocketValid( const ConstSocket_t xSocket )
{
    return pdTRUE;
}

BaseType_t vSocketBind( FreeRTOS_Socket_t * pxSocket,
                        struct freertos_sockaddr * pxBindAddress,
                        size_t uxAddressLength,
                        BaseType_t xInternal )
{
    return 0;
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

    xDHCPv4Socket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
    
    vDHCPProcess( xReset, pxNetworkEndPoint_Temp );

    //vDHCPProcessEndPoint( xReset, xDoCheck, pxNetworkEndPoint_Temp );
    
}
