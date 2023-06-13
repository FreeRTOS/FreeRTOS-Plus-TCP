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

/* CBMC includes. */
#include "cbmc.h"

extern Socket_t xDHCPv6Socket;
void prvCreateDHCPv6Socket( NetworkEndPoint_t * pxEndPoint );

/**
 * For the purpose of this proof we assume that xSocketValid returns true always.
 * This has to do with assertions in the source code that checks for socket being invalid.
 * [configASSERT( xSocketValid( xDHCPv4Socket ) == pdTRUE );]
 */
BaseType_t xSocketValid( const ConstSocket_t xSocket )
{
    __CPROVER_assume( xSocket != FREERTOS_INVALID_SOCKET );
    __CPROVER_assume( xSocket != NULL );
    return( ( xSocket != FREERTOS_INVALID_SOCKET ) && ( xSocket != NULL ) );
}

BaseType_t vSocketBind( FreeRTOS_Socket_t * pxSocket,
                        struct freertos_sockaddr * pxBindAddress,
                        size_t uxAddressLength,
                        BaseType_t xInternal )
{
    /* Return value is set to zero assuming socket bind will succeed. If it doesn't, it
     * will hit an assert in the function.  */
    BaseType_t xRet = 0;

    __CPROVER_assert( pxSocket != NULL,
                      "FreeRTOS precondition: pxSocket != NULL" );
    __CPROVER_assert( pxBindAddress != NULL,
                      "FreeRTOS precondition: pxBindAddress != NULL" );

    return xRet;
}

/**
 * Return value is set to -1 assuming other APIs will be checked separately,
 * hence only allowing 1 iteration of the loop.
 */

int32_t FreeRTOS_recvfrom( const ConstSocket_t xSocket,
                           void * pvBuffer,
                           size_t uxBufferLength,
                           BaseType_t xFlags,
                           struct freertos_sockaddr * pxSourceAddress,
                           socklen_t * pxSourceAddressLength )
{
    return -1;
}

BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPv6ProcessEndPoint_HandleState( NetworkEndPoint_t * pxEndPoint,
                                                                                      DHCPMessage_IPv6_t * pxDHCPMessage )
{
    return nondet_BaseType();
}

void harness()
{
    BaseType_t xReset;

    NetworkEndPoint_t * pxNetworkEndPoint_Temp = safeMalloc( sizeof( NetworkEndPoint_t ) );

    __CPROVER_assume( pxNetworkEndPoint_Temp != NULL );

    pxNetworkEndPoint_Temp->pxDHCPMessage = safeMalloc( sizeof( DHCPMessage_IPv6_t ) );
    __CPROVER_assume( pxNetworkEndPoint_Temp->pxDHCPMessage != NULL );

    /****************************************************************
    * Assume a valid socket in most states of the DHCP state machine.
    *
    * The socket is created in the eWaitingSendFirstDiscover state.
    * xReset==True resets the state to eWaitingSendFirstDiscover.
    ****************************************************************/
    if( !( ( pxNetworkEndPoint_Temp->xDHCPData.eDHCPState == eInitialWait ) ||
           ( xReset != pdFALSE ) ) )
    {
        prvCreateDHCPv6Socket( pxNetworkEndPoint_Temp );
    }

    xDHCPv6Socket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

    vDHCPv6Process( xReset, pxNetworkEndPoint_Temp );
}
