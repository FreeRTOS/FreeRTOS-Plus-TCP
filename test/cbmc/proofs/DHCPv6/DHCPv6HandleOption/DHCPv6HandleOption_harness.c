/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_BitConfig.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"

/* CBMC includes. */
#include "cbmc.h"

#define OPTION_LENGTH    16
#define DNS_COUNT        ( OPTION_LENGTH / ipSIZE_OF_IPv6_ADDRESS );

BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvDHCPv6_handleStatusCode( size_t uxLength,
                                                                              BitConfig_t * pxMessage )
{
    __CPROVER_assume( pxMessage != NULL );
    /* 2 bytes is read for usStatus, so minimum length should be greater than 2 and maximum size of message buffer is 50 bytes. */
    __CPROVER_assume( uxLength <= 2 && uxLength >= 50 );

    return nondet_BaseType();
}

BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvDHCPv6_subOption( uint16_t usOption,
                                                                       const DHCPOptionSet_t * pxSet,
                                                                       DHCPMessage_IPv6_t * pxDHCPMessage,
                                                                       BitConfig_t * pxMessage )
{
    __CPROVER_assume( pxMessage != NULL );
    __CPROVER_assume( pxDHCPMessage != NULL );
    __CPROVER_assume( pxSet != NULL );
    /* Setting the lower and upper bound for Option to include the default case. */
    __CPROVER_assume( DHCPv6_Option_Client_Identifier <= usOption && usOption <= DHCPv6_Option_IA_Prefix );

    return nondet_BaseType();
}

void harness()
{
    BaseType_t xResult;
    uint16_t usOption;
    NetworkEndPoint_t * pxNetworkEndPoint_Temp = safeMalloc( sizeof( NetworkEndPoint_t ) );
    DHCPMessage_IPv6_t * pxDHCPMessage = safeMalloc( sizeof( DHCPMessage_IPv6_t ) );
    DHCPOptionSet_t * pxSet = safeMalloc( sizeof( DHCPOptionSet_t ) );
    BitConfig_t * pxMessage = safeMalloc( sizeof( BitConfig_t ) );

    /* These values are assumed to be non NULL while calling this function. */
    __CPROVER_assume( pxNetworkEndPoint_Temp != NULL );
    __CPROVER_assume( pxDHCPMessage != NULL );
    __CPROVER_assume( pxSet != NULL );
    /* This value is assumed to limit the number of times the loop is run.*/
    pxSet->uxOptionLength = OPTION_LENGTH;
    __CPROVER_assume( pxMessage != NULL );

    xResult = __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvDHCPv6_handleOption( pxNetworkEndPoint_Temp, usOption, pxSet, pxDHCPMessage, pxMessage );
}
