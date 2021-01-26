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

/****************************************************************
* Signature of function under test
****************************************************************/

BaseType_t __CPROVER_file_local_FreeRTOS_DHCP_c_prvProcessDHCPReplies( BaseType_t xExpectedMessageType,
                                                                       NetworkEndPoint_t * pxEndPoint );

/****************************************************************
* The proof for FreeRTOS_gethostbyname.
****************************************************************/

void harness()
{
    /* Omitting model of an unconstrained xDHCPData because xDHCPData is */
    /* the source of uninitialized data only on line 647 to set a */
    /* transaction id is an outgoing message */

    BaseType_t xExpectedMessageType;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = &xEndPoint;

    __CPROVER_file_local_FreeRTOS_DHCP_c_prvProcessDHCPReplies( xExpectedMessageType, pxEndPoint );
}
