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
* The function name (prvProcessDHCPReplies) is mangled due to the
* use of a CBMC flag (--export-file-local-symbols) which allows us
* to access this static function outside the source file in which
* it is defined.
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

    /* The function under test is a private (static) function called only by
     * the TCP stack. The stack asserts that the endpoint cannot be NULL
     * before the function under test is invoked. */
    NetworkEndPoint_t * pxEndPoint = &xEndPoint;

    __CPROVER_file_local_FreeRTOS_DHCP_c_prvProcessDHCPReplies( xExpectedMessageType, pxEndPoint );
}
