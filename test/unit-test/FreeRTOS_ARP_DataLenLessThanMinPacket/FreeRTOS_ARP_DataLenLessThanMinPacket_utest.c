/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "FreeRTOSIPConfig.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_task.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_ARP_DataLenLessThanMinPacket_list_macros.h"
#include "FreeRTOS_ARP_DataLenLessThanMinPacket_stubs.c"

#include "FreeRTOS_ARP.h"

#include "catch_assert.h"

static uint32_t uInterfaceOut_Called = 0;

BaseType_t xNetworkInterfaceOutput_ARP_Stub( NetworkInterface_t * pxInterface,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                             BaseType_t bReleaseAfterSend )
{
    uInterfaceOut_Called = 1;

    return pdTRUE_UNSIGNED;
}


void test_FreeRTOS_OutputARPRequest_MinimumPacketSizeLessThanARPPacket( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkInterface_t xInterface;
    uint8_t ucBuffer[ sizeof( ARPPacket_t ) + ipBUFFER_PADDING + ipconfigETHERNET_MINIMUM_PACKET_BYTES ];
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulIPAddress = 0xAAAAAAAA;

    xNetworkBuffer.pucEthernetBuffer = ucBuffer;
    xNetworkBuffer.xDataLength = sizeof( ARPPacket_t );

    xInterface.pfOutput = xNetworkInterfaceOutput_ARP_Stub;

    xEndPoint.pxNetworkInterface = &xInterface;

    /* =================================================== */

    FreeRTOS_FirstNetworkInterface_ExpectAndReturn( &xInterface );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAndReturn( ulIPAddress, 25, &xEndPoint );
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( ARPPacket_t ), 0, &xNetworkBuffer );
    xIsCallingFromIPTask_IgnoreAndReturn( pdTRUE );

    FreeRTOS_NextNetworkInterface_ExpectAndReturn( &xInterface, NULL );

    FreeRTOS_OutputARPRequest( ulIPAddress );

    TEST_ASSERT_EQUAL( uInterfaceOut_Called, 1 );
    /* =================================================== */
}
