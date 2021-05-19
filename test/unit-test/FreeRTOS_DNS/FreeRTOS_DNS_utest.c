/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_UDP_IP.h"
//#include "mock_FreeRTOS_ARP.h"
#include "mock_task.h"
#include "mock_DNS_Callback.h"
#include "mock_DNS_Cache.h"
#include "mock_DNS_Parser.h"
#include "mock_NetworkBufferManagement.h"
//#include "mock_FreeRTOS_DHCP_mock.h"
#include "FreeRTOS_DNS.h"

//#include "FreeRTOS_DHCP.h"

//#include "FreeRTOS_DHCP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"



void test_dummy_test(void)
{
    TEST_PASS();
}

void test_vDNSInitialise(void)
{
    vDNSInitialise();
}


