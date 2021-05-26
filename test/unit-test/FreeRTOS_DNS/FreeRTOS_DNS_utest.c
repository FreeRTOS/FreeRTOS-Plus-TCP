/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
//#include "mock_FreeRTOS_ARP.h"
#include "mock_task.h"
#include "mock_list.h"
#include "mock_queue.h"

#include "mock_DNS_Callback.h"
#include "mock_DNS_Cache.h"
#include "mock_DNS_Parser.h"
#include "mock_DNS_Networking.h"
#include "mock_NetworkBufferManagement.h"
//#include "mock_FreeRTOS_DHCP_mock.h"
#include "FreeRTOS_DNS.h"

//#include "FreeRTOS_DHCP.h"

//#include "FreeRTOS_DHCP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#define LLMNR_ADDRESS "freertos"
#define GOOD_ADDRESS "www.freertos.org"
#define BAD_ADDRESS "this is a bad address"

void test_dummy_test(void)
{
    TEST_PASS();
}

void test_vDNSInitialise(void)
{
    vDNSCallbackInitialise_Expect();
    vDNSInitialise();
}

void test_FreeRTOS_gethostbyname_fail_bad_inet_addres(void)
{
    uint32_t ret;

    FreeRTOS_inet_addr_ExpectAndReturn(BAD_ADDRESS, 0);
    FreeRTOS_dnslookup_ExpectAndReturn(BAD_ADDRESS, 0);
    xApplicationGetRandomNumber_IgnoreAndReturn(34);
    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(NULL);

    ret = FreeRTOS_gethostbyname( BAD_ADDRESS );
    TEST_ASSERT_EQUAL(0, ret);
}

void test_FreeRTOS_gethostbyname_fail_NULL_address(void)
{
    uint32_t ret;

    ret = FreeRTOS_gethostbyname( NULL );
    TEST_ASSERT_EQUAL(0, ret);
}

void test_FreeRTOS_gethostbyname_fail_long_address(void)
{
    uint32_t ret;
    char address[ipconfigDNS_CACHE_NAME_LENGTH + 3];

    memset(address, 'a', ipconfigDNS_CACHE_NAME_LENGTH);
    address[ ipconfigDNS_CACHE_NAME_LENGTH  + 3 ] = '\0';


    ret = FreeRTOS_gethostbyname( address );
    TEST_ASSERT_EQUAL(0, ret);
}

/*
 * ensures that when the supplied address is in the dottet format, it is
 * translated to the numerical form and no lookup is performed
 */
void test_FreeRTOS_gethostbyname_success_dot_address(void)
{
    uint32_t ret;

    FreeRTOS_inet_addr_ExpectAndReturn("1.2.3.4", 12345);
    xApplicationGetRandomNumber_IgnoreAndReturn(34);

    ret = FreeRTOS_gethostbyname( "1.2.3.4" );
    TEST_ASSERT_EQUAL(12345, ret);
}

/*
 * ensures that if the address is not in the dotted form and found in the cache,
 * it is returned to the caller
 */
void test_FreeRTOS_gethostbyname_success_address_in_cache(void)
{
    uint32_t ret;

    FreeRTOS_inet_addr_ExpectAndReturn(GOOD_ADDRESS, 0);
    FreeRTOS_dnslookup_ExpectAndReturn(GOOD_ADDRESS, 12345);

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL(12345, ret);
}


/*
 * Ensures that the code can handle when the client can't create a socket
 */
void test_FreeRTOS_gethostbyname_fail_NULL_socket(void)
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;

    FreeRTOS_inet_addr_ExpectAndReturn(GOOD_ADDRESS, 0);
    FreeRTOS_dnslookup_ExpectAndReturn(GOOD_ADDRESS, 0);
    xApplicationGetRandomNumber_IgnoreAndReturn(34);
    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&xNetworkBuffer);
    /* back in prvGetHostByName */
    DNS_CreateSocket_ExpectAnyArgsAndReturn(NULL);
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL(0, ret);
}

void test_FreeRTOS_gethostbyname_fail_send_dns_request(void)
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;
    xNetworkBuffer.xDataLength = 2280;
    xNetworkBuffer.pucEthernetBuffer = malloc(2280);

    FreeRTOS_inet_addr_ExpectAndReturn(GOOD_ADDRESS, 0);
    FreeRTOS_dnslookup_ExpectAndReturn(GOOD_ADDRESS, 0);
    xApplicationGetRandomNumber_IgnoreAndReturn(34);
    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&xNetworkBuffer);
    /* back in prvGetHostByName */
    DNS_CreateSocket_ExpectAnyArgsAndReturn((void*) 23);
    /* prvGetHostByNameOp */
    /* prvFillockAddress */
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
    /* back prvGetHostByNameOp */
    DNS_SendRequest_ExpectAnyArgsAndReturn(pdFAIL);
    /* retry twice */
    /* prvFillockAddress */
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
    /* back prvGetHostByNameOp */
    DNS_SendRequest_ExpectAnyArgsAndReturn(pdFAIL);
    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL(0, ret);

    free(xNetworkBuffer.pucEthernetBuffer);
}

void test_FreeRTOS_gethostbyname_fail_send_dns_reply_null(void)
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct dns_buffer xReceiveBuffer;
    xReceiveBuffer.pucPayloadBuffer = NULL;
    xReceiveBuffer.uxPayloadLength = 0;
    xNetworkBuffer.xDataLength = 2280;
    xNetworkBuffer.pucEthernetBuffer = malloc(2280);

    FreeRTOS_inet_addr_ExpectAndReturn(LLMNR_ADDRESS, 0);
    FreeRTOS_dnslookup_ExpectAndReturn(LLMNR_ADDRESS, 0);
    xApplicationGetRandomNumber_IgnoreAndReturn(34);
    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&xNetworkBuffer);
    /* back in prvGetHostByName */
    DNS_CreateSocket_ExpectAnyArgsAndReturn((void*) 23);
    /* prvGetHostByNameOp */
    /* prvFillockAddress */
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
    /* back prvGetHostByNameOp */
    DNS_SendRequest_ExpectAnyArgsAndReturn(pdPASS);

    DNS_ReadReply_ExpectAnyArgs();
    DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    /* retry twice */
    /* prvFillockAddress */
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
    /* back prvGetHostByNameOp */
    DNS_SendRequest_ExpectAnyArgsAndReturn(pdPASS);
    DNS_ReadReply_ExpectAnyArgs();
    DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( LLMNR_ADDRESS );
    TEST_ASSERT_EQUAL(0, ret);

    free(xNetworkBuffer.pucEthernetBuffer);
}

void test_FreeRTOS_gethostbyname_fail_send_dns_reply_zero(void)
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct dns_buffer xReceiveBuffer;

    xReceiveBuffer.pucPayloadBuffer = malloc(300);
    xReceiveBuffer.uxPayloadLength = 300;

    xNetworkBuffer.xDataLength = 2280;
    xNetworkBuffer.pucEthernetBuffer = malloc(2280);

    FreeRTOS_inet_addr_ExpectAndReturn(GOOD_ADDRESS, 0);
    FreeRTOS_dnslookup_ExpectAndReturn(GOOD_ADDRESS, 0);
    xApplicationGetRandomNumber_IgnoreAndReturn(34);
    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&xNetworkBuffer);
    /* back in prvGetHostByName */
    DNS_CreateSocket_ExpectAnyArgsAndReturn((void*) 23);
    /* prvGetHostByNameOp */
    /* prvFillockAddress */
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
    /* back prvGetHostByNameOp */
    DNS_SendRequest_ExpectAnyArgsAndReturn(pdPASS);
    DNS_ReadReply_ExpectAnyArgs();
    DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    /* prvDNSReply */
    DNS_ParseDNSReply_ExpectAnyArgsAndReturn(0);
    FreeRTOS_ReleaseUDPPayloadBuffer_ExpectAnyArgs();

    /* retry twice */
    /* prvFillockAddress */
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
    /* back prvGetHostByNameOp */
    DNS_SendRequest_ExpectAnyArgsAndReturn(pdPASS);
    DNS_ReadReply_ExpectAnyArgs();
    DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    /* prvDNSReply */
    DNS_ParseDNSReply_ExpectAnyArgsAndReturn(0);

    /* back to prvGetHostByNameOp */
    FreeRTOS_ReleaseUDPPayloadBuffer_ExpectAnyArgs();
    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL(0, ret);

    free(xReceiveBuffer.pucPayloadBuffer );
}

void test_FreeRTOS_gethostbyname_succes(void)
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct dns_buffer xReceiveBuffer;

    xReceiveBuffer.pucPayloadBuffer = malloc(300);
    xReceiveBuffer.uxPayloadLength = 300;

    xNetworkBuffer.xDataLength = 2280;
    xNetworkBuffer.pucEthernetBuffer = malloc(2280);

    FreeRTOS_inet_addr_ExpectAndReturn(GOOD_ADDRESS, 0);
    FreeRTOS_dnslookup_ExpectAndReturn(GOOD_ADDRESS, 0);
    xApplicationGetRandomNumber_IgnoreAndReturn(34);
    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&xNetworkBuffer);
    /* back in prvGetHostByName */
    DNS_CreateSocket_ExpectAnyArgsAndReturn((void*) 23);
    /* prvGetHostByNameOp */
    /* prvFillockAddress */
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
    /* back prvGetHostByNameOp */
    DNS_SendRequest_ExpectAnyArgsAndReturn(pdPASS);
    DNS_ReadReply_ExpectAnyArgs();
    DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    /* prvDNSReply */
    DNS_ParseDNSReply_ExpectAnyArgsAndReturn(12345);
    FreeRTOS_ReleaseUDPPayloadBuffer_ExpectAnyArgs();

    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL(12345, ret);

    free(xReceiveBuffer.pucPayloadBuffer );
}

void test_ulDNSHandlePacket_success(void)
{
    uint32_t  ret;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t );
    xNetworkBuffer.pucEthernetBuffer = malloc( sizeof( UDPPacket_t ) +
                                                        sizeof( DNSMessage_t ));
    DNS_ParseDNSReply_ExpectAnyArgsAndReturn(0);

    ret = ulDNSHandlePacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ret );
    free( xNetworkBuffer.pucEthernetBuffer );
}

void test_ulDNSHandlePacket_fail_small_buffer(void)
{
    uint32_t  ret;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) - 2;
    xNetworkBuffer.pucEthernetBuffer = malloc( sizeof( UDPPacket_t ) - 2);

    ret = ulDNSHandlePacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ret );
    free( xNetworkBuffer.pucEthernetBuffer );
}

void test_ulDNSHandlePacket_fail_small_buffer2(void)
{
    uint32_t  ret;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 2;
    xNetworkBuffer.pucEthernetBuffer = malloc( sizeof( UDPPacket_t ) + 2 );

    ret = ulDNSHandlePacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ret );
    free( xNetworkBuffer.pucEthernetBuffer );
}

void test_ulNBNSHandlePacket_success( void )
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;
    size_t uxBytesNeeded = sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t );

    xNetworkBuffer.xDataLength = uxBytesNeeded;
    xNetworkBuffer.pucEthernetBuffer = malloc( uxBytesNeeded );

    DNS_TreatNBNS_ExpectAnyArgs();
    ret = ulNBNSHandlePacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ret );
    free( xNetworkBuffer.pucEthernetBuffer );
}

void test_ulNBNSHandlePacket_fail_small_buffer( void )
{
    uint32_t ret;
    NetworkBufferDescriptor_t xNetworkBuffer;
    size_t uxBytesNeeded = sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t );

    xNetworkBuffer.xDataLength = uxBytesNeeded - 5;
    xNetworkBuffer.pucEthernetBuffer = malloc( uxBytesNeeded - 5 );

    ret = ulNBNSHandlePacket( &xNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ret );

    free( xNetworkBuffer.pucEthernetBuffer );
}

void test_FreeRTOS_gethostbyname_cancel_success( void )
{
    void * pvSearchID = NULL;
    vDNSCheckCallBack_ExpectAnyArgs();
    FreeRTOS_gethostbyname_cancel( pvSearchID );
}

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                uint32_t /* ulIPAddress */ );

static int callback_called = 0;
void dns_callback (const char * pcName, void * pvSearchID, uint32_t ulIPAddress)
{
//    printf("callback called\n");
    callback_called = 1;
}

void test_FreeRTOS_gethostbyname_a_no_callback( void )
{
    uint32_t ret;
    int pvSearchID = 32;
    NetworkBufferDescriptor_t xNetworkBuffer;

    FreeRTOS_inet_addr_ExpectAndReturn(GOOD_ADDRESS, 0);
    FreeRTOS_dnslookup_ExpectAndReturn(GOOD_ADDRESS, 0);
    xApplicationGetRandomNumber_IgnoreAndReturn(pdTRUE);
    vDNSSetCallBack_ExpectAnyArgs();
    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&xNetworkBuffer);
    /* back in prvGetHostByName */
    DNS_CreateSocket_ExpectAnyArgsAndReturn(NULL);
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname_a( GOOD_ADDRESS,
                                    dns_callback,
                                    &pvSearchID,
                                    0 );
    TEST_ASSERT_EQUAL(0, ret);
    TEST_ASSERT_EQUAL(0, callback_called );
}

void test_FreeRTOS_gethostbyname_a_no_set_callback( void )
{
    uint32_t ret;
    int pvSearchID = 32;
    NetworkBufferDescriptor_t xNetworkBuffer;

    FreeRTOS_inet_addr_ExpectAndReturn(GOOD_ADDRESS, 0);
    FreeRTOS_dnslookup_ExpectAndReturn(GOOD_ADDRESS, 0);
    xApplicationGetRandomNumber_IgnoreAndReturn(pdFALSE);

    ret = FreeRTOS_gethostbyname_a( GOOD_ADDRESS,
                                    dns_callback,
                                    &pvSearchID,
                                    0 );
    TEST_ASSERT_EQUAL(0, ret);
    TEST_ASSERT_EQUAL(0, callback_called );
}


void test_FreeRTOS_gethostbyname_a_callback( void )
{
    uint32_t ret;
    int pvSearchID = 32;

    FreeRTOS_inet_addr_ExpectAndReturn(GOOD_ADDRESS, 0);
    FreeRTOS_dnslookup_ExpectAndReturn(GOOD_ADDRESS, 5);
    xApplicationGetRandomNumber_IgnoreAndReturn(pdTRUE);

    ret = FreeRTOS_gethostbyname_a( GOOD_ADDRESS,
                                    dns_callback,
                                    &pvSearchID,
                                    0 );
    TEST_ASSERT_EQUAL(5, ret);
    TEST_ASSERT_EQUAL(1, callback_called );
    callback_called = 0;
}

void test_FreeRTOS_gethostbyname_a_no_callback_retry_once( void )
{
    uint32_t ret;
    int pvSearchID = 32;
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct dns_buffer xReceiveBuffer;
    size_t uxBytesNeeded = sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t );

    xNetworkBuffer.pucEthernetBuffer = malloc( uxBytesNeeded );
    xNetworkBuffer.xDataLength = uxBytesNeeded;
    xReceiveBuffer.pucPayloadBuffer = malloc(300);
    xReceiveBuffer.uxPayloadLength = 300;

    FreeRTOS_inet_addr_ExpectAndReturn(GOOD_ADDRESS, 0);
    FreeRTOS_dnslookup_ExpectAndReturn(GOOD_ADDRESS, 0);
    xApplicationGetRandomNumber_IgnoreAndReturn(pdTRUE);
    vDNSSetCallBack_ExpectAnyArgs();
    /* in prvGetHostByName */
    /* in prvGetPayloadBuffer */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&xNetworkBuffer);
    /* back in prvGetHostByName */
    DNS_CreateSocket_ExpectAnyArgsAndReturn((void*) 23);
    /* prvGetHostByNameOp */
    /* prvFillockAddress */
    FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();
    /* back prvGetHostByNameOp */
    DNS_SendRequest_ExpectAnyArgsAndReturn(pdPASS);
    DNS_ReadReply_ExpectAnyArgs();
    DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    /* prvDNSReply */
    DNS_ParseDNSReply_ExpectAnyArgsAndReturn(12345);
    FreeRTOS_ReleaseUDPPayloadBuffer_ExpectAnyArgs();

    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname_a( GOOD_ADDRESS, dns_callback, &pvSearchID, 9);
    TEST_ASSERT_EQUAL(12345, ret);
    TEST_ASSERT_EQUAL(0, callback_called );

    free(xNetworkBuffer.pucEthernetBuffer );
    free(xReceiveBuffer.pucPayloadBuffer );
}


