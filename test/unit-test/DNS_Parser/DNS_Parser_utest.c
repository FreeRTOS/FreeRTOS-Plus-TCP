/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_task.h"
#include "mock_list.h"
#include "mock_queue.h"

#include "mock_DNS_Callback.h"
#include "mock_DNS_Cache.h"
#include "mock_DNS_Networking.h"
#include "mock_NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "DNS_Parser.h"

#define LLMNR_ADDRESS     "freertos"
#define GOOD_ADDRESS      "www.freertos.org"
#define BAD_ADDRESS       "this is a bad address"
#define DOTTED_ADDRESS    "192.268.0.1"

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                uint32_t /* ulIPAddress */ );

/* ===========================   GLOBAL VARIABLES =========================== */
static int callback_called = 0;
static BaseType_t hook_return = pdFALSE;



/* ===========================  STATIC FUNCTIONS  =========================== */
static void dns_callback( const char * pcName,
                          void * pvSearchID,
                          uint32_t ulIPAddress )
{
    callback_called = 1;
}

/* ============================  TEST FIXTURES  ============================= */

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
    callback_called = 0;
}

/**
 * @brief calls at the end of each test case
 */
void tearDown( void )
{
    hook_return  = pdFALSE;
}

/* =============================  TEST CASES  =============================== */

/**
 * @brief 
 */
void test_DNS_ReadNameField_success_empty_buffer( void )
{
    uint8_t buffer[300];
    size_t ret;

    ret = DNS_ReadNameField( buffer, 0, "name", 4);
    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief 
 */
void test_DNS_ReadNameField_fail_fully_coded( void )
{
    uint8_t buffer[300] = { 0 };
    size_t ret;

    buffer[0] = dnsNAME_IS_OFFSET;

    ret = DNS_ReadNameField(buffer, 2, "name", 4);
    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief 
 */
void test_DNS_ReadNameField_success_fully_coded_gt_uint16( void )
{
    uint8_t buffer[ 300 ] = { 0 };
    size_t ret;

    buffer[0] = dnsNAME_IS_OFFSET;

    ret = DNS_ReadNameField( buffer, 8, "name", 234 );
    TEST_ASSERT_EQUAL( sizeof(uint16_t), ret );
}

/**
 * @brief 
 */
void test_DNS_ReadNameField_fail_walk_over_nothing_to_do( void )
{
    uint8_t buffer[ 300 ] = { 0 };
    size_t ret;

    buffer[ 0 ] = 0;

    ret = DNS_ReadNameField( buffer, 1666666, "name", 234 );
    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief 
 */
void test_DNS_ReadNameField_fail_walk_over( void )
{
    uint8_t buffer[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    size_t ret;

    buffer[ 0 ] = 8;

    ret = DNS_ReadNameField( buffer, 300, pcName, 300 );
    TEST_ASSERT_EQUAL( 10, ret );
}

/**
 * @brief 
 */
void test_DNS_ReadNameField_walk_over_copy_name( void )
{
    uint8_t buffer[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    size_t ret;

    buffer[ 0 ] = 8;
    strcpy(buffer + 1, "FreeRTOS");

    ret = DNS_ReadNameField( buffer, 300, pcName, 300 );
    TEST_ASSERT_EQUAL( 10, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS", pcName );
}
/**
 * @brief 
 */
void test_DNS_ReadNameField_walk_over_copy_2_names( void )
{
    uint8_t buffer[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    buffer[ 0 ] = 8;
    strcpy(buffer + 1, "FreeRTOS");
    buffer[ 9 ] = 7;
    strcpy(buffer + 10, "PlusTCP");
    size_t ret;

    ret = DNS_ReadNameField( buffer, 300, pcName, 300 );
    TEST_ASSERT_EQUAL( 18, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.PlusTCP", pcName );
}

/**
 * @brief 
 */
void test_DNS_ReadNameField_short_destination( void )
{
    uint8_t buffer[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    buffer[ 0 ] = 8;
    strcpy(buffer + 1, "FreeRTOS");
    buffer[ 9 ] = 7;
    strcpy(buffer + 10, "PlusTCP");
    size_t ret;

    ret = DNS_ReadNameField( buffer, 300, pcName, 12 );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.Plu", pcName );
}

/**
 * @brief 
 */
void test_DNS_ReadNameField_short_source( void )
{
    uint8_t buffer[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    buffer[ 0 ] = 8;
    strcpy(buffer + 1, "FreeRTOS");
    buffer[ 9 ] = 7;
    strcpy(buffer + 10, "PlusTCP");
    size_t ret;

    ret = DNS_ReadNameField( buffer, 10, pcName, 300 );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.", pcName );
}

/**
 * @brief 
 */
void test_DNS_ReadNameField_fail_name_len_gt_destlen( void )
{
    uint8_t buffer[ 15 ] = { 0 };
    char pcName[ 10 ] = { 0 };
    buffer[ 0 ] = 8;
    strcpy(buffer + 1, "FreeRTOS");
    buffer[ 9 ] = 1;
    size_t ret;

    ret = DNS_ReadNameField( buffer, 15, pcName, 10 );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.", pcName );
}

/**
 * @brief  useless
 */
/*
void test_DNS_ReadNameField_end_of_input( void )
{
    uint8_t buffer[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    buffer[ 0 ] = 8;
    strcpy(buffer + 1, "FreeRTOS");
    buffer[ 9 ] = 1;
    size_t ret;

    ret = DNS_ReadNameField( buffer, 300, pcName, 300 );
    TEST_ASSERT_EQUAL( 12, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.", pcName );
}
*/


/* ==================== Testing  DNS_SkipNameField ===========================*/
/**
 * @brief
 */
void test_DNS_SkipNameField_failed_zero_length()
{
    size_t ret;
    uint8_t pucByte[20];

    ret = DNS_SkipNameField(pucByte, 0);

    TEST_ASSERT_EQUAL(0, ret);
}

/**
 * @brief
 */
void test_DNS_SkipNameField_failed_()
{
    uint8_t buffer[ 300 ] = { 0 };
    size_t ret;

    buffer[ 0 ] = 8;
    strcpy(buffer + 1, "FreeRTOS");
    buffer[ 9 ] = 7;
    strcpy(buffer + 10, "PlusTCP");

    ret = DNS_SkipNameField( buffer, 300 );

    TEST_ASSERT_EQUAL( 18, ret );
}


/**
 * @brief 
 */
void test_DNS_SkipNameField_fail_fully_coded( void )
{
    uint8_t buffer[300] = { 0 };
    size_t ret;

    buffer[0] = dnsNAME_IS_OFFSET;

    ret = DNS_SkipNameField(buffer, 2);
    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief 
 */
void test_DNS_SkipNameField_success_fully_coded_gt_uint16( void )
{
    uint8_t buffer[ 300 ] = { 0 };
    size_t ret;

    buffer[0] = dnsNAME_IS_OFFSET;

    ret = DNS_SkipNameField( buffer, 84 );
    TEST_ASSERT_EQUAL( sizeof(uint16_t), ret );
}

/**
 * @brief 
 */
void test_DNS_SkipNameField_short_source( void )
{
    uint8_t buffer[ 300 ] = { 0 };
    buffer[ 0 ] = 8;
    strcpy(buffer + 1, "FreeRTOS");
    buffer[ 9 ] = 7;
    strcpy(buffer + 10, "PlusTCP");
    size_t ret;

    ret = DNS_SkipNameField( buffer, 10 );
    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief 
 */
void test_DNS_SkipNameField_small_buffer( void )
{
    uint8_t buffer[ 300 ] = { 0 };
    buffer[ 0 ] = 8;
    strcpy(buffer + 1, "FreeRTOS");
    buffer[ 9 ] = 7;
    strcpy(buffer + 10, "PlusTCP");
    size_t ret;

    ret = DNS_SkipNameField( buffer, 6 );
    TEST_ASSERT_EQUAL( 0, ret );
}

/* ===================== prepareReplyDNSMessage ============================= */
/**
 * @brief 
 */
void test_prepareReplyDNSMessage_success( void )
{
    NetworkBufferDescriptor_t pxNetworkBuffer;
    uint8_t ether_buffer[ 300 ];
    size_t uxDataLength;
    pxNetworkBuffer.pucEthernetBuffer = ether_buffer;

    BaseType_t lNetLength = 50;
    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;
    UDPHeader_t * pxUDPHeader;

    pxUDPPacket = ipCAST_PTR_TO_TYPE_PTR( UDPPacket_t,
                                          &pxNetworkBuffer.pucEthernetBuffer );
    pxIPHeader = &pxUDPPacket->xIPHeader;
    pxUDPHeader = &pxUDPPacket->xUDPHeader;

    pxIPHeader->ulSourceIPAddress = 1234;

    usGenerateChecksum_ExpectAnyArgsAndReturn(555);
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn(444);

    prepareReplyDNSMessage( &pxNetworkBuffer,
                            lNetLength );

    uxDataLength = ( ( size_t ) lNetLength ) + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER + ipSIZE_OF_ETH_HEADER;
    TEST_ASSERT_EQUAL( pxNetworkBuffer.xDataLength, uxDataLength );

}

/* =========================== test DNS_TreatNBNS  ========================== */
/**
 * @brief 
 */
void test_DNS_TreatNBNS_success (void)
{

    uint8_t pucPayload[300];
    size_t uxBufferLength;
    uint32_t ulIPAddress;


    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief 
 */
void test_DNS_TreatNBNS_success_nbns_mask (void)
{

    uint8_t pucPayload[300];
    size_t uxBufferLength;
    uint32_t ulIPAddress;


    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_MASK );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief 
 */
void test_DNS_TreatNBNS_success_nbns_query_trailing_space (void)
{

    uint8_t pucPayload[300];
    size_t uxBufferLength;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t  pxNetworkBuffer;

    hook_return = pdTRUE;
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(NULL);

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief 
 */
void test_DNS_TreatNBNS_success_nbns_query (void)
{

    uint8_t pucPayload[300];
    size_t uxBufferLength;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t  pxNetworkBuffer;

    hook_return = pdTRUE;
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(NULL);

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief 
 */
void test_DNS_TreatNBNS_success_nbns_query_network_buffer_null (void)
{

    uint8_t pucPayload[300];
    size_t uxBufferLength;
    uint32_t ulIPAddress;


    hook_return = pdTRUE;
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( NULL );


    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief 
 */
void test_DNS_TreatNBNS_success_nbns_non_fixed_size_buffer (void)
{

    uint8_t pucPayload[300];
    size_t uxBufferLength;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t  pxNetworkBuffer;
    NetworkBufferDescriptor_t  pxNetworkBuffer_dup;

    uint8_t buffer[300];
  pxNetworkBuffer_dup.pucEthernetBuffer = buffer;

    hook_return = pdTRUE;
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
 //   pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(NULL);
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&pxNetworkBuffer_dup);
    usGenerateChecksum_ExpectAnyArgsAndReturn(4);
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn(4);
    vReturnEthernetFrame_ExpectAnyArgs();
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief 
 */
void test_DNS_TreatNBNS_success_empty_char_nbns_name (void)
{

    uint8_t pucPayload[300];
    size_t uxBufferLength;
    uint32_t ulIPAddress;

    pucPayload[ (dnsNBNS_ENCODED_NAME_LENGTH -2 ) +
                         offsetof( NBNSRequest_t, ucName ) ] =  2 + 0x41U;
    pucPayload[ (dnsNBNS_ENCODED_NAME_LENGTH - 2 ) +
                        offsetof( NBNSRequest_t, ucName ) + 1] =  ' ' + 0x41U;

    NetworkBufferDescriptor_t  pxNetworkBuffer;
    NetworkBufferDescriptor_t  pxNetworkBuffer_dup;

    uint8_t buffer[300];
  pxNetworkBuffer_dup.pucEthernetBuffer = buffer;

    hook_return = pdTRUE;
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY| dnsNBNS_FLAGS_RESPONSE  );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn(1);

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}
 /* ======================= tes  DNS_ParseDNSReply ========================== */
/**
 * @brief 
 */
void test_DNS_ParseDNSReply_fail_no_namefield (void)
{
    uint32_t ret;
    uint8_t  pucUDPPayloadBuffer[300];
    size_t uxBufferLength = 300;
    BaseType_t xExpected = pdFALSE;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                              uxBufferLength,
                              xExpected );
    TEST_ASSERT_EQUAL(pdFALSE, ret);
}

/**
 * @brief 
 */
void test_DNS_ParseDNSReply_fail_small_buffer (void)
{
    uint32_t ret;
    uint8_t  pucUDPPayloadBuffer[sizeof(DNSMessage_t) - 2];
    size_t uxBufferLength = sizeof(DNSMessage_t) - 2;
    BaseType_t xExpected = pdFALSE;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                              uxBufferLength,
                              xExpected );
    TEST_ASSERT_EQUAL(pdFALSE, ret);
}

/**
 * @brief 
 */
void test_DNS_ParseDNSReply_fail (void)
{
    uint32_t ret;
    uint8_t  pucUDPPayloadBuffer[300];
    size_t uxBufferLength = 300;
    BaseType_t xExpected = pdFALSE;
    int beg = sizeof( DNSMessage_t );
    pucUDPPayloadBuffer[ beg++ ] = 8;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOS");

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                              uxBufferLength,
                              xExpected );
    TEST_ASSERT_EQUAL(pdFALSE, ret);
}

/**
 * @brief 
 */
void test_DNS_ParseDNSReply_fail_empty_namefield (void)
{
    uint32_t ret;
    uint8_t  pucUDPPayloadBuffer[300];
    size_t uxBufferLength = 300;
    BaseType_t xExpected = pdFALSE;
    uint8_t beg = sizeof( DNSMessage_t );
    pucUDPPayloadBuffer[offsetof( DNSMessage_t, usQuestions)] = 4;

    pucUDPPayloadBuffer[ beg++ ] = 8;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOS");

    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); // usType
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); // usClass
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                              uxBufferLength,
                              xExpected );
    TEST_ASSERT_EQUAL(pdFALSE, ret);
}

/**
 * @brief 
 */
void test_DNS_ParseDNSReply_fail_not_enough_space_lt_32 (void)
{
    uint32_t ret;
    uint8_t  pucUDPPayloadBuffer[250];
    size_t uxBufferLength = 250;
    char dns[64];
    memset(dns, 'a', 64);
    dns[63] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );
    pucUDPPayloadBuffer[offsetof( DNSMessage_t, usQuestions)] = 4;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq");
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111");
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111");
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111");
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111");
    beg += 38;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                              uxBufferLength,
                              xExpected );
    TEST_ASSERT_EQUAL(pdFALSE, ret);
}

/**
 * @brief 
 */
void test_DNS_ParseDNSReply_ansswer_record_no_answers (void)
{
    uint32_t ret;
    uint8_t  pucUDPPayloadBuffer[250];
    size_t uxBufferLength = 250;
    char dns[64];
    memset(dns, 'a', 64);
    dns[63] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    pucUDPPayloadBuffer[offsetof( DNSMessage_t, usQuestions)] = 0;
    pucUDPPayloadBuffer[offsetof( DNSMessage_t, usAnswers)] = 0;

    pucUDPPayloadBuffer[offsetof( DNSMessage_t, usFlags)] =  dnsRX_FLAGS_MASK| dnsEXPECTED_RX_FLAGS;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                              uxBufferLength,
                              xExpected );
    TEST_ASSERT_EQUAL(pdFALSE, ret);
}

/**
 * @brief 
 */
void test_DNS_ParseDNSReply_ansswer_record_too_many_answers(void)
{
    uint32_t ret;
    uint8_t  pucUDPPayloadBuffer[250] = {0};
    size_t uxBufferLength = 250;
    char dns[64];
    memset(dns, 'a', 64);
    dns[63] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons(1);
    dns_header->usAnswers = FreeRTOS_htons(2);
    dns_header->usFlags = dnsEXPECTED_RX_FLAGS;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    beg+= sizeof(uint32_t);

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); // usType
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); // usClass
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); // usType

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                              uxBufferLength,
                              xExpected );
    TEST_ASSERT_EQUAL(pdFALSE, ret);
}

/**
 * @brief 
 */
void test_DNS_ParseDNSReply_ansswer_lmmnr_reply(void)
{
    uint32_t ret;
    uint8_t  pucUDPPayloadBuffer[250] = {0};
    size_t uxBufferLength = 250;

    NetworkBufferDescriptor_t pxNetworkBuffer;
    pxNetworkBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    char dns[64];
    memset(dns, 'a', 64);
    dns[63] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons(1);
    dns_header->usAnswers = FreeRTOS_htons(2);
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    beg+= sizeof(uint32_t);

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); // usType
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN ); // usClass
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(&pxNewBuffer);
    usGenerateChecksum_ExpectAnyArgsAndReturn(1234);
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn(123);
    vReturnEthernetFrame_ExpectAnyArgs();
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                              uxBufferLength,
                              xExpected );
    TEST_ASSERT_EQUAL(pdFALSE, ret);
}

/**
 * @brief 
 */
void test_DNS_ParseDNSReply_ansswer_lmmnr_reply_query_hook_false(void)
{
    uint32_t ret;
    uint8_t  pucUDPPayloadBuffer[250] = {0};
    size_t uxBufferLength = 250;

    NetworkBufferDescriptor_t pxNetworkBuffer;
    pxNetworkBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    char dns[64];
    memset(dns, 'a', 64);
    dns[63] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons(1);
    dns_header->usAnswers = FreeRTOS_htons(2);
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    beg+= sizeof(uint32_t);

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); // usType
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN ); // usClass
    hook_return = pdFALSE;
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                              uxBufferLength,
                              xExpected );
    TEST_ASSERT_EQUAL(pdFALSE, ret);
}

/**
 * @brief 
 */
void test_DNS_ParseDNSReply_ansswer_lmmnr_reply_null_new_netbuffer(void)
{
    uint32_t ret;
    uint8_t  pucUDPPayloadBuffer[250] = {0};
    size_t uxBufferLength = 250;

    NetworkBufferDescriptor_t pxNetworkBuffer;
    pxNetworkBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    char dns[64];
    memset(dns, 'a', 64);
    dns[63] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons(1);
    dns_header->usAnswers = FreeRTOS_htons(2);
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    beg+= sizeof(uint32_t);

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); // usType
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN ); // usClass
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( NULL );
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                              uxBufferLength,
                              xExpected );
    TEST_ASSERT_EQUAL(pdFALSE, ret);
}

/**
 * @brief 
 */
void test_DNS_ParseDNSReply_ansswer_lmmnr_reply_null_new_netbuffer2(void)
{
    uint32_t ret;
    uint8_t  pucUDPPayloadBuffer[250] = {0};
    size_t uxBufferLength = 250;

    NetworkBufferDescriptor_t pxNetworkBuffer;
    pxNetworkBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = pucUDPPayloadBuffer;
    char dns[64];
    memset(dns, 'a', 64);
    dns[63] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons(1);
    dns_header->usAnswers = FreeRTOS_htons(2);
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    beg+= sizeof(uint32_t);

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy(pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); // usType
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN ); // usClass
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn(NULL);
    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                              uxBufferLength,
                              xExpected );
    TEST_ASSERT_EQUAL(pdFALSE, ret);
}

/**
 * @brief 
 */
void test_parseDNSAnswer_no_answers(void)
{
    BaseType_t ret;
    DNSMessage_t  pxDNSMessageHeader;
    char pucByte[300];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[300];
    BaseType_t xDoStore = pdFALSE;

    pxDNSMessageHeader.usAnswers = 0;

    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore);
    TEST_ASSERT_EQUAL( pdTRUE, ret );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is resured
 */
void test_parseDNSAnswer_recordstored_gt_count(void)
{
    BaseType_t ret;
    DNSMessage_t  pxDNSMessageHeader;
    char pucByte[300];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[300];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;



    pucByte[ 0 ] = 38;
    strcpy(pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");

    pxDNSMessageHeader.usAnswers =  ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); // usType
    xDNSDoCallback_ExpectAnyArgsAndReturn(pdTRUE);
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn(pdTRUE);
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn(pdTRUE);

    pxDNSAnswerRecord = ( DNSAnswerRecord_t *) (pucByte + 40 );
    pxDNSAnswerRecord->usDataLength =  FreeRTOS_htons(ipSIZE_OF_IPv4_ADDRESS);
    //pxDNSAnswerRecord->usDataLength =  (ipSIZE_OF_IPv4_ADDRESS);
    pxDNSAnswerRecord->usType =  (dnsTYPE_A_HOST);

    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore);
    TEST_ASSERT_EQUAL( pdTRUE, ret );
}

/**
 * @brief 
 * 
 */
void test_parseDNSAnswer_remaining_gt_datalength(void)
{
    BaseType_t ret;
    DNSMessage_t  pxDNSMessageHeader;
    char pucByte[300];
    size_t uxsourceBytesRemaining = 40 + sizeof(DNSAnswerRecord_t) + 2 ;
    size_t uxBytesRead = 0;
    char pcName[300];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;



    pucByte[ 0 ] = 38;
    strcpy(pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");

    pxDNSMessageHeader.usAnswers =  ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); // usType
    //xDNSDoCallback_ExpectAnyArgsAndReturn(pdTRUE);
    //FreeRTOS_dns_update_ExpectAnyArgsAndReturn(pdTRUE);
    //FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn(pdTRUE);

    pxDNSAnswerRecord = ( DNSAnswerRecord_t *) (pucByte + 40 );
    pxDNSAnswerRecord->usDataLength =  FreeRTOS_htons(ipSIZE_OF_IPv4_ADDRESS);
    pxDNSAnswerRecord->usType =  (dnsTYPE_A_HOST);

    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore);
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief 
 * 
 */
void test_parseDNSAnswer_remaining_lt_uint16(void)
{
    BaseType_t ret;
    DNSMessage_t  pxDNSMessageHeader;
    char pucByte[300];
    size_t uxsourceBytesRemaining = 40 + 1 ;
    size_t uxBytesRead = 0;
    char pcName[300];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;



    pucByte[ 0 ] = 38;
    strcpy(pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");

    pxDNSMessageHeader.usAnswers =  ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    //usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); // usType
    //xDNSDoCallback_ExpectAnyArgsAndReturn(pdTRUE);
    //FreeRTOS_dns_update_ExpectAnyArgsAndReturn(pdTRUE);
    //FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn(pdTRUE);

    pxDNSAnswerRecord = ( DNSAnswerRecord_t *) (pucByte + 40 );
    pxDNSAnswerRecord->usDataLength =  FreeRTOS_htons(ipSIZE_OF_IPv4_ADDRESS);
    pxDNSAnswerRecord->usType =  (dnsTYPE_A_HOST);

    ret = parseDNSAnswer( &pxDNSMessageHeader,
                          pucByte,
                          uxsourceBytesRemaining,
                          &uxBytesRead,
                          pcName,
                          xDoStore);
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}
BaseType_t xApplicationDNSQueryHook( const char * pcName )
{
    return hook_return;;
}
