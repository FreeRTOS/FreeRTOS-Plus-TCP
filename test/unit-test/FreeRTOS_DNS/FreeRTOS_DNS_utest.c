/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_list.h"
/* This must come after list.h is included. */
#include "mock_list_macros.h"
#include "mock_task.h"
#include "mock_semphr.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_NetworkBufferManagement.h"

#include "mock_portable_functions.h"

#include "mock_FreeRTOS_DNS_mock.h"

#include "FreeRTOS_DNS.h"

#include "FreeRTOS_DNS_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

extern DNSCacheRow_t xDNSCache[ ipconfigDNS_CACHE_ENTRIES ];

DNSCacheRow_t xTestDNSCache[ ipconfigDNS_CACHE_ENTRIES ];

List_t xCallbackList;


static void vListInitialise_stub( List_t * const pxList,
                                  int callbackcount )
{
    /* The list structure contains a list item which is used to mark the
     * end of the list.  To initialise the list the list end is inserted
     * as the only list entry. */
    pxList->pxIndex = ( ListItem_t * ) &( pxList->xListEnd );

    /* The list end value is the highest possible value in the list to
     * ensure it remains at the end of the list. */
    pxList->xListEnd.xItemValue = portMAX_DELAY;

    /* The list end next and previous pointers point to itself so we know
     * when the list is empty. */
    pxList->xListEnd.pxNext = ( ListItem_t * ) &( pxList->xListEnd );
    pxList->xListEnd.pxPrevious = ( ListItem_t * ) &( pxList->xListEnd );

    pxList->uxNumberOfItems = ( UBaseType_t ) 0U;

    /* Write known values into the list if
     * configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    listSET_LIST_INTEGRITY_CHECK_1_VALUE( pxList );
    listSET_LIST_INTEGRITY_CHECK_2_VALUE( pxList );
}

static int CallBackFunction_CallCount = 0;
static void CallBackFunction_CalledXTimes( const char * pcName,
                                           void * pvsearchID,
                                           uint32_t ulIPAddress )
{
    if( --CallBackFunction_CallCount < 0 )
    {
        TEST_FAIL_MESSAGE( "Not expected to be called these many times" );
    }
}


static void vListInsertEnd_stub( List_t * const pxList,
                                 ListItem_t * const pxNewListItem )
{
    ListItem_t * const pxIndex = pxList->pxIndex;

    /* Only effective when configASSERT() is also defined, these tests may catch
     * the list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
    listTEST_LIST_INTEGRITY( pxList );
    listTEST_LIST_ITEM_INTEGRITY( pxNewListItem );

    /* Insert a new list item into pxList, but rather than sort the list,
     * makes the new list item the last item to be removed by a call to
     * listGET_OWNER_OF_NEXT_ENTRY(). */
    pxNewListItem->pxNext = pxIndex;
    pxNewListItem->pxPrevious = pxIndex->pxPrevious;

    /* Only used during decision coverage testing. */
    mtCOVERAGE_TEST_DELAY();

    pxIndex->pxPrevious->pxNext = pxNewListItem;
    pxIndex->pxPrevious = pxNewListItem;

    /* Remember which list the item is in. */
    pxNewListItem->pxContainer = pxList;

    ( pxList->uxNumberOfItems )++;
}

static uint8_t * ucGenericPtr;
static int32_t ulGenericLength;
static int32_t FreeRTOS_recvfrom_Generic( Socket_t xSocket,
                                          void * pvBuffer,
                                          size_t uxBufferLength,
                                          BaseType_t xFlags,
                                          struct freertos_sockaddr * pxSourceAddress,
                                          socklen_t * pxSourceAddressLength,
                                          int callbacks )
{
    if( xFlags == FREERTOS_ZERO_COPY )
    {
        *( ( uint8_t ** ) pvBuffer ) = ucGenericPtr;
    }

    return ulGenericLength;
}

static uint32_t RNGtoReturn;
static BaseType_t RNGstatus;
static BaseType_t xApplicationGetRandomNumber_Generic( uint32_t * pulPointer,
                                                       int callbacks )
{
    *pulPointer = RNGtoReturn;

    return RNGstatus;
}



void test_FreeRTOS_dnsclear( void )
{
    /* Fill in some data. */
    memset( xDNSCache, 0xAA, sizeof( xDNSCache ) );
    /* Fill in test cache to compare against */
    memset( xTestDNSCache, 0x00, sizeof( xTestDNSCache ) );

    FreeRTOS_dnsclear();

    TEST_ASSERT_EQUAL_MEMORY( xTestDNSCache, xDNSCache, sizeof( xTestDNSCache ) );
}
void test_FreeRTOS_dnslookup_NULLHostName( void )
{
    xTaskGetTickCount_ExpectAndReturn( 100 );
    catch_assert( FreeRTOS_dnslookup( NULL ) );
}

void test_FreeRTOS_dnslookup_EmptyCache( void )
{
    char * pcHostName = "Test Host";
    uint32_t ulIPAddress;

    /* For each entry in the DNS cache table. */
    for( int x = 0; x < ipconfigDNS_CACHE_ENTRIES; x++ )
    {
        /* Clear the DNS cache. */
        memset( xDNSCache[ x ].pcName, 0, ipconfigDNS_CACHE_NAME_LENGTH );
    }

    xTaskGetTickCount_ExpectAndReturn( 100 );
    ulIPAddress = FreeRTOS_dnslookup( pcHostName );

    TEST_ASSERT_EQUAL( 0, ulIPAddress );
}

void test_FreeRTOS_dnslookup_NoMatchingName( void )
{
    char * pcHostName = "Test Host";
    char * pcIncorrectname = "Some Name";
    uint32_t ulIPAddress;

    /* For each entry in the DNS cache table. */
    for( int x = 0; x < ipconfigDNS_CACHE_ENTRIES; x++ )
    {
        /* Clear the DNS cache. */
        memset( xDNSCache[ x ].pcName, 0, ipconfigDNS_CACHE_NAME_LENGTH );
        /* Add Incorrect names. */
        memcpy( xDNSCache[ x ].pcName, pcIncorrectname, sizeof( pcIncorrectname ) );
    }

    xTaskGetTickCount_ExpectAndReturn( 100 );
    ulIPAddress = FreeRTOS_dnslookup( pcHostName );

    /* IP address should not be found. */
    TEST_ASSERT_EQUAL( 0, ulIPAddress );
}

void test_FreeRTOS_dnslookup_MatchingName_AgedEntry( void )
{
    char * pcHostName = "TestHost\0";
    char * pcIncorrectname = "SomeName\0";
    uint32_t ulIPAddress;
    int EntryToCheck = 1;

    /* The entry to check must be in range. */
    assert( EntryToCheck < ipconfigDNS_CACHE_ENTRIES );

    /* For each entry in the DNS cache table. */
    for( int x = 0; x < ipconfigDNS_CACHE_ENTRIES; x++ )
    {
        /* Clear the DNS cache. */
        memset( xDNSCache[ x ].pcName, 0, ipconfigDNS_CACHE_NAME_LENGTH );
        /* Add Incorrect names. */
        memcpy( xDNSCache[ x ].pcName, pcIncorrectname, sizeof( pcIncorrectname ) );

        /* Make sure that timeout occurs */
        xDNSCache[ x ].ulTimeWhenAddedInSeconds = 0;
        xDNSCache[ x ].ulTTL = 0;
    }

    /* Add an entry which will match. */
    /* Clear the DNS cache. */
    memset( xDNSCache[ EntryToCheck ].pcName, 0, ipconfigDNS_CACHE_NAME_LENGTH );
    /* Add Correct name. */
    memcpy( xDNSCache[ EntryToCheck ].pcName, pcHostName, sizeof( pcHostName ) );

    /* Make sure that timeout occurs */
    xTaskGetTickCount_ExpectAndReturn( 100 );
    ulIPAddress = FreeRTOS_dnslookup( pcHostName );

    /* IP address should not be found. */
    TEST_ASSERT_EQUAL( 0, ulIPAddress );
    /* Aged out - the entry should be cleared. */
    TEST_ASSERT_EQUAL( 0, xDNSCache[ EntryToCheck ].pcName[ 0 ] );
}

void test_FreeRTOS_dnslookup_MatchingName_NotAgedEntry_NumIPAddressIsZero( void )
{
    char * pcHostName = "TestHost\0";
    char * pcIncorrectname = "SomeName\0";
    uint32_t ulIPAddress;
    int EntryToCheck = 1;

    /* The entry to check must be in range. */
    assert( EntryToCheck < ipconfigDNS_CACHE_ENTRIES );

    /* For each entry in the DNS cache table. */
    for( int x = 0; x < ipconfigDNS_CACHE_ENTRIES; x++ )
    {
        /* Clear the DNS cache. */
        memset( xDNSCache[ x ].pcName, 0, ipconfigDNS_CACHE_NAME_LENGTH );
        /* Add Incorrect names. */
        memcpy( xDNSCache[ x ].pcName, pcIncorrectname, sizeof( pcIncorrectname ) );

        /* Make sure that timeout doesn't occur */
        xDNSCache[ x ].ulTimeWhenAddedInSeconds = 200;
        xDNSCache[ x ].ulTTL = 0;

        /* Try a lookup with 0 IP addresses. */
        xDNSCache[ x ].ucNumIPAddresses = 0;
    }

    /* Add an entry which will match. */
    /* Clear the DNS cache. */
    memset( xDNSCache[ EntryToCheck ].pcName, 0, ipconfigDNS_CACHE_NAME_LENGTH );
    /* Add Correct name. */
    memcpy( xDNSCache[ EntryToCheck ].pcName, pcHostName, sizeof( pcHostName ) );

    /* Make sure that timeout doesn't occur */
    xTaskGetTickCount_ExpectAndReturn( 100 );
    ulIPAddress = FreeRTOS_dnslookup( pcHostName );

    /* IP address should not be found. */
    TEST_ASSERT_EQUAL( 0, ulIPAddress );
}

void test_FreeRTOS_dnslookup_MatchingName_NotAgedEntry_NumIPAddressIsNonZero( void )
{
    char * pcHostName = "TestHost\0";
    char * pcIncorrectname = "SomeName\0";
    uint32_t ulIPAddress;
    uint32_t ulTestIPAddress = 0x12345678;
    int EntryToCheck = 1;

    /* The entry to check must be in range. */
    assert( EntryToCheck < ipconfigDNS_CACHE_ENTRIES );

    /* For each entry in the DNS cache table. */
    for( int x = 0; x < ipconfigDNS_CACHE_ENTRIES; x++ )
    {
        /* Clear the DNS cache. */
        memset( xDNSCache[ x ].pcName, 0, ipconfigDNS_CACHE_NAME_LENGTH );

        /* Make sure that timeout doesn't occur */
        xDNSCache[ x ].ulTimeWhenAddedInSeconds = 200;
        xDNSCache[ x ].ulTTL = 0;

        /* Try a lookup with non 0 IP addresses. */
        xDNSCache[ x ].ucNumIPAddresses = 2;

        /* Any value greater than the ucNumIPAddresses. */
        xDNSCache[ x ].ucCurrentIPAddress = 3;
        xDNSCache[ x ].ulIPAddresses[ xDNSCache[ x ].ucCurrentIPAddress % xDNSCache[ x ].ucNumIPAddresses ] = 0;
    }

    /* Add an entry which will match. */
    /* Clear the DNS cache. */
    memset( xDNSCache[ EntryToCheck ].pcName, 0, ipconfigDNS_CACHE_NAME_LENGTH );
    /* Add Correct name. */
    memcpy( xDNSCache[ EntryToCheck ].pcName, pcHostName, sizeof( pcHostName ) );
    /* Add the IP address we want. */
    xDNSCache[ EntryToCheck ].ulIPAddresses[
        xDNSCache[ EntryToCheck ].ucCurrentIPAddress %
        xDNSCache[ EntryToCheck ].ucNumIPAddresses ] = ulTestIPAddress;

    /* Make sure that timeout doesn't occur */
    xTaskGetTickCount_ExpectAndReturn( 100 );
    ulIPAddress = FreeRTOS_dnslookup( pcHostName );

    /* IP address should not be found. */
    TEST_ASSERT_EQUAL( ulTestIPAddress, ulIPAddress );
}

void test_vDNSInitialise( void )
{
    vListInitialise_Expect( &xCallbackList );
    vDNSInitialise();
}

void test_vDNSCheckCallBack_EmptyCallBackList( void )
{
    ListItem_t xLocalList1, xLocalList2;

    /* We should not worry about the return value since we
     * can control all the flow. */
    listGET_END_MARKER_ExpectAndReturn( &xCallbackList, &xLocalList1 );

    /* Expect a call the suspend the scheduler. */
    vTaskSuspendAll_Expect();

    /* The next element is the current element - meaning that the list is empty. */
    listGET_NEXT_ExpectAndReturn( &xLocalList1, &xLocalList1 );

    /* Expect a call to the resume the scheduler since the list is empty. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* The list should be empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdTRUE );

    /* Expect the DNS timer to be stopeed.  */
    vIPSetDnsTimerEnableState_Expect( pdFALSE );

    /* The search ID soesn't matter since the list is empty. */
    vDNSCheckCallBack( NULL );
}

void test_vDNSCheckCallBack_OneEntryCallBackList_NULLSearch_NoTimeOut( void )
{
    ListItem_t xLocalList1, xLocalList2;
    DNSCallback_t xLocalCallback;

    /* Put some value. */
    xLocalCallback.pvSearchID = NULL;

    /* We should not worry about the return value since we
     * can control all the flow. */
    listGET_END_MARKER_ExpectAndReturn( &xCallbackList, &xLocalList1 );

    /* Expect a call the suspend the scheduler. */
    vTaskSuspendAll_Expect();

    /* The next element is returned. */
    listGET_NEXT_ExpectAndReturn( &xLocalList1, &xLocalList2 );

    /* Expect the call and return a local variable. */
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalList2, &xLocalCallback );

    /* Return the starting point. Making the list just one element long. */
    listGET_NEXT_ExpectAndReturn( &xLocalList2, &xLocalList1 );

    /* There should be no timeout. */
    xTaskCheckForTimeOut_ExpectAndReturn( &xLocalCallback.uxTimeoutState, &xLocalCallback.uxRemaningTime, pdFALSE );

    /* Expect a call to the resume the scheduler since the list is empty. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* The list should not be empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdFALSE );

    /* Call with a NULL search ID. */
    vDNSCheckCallBack( NULL );
}

void test_vDNSCheckCallBack_OneEntryCallBackList_NULLSearch_TimeOut( void )
{
    ListItem_t xLocalList1, xLocalList2;
    DNSCallback_t xLocalCallback;

    /* Set the callback. */
    /* And expect it to be called only once. */
    CallBackFunction_CallCount = 1;
    xLocalCallback.pCallbackFunction = CallBackFunction_CalledXTimes;
    /* Put some value. */
    xLocalCallback.pvSearchID = ( void * ) 2;

    /* We should not worry about the return value since we
     * can control all the flow. */
    listGET_END_MARKER_ExpectAndReturn( &xCallbackList, &xLocalList1 );

    /* Expect a call the suspend the scheduler. */
    vTaskSuspendAll_Expect();

    /* The next element is returned. */
    listGET_NEXT_ExpectAndReturn( &xLocalList1, &xLocalList2 );

    /* Expect the call and return a local variable. */
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalList2, &xLocalCallback );

    /* Return the starting point. Making the list just one element long. */
    listGET_NEXT_ExpectAndReturn( &xLocalList2, &xLocalList1 );

    /* There should be timeout. */
    xTaskCheckForTimeOut_ExpectAndReturn( &xLocalCallback.uxTimeoutState, &xLocalCallback.uxRemaningTime, pdTRUE );

    /* Expect this to be removed. */
    uxListRemove_ExpectAndReturn( &xLocalCallback.xListItem, pdTRUE );

    /* Expect this to be freed. */
    vPortFree_Expect( &xLocalCallback );

    /* Expect a call to the resume the scheduler since the list is empty. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* The list should be empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdTRUE );

    /* Expect the DNS timer to be stopeed.  */
    vIPSetDnsTimerEnableState_Expect( pdFALSE );

    /* Call with a NULL search ID. */
    vDNSCheckCallBack( NULL );
}

void test_vDNSCheckCallBack_OneEntryCallBackList_NonNULLMatchingSearch( void )
{
    ListItem_t xLocalList1, xLocalList2;
    DNSCallback_t xLocalCallback;

    /* Set the callback. */
    /* And expect it to be called only once. */
    CallBackFunction_CallCount = 1;
    xLocalCallback.pCallbackFunction = CallBackFunction_CalledXTimes;
    /* Put some value. */
    xLocalCallback.pvSearchID = ( void * ) 2;

    /* We should not worry about the return value since we
     * can control all the flow. */
    listGET_END_MARKER_ExpectAndReturn( &xCallbackList, &xLocalList1 );

    /* Expect a call the suspend the scheduler. */
    vTaskSuspendAll_Expect();

    /* The next element is returned. */
    listGET_NEXT_ExpectAndReturn( &xLocalList1, &xLocalList2 );

    /* Expect the call and return a local variable. */
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalList2, &xLocalCallback );

    /* Return the starting point. Making the list just one element long. */
    listGET_NEXT_ExpectAndReturn( &xLocalList2, &xLocalList1 );

    /* Expect the item to be removed. */
    uxListRemove_ExpectAndReturn( &xLocalCallback.xListItem, pdTRUE );

    /* Expect this to be freed. */
    vPortFree_Expect( &xLocalCallback );

    /* Expect a call to the resume the scheduler since the list is empty. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* The list should be empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdTRUE );

    /* Expect the DNS timer to be stopeed.  */
    vIPSetDnsTimerEnableState_Expect( pdFALSE );

    /* Call with a same search ID. */
    vDNSCheckCallBack( xLocalCallback.pvSearchID );
}

void test_vDNSCheckCallBack_OneEntryCallBackList_NonNULLNotMatchingSearch( void )
{
    ListItem_t xLocalList1, xLocalList2;
    DNSCallback_t xLocalCallback;

    /* Set the callback. */
    /* And expect it to be called only once. */
    CallBackFunction_CallCount = 1;
    xLocalCallback.pCallbackFunction = CallBackFunction_CalledXTimes;
    /* Put some value. */
    xLocalCallback.pvSearchID = ( void * ) 2;

    /* We should not worry about the return value since we
     * can control all the flow. */
    listGET_END_MARKER_ExpectAndReturn( &xCallbackList, &xLocalList1 );

    /* Expect a call the suspend the scheduler. */
    vTaskSuspendAll_Expect();

    /* The next element is returned. */
    listGET_NEXT_ExpectAndReturn( &xLocalList1, &xLocalList2 );

    /* Expect the call and return a local variable. */
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalList2, &xLocalCallback );

    /* Return the starting point. Making the list just one element long. */
    listGET_NEXT_ExpectAndReturn( &xLocalList2, &xLocalList1 );

    /* There should be no timeout. */
    xTaskCheckForTimeOut_ExpectAndReturn( &xLocalCallback.uxTimeoutState, &xLocalCallback.uxRemaningTime, pdFALSE );

    /* Expect a call to the resume the scheduler since the list is empty. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* The list should not be empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdFALSE );

    /* Call with a same search ID. */
    vDNSCheckCallBack( ( void * ) 3 );
}


void test_FreeRTOS_gethostbyname_NULL( void )
{
    const char * pcHostName = NULL;
    uint32_t ulReturn = FreeRTOS_gethostbyname( pcHostName );

    /* For NULL, we should get a 0 IP address. */
    TEST_ASSERT_EQUAL( ulReturn, 0 );
}

void test_FreeRTOS_gethostbyname_RecvFromFails( void )
{
    const char * pcHostName = "TestHostName";
    uint32_t ulReturn;
    Socket_t xSocket;
    NetworkBufferDescriptor_t xNetworkBuffer;

    /* Clear the cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Return any value. */
    xTaskGetTickCount_ExpectAndReturn( 0 );

    /* RNG succeds. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xSocket );
    xSocketValid_ExpectAndReturn( xSocket, pdTRUE );
    /* Return success. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );

    FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( 0 );
    FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( 0 );

    for( int xAttempt = 0; xAttempt < ipconfigDNS_REQUEST_ATTEMPTS; xAttempt++ )
    {
        pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
        FreeRTOS_GetAddressConfiguration_ExpectAnyArgs();

        /* Return non zero value to indicate success. */
        FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

        FreeRTOS_recvfrom_ExpectAnyArgsAndReturn( 0 );
    }

    FreeRTOS_closesocket_ExpectAnyArgsAndReturn( 0 );
    ulReturn = FreeRTOS_gethostbyname( pcHostName );

    /* For NULL, we should get a 0 IP address. */
    TEST_ASSERT_EQUAL( 0, ulReturn );
}

void test_FreeRTOS_gethostbyname_inetaddrFails( void )
{
    const char * pcHostName = "TestHostName";
    uint32_t ulReturn, ulIPAddress = 0x12345678;
    Socket_t xSocket;
    NetworkBufferDescriptor_t xNetworkBuffer;

    /* Clear the cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, ulIPAddress );

    ulReturn = FreeRTOS_gethostbyname( pcHostName );

    /* For NULL, we should get a 0 IP address. */
    TEST_ASSERT_EQUAL( ulIPAddress, ulReturn );
}

void test_FreeRTOS_gethostbyname_VeryLongName( void )
{
    char pcHostName[ ipconfigDNS_CACHE_NAME_LENGTH * 2 ];
    uint32_t ulReturn;
    Socket_t xSocket;
    NetworkBufferDescriptor_t xNetworkBuffer;

    for( int i = 0; i < ipconfigDNS_CACHE_NAME_LENGTH * 2; i++ )
    {
        pcHostName[ i ] = 'a';
    }

    pcHostName[ ipconfigDNS_CACHE_NAME_LENGTH * 2 - 1 ] = '\0';

    /* Clear the cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    ulReturn = FreeRTOS_gethostbyname( pcHostName );

    /* For NULL, we should get a 0 IP address. */
    TEST_ASSERT_EQUAL( ulReturn, 0 );
}

void test_FreeRTOS_gethostbyname_cancel( void )
{
    ListItem_t xLocalList;

    listGET_END_MARKER_ExpectAndReturn( &xCallbackList, &xLocalList );

    vTaskSuspendAll_Expect();

    /* Essentially return the end therefore making the list empty. */
    listGET_NEXT_ExpectAndReturn( &xLocalList, &xLocalList );
    xTaskResumeAll_ExpectAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdFALSE );
    FreeRTOS_gethostbyname_cancel( NULL );
}

void test_FreeRTOS_gethostbyname_a_inetaddrsuccess( void )
{
    const char * pcHostName = "TestHostName";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, ulIPAddr );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    TEST_ASSERT_EQUAL( ulIPAddr, ulResult );
}

void test_FreeRTOS_gethostbyname_a_inetaddrfails_mallocfails_socketfails( void )
{
    const char * pcHostName = "TestHostName";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );

    /* Make the call to socket fail. */
    FreeRTOS_socket_ExpectAnyArgsAndReturn( NULL );
    xSocketValid_ExpectAndReturn( NULL, pdFALSE );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_socketfails( void )
{
    const char * pcHostName = "someThing.com";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );

    /* Make the call to socket fail. */
    FreeRTOS_socket_ExpectAnyArgsAndReturn( NULL );
    xSocketValid_ExpectAndReturn( NULL, pdFALSE );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_socketBindfails( void )
{
    const char * pcHostName = "someThing.com";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;
    Socket_t xLocalSocket;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );

    /* Make the call to socket fail. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocket );
    xSocketValid_ExpectAndReturn( xLocalSocket, pdTRUE );
    /* Make socket bind fail. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 100 );
    /* Expect the socket to be closed. Return any value. */
    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocket, 0 );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_GNWFails( void )
{
    const char * pcHostName = "someThing.com";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;
    Socket_t xLocalSocket;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );

    /* Make the call to socket fail. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocket );
    xSocketValid_ExpectAndReturn( xLocalSocket, pdTRUE );
    /* Make socket bind succeed. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocket, 0, FREERTOS_SO_SNDTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocket, 0, FREERTOS_SO_RCVTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Make the network buffer descriptor fail. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocket, 0 );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_GNWSucceeds_sendfails( void )
{
    const char * pcHostName = "someThing.com";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;
    Socket_t xLocalSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint8_t xLocalEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER +
                                  ipSIZE_OF_UDP_HEADER + 20 /* sizeof( DNSMessage_t ) */ +
                                  strlen( pcHostName ) + sizeof( uint16_t ) +
                                  sizeof( uint16_t ) + 2U ];

    /* Set the ethernet buffer. */
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );

    /* Make the call to socket fail. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocket );
    xSocketValid_ExpectAndReturn( xLocalSocket, pdTRUE );
    /* Make socket bind succeed. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocket, 0, FREERTOS_SO_SNDTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocket, 0, FREERTOS_SO_RCVTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Make the network buffer descriptor succeed. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xLocalNetworkBuffer );

    /* Get the address configuration. Ignore the 4th argument. */
    FreeRTOS_GetAddressConfiguration_Expect( NULL, NULL, NULL, NULL );
    FreeRTOS_GetAddressConfiguration_IgnoreArg_pulDNSServerAddress();

    /* Make send fail. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 0 );

    vReleaseNetworkBufferAndDescriptor_Expect( &xLocalNetworkBuffer );

    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocket, 0 );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_inetaddrfails_RNGfails( void )
{
    const char * pcHostName = "TestHostName";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}



void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_differentID( void )
{
    const char * pcHostName = "someThing.com";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;
    struct xSOCKET xLocalSocket;
    Socket_t xLocalSocketPtr = &xLocalSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint8_t xLocalEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER +
                                  ipSIZE_OF_UDP_HEADER + 20 /* sizeof( DNSMessage_t ) */ +
                                  strlen( pcHostName ) + sizeof( uint16_t ) +
                                  sizeof( uint16_t ) + 2U ];
    uint8_t xLocalReceivedBuffer[ 200 ];

    /* Set the ethernet buffer. */
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    RNGtoReturn = 0x1234;
    RNGstatus = pdTRUE;
    xApplicationGetRandomNumber_Stub( xApplicationGetRandomNumber_Generic );

    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );

    /* Make the call to socket succeed. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocketPtr );
    xSocketValid_ExpectAndReturn( xLocalSocketPtr, pdTRUE );
    /* Make socket bind succeed. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_SNDTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_RCVTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Make the network buffer descriptor succeed. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xLocalNetworkBuffer );

    /* Get the address configuration. Ignore the 4th argument. */
    FreeRTOS_GetAddressConfiguration_Expect( NULL, NULL, NULL, NULL );
    FreeRTOS_GetAddressConfiguration_IgnoreArg_pulDNSServerAddress();

    /* Make send succeeds. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    ucGenericPtr = xLocalReceivedBuffer;
    ulGenericLength = 200;

    /* Make sure that identifiers don't match. */
    DNSMessage_t * pxDNSMessageHeader = ( DNSMessage_t * ) xLocalReceivedBuffer;
    pxDNSMessageHeader->usIdentifier = RNGtoReturn + 1;

    /* Return non zero value. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( xLocalReceivedBuffer );

    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocketPtr, 0 );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_sameID( void )
{
    const char * pcHostName = "someThing.com";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;
    struct xSOCKET xLocalSocket;
    Socket_t xLocalSocketPtr = &xLocalSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint8_t xLocalEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER +
                                  ipSIZE_OF_UDP_HEADER + 20 /* sizeof( DNSMessage_t ) */ +
                                  strlen( pcHostName ) + sizeof( uint16_t ) +
                                  sizeof( uint16_t ) + 2U ];
    uint8_t xLocalReceivedBuffer[ 200 ];

    /* Set the ethernet buffer. */
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    RNGtoReturn = 0x1234;
    RNGstatus = pdTRUE;
    xApplicationGetRandomNumber_Stub( xApplicationGetRandomNumber_Generic );

    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );

    /* Make the call to socket succeed. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocketPtr );
    xSocketValid_ExpectAndReturn( xLocalSocketPtr, pdTRUE );
    /* Make socket bind succeed. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_SNDTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_RCVTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Make the network buffer descriptor succeed. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xLocalNetworkBuffer );

    /* Get the address configuration. Ignore the 4th argument. */
    FreeRTOS_GetAddressConfiguration_Expect( NULL, NULL, NULL, NULL );
    FreeRTOS_GetAddressConfiguration_IgnoreArg_pulDNSServerAddress();

    /* Make send succeeds. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    ucGenericPtr = xLocalReceivedBuffer;
    ulGenericLength = 200;

    /* Make sure that identifiers match. */
    DNSMessage_t * pxDNSMessageHeader = ( DNSMessage_t * ) xLocalReceivedBuffer;
    pxDNSMessageHeader->usIdentifier = RNGtoReturn;

    /* Return non zero value. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( xLocalReceivedBuffer );

    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocketPtr, 0 );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocSucceeds_EmptyList( void )
{
    const char * pcHostName = "someThing.com";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;
    struct xSOCKET xLocalSocket;
    Socket_t xLocalSocketPtr = &xLocalSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint8_t xLocalEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER +
                                  ipSIZE_OF_UDP_HEADER + 20 /* sizeof( DNSMessage_t ) */ +
                                  strlen( pcHostName ) + sizeof( uint16_t ) +
                                  sizeof( uint16_t ) + 2U ];
    uint8_t xLocalReceivedBuffer[ 200 ];
    uint8_t pucCallBack[ sizeof( DNSCallback_t ) + 15 /* length of string. */ ];


    /* Set the ethernet buffer. */
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    RNGtoReturn = 0x1234;
    RNGstatus = pdTRUE;
    xApplicationGetRandomNumber_Stub( xApplicationGetRandomNumber_Generic );

    /* Make malloc succeed. */
    pvPortMalloc_ExpectAnyArgsAndReturn( pucCallBack );

    /* Make sure that the list is empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdTRUE );

    FreeRTOS_min_uint32_ExpectAndReturn( 1000U, uxTimeout, 1000U );
    vIPReloadDNSTimer_Expect( 1000U );

    /* Expect the timeout to be set. */
    vTaskSetTimeOutState_ExpectAnyArgs();

    /* Expect the owner and value to be set. */
    listSET_LIST_ITEM_OWNER_ExpectAnyArgs();
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();

    /* Expect the task to be suspended before a possible race scenario. */
    vTaskSuspendAll_Expect();

    /* Now expect the data to be inserted. */
    vListInsertEnd_ExpectAnyArgs();

    /* Now we can expect the task to be resumed. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* Make the call to socket succeed. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocketPtr );
    xSocketValid_ExpectAndReturn( xLocalSocketPtr, pdTRUE );
    /* Make socket bind succeed. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_SNDTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_RCVTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Make the network buffer descriptor succeed. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xLocalNetworkBuffer );

    /* Get the address configuration. Ignore the 4th argument. */
    FreeRTOS_GetAddressConfiguration_Expect( NULL, NULL, NULL, NULL );
    FreeRTOS_GetAddressConfiguration_IgnoreArg_pulDNSServerAddress();

    /* Make send succeeds. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    ucGenericPtr = xLocalReceivedBuffer;
    ulGenericLength = 200;

    /* Make sure that identifiers match. */
    DNSMessage_t * pxDNSMessageHeader = ( DNSMessage_t * ) xLocalReceivedBuffer;
    pxDNSMessageHeader->usIdentifier = RNGtoReturn;

    /* Return non zero value. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( xLocalReceivedBuffer );

    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocketPtr, 0 );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocSucceeds_NonEmptyList( void )
{
    const char * pcHostName = "someThing.com";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;
    struct xSOCKET xLocalSocket;
    Socket_t xLocalSocketPtr = &xLocalSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint8_t xLocalEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER +
                                  ipSIZE_OF_UDP_HEADER + 20 /* sizeof( DNSMessage_t ) */ +
                                  strlen( pcHostName ) + sizeof( uint16_t ) +
                                  sizeof( uint16_t ) + 2U ];
    uint8_t xLocalReceivedBuffer[ 200 ];
    uint8_t pucCallBack[ sizeof( DNSCallback_t ) + 15 /* length of string. */ ];


    /* Set the ethernet buffer. */
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    RNGtoReturn = 0x1234;
    RNGstatus = pdTRUE;
    xApplicationGetRandomNumber_Stub( xApplicationGetRandomNumber_Generic );

    /* Make malloc succeed. */
    pvPortMalloc_ExpectAnyArgsAndReturn( pucCallBack );

    /* Make sure that the list is non empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdFALSE );

    /* Expect the timeout to be set. */
    vTaskSetTimeOutState_ExpectAnyArgs();

    /* Expect the owner and value to be set. */
    listSET_LIST_ITEM_OWNER_ExpectAnyArgs();
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();

    /* Expect the task to be suspended before a possible race scenario. */
    vTaskSuspendAll_Expect();

    /* Now expect the data to be inserted. */
    vListInsertEnd_ExpectAnyArgs();

    /* Now we can expect the task to be resumed. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* Make the call to socket succeed. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocketPtr );
    xSocketValid_ExpectAndReturn( xLocalSocketPtr, pdTRUE );
    /* Make socket bind succeed. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_SNDTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_RCVTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Make the network buffer descriptor succeed. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xLocalNetworkBuffer );

    /* Get the address configuration. Ignore the 4th argument. */
    FreeRTOS_GetAddressConfiguration_Expect( NULL, NULL, NULL, NULL );
    FreeRTOS_GetAddressConfiguration_IgnoreArg_pulDNSServerAddress();

    /* Make send succeeds. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    ucGenericPtr = xLocalReceivedBuffer;
    ulGenericLength = 200;

    /* Make sure that identifiers match. */
    DNSMessage_t * pxDNSMessageHeader = ( DNSMessage_t * ) xLocalReceivedBuffer;
    pxDNSMessageHeader->usIdentifier = RNGtoReturn;

    /* Return non zero value. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( xLocalReceivedBuffer );

    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocketPtr, 0 );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocSucceeds_lessbytesreceived( void )
{
    const char * pcHostName = "someThing.com";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;
    struct xSOCKET xLocalSocket;
    Socket_t xLocalSocketPtr = &xLocalSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint8_t xLocalEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER +
                                  ipSIZE_OF_UDP_HEADER + 20 /* sizeof( DNSMessage_t ) */ +
                                  strlen( pcHostName ) + sizeof( uint16_t ) +
                                  sizeof( uint16_t ) + 2U ];
    uint8_t xLocalReceivedBuffer[ 200 ];
    uint8_t pucCallBack[ sizeof( DNSCallback_t ) + 15 /* length of string. */ ];


    /* Set the ethernet buffer. */
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    RNGtoReturn = 0x1234;
    RNGstatus = pdTRUE;
    xApplicationGetRandomNumber_Stub( xApplicationGetRandomNumber_Generic );

    /* Make malloc succeed. */
    pvPortMalloc_ExpectAnyArgsAndReturn( pucCallBack );

    /* Make sure that the list is non empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdFALSE );

    /* Expect the timeout to be set. */
    vTaskSetTimeOutState_ExpectAnyArgs();

    /* Expect the owner and value to be set. */
    listSET_LIST_ITEM_OWNER_ExpectAnyArgs();
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();

    /* Expect the task to be suspended before a possible race scenario. */
    vTaskSuspendAll_Expect();

    /* Now expect the data to be inserted. */
    vListInsertEnd_ExpectAnyArgs();

    /* Now we can expect the task to be resumed. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* Make the call to socket succeed. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocketPtr );
    xSocketValid_ExpectAndReturn( xLocalSocketPtr, pdTRUE );
    /* Make socket bind succeed. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_SNDTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_RCVTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Make the network buffer descriptor succeed. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xLocalNetworkBuffer );

    /* Get the address configuration. Ignore the 4th argument. */
    FreeRTOS_GetAddressConfiguration_Expect( NULL, NULL, NULL, NULL );
    FreeRTOS_GetAddressConfiguration_IgnoreArg_pulDNSServerAddress();

    /* Make send succeeds. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    /* Set the values to be returned by recvfrom. */
    ucGenericPtr = xLocalReceivedBuffer;
    /* Anything less than the size of a DNS packet which will fail. */
    ulGenericLength = 1;

    /* Make sure that identifiers match. */
    DNSMessage_t * pxDNSMessageHeader = ( DNSMessage_t * ) xLocalReceivedBuffer;
    pxDNSMessageHeader->usIdentifier = RNGtoReturn;

    /* Return non zero value. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( xLocalReceivedBuffer );

    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocketPtr, 0 );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_ZeroQuestions_IDsNotMatching( void )
{
    const char * pcHostName = "someThing.com";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;
    struct xSOCKET xLocalSocket;
    Socket_t xLocalSocketPtr = &xLocalSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint8_t xLocalEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER +
                                  ipSIZE_OF_UDP_HEADER + 20 /* sizeof( DNSMessage_t ) */ +
                                  strlen( pcHostName ) + sizeof( uint16_t ) +
                                  sizeof( uint16_t ) + 2U ];
    uint8_t xLocalReceivedBuffer[ 200 ];
    uint8_t pucCallBack[ sizeof( DNSCallback_t ) + 15 /* length of string. */ ];



    /* Set the ethernet buffer. */
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    RNGtoReturn = 0x1234;
    RNGstatus = pdTRUE;
    xApplicationGetRandomNumber_Stub( xApplicationGetRandomNumber_Generic );

    /* Make malloc succeed. */
    pvPortMalloc_ExpectAnyArgsAndReturn( pucCallBack );

    /* Make sure that the list is non empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdFALSE );

    /* Expect the timeout to be set. */
    vTaskSetTimeOutState_ExpectAnyArgs();

    /* Expect the owner and value to be set. */
    listSET_LIST_ITEM_OWNER_ExpectAnyArgs();
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();

    /* Expect the task to be suspended before a possible race scenario. */
    vTaskSuspendAll_Expect();

    /* Now expect the data to be inserted. */
    vListInsertEnd_ExpectAnyArgs();

    /* Now we can expect the task to be resumed. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* Make the call to socket succeed. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocketPtr );
    xSocketValid_ExpectAndReturn( xLocalSocketPtr, pdTRUE );
    /* Make socket bind succeed. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_SNDTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_RCVTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Make the network buffer descriptor succeed. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xLocalNetworkBuffer );

    /* Get the address configuration. Ignore the 4th argument. */
    FreeRTOS_GetAddressConfiguration_Expect( NULL, NULL, NULL, NULL );
    FreeRTOS_GetAddressConfiguration_IgnoreArg_pulDNSServerAddress();

    /* Make send succeeds. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    /* Set the values to be returned by recvfrom. */
    ucGenericPtr = xLocalReceivedBuffer;
    /* Anything less than the size of a DNS packet which will fail. */
    ulGenericLength = 200;

    /* Map the buffer onto the dns header. */
    DNSMessage_t * pxDNSMessageHeader = ( DNSMessage_t * ) xLocalReceivedBuffer;
    /* Make sure that identifiers match. */
    pxDNSMessageHeader->usIdentifier = RNGtoReturn + 1;
    /* Set zero questions. */
    pxDNSMessageHeader->usQuestions = 0;
    /* Also make sure that the usflags don't match. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS >> 1;

    /* Return non zero value. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( xLocalReceivedBuffer );

    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocketPtr, 0 );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_ZeroQuestions_IDsMatching_NonZeroAnswers_Success( void )
{
    const char * pcHostName = "someThing.com";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout = 1231;
    uint32_t ulIPAddr = 0x12345678;
    uint32_t ulResult;
    struct xSOCKET xLocalSocket;
    Socket_t xLocalSocketPtr = &xLocalSocket;
    NetworkBufferDescriptor_t xLocalNetworkBuffer;
    uint8_t xLocalEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER +
                                  ipSIZE_OF_UDP_HEADER + 20 /* sizeof( DNSMessage_t ) */ +
                                  strlen( pcHostName ) + sizeof( uint16_t ) +
                                  sizeof( uint16_t ) + 2U ];
    uint8_t xLocalReceivedBuffer[ 200 ];
    uint8_t pucCallBack[ sizeof( DNSCallback_t ) + 15 /* length of string. */ ];



    /* Set the ethernet buffer. */
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Clear the DNS cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );

    /* since inet address call failed, RNG should be called. */
    RNGtoReturn = 0x1234;
    RNGstatus = pdTRUE;
    xApplicationGetRandomNumber_Stub( xApplicationGetRandomNumber_Generic );

    /* Make malloc succeed. */
    pvPortMalloc_ExpectAnyArgsAndReturn( pucCallBack );

    /* Make sure that the list is non empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdFALSE );

    /* Expect the timeout to be set. */
    vTaskSetTimeOutState_ExpectAnyArgs();

    /* Expect the owner and value to be set. */
    listSET_LIST_ITEM_OWNER_ExpectAnyArgs();
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();

    /* Expect the task to be suspended before a possible race scenario. */
    vTaskSuspendAll_Expect();

    /* Now expect the data to be inserted. */
    vListInsertEnd_ExpectAnyArgs();

    /* Now we can expect the task to be resumed. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* Make the call to socket succeed. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocketPtr );
    xSocketValid_ExpectAndReturn( xLocalSocketPtr, pdTRUE );
    /* Make socket bind succeed. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_SNDTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Expect the arguments. */
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_RCVTIMEO, NULL, sizeof( TickType_t ), 0 );
    /* Ignore this option since this is local argument. */
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();

    /* Make the network buffer descriptor succeed. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xLocalNetworkBuffer );

    /* Get the address configuration. Ignore the 4th argument. */
    FreeRTOS_GetAddressConfiguration_Expect( NULL, NULL, NULL, NULL );
    FreeRTOS_GetAddressConfiguration_IgnoreArg_pulDNSServerAddress();

    /* Make send succeeds. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    /* Set the values to be returned by recvfrom. */
    ucGenericPtr = xLocalReceivedBuffer;
    /* Anything less than the size of a DNS packet which will fail. */
    ulGenericLength = 200;

    /* Map the buffer onto the dns header. */
    DNSMessage_t * pxDNSMessageHeader = ( DNSMessage_t * ) xLocalReceivedBuffer;
    /* Make sure that identifiers match. */
    pxDNSMessageHeader->usIdentifier = RNGtoReturn;
    /* Set zero questions. */
    pxDNSMessageHeader->usQuestions = 0;
    /* Also make sure that the usflags don't match. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;
    /* Have one answer. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( 1 );

    /* Start at the first byte after the header. */
    uint8_t * pucByte = &( xLocalReceivedBuffer[ sizeof( DNSMessage_t ) ] );

    /* Get the answer record. */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Say that the DNS name is offset. */
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;

    /* Add the answer record. */
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) &pucByte[ 2 ];

    /* Add the proper data length. */
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    memcpy( &pucByte[ 2 + sizeof( DNSAnswerRecord_t ) ], &ulIPAddr, sizeof( uint32_t ) );

    /* Return non zero value. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    /* Return a DNS type A host. */
    usChar2u16_ExpectAndReturn( &pucByte[ 2 ], dnsTYPE_A_HOST );

    /* Try to skip over xTaskResumeAll. */
    listGET_END_MARKER_ExpectAndReturn( &xCallbackList, NULL );
    vTaskSuspendAll_Expect();
    listGET_NEXT_ExpectAndReturn( NULL, NULL );
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    xTaskGetTickCount_ExpectAndReturn( 0 );

    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( xLocalReceivedBuffer );

    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocketPtr, 0 );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( ulIPAddr, ulResult );
}

void test_ulDNSHandlePacket_LessDataLength( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;

    /* Add a small data length. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) - 1;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_DataLengthUDPnotDNS( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 1;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_AptDataLength_EmptyPacket( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 10 ];

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 10;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 10 );

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_AptDataLength_OneValidQuery_OffsetName( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 10 ];
    uint16_t usQuestions = 2;
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 10;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 10 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );
    /* Set the DNS name as offset. */
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;

    /* Return type A host. */
    usChar2u16_ExpectAndReturn( &pucByte[ 2 ], dnsTYPE_A_HOST );
    /* Return IN class. */
    usChar2u16_ExpectAndReturn( &pucByte[ 4 ], dnsCLASS_IN );

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_SmallDataLengthToJustHoldTheName( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 2;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = 0;

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );
    /* Add length of label "freertos" */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;
    /* Set the DNS name. */
    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add length of label "com". */
    *pucByte = sizeof( DNSQueryExtention ) - 1;
    pucByte++;
    /* Set the DNS extention. */
    memcpy( pucByte, DNSQueryExtention, sizeof( DNSQueryExtention ) - 1 );
    pucByte += sizeof( DNSQueryExtention ) - 1;

    /* Add a 0 length octet */
    *pucByte = 0;
    pucByte++;

    /* Override the data length so that only the name is added. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_AptDataLength_MultipleValidQueries_OffsetName_NoLLMNR( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 2;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = 0;

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );
    /* Add length of label "freertos" */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;
    /* Set the DNS name. */
    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add length of label "com". */
    *pucByte = sizeof( DNSQueryExtention ) - 1;
    pucByte++;
    /* Set the DNS extention. */
    memcpy( pucByte, DNSQueryExtention, sizeof( DNSQueryExtention ) - 1 );
    pucByte += sizeof( DNSQueryExtention ) - 1;

    /* Add a 0 length octet */
    *pucByte = 0;
    pucByte++;

    /* Skip the Type and class fields */
    pucByte += 4;
    /* Return type A host. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );
    /* Return IN class. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );

    pucByte[ 0 ] = dnsNAME_IS_OFFSET;


    /* Return type A host. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );
    /* Return IN class. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_AptDataLength_MultipleValidQueries_MultipleBlankAnswers( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 2, usAnswers = 2;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    /* Add length of label "freertos" */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;
    /* Set the DNS name. */
    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add length of label "com". */
    *pucByte = sizeof( DNSQueryExtention ) - 1;
    pucByte++;
    /* Set the DNS extention. */
    memcpy( pucByte, DNSQueryExtention, sizeof( DNSQueryExtention ) - 1 );
    pucByte += sizeof( DNSQueryExtention ) - 1;

    /* Add a 0 length octet */
    *pucByte = 0;
    pucByte++;

    /* Skip the Type and class fields */
    pucByte += 4;
    /* Return type A host. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );
    /* Return IN class. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );

    pucByte[ 0 ] = dnsNAME_IS_OFFSET;

    /* Return type A host. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );
    /* Return IN class. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );

    /****************** Answers **********************/
    /* Nothing to do here. */

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_DataLengthOnlyHasQuestions( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 2, usAnswers = 2;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    /* Add length of label "freertos" */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;
    /* Set the DNS name. */
    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add length of label "com". */
    *pucByte = sizeof( DNSQueryExtention ) - 1;
    pucByte++;
    /* Set the DNS extention. */
    memcpy( pucByte, DNSQueryExtention, sizeof( DNSQueryExtention ) - 1 );
    pucByte += sizeof( DNSQueryExtention ) - 1;

    /* Add a 0 length octet */
    *pucByte = 0;
    pucByte++;

    /* Skip the Type and class fields */
    pucByte += 4;
    /* Return type A host. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );
    /* Return IN class. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );

    /* Add the offset to the name. */
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;
    pucByte += 2;

    /* Skip the Type and class fields */
    pucByte += 4;
    /* Return type A host. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );
    /* Return IN class. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );


    /****************** Answers **********************/
    /* Nothing to do here. */

    /* Mangle the data length to just hold the questions. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_DataLengthOnlyHasQuestionsAndAnswerFlag( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 2, usAnswers = 2;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    /* Add length of label "freertos" */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;
    /* Set the DNS name. */
    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add length of label "com". */
    *pucByte = sizeof( DNSQueryExtention ) - 1;
    pucByte++;
    /* Set the DNS extention. */
    memcpy( pucByte, DNSQueryExtention, sizeof( DNSQueryExtention ) - 1 );
    pucByte += sizeof( DNSQueryExtention ) - 1;

    /* Add a 0 length octet */
    *pucByte = 0;
    pucByte++;

    /* Skip the Type and class fields */
    pucByte += 4;
    /* Return type A host. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );
    /* Return IN class. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );

    /* Add the offset to the name. */
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;
    pucByte += 2;

    /* Skip the Type and class fields */
    pucByte += 4;
    /* Return type A host. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );
    /* Return IN class. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );


    /****************** Answers **********************/
    /* Add the offset to the name. */
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;
    pucByte++;

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_DataLengthOnlyHasZeroQuestionsAndAnswerLabel( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 0, usAnswers = 2;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_DataLengthOnlyHasZeroQuestionsAndAnswerLabel_OneExtraByte( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 0, usAnswers = 2;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = 1 + ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_DataLengthOnlyHasZeroQuestionsAndAnswer( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 0, usAnswers = 2;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    /* Add length of label "freertos" */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;
    /* Set the DNS name. */
    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add length of label "com". */
    *pucByte = sizeof( DNSQueryExtention ) - 1;
    pucByte++;
    /* Set the DNS extention. */
    memcpy( pucByte, DNSQueryExtention, sizeof( DNSQueryExtention ) - 1 );
    pucByte += sizeof( DNSQueryExtention ) - 1;

    /* Add a 0 length octet */
    *pucByte = 0;
    pucByte++;

    /* Skip the Type and class fields */
    pucByte += 4;
    /* Return type A host. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );

    /* Add the offset to the name. */
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;
    pucByte += 2;

    /* Skip the Type and class fields */
    pucByte += 4;

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}


void test_ulDNSHandlePacket_MalformedQuestions( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 2, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;
    pucByte += 2;

    /* Skip the Type and class fields */
    pucByte += 4;
    /* Return type A host. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );
    /* Return IN class. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );

    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    *pucByte = sizeof( DNSQueryExtention ) - 1;
    pucByte++;

    /****************** Answers **********************/
    /* Nothing to do here. */

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_MalformedQuestions_1( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 2, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;
    pucByte += 2;

    /* Skip the Type and class fields */
    pucByte += 4;
    /* Return type A host. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );
    /* Return IN class. */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );

    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    *pucByte = 0; /*sizeof(DNSQueryExtention) - 1; */
    pucByte++;

    /****************** Answers **********************/
    /* Nothing to do here. */

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_MalformedQuestions_2_OnlyDNSHeader( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 2, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    /* Nothing to do here. */

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_MalformedQuestions_3_JustOffset( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 2, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;
    pucByte++;

    /****************** Answers **********************/
    /* Nothing to do here. */

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_MalformedQuestions_4_MoreLengthThanAllowedValue( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];
    uint16_t usQuestions = 2, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    *pucByte = ipconfigDNS_CACHE_NAME_LENGTH + 2;
    pucByte++;

    memset( pucByte, 0x11, ipconfigDNS_CACHE_NAME_LENGTH + 2 );
    pucByte += ipconfigDNS_CACHE_NAME_LENGTH + 2;

    *pucByte = sizeof( DNSQueryExtention ) - 1;
    pucByte++;

    /****************** Answers **********************/
    /* Nothing to do here. */

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_MalformedQuestions_5_BigLengthWithoutName( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];
    uint16_t usQuestions = 2, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    *pucByte = ipconfigDNS_CACHE_NAME_LENGTH + 2;
    pucByte++;

    *pucByte = sizeof( DNSQueryExtention ) - 1;
    pucByte++;

    /****************** Answers **********************/
    /* Nothing to do here. */

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}



void test_ulDNSHandlePacket_MalformedQuestions_6_BigLengthWithoutName( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];
    uint16_t usQuestions = 2, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    *pucByte = 0; /*sizeof(DNSQueryExtention) - 1; */
    pucByte++;

    /****************** Answers **********************/
    /* Nothing to do here. */

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer - 2;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_Answers_JustName( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];
    uint16_t usQuestions = 0, usAnswers = 2;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    *pucByte = 0;
    pucByte++;

    /* Mangle the data length to just hold the questions and the flag. */
    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

#define SETUP_FOR_PARSE_DNS_REPLY_CALL                                                                               \
    const char * pcHostName = "someThing.com";                                                                       \
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;                                                           \
    void * pvSearchID;                                                                                               \
    TickType_t uxTimeout = 1231;                                                                                     \
    uint32_t ulIPAddr = 0x12345678;                                                                                  \
    uint32_t ulResult;                                                                                               \
    struct xSOCKET xLocalSocket;                                                                                     \
    Socket_t xLocalSocketPtr = &xLocalSocket;                                                                        \
    NetworkBufferDescriptor_t xLocalNetworkBuffer;                                                                   \
    uint8_t xLocalEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER +                                     \
                                  ipSIZE_OF_UDP_HEADER + 20 /* sizeof( DNSMessage_t ) */ +                           \
                                  strlen( pcHostName ) + sizeof( uint16_t ) +                                        \
                                  sizeof( uint16_t ) + 2U ];                                                         \
                                                                                                                     \
    /* Set the ethernet buffer. */                                                                                   \
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;                                                    \
                                                                                                                     \
    /* Ex[ect the function to be called once. */                                                                     \
    CallBackFunction_CallCount = 1;                                                                                  \
                                                                                                                     \
    /* Hostname is expected. */                                                                                      \
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );                                                             \
                                                                                                                     \
    /* Clear the DNS cache so that nothing matches. */                                                               \
    memset( xDNSCache, 0, sizeof( xDNSCache ) );                                                                     \
                                                                                                                     \
    /* Since the above failed, DNS lookup should be called which will note the current time. */                      \
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );                                                                  \
                                                                                                                     \
    /* since inet address call failed, RNG should be called. */                                                      \
    RNGtoReturn = 0x1234;                                                                                            \
    RNGstatus = pdTRUE;                                                                                              \
    xApplicationGetRandomNumber_Stub( xApplicationGetRandomNumber_Generic );                                         \
                                                                                                                     \
    /* Make malloc fail. */                                                                                          \
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );                                                                     \
                                                                                                                     \
    /* Make the call to socket succeed. */                                                                           \
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocketPtr ); \
    xSocketValid_ExpectAndReturn( xLocalSocketPtr, pdTRUE );                                                         \
    /* Make socket bind succeed. */                                                                                  \
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );                                                                       \
                                                                                                                     \
    /* Expect the arguments. */                                                                                      \
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_SNDTIMEO, NULL, sizeof( TickType_t ), 0 );  \
    /* Ignore this option since this is local argument. */                                                           \
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();                                                                   \
                                                                                                                     \
    /* Expect the arguments. */                                                                                      \
    FreeRTOS_setsockopt_ExpectAndReturn( xLocalSocketPtr, 0, FREERTOS_SO_RCVTIMEO, NULL, sizeof( TickType_t ), 0 );  \
    /* Ignore this option since this is local argument. */                                                           \
    FreeRTOS_setsockopt_IgnoreArg_pvOptionValue();                                                                   \
                                                                                                                     \
    /* Make the network buffer descriptor succeed. */                                                                \
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xLocalNetworkBuffer );                                 \
                                                                                                                     \
    /* Get the address configuration. Ignore the 4th argument. */                                                    \
    FreeRTOS_GetAddressConfiguration_Expect( NULL, NULL, NULL, NULL );                                               \
    FreeRTOS_GetAddressConfiguration_IgnoreArg_pulDNSServerAddress();                                                \
                                                                                                                     \
    /* Make send succeeds. */                                                                                        \
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );                                                                     \
                                                                                                                     \
    /* Clear the buffer. */                                                                                          \
    memset( xLocalReceivedBuffer, 0, sizeof( xLocalReceivedBuffer ) );                                               \
                                                                                                                     \
    /* Make sure that identifiers don't match. */                                                                    \
    pxDNSMessageHeader = ( DNSMessage_t * ) xLocalReceivedBuffer;                                                    \
                                                                                                                     \
    pxDNSMessageHeader->usIdentifier = RNGtoReturn;                                                                  \
    /* Put in expected flags. */                                                                                     \
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;                                                              \
                                                                                                                     \
    /* Add questions in proper format. */                                                                            \
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );                                                 \
                                                                                                                     \
    /* No answers. */                                                                                                \
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );                                                     \
                                                                                                                     \
    /* Get the DNS packet */                                                                                         \
    pucByte = &( xLocalReceivedBuffer[ sizeof( DNSMessage_t ) ] );                                                   \
                                                                                                                     \
    /* Return non zero value. */                                                                                     \
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

#define CLEANUP                                                      \
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( xLocalReceivedBuffer ); \
                                                                     \
    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocketPtr, 0 );


void test_FreeRTOS_gethostbyname_a_MoreAnswersThanCacheEntries( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 0, usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    CallBackFunction_CallCount = 0;

    for( int i = 0; i < usAnswers - 1; i++ )
    {
        /* Add length of label. */
        *pucByte = sizeof( DNSQueryName ) - 1;
        pucByte++;

        memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
        pucByte += sizeof( DNSQueryName ) - 1;

        *pucByte = 0;
        pucByte++;

        /* Return Type A host */
        usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST );

        /* Add in the answer record. */
        pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) pucByte;
        pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ( uint16_t ) ipSIZE_OF_IPv4_ADDRESS );
        pucByte += sizeof( DNSAnswerRecord_t );

        /* Add in the IP address. */
        ulIPAddr++;
        memcpy( pucByte, &ulIPAddr, sizeof( ulIPAddr ) );
        pucByte += sizeof( ulIPAddr );

        /* DNSDoCallback function calls. */
        listGET_END_MARKER_ExpectAndReturn( &xCallbackList, &ListItem1 );
        vTaskSuspendAll_Expect();
        listGET_NEXT_ExpectAndReturn( &ListItem1, &ListItem2 );
        listGET_LIST_ITEM_VALUE_ExpectAndReturn( &ListItem2, RNGtoReturn );
        CallBackFunction_CallCount++;
        xCallback.pCallbackFunction = CallBackFunction_CalledXTimes;
        listGET_LIST_ITEM_OWNER_ExpectAndReturn( &ListItem2, &xCallback );
        xCallback.xListItem = ListItem1;
        uxListRemove_ExpectAndReturn( &xCallback.xListItem, pdTRUE );
        vPortFree_Expect( &xCallback );
        listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdFALSE );
        xTaskResumeAll_ExpectAndReturn( pdTRUE );

        /* prvProcessDNSCache function calls. */
        xTaskGetTickCount_ExpectAndReturn( 0 );

        FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( pdFALSE );
    }

    ucGenericPtr = xLocalReceivedBuffer;
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* The last IP address should be returned. */
    TEST_ASSERT_EQUAL( ulIPAddr, ulResult );
}


void test_FreeRTOS_gethostbyname_a_MoreAnswersThanCacheEntries_EmptyListAfterOneElement( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 0, usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    CallBackFunction_CallCount = 0;

    for( int i = 0; i < usAnswers - 1; i++ )
    {
        /* Add length of label. */
        *pucByte = sizeof( DNSQueryName ) - 1;
        pucByte++;

        memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
        pucByte += sizeof( DNSQueryName ) - 1;

        *pucByte = 0;
        pucByte++;

        /* Return Type A host */
        usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST );

        /* Add in the answer record. */
        pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) pucByte;
        pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ( uint16_t ) ipSIZE_OF_IPv4_ADDRESS );
        pucByte += sizeof( DNSAnswerRecord_t );

        /* Add in the IP address. */
        ulIPAddr++;
        memcpy( pucByte, &ulIPAddr, sizeof( ulIPAddr ) );
        pucByte += sizeof( ulIPAddr );

        /* DNSDoCallback function calls. */
        listGET_END_MARKER_ExpectAndReturn( &xCallbackList, &ListItem1 );
        vTaskSuspendAll_Expect();
        listGET_NEXT_ExpectAndReturn( &ListItem1, &ListItem2 );
        listGET_LIST_ITEM_VALUE_ExpectAndReturn( &ListItem2, RNGtoReturn );
        CallBackFunction_CallCount++;
        xCallback.pCallbackFunction = CallBackFunction_CalledXTimes;
        listGET_LIST_ITEM_OWNER_ExpectAndReturn( &ListItem2, &xCallback );
        xCallback.xListItem = ListItem1;
        uxListRemove_ExpectAndReturn( &xCallback.xListItem, pdTRUE );
        vPortFree_Expect( &xCallback );
        listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdTRUE );
        vIPSetDnsTimerEnableState_Expect( pdFALSE );
        xTaskResumeAll_ExpectAndReturn( pdTRUE );

        /* prvProcessDNSCache function calls. */
        xTaskGetTickCount_ExpectAndReturn( 0 );

        FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( pdFALSE );
    }

    ucGenericPtr = xLocalReceivedBuffer;
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* The last IP address should be returned. */
    TEST_ASSERT_EQUAL( ulIPAddr, ulResult );
}

void test_FreeRTOS_gethostbyname_a_MoreAnswersThanCacheEntries_( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 0, usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    CallBackFunction_CallCount = 0;

    for( int i = 0; i < usAnswers - 1; i++ )
    {
        /* Add length of label. */
        *pucByte = sizeof( DNSQueryName ) - 1;
        pucByte++;

        memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
        pucByte += sizeof( DNSQueryName ) - 1;

        *pucByte = 0;
        pucByte++;

        /* Return Type A host */
        usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST );

        /* Add in the answer record. */
        pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) pucByte;
        pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ( uint16_t ) ipSIZE_OF_IPv4_ADDRESS );
        pucByte += sizeof( DNSAnswerRecord_t );

        /* Add in the IP address. */
        ulIPAddr++;
        memcpy( pucByte, &ulIPAddr, sizeof( ulIPAddr ) );
        pucByte += sizeof( ulIPAddr );

        /* DNSDoCallback function calls. */
        listGET_END_MARKER_ExpectAndReturn( &xCallbackList, &ListItem1 );
        vTaskSuspendAll_Expect();
        listGET_NEXT_ExpectAndReturn( &ListItem1, &ListItem2 );
        listGET_LIST_ITEM_VALUE_ExpectAndReturn( &ListItem2, RNGtoReturn + 1 );

        /* Continue looping - do not return ListItem1. */
        listGET_NEXT_ExpectAndReturn( &ListItem2, &ListItem2 );
        listGET_LIST_ITEM_VALUE_ExpectAndReturn( &ListItem2, RNGtoReturn );

        CallBackFunction_CallCount++;
        xCallback.pCallbackFunction = CallBackFunction_CalledXTimes;
        listGET_LIST_ITEM_OWNER_ExpectAndReturn( &ListItem2, &xCallback );
        xCallback.xListItem = ListItem1;
        uxListRemove_ExpectAndReturn( &xCallback.xListItem, pdTRUE );
        vPortFree_Expect( &xCallback );
        listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdTRUE );
        vIPSetDnsTimerEnableState_Expect( pdFALSE );
        xTaskResumeAll_ExpectAndReturn( pdTRUE );

        /* prvProcessDNSCache function calls. */
        xTaskGetTickCount_ExpectAndReturn( 0 );

        FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( pdFALSE );
    }

    ucGenericPtr = xLocalReceivedBuffer;
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* The last IP address should be returned. */
    TEST_ASSERT_EQUAL( ulIPAddr, ulResult );
}

void test_FreeRTOS_gethostbyname_a_UnexpectedReply_MoreAnswersThanCacheEntries( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 0, usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    /* Get unexpected answer. */
    pxDNSMessageHeader->usIdentifier = RNGtoReturn++;

    for( int i = 0; i < usAnswers - 1; i++ )
    {
        /* Add length of label. */
        *pucByte = sizeof( DNSQueryName ) - 1;
        pucByte++;

        memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
        pucByte += sizeof( DNSQueryName ) - 1;

        *pucByte = 0;
        pucByte++;

        /* Return Type A host */
        usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST );

        /* Add in the answer record. */
        pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) pucByte;
        pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ( uint16_t ) ipSIZE_OF_IPv4_ADDRESS );
        pucByte += sizeof( DNSAnswerRecord_t );

        /* Add in the IP address. */
        ulIPAddr++;
        memcpy( pucByte, &ulIPAddr, sizeof( ulIPAddr ) );
        pucByte += sizeof( ulIPAddr );

        /* DNSDoCallback function calls. */
        listGET_END_MARKER_ExpectAndReturn( &xCallbackList, &ListItem1 );
        vTaskSuspendAll_Expect();
        /* Return an empty list. */
        listGET_NEXT_ExpectAndReturn( &ListItem1, &ListItem1 );
        xTaskResumeAll_ExpectAndReturn( pdTRUE );

        FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( pdFALSE );
    }

    ucGenericPtr = xLocalReceivedBuffer;
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since the reply was unexpected, nothing should be stored. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_NotIPv4Address_MoreAnswersThanCacheEntries( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 0, usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    /* Get unexpected answer. */
    pxDNSMessageHeader->usIdentifier = RNGtoReturn++;

    for( int i = 0; i < usAnswers - 1; i++ )
    {
        /* Add length of label. */
        *pucByte = sizeof( DNSQueryName ) - 1;
        pucByte++;

        memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
        pucByte += sizeof( DNSQueryName ) - 1;

        *pucByte = 0;
        pucByte++;

        /* Return Type A host */
        usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST );

        /* Add in the answer record. */
        pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) pucByte;
        pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ( uint16_t ) ipSIZE_OF_IPv4_ADDRESS + 1 );
        pucByte += sizeof( DNSAnswerRecord_t );

        /* Add in the IP address. */
        ulIPAddr++;
        memcpy( pucByte, &ulIPAddr, sizeof( ulIPAddr ) );
        pucByte += sizeof( ulIPAddr );
    }

    ucGenericPtr = xLocalReceivedBuffer;
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since the reply was not IPv4 address, nothing should be stored. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_NotTypeARecord_LessBytesReceived( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 0, usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    /* Get unexpected answer. */
    pxDNSMessageHeader->usIdentifier = RNGtoReturn++;

    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    *pucByte = 0;
    pucByte++;

    /* Return Type A host */
    usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST + 1 );

    /* Add in the answer record. */
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) pucByte;
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ( uint16_t ) ipSIZE_OF_IPv4_ADDRESS );
    pucByte += sizeof( DNSAnswerRecord_t );

    /* Add in the IP address. */
    ulIPAddr++;
    memcpy( pucByte, &ulIPAddr, sizeof( ulIPAddr ) );
    pucByte += sizeof( ulIPAddr );


    ucGenericPtr = xLocalReceivedBuffer;
    /* Make sure that 1 less byte is received than expected. */
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer - 1;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since the reply was unexpected, nothing should be stored. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_NotTypeARecord_JustTypeReceived( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 0, usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /******************* Queries ********************/
    /* Nothing to do here. */

    /****************** Answers **********************/
    /* Get unexpected answer. */
    pxDNSMessageHeader->usIdentifier = RNGtoReturn++;

    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    *pucByte = 0;
    pucByte++;

    /* Return Type A host */
    usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST + 1 );

    /* Add in just the type from the answer record. */
    pucByte += 2;

    ucGenericPtr = xLocalReceivedBuffer;
    /* Make sure that 1 less byte is received than expected. */
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since the reply was unexpected, nothing should be stored. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_IncorrectFlags_IncorrectType( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 1, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /* Add unexpected Rx flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS << 1;

    /******************* Queries ********************/
    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add a 0 label. */
    *pucByte = 0;
    pucByte++;

    /* Return Not Type A host */
    usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST << 1 );
    /* Return not IN class. */
    usChar2u16_ExpectAndReturn( &pucByte[ 2 ], dnsCLASS_IN );

    pucByte += 4;

    /****************** Answers **********************/
    /* Nothing to do here */

    ucGenericPtr = xLocalReceivedBuffer;
    /* Make sure that 1 less byte is received than expected. */
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since the reply was unexpected, nothing should be stored. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_IncorrectFlags_IncorrectClass( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 1, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /* Add unexpected Rx flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS << 1;

    /******************* Queries ********************/
    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add a 0 label. */
    *pucByte = 0;
    pucByte++;

    /* Return Not Type A host */
    usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST );
    /* Return not IN class. */
    usChar2u16_ExpectAndReturn( &pucByte[ 2 ], dnsCLASS_IN << 1 );

    pucByte += 4;

    /****************** Answers **********************/
    /* Nothing to do here */

    ucGenericPtr = xLocalReceivedBuffer;
    /* Make sure that 1 less byte is received than expected. */
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since the reply was unexpected, nothing should be stored. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_CorrectFlagsAndClass_NotMatchingName( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 1, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /* Add unexpected Rx flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS << 1;

    /******************* Queries ********************/
    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add a 0 label. */
    *pucByte = 0;
    pucByte++;

    /* Return Not Type A host */
    usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST );
    /* Return not IN class. */
    usChar2u16_ExpectAndReturn( &pucByte[ 2 ], dnsCLASS_IN );

    pucByte += 4;

    /****************** Answers **********************/
    /* Nothing to do here */

    /* Not matching name */
    xApplicationDNSQueryHook_ExpectAndReturn( &( xLocalReceivedBuffer[ sizeof( DNSMessage_t ) + 1 ] ), pdFALSE );

    ucGenericPtr = xLocalReceivedBuffer;
    /* Make sure that 1 less byte is received than expected. */
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since the reply was unexpected, nothing should be stored. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_CorrectFlagsAndClass_MatchingName_CannotGetNetBufFromUDPPayload( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 1, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /* Add unexpected Rx flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS << 1;

    /******************* Queries ********************/
    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add a 0 label. */
    *pucByte = 0;
    pucByte++;

    /* Return Not Type A host */
    usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST );
    /* Return not IN class. */
    usChar2u16_ExpectAndReturn( &pucByte[ 2 ], dnsCLASS_IN );

    pucByte += 4;

    /****************** Answers **********************/
    /* Nothing to do here */

    /* Matching name */
    xApplicationDNSQueryHook_ExpectAndReturn( &( xLocalReceivedBuffer[ sizeof( DNSMessage_t ) + 1 ] ), pdTRUE );

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( xLocalReceivedBuffer, NULL );

    ucGenericPtr = xLocalReceivedBuffer;
    /* Make sure that 1 less byte is received than expected. */
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since the reply was unexpected, nothing should be stored. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_CorrectFlagsAndClass_MatchingName_DuplicationFails( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 1, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    /* Add unexpected Rx flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS << 1;

    /******************* Queries ********************/
    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add a 0 label. */
    *pucByte = 0;
    pucByte++;

    /* Return Not Type A host */
    usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST );
    /* Return not IN class. */
    usChar2u16_ExpectAndReturn( &pucByte[ 2 ], dnsCLASS_IN );

    pucByte += 4;

    /****************** Answers **********************/
    /* Nothing to do here */

    /* Matching name */
    xApplicationDNSQueryHook_ExpectAndReturn( &( xLocalReceivedBuffer[ sizeof( DNSMessage_t ) + 1 ] ), pdTRUE );

    /* Return the local network buffer. */
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( xLocalReceivedBuffer, &xLocalNetworkBuffer );

    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( &xLocalNetworkBuffer, 0, NULL );
    pxDuplicateNetworkBufferWithDescriptor_IgnoreArg_uxNewLength();

    ucGenericPtr = xLocalReceivedBuffer;
    /* Make sure that 1 less byte is received than expected. */
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since the reply was unexpected, nothing should be stored. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_FreeRTOS_gethostbyname_a_CorrectFlagsAndClass_MatchingName_LLMNRSuccess( void )
{
    uint8_t xLocalReceivedBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 + ipconfigDNS_CACHE_NAME_LENGTH ];

    uint16_t usQuestions = 1, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSCallback_t xCallback;

    ListItem_t ListItem1, ListItem2;

    SETUP_FOR_PARSE_DNS_REPLY_CALL;

    NetworkBufferDescriptor_t xNewBuffer, * pxNewBufferPointer;
    uint8_t ucNewEthBuffer[ sizeof( xLocalEthernetBuffer ) + sizeof( LLMNRAnswer_t ) ];
    xNewBuffer.pucEthernetBuffer = ucNewEthBuffer;
    pxNewBufferPointer = &xNewBuffer;

    /* Add unexpected Rx flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS << 1;

    /******************* Queries ********************/
    /* Add length of label. */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;

    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    /* Add a 0 label. */
    *pucByte = 0;
    pucByte++;

    /* Return Not Type A host */
    usChar2u16_ExpectAndReturn( pucByte, dnsTYPE_A_HOST );
    /* Return not IN class. */
    usChar2u16_ExpectAndReturn( &pucByte[ 2 ], dnsCLASS_IN );

    pucByte += 4;

    /****************** Answers **********************/
    /* Nothing to do here */

    /* Matching name */
    xApplicationDNSQueryHook_ExpectAndReturn( &( xLocalReceivedBuffer[ sizeof( DNSMessage_t ) + 1 ] ), pdTRUE );

    /* Return the local network buffer. */
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( xLocalReceivedBuffer, &xLocalNetworkBuffer );

    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( &xLocalNetworkBuffer, 0, pxNewBufferPointer );
    pxDuplicateNetworkBufferWithDescriptor_IgnoreArg_uxNewLength();

    /* Expect these argument except the Next data which is a variable address. Return 0 - this value doesn't matter. */
    usGenerateChecksum_ExpectAndReturn( 0U, 0, ipSIZE_OF_IPv4_HEADER, 0 );
    usGenerateChecksum_IgnoreArg_pucNextData();

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( pdTRUE );

    vReturnEthernetFrame_Expect( &xNewBuffer, pdFALSE );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNewBuffer );

    ucGenericPtr = xLocalReceivedBuffer;
    /* Make sure that 1 less byte is received than expected. */
    ulGenericLength = ( uintptr_t ) pucByte - ( uintptr_t ) xLocalReceivedBuffer;

    CLEANUP;

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );

    /* Since the reply was unexpected, nothing should be stored. */
    TEST_ASSERT_EQUAL( 0, ulResult );
}

void test_ulNBNSHandlePacket_JustUDPPacket( void )
{
    uint32_t ulResult;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ sizeof( UDPPacket_t ) ];

    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = sizeof( ucEthernetBuffer );

    UDPPacket_t * pxUDPPacket = ( UDPPacket_t * ) &( pxNetworkBuffer->pucEthernetBuffer );
    uint8_t * pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( *pxUDPPacket ) ] );

    ulResult = ulNBNSHandlePacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulNBNSHandlePacket_NotMatchingFlag( void )
{
    uint32_t ulResult;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t ) ];

    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = sizeof( ucEthernetBuffer );

    UDPPacket_t * pxUDPPacket = ( UDPPacket_t * ) &( pxNetworkBuffer->pucEthernetBuffer );
    uint8_t * pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( *pxUDPPacket ) ] );

    NBNSRequest_t * NBNSRequest = ( NBNSRequest_t * ) pucUDPPayloadBuffer;

    /* Return an erraneous flag. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usFlags ) ), 0x7800 );

    ulResult = ulNBNSHandlePacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulNBNSHandlePacket_BlankNameEnding( void )
{
    uint32_t ulResult;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t ) ];

    memset( ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = sizeof( ucEthernetBuffer );

    UDPPacket_t * pxUDPPacket = ( UDPPacket_t * ) &( pxNetworkBuffer->pucEthernetBuffer );
    uint8_t * pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( *pxUDPPacket ) ] );

    NBNSRequest_t * NBNSRequest = ( NBNSRequest_t * ) pucUDPPayloadBuffer;

    uint8_t * pucSource = &( pucUDPPayloadBuffer[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + offsetof( NBNSRequest_t, ucName ) ] );

    uint8_t Mychar = ' ';

    pucSource[ 0 ] = ( Mychar >> 4 ) + 'A';
    pucSource[ 1 ] = ( Mychar & 0x0F ) + 'A';


    /* Return a correct flag. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usFlags ) ), dnsNBNS_FLAGS_OPCODE_QUERY );
    /* Return any class and type. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usType ) ), 0x00 );
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usClass ) ), 0x01 );


    ulResult = ulNBNSHandlePacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulNBNSHandlePacket_NonEmptyEnding( void )
{
    uint32_t ulResult;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t ) ];

    memset( ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = sizeof( ucEthernetBuffer );

    UDPPacket_t * pxUDPPacket = ( UDPPacket_t * ) &( pxNetworkBuffer->pucEthernetBuffer );
    uint8_t * pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( *pxUDPPacket ) ] );

    NBNSRequest_t * NBNSRequest = ( NBNSRequest_t * ) pucUDPPayloadBuffer;

    uint8_t * pucSource = &( pucUDPPayloadBuffer[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + offsetof( NBNSRequest_t, ucName ) ] );

    uint8_t Mychar = ' ';

    /* Clear the cache. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    pucSource[ 0 ] = ( 1 >> 4 ) + 'A';
    pucSource[ 1 ] = ( 1 & 0x0F ) + 'A';

    pucSource--;
    pucSource[ 0 ] = ( 1 >> 4 ) + 'A';
    pucSource[ 1 ] = ( 1 & 0x0F ) + 'A';

    pucSource--;
    pucSource[ 0 ] = ( Mychar >> 4 ) + 'A';
    pucSource[ 1 ] = ( Mychar & 0x0F ) + 'A';

    /* Return a correct flag. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usFlags ) ), dnsNBNS_FLAGS_RESPONSE );
    /* Return any class and type. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usType ) ), 0x00 );
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usClass ) ), 0x01 );

    /* Function calls from prvProcessDNSCache. */
    xTaskGetTickCount_ExpectAndReturn( 100 );

    ulResult = ulNBNSHandlePacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulNBNSHandlePacket_BlankNameEnding_MatchingName( void )
{
    uint32_t ulResult;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t ) ];
    uint32_t ulIPAddress = 0x43218765;

    memset( ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = sizeof( ucEthernetBuffer );

    UDPPacket_t * pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    uint8_t * pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( *pxUDPPacket ) ] );

    NBNSRequest_t * NBNSRequest = ( NBNSRequest_t * ) pucUDPPayloadBuffer;

    uint8_t * pucSource = &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, ucName ) ] );

    uint8_t Mychar = ' ';

    /* Add the IP address to be tested. */
    memcpy( &( pxUDPPacket->xIPHeader.ulSourceIPAddress ), &ulIPAddress, sizeof( ulIPAddress ) );

    /* Clear the cache. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Add 'test' to the NBNS name. */
    pucSource[ 0 ] = ( 't' >> 4 ) + 'A';
    pucSource[ 1 ] = ( 't' & 0x0F ) + 'A';
    pucSource += 2;

    pucSource[ 0 ] = ( 'e' >> 4 ) + 'A';
    pucSource[ 1 ] = ( 'e' & 0x0F ) + 'A';
    pucSource += 2;

    pucSource[ 0 ] = ( 's' >> 4 ) + 'A';
    pucSource[ 1 ] = ( 's' & 0x0F ) + 'A';
    pucSource += 2;

    pucSource[ 0 ] = ( 't' >> 4 ) + 'A';
    pucSource[ 1 ] = ( 't' & 0x0F ) + 'A';
    pucSource += 2;

    /* Fill with null terminator. */
    for( int i = 0; i < 12; i++ )
    {
        pucSource[ 0 ] = ( 0 >> 4 ) + 'A';
        pucSource[ 1 ] = ( 0 & 0x0F ) + 'A';
        pucSource += 2;
    }

    /* Return a correct flag. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usFlags ) ), dnsNBNS_FLAGS_RESPONSE );
    /* Return any class and type. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usType ) ), 0x00 );
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usClass ) ), 0x01 );

    /* Function calls from prvProcessDNSCache. */
    xTaskGetTickCount_ExpectAndReturn( 100 );

    /* Make sure that the name matches. */
    memcpy( xDNSCache[ 1 ].pcName, "test", strlen( "test" ) );

    ulResult = ulNBNSHandlePacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
    TEST_ASSERT_EQUAL( ulIPAddress, xDNSCache[ 1 ].ulIPAddresses[ 0 ] );
}

void test_ulNBNSHandlePacket_BlankNameEnding_MatchingName_MaxAddressesStored( void )
{
    uint32_t ulResult;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t ) ];
    uint32_t ulIPAddress = 0x43218765;

    memset( ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->xDataLength = sizeof( ucEthernetBuffer );

    UDPPacket_t * pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    uint8_t * pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( *pxUDPPacket ) ] );

    NBNSRequest_t * NBNSRequest = ( NBNSRequest_t * ) pucUDPPayloadBuffer;

    uint8_t * pucSource = &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, ucName ) ] );

    uint8_t Mychar = ' ';

    /* Add the IP address to be tested. */
    memcpy( &( pxUDPPacket->xIPHeader.ulSourceIPAddress ), &ulIPAddress, sizeof( ulIPAddress ) );

    /* Clear the cache. */
    memset( xDNSCache, 0, sizeof( xDNSCache ) );

    /* Add 'test' to the NBNS name. */
    pucSource[ 0 ] = ( 't' >> 4 ) + 'A';
    pucSource[ 1 ] = ( 't' & 0x0F ) + 'A';
    pucSource += 2;

    pucSource[ 0 ] = ( 'e' >> 4 ) + 'A';
    pucSource[ 1 ] = ( 'e' & 0x0F ) + 'A';
    pucSource += 2;

    pucSource[ 0 ] = ( 's' >> 4 ) + 'A';
    pucSource[ 1 ] = ( 's' & 0x0F ) + 'A';
    pucSource += 2;

    pucSource[ 0 ] = ( 't' >> 4 ) + 'A';
    pucSource[ 1 ] = ( 't' & 0x0F ) + 'A';
    pucSource += 2;

    /* Fill with null terminator. */
    for( int i = 0; i < 12; i++ )
    {
        pucSource[ 0 ] = ( 0 >> 4 ) + 'A';
        pucSource[ 1 ] = ( 0 & 0x0F ) + 'A';
        pucSource += 2;
    }

    /* Return a correct flag. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usFlags ) ), dnsNBNS_FLAGS_RESPONSE );
    /* Return any class and type. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usType ) ), 0x00 );
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usClass ) ), 0x01 );

    /* Function calls from prvProcessDNSCache. */
    xTaskGetTickCount_ExpectAndReturn( 100 );

    /* Make sure that the name matches. */
    memcpy( xDNSCache[ 1 ].pcName, "test", strlen( "test" ) );
    /* Assign max number of DNS addresses. */
    xDNSCache[ 1 ].ucNumIPAddresses = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;

    ulResult = ulNBNSHandlePacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
    /* Still the value should be in 0th slot. */
    TEST_ASSERT_EQUAL( ulIPAddress, xDNSCache[ 1 ].ulIPAddresses[ 0 ] );
}

#define ulNBNSHandlePacket_SETUP                                                                          \
    uint32_t ulResult;                                                                                    \
    NetworkBufferDescriptor_t xNetworkBuffer;                                                             \
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;                                        \
    uint8_t ucEthernetBuffer[ sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t ) + sizeof( NBNSAnswer_t ) ]; \
    uint32_t ulIPAddress = 0x43218765;                                                                    \
                                                                                                          \
    memset( ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );                                            \
                                                                                                          \
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;                                                \
    pxNetworkBuffer->xDataLength = sizeof( ucEthernetBuffer );                                            \
                                                                                                          \
    UDPPacket_t * pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;                     \
    uint8_t * pucUDPPayloadBuffer = &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( *pxUDPPacket ) ] );    \
                                                                                                          \
    NBNSRequest_t * NBNSRequest = ( NBNSRequest_t * ) pucUDPPayloadBuffer;                                \
                                                                                                          \
    uint8_t * pucSource = &( pucUDPPayloadBuffer[ offsetof( NBNSRequest_t, ucName ) ] );                  \
                                                                                                          \
    uint8_t Mychar = ' ';                                                                                 \
                                                                                                          \
    /* Add the IP address to be tested. */                                                                \
    memcpy( &( pxUDPPacket->xIPHeader.ulSourceIPAddress ), &ulIPAddress, sizeof( ulIPAddress ) );         \
                                                                                                          \
    /* Clear the cache. */                                                                                \
    memset( xDNSCache, 0, sizeof( xDNSCache ) );                                                          \
                                                                                                          \
    /* Add 'test' to the NBNS name. */                                                                    \
    pucSource[ 0 ] = ( 't' >> 4 ) + 'A';                                                                  \
    pucSource[ 1 ] = ( 't' & 0x0F ) + 'A';                                                                \
    pucSource += 2;                                                                                       \
                                                                                                          \
    pucSource[ 0 ] = ( 'e' >> 4 ) + 'A';                                                                  \
    pucSource[ 1 ] = ( 'e' & 0x0F ) + 'A';                                                                \
    pucSource += 2;                                                                                       \
                                                                                                          \
    pucSource[ 0 ] = ( 's' >> 4 ) + 'A';                                                                  \
    pucSource[ 1 ] = ( 's' & 0x0F ) + 'A';                                                                \
    pucSource += 2;                                                                                       \
                                                                                                          \
    pucSource[ 0 ] = ( 't' >> 4 ) + 'A';                                                                  \
    pucSource[ 1 ] = ( 't' & 0x0F ) + 'A';                                                                \
    pucSource += 2;                                                                                       \
                                                                                                          \
    /* Fill with null terminator. */                                                                      \
    for( int i = 0; i < 12; i++ )                                                                         \
    {                                                                                                     \
        pucSource[ 0 ] = ( 0 >> 4 ) + 'A';                                                                \
        pucSource[ 1 ] = ( 0 & 0x0F ) + 'A';                                                              \
        pucSource += 2;                                                                                   \
    }



void test_ulNBNSHandlePacket_DNSQueryHookFails( void )
{
    ulNBNSHandlePacket_SETUP;

    /* Return a correct flag. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usFlags ) ), 0 );
    /* Return any class and type. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usType ) ), dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usClass ) ), 0x01 );

    /* Make sure that the xApplicationDNSQueryHook fails */
    xApplicationDNSQueryHook_ExpectAnyArgsAndReturn( pdFALSE );

    ulResult = ulNBNSHandlePacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulNBNSHandlePacket_UDP2NetworkBufferFails( void )
{
    ulNBNSHandlePacket_SETUP;

    /* Return a correct flag. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usFlags ) ), 0 );
    /* Return any class and type. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usType ) ), dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usClass ) ), 0x01 );

    /* Make sure that the xApplicationDNSQueryHook doesn't fail */
    xApplicationDNSQueryHook_ExpectAnyArgsAndReturn( pdTRUE );

    /* Make sure that we cannot get the network buffer from the UDP payload buffer. */
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pucUDPPayloadBuffer, NULL );

    ulResult = ulNBNSHandlePacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulNBNSHandlePacket_DuplicationFails( void )
{
    ulNBNSHandlePacket_SETUP;

    /* Return a correct flag. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usFlags ) ), 0 );
    /* Return any class and type. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usType ) ), dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usClass ) ), 0x01 );

    /* Make sure that the xApplicationDNSQueryHook doesn't fail */
    xApplicationDNSQueryHook_ExpectAnyArgsAndReturn( pdTRUE );

    /* Make sure that we cannot get the network buffer from the UDP payload buffer. */
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pucUDPPayloadBuffer, pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( pxNetworkBuffer, pxNetworkBuffer->xDataLength + sizeof( NBNSAnswer_t ), NULL );

    ulResult = ulNBNSHandlePacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulNBNSHandlePacket_AllSuccess( void )
{
    ulNBNSHandlePacket_SETUP;

    /* Return a correct flag. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usFlags ) ), 0 );
    /* Return any class and type. */
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usType ) ), dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAndReturn( ( uint8_t * ) ( &( NBNSRequest->usClass ) ), 0x01 );

    /* Make sure that the xApplicationDNSQueryHook doesn't fail */
    xApplicationDNSQueryHook_ExpectAnyArgsAndReturn( pdTRUE );

    /* Make sure that we cannot get the network buffer from the UDP payload buffer. */
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pucUDPPayloadBuffer, pxNetworkBuffer );
    /* Duplication succeeds. */
    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( pxNetworkBuffer, pxNetworkBuffer->xDataLength + sizeof( NBNSAnswer_t ), pxNetworkBuffer );

    /* Expect these argument except the Next data which is a variable address. Return 0 - this value doesn't matter. */
    usGenerateChecksum_ExpectAndReturn( 0U, 0, ipSIZE_OF_IPv4_HEADER, 0 );
    usGenerateChecksum_IgnoreArg_pucNextData();

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( pdTRUE );

    vReturnEthernetFrame_Expect( pxNetworkBuffer, pdFALSE );

    ulResult = ulNBNSHandlePacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_JustNameInThePacket( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 2, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    /* Add length of label "freertos" */
    *pucByte = sizeof( DNSQueryName ) - 1;
    pucByte++;
    /* Set the DNS name. */
    memcpy( pucByte, DNSQueryName, sizeof( DNSQueryName ) - 1 );
    pucByte += sizeof( DNSQueryName ) - 1;

    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    /****************** Answers **********************/
    /* Nothing to do here. */

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}

void test_ulDNSHandlePacket_NameBiggerThanCacheLine( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint32_t ulResult;
    uint8_t ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 ];
    uint16_t usQuestions = 2, usAnswers = 0;
    char DNSQueryName[] = "freertos";
    char DNSQueryExtention[] = "com";
    uint8_t * pucByte;

    /*ipconfigDNS_CACHE_NAME_LENGTH */
    DNSMessage_t * pxDNSMessageHeader;
    /* This pointer is not used to modify anything */
    DNSAnswerRecord_t * pxDNSAnswerRecord;

    /* Add a data length for UDP packet but smaller than DNS packet. */
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100;
    xNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    /* Clear the buffer. */
    memset( ucEthBuffer, 0, sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) + 100 );

    pxDNSMessageHeader = ( DNSMessage_t * ) &ucEthBuffer[ sizeof( UDPPacket_t ) ];

    /* Put in expected flags. */
    pxDNSMessageHeader->usFlags = dnsEXPECTED_RX_FLAGS;

    /* Add questions in proper format. */
    pxDNSMessageHeader->usQuestions = FreeRTOS_htons( usQuestions );

    /* No answers. */
    pxDNSMessageHeader->usAnswers = FreeRTOS_htons( usAnswers );

    /* Get the DNS packet */
    pucByte = &( ucEthBuffer[ sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) ] );

    /******************* Queries ********************/
    /* Add length of label "freertos" */
    *pucByte = ipconfigDNS_CACHE_NAME_LENGTH;
    pucByte++;
    /* Set the DNS name. */
    memset( pucByte, 'A', ipconfigDNS_CACHE_NAME_LENGTH );
    pucByte += ipconfigDNS_CACHE_NAME_LENGTH;

    xNetworkBuffer.xDataLength = ( uintptr_t ) pucByte - ( uintptr_t ) ucEthBuffer;

    /****************** Answers **********************/
    /* Nothing to do here. */

    ulResult = ulDNSHandlePacket( &xNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, ulResult );
}
