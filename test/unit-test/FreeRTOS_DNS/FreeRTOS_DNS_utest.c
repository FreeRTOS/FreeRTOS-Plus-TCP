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

#include "FreeRTOS_DNS.h"

#include "FreeRTOS_DNS_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

extern DNSCacheRow_t xDNSCache[ ipconfigDNS_CACHE_ENTRIES ];

DNSCacheRow_t xTestDNSCache[ ipconfigDNS_CACHE_ENTRIES ];

List_t xCallbackList;


static void vListInitialise_stub( List_t * const pxList, int callbackcount )
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
static void CallBackFunction_CalledXTimes( const char * pcName, void * pvsearchID, uint32_t ulIPAddress )
{
    if( --CallBackFunction_CallCount < 0 )
    {
        TEST_FAIL_MESSAGE( "Not expected to be called these many times");
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





void test_FreeRTOS_dnsclear( void )
{
    /* Fill in some data. */
    memset( xDNSCache, 0xAA, sizeof( xDNSCache ) );
    /* Fill in test cache to compare against */
    memset( xTestDNSCache, 0x00, sizeof( xTestDNSCache ) );

    FreeRTOS_dnsclear();

    TEST_ASSERT_EQUAL_MEMORY( xTestDNSCache,xDNSCache,sizeof( xTestDNSCache ) );
}
void test_FreeRTOS_dnslookup_NULLHostName(void)
{
    xTaskGetTickCount_ExpectAndReturn(100);
    catch_assert( FreeRTOS_dnslookup( NULL ) );
}

void test_FreeRTOS_dnslookup_EmptyCache(void)
{
    char * pcHostName = "Test Host";
    uint32_t ulIPAddress;

    /* For each entry in the DNS cache table. */
    for( int x = 0; x < ipconfigDNS_CACHE_ENTRIES; x++ )
    {
        /* Clear the DNS cache. */
        memset( xDNSCache[ x ].pcName, 0, ipconfigDNS_CACHE_NAME_LENGTH );
    }

    xTaskGetTickCount_ExpectAndReturn(100);
    ulIPAddress = FreeRTOS_dnslookup(pcHostName);

    TEST_ASSERT_EQUAL( 0, ulIPAddress);
}

void test_FreeRTOS_dnslookup_NoMatchingName(void)
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
        memcpy( xDNSCache[ x ].pcName, pcIncorrectname, sizeof(pcIncorrectname) );
    }

    xTaskGetTickCount_ExpectAndReturn(100);
    ulIPAddress = FreeRTOS_dnslookup(pcHostName);

    /* IP address should not be found. */
    TEST_ASSERT_EQUAL( 0, ulIPAddress);
}

void test_FreeRTOS_dnslookup_MatchingName_AgedEntry(void)
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
        memcpy( xDNSCache[ x ].pcName, pcIncorrectname, sizeof(pcIncorrectname) );

        /* Make sure that timeout occurs */
        xDNSCache[ x ].ulTimeWhenAddedInSeconds = 0;
        xDNSCache[ x ].ulTTL = 0;
    }

    /* Add an entry which will match. */
    /* Clear the DNS cache. */
    memset( xDNSCache[ EntryToCheck ].pcName, 0, ipconfigDNS_CACHE_NAME_LENGTH );
    /* Add Correct name. */
    memcpy( xDNSCache[ EntryToCheck ].pcName, pcHostName, sizeof(pcHostName) );

    /* Make sure that timeout occurs */
    xTaskGetTickCount_ExpectAndReturn(100);
    ulIPAddress = FreeRTOS_dnslookup(pcHostName);

    /* IP address should not be found. */
    TEST_ASSERT_EQUAL( 0, ulIPAddress);
    /* Aged out - the entry should be cleared. */
    TEST_ASSERT_EQUAL( 0, xDNSCache[ EntryToCheck ].pcName[0] );
}

void test_FreeRTOS_dnslookup_MatchingName_NotAgedEntry_NumIPAddressIsZero(void)
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
        memcpy( xDNSCache[ x ].pcName, pcIncorrectname, sizeof(pcIncorrectname) );

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
    memcpy( xDNSCache[ EntryToCheck ].pcName, pcHostName, sizeof(pcHostName) );

    /* Make sure that timeout doesn't occur */
    xTaskGetTickCount_ExpectAndReturn(100);
    ulIPAddress = FreeRTOS_dnslookup(pcHostName);

    /* IP address should not be found. */
    TEST_ASSERT_EQUAL( 0, ulIPAddress);
}

void test_FreeRTOS_dnslookup_MatchingName_NotAgedEntry_NumIPAddressIsNonZero(void)
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
    memcpy( xDNSCache[ EntryToCheck ].pcName, pcHostName, sizeof(pcHostName) );
    /* Add the IP address we want. */
    xDNSCache[ EntryToCheck ].ulIPAddresses[
                          xDNSCache[ EntryToCheck ].ucCurrentIPAddress %
                            xDNSCache[ EntryToCheck ].ucNumIPAddresses ] = ulTestIPAddress;

    /* Make sure that timeout doesn't occur */
    xTaskGetTickCount_ExpectAndReturn(100);
    ulIPAddress = FreeRTOS_dnslookup(pcHostName);

    /* IP address should not be found. */
    TEST_ASSERT_EQUAL( ulTestIPAddress, ulIPAddress);
}

void test_vDNSInitialise( void )
{
    vListInitialise_Expect( &xCallbackList );
    vDNSInitialise();
}

void test_vDNSCheckCallBack_EmptyCallBackList(void)
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
    vDNSCheckCallBack(NULL);
}

void test_vDNSCheckCallBack_OneEntryCallBackList_NULLSearch_NoTimeOut(void)
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
    vDNSCheckCallBack(NULL);
}

void test_vDNSCheckCallBack_OneEntryCallBackList_NULLSearch_TimeOut(void)
{
    ListItem_t xLocalList1, xLocalList2;
    DNSCallback_t xLocalCallback;

    /* Set the callback. */
    /* And expect it to be called only once. */
    CallBackFunction_CallCount = 1;
    xLocalCallback.pCallbackFunction = CallBackFunction_CalledXTimes;
    /* Put some value. */
    xLocalCallback.pvSearchID = (void* ) 2;

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
    vPortFree_Expect(&xLocalCallback);

    /* Expect a call to the resume the scheduler since the list is empty. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* The list should be empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdTRUE );

    /* Expect the DNS timer to be stopeed.  */
    vIPSetDnsTimerEnableState_Expect( pdFALSE );

    /* Call with a NULL search ID. */
    vDNSCheckCallBack(NULL);
}

void test_vDNSCheckCallBack_OneEntryCallBackList_NonNULLMatchingSearch(void)
{
    ListItem_t xLocalList1, xLocalList2;
    DNSCallback_t xLocalCallback;

    /* Set the callback. */
    /* And expect it to be called only once. */
    CallBackFunction_CallCount = 1;
    xLocalCallback.pCallbackFunction = CallBackFunction_CalledXTimes;
    /* Put some value. */
    xLocalCallback.pvSearchID = (void* ) 2;

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
    vPortFree_Expect(&xLocalCallback);

    /* Expect a call to the resume the scheduler since the list is empty. */
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    /* The list should be empty. */
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdTRUE);

    /* Expect the DNS timer to be stopeed.  */
    vIPSetDnsTimerEnableState_Expect( pdFALSE );

    /* Call with a same search ID. */
    vDNSCheckCallBack( xLocalCallback.pvSearchID );
}

void test_vDNSCheckCallBack_OneEntryCallBackList_NonNULLNotMatchingSearch(void)
{
    ListItem_t xLocalList1, xLocalList2;
    DNSCallback_t xLocalCallback;

    /* Set the callback. */
    /* And expect it to be called only once. */
    CallBackFunction_CallCount = 1;
    xLocalCallback.pCallbackFunction = CallBackFunction_CalledXTimes;
    /* Put some value. */
    xLocalCallback.pvSearchID = (void* ) 2;

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
    listLIST_IS_EMPTY_ExpectAndReturn( &xCallbackList, pdFALSE);

    /* Call with a same search ID. */
    vDNSCheckCallBack( (void * )3 );
}


void test_FreeRTOS_gethostbyname_NULL(void)
{
    const char * pcHostName = NULL;
    uint32_t ulReturn = FreeRTOS_gethostbyname(pcHostName);

    /* For NULL, we should get a 0 IP address. */
    TEST_ASSERT_EQUAL( ulReturn,0 );
}

void test_FreeRTOS_gethostbyname_RecvFromFails(void)
{
    const char * pcHostName = "TestHostName";
    uint32_t ulReturn;
    Socket_t xSocket;
    NetworkBufferDescriptor_t xNetworkBuffer;

    /* Clear the cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof(xDNSCache) );

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    /* Return any value. */
    xTaskGetTickCount_ExpectAndReturn(0);

    /* RNG succeds. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn(pdTRUE);

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
    FreeRTOS_sendto_ExpectAnyArgsAndReturn(1);

    FreeRTOS_recvfrom_ExpectAnyArgsAndReturn(0);
    }

    FreeRTOS_closesocket_ExpectAnyArgsAndReturn(0);
    ulReturn = FreeRTOS_gethostbyname(pcHostName);

    /* For NULL, we should get a 0 IP address. */
    TEST_ASSERT_EQUAL( 0,ulReturn );
}

void test_FreeRTOS_gethostbyname_inetaddrFails(void)
{
    const char * pcHostName = "TestHostName";
    uint32_t ulReturn,ulIPAddress = 0x12345678;
    Socket_t xSocket;
    NetworkBufferDescriptor_t xNetworkBuffer;

    /* Clear the cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof(xDNSCache) );

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, ulIPAddress );

    ulReturn = FreeRTOS_gethostbyname(pcHostName);

    /* For NULL, we should get a 0 IP address. */
    TEST_ASSERT_EQUAL( ulIPAddress,ulReturn);
}

void test_FreeRTOS_gethostbyname_VeryLongName(void)
{
    char pcHostName[ipconfigDNS_CACHE_NAME_LENGTH*2];
    uint32_t ulReturn;
    Socket_t xSocket;
    NetworkBufferDescriptor_t xNetworkBuffer;

    for(int i =0; i<ipconfigDNS_CACHE_NAME_LENGTH*2;i++)
    {
      pcHostName[i] = 'a';
    }
    pcHostName[ipconfigDNS_CACHE_NAME_LENGTH*2 - 1] = '\0';

    /* Clear the cache so that nothing matches. */
    memset( xDNSCache, 0, sizeof(xDNSCache) );

    ulReturn = FreeRTOS_gethostbyname(pcHostName);

    /* For NULL, we should get a 0 IP address. */
    TEST_ASSERT_EQUAL( ulReturn,0 );
}

void test_FreeRTOS_gethostbyname_a_(void)
{
    const char * pcHostName = "TestHostName";
    FOnDNSEvent pCallback = CallBackFunction_CalledXTimes;
    void * pvSearchID;
    TickType_t uxTimeout;

    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn(pdTRUE);

    FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );
}


void test_FreeRTOS_gethostbyname_cancel(void)
{
    ListItem_t xLocalList;
    listGET_END_MARKER_ExpectAndReturn( &xCallbackList, &xLocalList );

    vTaskSuspendAll_Expect();

    /* Essentially return the end therefore making the list empty. */
    listGET_NEXT_ExpectAndReturn( &xLocalList,&xLocalList );
    xTaskResumeAll_ExpectAndReturn(pdTRUE);
    listLIST_IS_EMPTY_ExpectAndReturn(&xCallbackList,pdFALSE);
    FreeRTOS_gethostbyname_cancel(NULL);
}
