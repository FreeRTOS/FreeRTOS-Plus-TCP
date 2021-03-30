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
static BaseType_t xApplicationGetRandomNumber_Generic( uint32_t * pulPointer, int callbacks )
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

void test_FreeRTOS_gethostbyname_a_inetaddrsuccess(void)
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
    
    TEST_ASSERT_EQUAL( ulIPAddr, ulResult);
}

void test_FreeRTOS_gethostbyname_a_inetaddrfails_mallocfails_socketfails(void)
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
    memset(xDNSCache, 0, sizeof(xDNSCache));
    
    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );
    
    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn(pdTRUE);
    
    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn(NULL);
    
    /* Make the call to socket fail. */
    FreeRTOS_socket_ExpectAnyArgsAndReturn(NULL);
    xSocketValid_ExpectAndReturn( NULL, pdFALSE );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );
    
    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult);
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_socketfails(void)
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
    memset(xDNSCache, 0, sizeof(xDNSCache));
    
    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );
    
    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn(pdTRUE);
    
    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn(NULL);
    
    /* Make the call to socket fail. */
    FreeRTOS_socket_ExpectAnyArgsAndReturn(NULL);
    xSocketValid_ExpectAndReturn( NULL, pdFALSE );

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );
    
    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult);
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_socketBindfails(void)
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
    memset(xDNSCache, 0, sizeof(xDNSCache));
    
    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );
    
    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn(pdTRUE);
    
    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn(NULL);
    
    /* Make the call to socket fail. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, xLocalSocket );
    xSocketValid_ExpectAndReturn( xLocalSocket, pdTRUE );
    /* Make socket bind fail. */
    FreeRTOS_bind_ExpectAnyArgsAndReturn( 100 );
    /* Expect the socket to be closed. Return any value. */
    FreeRTOS_closesocket_ExpectAndReturn(xLocalSocket, 0);

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );
    
    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult);
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_GNWFails(void)
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
    memset(xDNSCache, 0, sizeof(xDNSCache));
    
    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );
    
    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn(pdTRUE);
    
    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn(NULL);
    
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
    
    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocket,0);
    
    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );
    
    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult);
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_GNWSucceeds_sendfails(void)
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
                                  sizeof( uint16_t ) + 2U];

    /* Set the ethernet buffer. */
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;
    
    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );
    
    /* Clear the DNS cache so that nothing matches. */
    memset(xDNSCache, 0, sizeof(xDNSCache));
    
    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );
    
    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn(pdTRUE);
    
    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn(NULL);
    
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
    FreeRTOS_sendto_ExpectAnyArgsAndReturn(0);
    
    vReleaseNetworkBufferAndDescriptor_Expect(&xLocalNetworkBuffer);
    
    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocket,0);
    
    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );
    
    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult);
}

void test_FreeRTOS_gethostbyname_a_inetaddrfails_RNGfails(void)
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
    memset(xDNSCache, 0, sizeof(xDNSCache));
    
    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );
    
    /* since inet address call failed, RNG should be called. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn(pdFALSE);

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );
    
    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult);
}



void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_differentID(void)
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
                                  sizeof( uint16_t ) + 2U];
    uint8_t xLocalReceivedBuffer[200];

    /* Set the ethernet buffer. */
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;
    
    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );
    
    /* Clear the DNS cache so that nothing matches. */
    memset(xDNSCache, 0, sizeof(xDNSCache));
    
    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );
    
    /* since inet address call failed, RNG should be called. */
    RNGtoReturn = 0x1234;
    RNGstatus = pdTRUE;
    xApplicationGetRandomNumber_Stub(xApplicationGetRandomNumber_Generic);
    
    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn(NULL);
    
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
    FreeRTOS_sendto_ExpectAnyArgsAndReturn(1);
    
    ucGenericPtr = xLocalReceivedBuffer;
    ulGenericLength = 200;
    
    /* Make sure that identifiers don't match. */
    DNSMessage_t * pxDNSMessageHeader = xLocalReceivedBuffer;
    pxDNSMessageHeader->usIdentifier = RNGtoReturn + 1;
    
    /* Return non zero value. */
    FreeRTOS_recvfrom_Stub(FreeRTOS_recvfrom_Generic);
    
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( xLocalReceivedBuffer );
    
    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocketPtr,0);

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );
    
    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult);
}

void test_FreeRTOS_gethostbyname_a_HostNameWithDot_inetaddrfails_mallocfails_sameID(void)
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
                                  sizeof( uint16_t ) + 2U];
    uint8_t xLocalReceivedBuffer[200];

    /* Set the ethernet buffer. */
    xLocalNetworkBuffer.pucEthernetBuffer = xLocalEthernetBuffer;

    /* Ex[ect the function to be called once. */
    CallBackFunction_CallCount = 1;
    
    /* Hostname is expected. */
    FreeRTOS_inet_addr_ExpectAndReturn( pcHostName, 0 );
    
    /* Clear the DNS cache so that nothing matches. */
    memset(xDNSCache, 0, sizeof(xDNSCache));
    
    /* Since the above failed, DNS lookup should be called which will note the current time. */
    xTaskGetTickCount_ExpectAndReturn( uxTimeout );
    
    /* since inet address call failed, RNG should be called. */
    RNGtoReturn = 0x1234;
    RNGstatus = pdTRUE;
    xApplicationGetRandomNumber_Stub(xApplicationGetRandomNumber_Generic);
    
    /* Make malloc fail. */
    pvPortMalloc_ExpectAnyArgsAndReturn(NULL);
    
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
    FreeRTOS_sendto_ExpectAnyArgsAndReturn(1);
    
    ucGenericPtr = xLocalReceivedBuffer;
    ulGenericLength = 200;
    
    /* Make sure that identifiers match. */
    DNSMessage_t * pxDNSMessageHeader = xLocalReceivedBuffer;
    pxDNSMessageHeader->usIdentifier = RNGtoReturn;
    
    /* Return non zero value. */
    FreeRTOS_recvfrom_Stub(FreeRTOS_recvfrom_Generic);
    
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( xLocalReceivedBuffer );
    
    FreeRTOS_closesocket_ExpectAndReturn( xLocalSocketPtr,0);

    ulResult = FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, uxTimeout );
    
    /* Since everything failed, 0 should have been returned. */
    TEST_ASSERT_EQUAL( 0, ulResult);
}


