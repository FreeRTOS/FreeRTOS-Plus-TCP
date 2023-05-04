/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */


/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_task.h"
#include "mock_list.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_BitConfig.h"
#include "mock_FreeRTOS_Sockets.h"

/*#include "FreeRTOS_IP_stubs.c" */
#include "catch_assert.h"

#include "FreeRTOS_DHCPv6.h"
#include "FreeRTOS_DHCPv6_stubs.c"

/* ===========================  EXTERN VARIABLES  =========================== */

#define TEST_DHCPV6_DEBUG               ( 1 )

#define TEST_DHCPV6_IAID                ( 0x27fe8f95 )

#define TEST_DHCPV6_TRANSACTION_ID      ( 0x123456 )
static uint8_t ucTestDHCPv6TransactionID[] = { 0x12, 0x34, 0x56 };

#define TEST_DHCPV6_OPTION_CLIENT_ID    ( 0x00010001C792BC80121122334422 )
static uint8_t ucTestDHCPv6OptionClientID[] = { 0x00, 0x01, 0x00, 0x01, 0xC7, 0x92, 0xBC, 0x80, 0x12, 0x11, 0x22, 0x33, 0x44, 0x22 };

#define TEST_DHCPV6_OPTION_SERVER_ID    ( 0x28BADC54000ACD295EB6 )
static uint8_t ucTestDHCPv6OptionServerID[] = { 0x28, 0xBA, 0xDC, 0x54, 0x00, 0x0A, 0xCD, 0x29, 0x5E, 0xB6 };

const uint8_t ucDefaultMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };
const IPv6_Address_t xDefaultNetPrefix = { 0x20, 0x01, 0x04, 0x70, 0xEC, 0x54, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };

/* Default IPv6 address is set to 2001:0470:EC54::5 */
const IPv6_Address_t xDefaultIPAddress = { 0x20, 0x01, 0x04, 0x70, 0xEC, 0x54, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05 };

Socket_t xStubFreeRTOS_setsockopt_xSocket;
size_t xStubFreeRTOS_setsockopt_uxOptionLength;
int32_t xStubFreeRTOS_setsockopt_lOptionName_BitMap;
FreeRTOS_Socket_t * xStubvSocketBind_pxSocket;

/* The maximum size in single read/write operation. */
#define TEST_DHCPv6_BIT_OPERATION_MAX_SIZE              ( 64 )
/* The maximum number of bit operations in a test case. */
#define TEST_DHCPv6_BIT_OPERATION_MAX_NUM               ( 128 )
/* The maximum size of debug message of bit operations. */
#define TEST_DHCPv6_BIT_OPERATION_DEBUG_MSG_MAX_SIZE    ( 64 )

typedef enum eTestDHCPv6BitOperationType
{
    eTestDHCPv6BitOperationNone = 0,
    eTestDHCPv6BitOperationWrite8,
    eTestDHCPv6BitOperationWrite16,
    eTestDHCPv6BitOperationWrite32,
    eTestDHCPv6BitOperationWriteCustom,
    eTestDHCPv6BitOperationRead8,
    eTestDHCPv6BitOperationRead16,
    eTestDHCPv6BitOperationRead32,
    eTestDHCPv6BitOperationReadCustom,
    eTestDHCPv6BitOperationReadPeek,
    eTestDHCPv6BitOperationSetError,
} eTestDHCPv6BitOperationType_t;

typedef struct xTestDHCPv6BitOperation
{
    eTestDHCPv6BitOperationType_t eOperationType;
    uint32_t ulCustomLength;
    union operationValue
    {
        uint8_t ucVal;
        uint16_t usVal;
        uint32_t ulVal;
        uint8_t ucValCustom[ TEST_DHCPv6_BIT_OPERATION_MAX_SIZE ];
    } val;
    uint8_t ucDebugMsg[ TEST_DHCPv6_BIT_OPERATION_DEBUG_MSG_MAX_SIZE ];
} xTestDHCPv6BitOperation_t;

xTestDHCPv6BitOperation_t xTestDHCPv6BitOperation[ TEST_DHCPv6_BIT_OPERATION_MAX_NUM ];
uint32_t ulTestDHCPv6BitOperationWriteIndex;
uint32_t ulTestDHCPv6BitOperationReadIndex;

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
    InitializeUnitTest();
    memset( xTestDHCPv6BitOperation, 0, sizeof( xTestDHCPv6BitOperation ) );
    ulTestDHCPv6BitOperationWriteIndex = 0;
    ulTestDHCPv6BitOperationReadIndex = 0;
}

/*! called after each test case */
void tearDown( void )
{
}

/* ======================== Stub Callback Functions ========================= */

void prvSetCheckerAndReturn_FreeRTOS_setsockopt( Socket_t xSocket,
                                                 size_t uxOptionLength )
{
    xStubFreeRTOS_setsockopt_xSocket = xSocket;
    xStubFreeRTOS_setsockopt_uxOptionLength = uxOptionLength;
    xStubFreeRTOS_setsockopt_lOptionName_BitMap = 0;
}

BaseType_t xStubFreeRTOS_setsockopt( Socket_t xSocket,
                                     int32_t lLevel,
                                     int32_t lOptionName,
                                     const void * pvOptionValue,
                                     size_t uxOptionLength,
                                     int NumCalls )
{
    TEST_ASSERT_EQUAL( xStubFreeRTOS_setsockopt_xSocket, xSocket );
    TEST_ASSERT_EQUAL( xStubFreeRTOS_setsockopt_uxOptionLength, uxOptionLength );

    xStubFreeRTOS_setsockopt_lOptionName_BitMap |= ( 1 << lOptionName );

    return pdTRUE;
}

void prvSetCheckerAndReturn_vSocketBind( FreeRTOS_Socket_t * pxSocket )
{
    xStubvSocketBind_pxSocket = pxSocket;
}

BaseType_t xStubvSocketBind( FreeRTOS_Socket_t * pxSocket,
                             struct freertos_sockaddr * pxBindAddress,
                             size_t uxAddressLength,
                             BaseType_t xInternal,
                             int NumCalls )
{
    TEST_ASSERT_EQUAL( xStubvSocketBind_pxSocket, pxSocket );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, pxBindAddress->sin_family );
    TEST_ASSERT_EQUAL( sizeof( struct freertos_sockaddr ), pxBindAddress->sin_len );
    TEST_ASSERT_EQUAL( ipDHCPv6_CLIENT_PORT, FreeRTOS_ntohs( pxBindAddress->sin_port ) );
    TEST_ASSERT_EQUAL( pdFALSE, xInternal );

    return 0;
}

BaseType_t xStubxApplicationGetRandomNumber( uint32_t * pulNumber,
                                             int NumCalls )
{
    if( pulNumber != NULL )
    {
        *pulNumber = 0xFF000000 | TEST_DHCPV6_TRANSACTION_ID;
    }

    return pdPASS;
}

void xStubvBitConfig_write_8( BitConfig_t * pxConfig,
                              uint8_t ucValue,
                              int NumCalls )
{
    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationWrite8, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    TEST_ASSERT_EQUAL( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ucVal, ucValue );
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }
}

void xStubvBitConfig_write_16( BitConfig_t * pxConfig,
                               uint16_t usValue,
                               int NumCalls )
{
    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationWrite16, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    TEST_ASSERT_EQUAL( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.usVal, usValue );
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }
}

void xStubvBitConfig_write_32( BitConfig_t * pxConfig,
                               uint32_t ulValue,
                               int NumCalls )
{
    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationWrite32, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    TEST_ASSERT_EQUAL( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ulVal, ulValue );
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }
}

void xStubvBitConfig_write_uc( BitConfig_t * pxConfig,
                               const uint8_t * pucData,
                               size_t uxSize,
                               int NumCalls )
{
    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationWriteCustom, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    TEST_ASSERT_EQUAL_MEMORY( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ucValCustom, pucData, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ulCustomLength );
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }
}

BaseType_t xStubxBitConfig_init( BitConfig_t * pxConfig,
                                           const uint8_t * pucData,
                                           size_t uxSize,
                                           int NumCalls )
{
    BaseType_t xReturn = pdPASS;

    memset( pxConfig, 0, sizeof( BitConfig_t ) );

    pxConfig->uxSize = uxSize;
    pxConfig->uxIndex = 0;
    pxConfig->xHasError = pdFALSE;

    return xReturn;
}

uint8_t xStubucBitConfig_read_8( BitConfig_t * pxConfig,
                                 int NumCalls )
{
    uint8_t ucReturn = 0;

    pxConfig->uxIndex++;

    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationRead8, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    ucReturn = xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ucVal;
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }

    return ucReturn;
}

BaseType_t xStubxBitConfig_read_uc( BitConfig_t * pxConfig,
                                    uint8_t * pucData,
                                    size_t uxSize,
                                    int NumCalls )
{
    BaseType_t xReturn = pdTRUE;

    pxConfig->uxIndex += uxSize;

    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationReadCustom, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    memcpy( pucData, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ucValCustom, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ulCustomLength );
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }

    return xReturn;
}

uint16_t xStubusBitConfig_read_16( BitConfig_t * pxConfig,
                                   int NumCalls )
{
    uint16_t usReturn = 0;

    pxConfig->uxIndex += 2;

    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationRead16, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    usReturn = xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.usVal;
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }

    return usReturn;
}

uint32_t xStubulBitConfig_read_32( BitConfig_t * pxConfig,
                                   int NumCalls )
{
    uint32_t ulReturn = 0;

    pxConfig->uxIndex += 4;

    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationRead32, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    ulReturn = xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ulVal;
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }

    return ulReturn;
}

BaseType_t xStubpucBitConfig_peek_last_index_uc( BitConfig_t * pxConfig,
                                                 uint8_t * pucData,
                                                 size_t uxSize,
                                                 int NumCalls )
{
    BaseType_t xReturn = pdTRUE;

    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationReadPeek, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    memcpy( pucData, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ucValCustom, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ulCustomLength );
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }

    return xReturn;
}

/* ==============================  Test Cases  ============================== */

static void vAddBitOperation( eTestDHCPv6BitOperationType_t eType,
                              const void * pvVal,
                              uint32_t ulSize,
                              uint8_t * pucDebugMsg )
{
    const uint8_t * pucVal;
    const uint16_t * pusVal;
    const uint32_t * pulVal;

    TEST_ASSERT_TRUE( ulTestDHCPv6BitOperationWriteIndex < TEST_DHCPv6_BIT_OPERATION_MAX_NUM );

    xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].eOperationType = eType;
    xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].ulCustomLength = ulSize;

    switch( eType )
    {
        case eTestDHCPv6BitOperationWrite8:
        case eTestDHCPv6BitOperationRead8:
            pucVal = ( uint8_t * ) pvVal;
            xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].val.ucVal = *pucVal;
            break;

        case eTestDHCPv6BitOperationWrite16:
        case eTestDHCPv6BitOperationRead16:
            pusVal = ( uint16_t * ) pvVal;
            xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].val.usVal = *pusVal;
            break;

        case eTestDHCPv6BitOperationWrite32:
        case eTestDHCPv6BitOperationRead32:
            pulVal = ( uint32_t * ) pvVal;
            xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].val.ulVal = *pulVal;
            break;

        case eTestDHCPv6BitOperationWriteCustom:
        case eTestDHCPv6BitOperationReadCustom:
        case eTestDHCPv6BitOperationReadPeek:
            memcpy( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].val.ucValCustom, pvVal, ulSize );
            break;
    }

    TEST_ASSERT_LESS_THAN_size_t( TEST_DHCPv6_BIT_OPERATION_DEBUG_MSG_MAX_SIZE, strlen( pucDebugMsg ) );
    strcpy( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].ucDebugMsg, pucDebugMsg );

    ulTestDHCPv6BitOperationWriteIndex++;
}

/**
 * @brief prvPrepareSolicitation
 * Prepare function calls for sending DHCPv6 solicitation message.
 */
static void prvPrepareSolicitation()
{
    uint8_t ucVal;
    uint16_t usVal;
    uint32_t ulVal;

    /* Prepare transaction ID. */
    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );

    xBitConfig_init_IgnoreAndReturn( pdTRUE );
    vBitConfig_write_8_Stub( xStubvBitConfig_write_8 );
    vBitConfig_write_uc_Stub( xStubvBitConfig_write_uc );
    vBitConfig_write_16_Stub( xStubvBitConfig_write_16 );
    vBitConfig_write_32_Stub( xStubvBitConfig_write_32 );
    pucBitConfig_peek_last_index_uc_Stub( xStubpucBitConfig_peek_last_index_uc );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );
    vBitConfig_release_Ignore();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Solicit;
    vAddBitOperation( eTestDHCPv6BitOperationWrite8, &ucVal, 1, "TypeSolicit" );
    vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );

    /* Option Client ID */
    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientIDLength" );
    /* Client ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientIDHWType" );
    /* Client ID - Time Stamp */
    ulVal = ulApplicationTimeHook() - SECS_FROM_1970_TILL_2000;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionClientIDTimeStamp" );
    /* Client ID - MAC Address */
    vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, ucDefaultMACAddress, ipMAC_ADDRESS_LENGTH_BYTES, "OptionClientIDMAC" );
    /* Call peek function to compare client ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadPeek, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ), "OptionClientIDPeek" );

    /* Option Elapsed Time */
    usVal = DHCPv6_Option_Elapsed_Time;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionElapsed" );
    usVal = 2U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionElapsedLength" );
    usVal = 0U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionElapsedValue" );

    /* Option IA_PD */
    usVal = DHCPv6_Option_IA_for_Prefix_Delegation;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_PD" );
    usVal = 41U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_PDLength" );
    ulVal = TEST_DHCPV6_IAID;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PDIAID" );
    ulVal = 3600U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PDT1" );
    ulVal = 5400U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PDT2" );

    /* Option IA_Prefix */
    usVal = DHCPv6_Option_IA_Prefix;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_Prefix" );
    usVal = 25U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_PrefixLength" );
    /* Preferred Life Time */
    ulVal = 4500U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PrefixPreferLifeTime" );
    /* Valid Life Time */
    ulVal = 7200U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PrefixValidLifeTime" );
    /* Prefix length */
    ucVal = 64U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite8, &ucVal, 1, "OptionIA_PrefixPrefixLength" );
    /* Prefix */
    vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, xDefaultNetPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS, "OptionIA_PrefixAddress" );

    /* Option IA_NA */
    usVal = DHCPv6_Option_NonTemporaryAddress;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_NA" );
    usVal = 12U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_NALength" );
    ulVal = TEST_DHCPV6_IAID;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_NAIAID" );
    /* T1 */
    ulVal = 4500U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_NAT1" );
    /* T2 */
    ulVal = 7200U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_NAT2" );
}

/**
 * @brief prvPrepareAdvertise
 * Prepare buffer content as DHCPv6 advertise.
 */
static void prvPrepareAdvertise()
{
    /* We hardcoded the option sequence in advertise message.
     * 1. Client ID
     * 2. Server ID
     * 3. IA_NA
     *     - Sub-option IA Address
     *     - Sub-option IA Prefix
     *     - Sub-option Status Code
     * 4. Status Code
     * 5. Preference
     */
    uint8_t ucVal;
    uint16_t usVal;
    uint32_t ulVal;
    const uint8_t ucStatusCodeSuccess[] = "success";

    xBitConfig_init_Stub( xStubxBitConfig_init );
    pucBitConfig_peek_last_index_uc_Stub( xStubpucBitConfig_peek_last_index_uc );
    ucBitConfig_read_8_Stub( xStubucBitConfig_read_8 );
    xBitConfig_read_uc_Stub( xStubxBitConfig_read_uc );
    usBitConfig_read_16_Stub( xStubusBitConfig_read_16 );
    ulBitConfig_read_32_Stub( xStubulBitConfig_read_32 );
    vBitConfig_release_Ignore();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Advertise;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "TypeAdvertise" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );

    /* Option Client ID */
    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDLength" );
    /* Client ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDHWType" );
    /* Client ID - remain ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &ucTestDHCPv6OptionClientID[ 4 ], sizeof( ucTestDHCPv6OptionClientID ) - 4, "OptionClientIDRemain" );
    /* Call peek function to compare client ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadPeek, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ), "OptionClientIDPeek" );

    /* Option Server ID */
    usVal = DHCPv6_Option_Server_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDLength" );
    /* Server ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDHWType" );
    /* Server ID - remain ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ), "OptionServerIDRemain" );

    /* IA_NA */
    usVal = DHCPv6_Option_NonTemporaryAddress;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NA" );
    usVal = 82U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NALength" );
    ulVal = TEST_DHCPV6_IAID;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAIAID" );
    /* T1 */
    ulVal = 450U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAT1" );
    /* T2 */
    ulVal = 784U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAT2" );

    /* IA_NA sub-option IA Address */
    usVal = DHCPv6_Option_IA_Address;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAAddress" );
    usVal = 24U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAAddressLength" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS, "OptionIA_NASubIAAddressIP" );
    /* Preferred Life Time */
    ulVal = 900U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAAddressPreferLifeTime" );
    /* Valid Life Time */
    ulVal = 900U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAAddressValidLifeTime" );

    /* IA_NA sub-option IA Prefix */
    usVal = DHCPv6_Option_IA_Prefix;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAPrefix" );
    usVal = 25U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAPrefixLength" );
    /* Preferred Life Time */
    ulVal = 4500U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAPrefixPreferLifeTime" );
    /* Valid Life Time */
    ulVal = 7200U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAPrefixValidLifeTime" );
    /* Prefix length */
    ucVal = 64U;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "OptionIA_NASubIAPrefixPrefixLength" );
    /* Prefix */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, xDefaultNetPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS, "OptionIA_NASubIAPrefixPrefixAddress" );

    /* IA_NA sub-option Status Code */
    usVal = DHCPv6_Option_Status_Code;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubStatus" );
    usVal = 9U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubStatusLength" );
    usVal = 0U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubStatusValue" );
    /* Status message */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucStatusCodeSuccess, sizeof( ucStatusCodeSuccess ), "OptionIA_NASubStatusMessage" );

    /* Option Status Code */
    usVal = DHCPv6_Option_Status_Code;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatus" );
    usVal = 9U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusLength" );
    usVal = 0U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusValue" );
    /* Status message */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucStatusCodeSuccess, sizeof( ucStatusCodeSuccess ), "OptionStatusmessage" );

    /* Option Preference */
    usVal = DHCPv6_Option_Preference;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionPreference" );
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionPreferenceLength" );
    /* Put 0 as preference value */
    ucVal = 0U;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "OptionPreferenceValue" );
}

/**
 * @brief prvPrepareAdvertiseNoServerID
 * Prepare buffer content as DHCPv6 advertise without server ID.
 */
static void prvPrepareAdvertiseNoServerID()
{
    /* We hardcoded the option sequence in advertise message.
     * 1. Client ID
     * 2. IA_NA
     *     - Sub-option IA Address
     *     - Sub-option IA Prefix
     *     - Sub-option Status Code
     * 3. Status Code
     * 5. Preference
     */
    uint8_t ucVal;
    uint16_t usVal;
    uint32_t ulVal;
    const uint8_t ucStatusCodeSuccess[] = "success";

    xBitConfig_init_Stub( xStubxBitConfig_init );
    pucBitConfig_peek_last_index_uc_Stub( xStubpucBitConfig_peek_last_index_uc );
    ucBitConfig_read_8_Stub( xStubucBitConfig_read_8 );
    xBitConfig_read_uc_Stub( xStubxBitConfig_read_uc );
    usBitConfig_read_16_Stub( xStubusBitConfig_read_16 );
    ulBitConfig_read_32_Stub( xStubulBitConfig_read_32 );
    vBitConfig_release_Ignore();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Advertise;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "TypeAdvertise" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );

    /* Option Client ID */
    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDLength" );
    /* Client ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDHWType" );
    /* Client ID - remain ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &ucTestDHCPv6OptionClientID[ 4 ], sizeof( ucTestDHCPv6OptionClientID ) - 4, "OptionClientIDRemain" );
    /* Call peek function to compare client ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadPeek, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ), "OptionClientIDPeek" );

    /* IA_NA */
    usVal = DHCPv6_Option_NonTemporaryAddress;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NA" );
    usVal = 82U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NALength" );
    ulVal = TEST_DHCPV6_IAID;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAIAID" );
    /* T1 */
    ulVal = 450U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAT1" );
    /* T2 */
    ulVal = 784U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAT2" );

    /* IA_NA sub-option IA Address */
    usVal = DHCPv6_Option_IA_Address;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAAddress" );
    usVal = 24U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAAddressLength" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS, "OptionIA_NASubIAAddressIP" );
    /* Preferred Life Time */
    ulVal = 900U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAAddressPreferLifeTime" );
    /* Valid Life Time */
    ulVal = 900U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAAddressValidLifeTime" );

    /* IA_NA sub-option IA Prefix */
    usVal = DHCPv6_Option_IA_Prefix;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAPrefix" );
    usVal = 25U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAPrefixLength" );
    /* Preferred Life Time */
    ulVal = 4500U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAPrefixPreferLifeTime" );
    /* Valid Life Time */
    ulVal = 7200U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAPrefixValidLifeTime" );
    /* Prefix length */
    ucVal = 64U;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "OptionIA_NASubIAPrefixPrefixLength" );
    /* Prefix */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, xDefaultNetPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS, "OptionIA_NASubIAPrefixPrefixAddress" );

    /* IA_NA sub-option Status Code */
    usVal = DHCPv6_Option_Status_Code;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubStatus" );
    usVal = 9U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubStatusLength" );
    usVal = 0U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubStatusValue" );
    /* Status message */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucStatusCodeSuccess, sizeof( ucStatusCodeSuccess ), "OptionIA_NASubStatusMessage" );

    /* Option Status Code */
    usVal = DHCPv6_Option_Status_Code;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatus" );
    usVal = 9U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusLength" );
    usVal = 0U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusValue" );
    /* Status message */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucStatusCodeSuccess, sizeof( ucStatusCodeSuccess ), "OptionStatusmessage" );

    /* Option Preference */
    usVal = DHCPv6_Option_Preference;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionPreference" );
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionPreferenceLength" );
    /* Put 0 as preference value */
    ucVal = 0U;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "OptionPreferenceValue" );
}

/**
 * @brief prvPrepareRequest
 * Prepare function calls for sending DHCPv6 request message.
 */
static void prvPrepareRequest()
{
    uint8_t ucVal;
    uint16_t usVal;
    uint32_t ulVal;

    /* Prepare transaction ID. */
    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );
    xBitConfig_init_Stub( xStubxBitConfig_init );
    vBitConfig_write_8_Stub( xStubvBitConfig_write_8 );
    vBitConfig_write_uc_Stub( xStubvBitConfig_write_uc );
    vBitConfig_write_16_Stub( xStubvBitConfig_write_16 );
    vBitConfig_write_32_Stub( xStubvBitConfig_write_32 );
    pucBitConfig_peek_last_index_uc_Stub( xStubpucBitConfig_peek_last_index_uc );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );
    vBitConfig_release_Ignore();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Request;
    vAddBitOperation( eTestDHCPv6BitOperationWrite8, &ucVal, 1, "TypeRequest" );
    vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );

    /* Option Client ID */
    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientIDLength" );
    /* Client ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientIDHWType" );
    /* Client ID - Time Stamp */
    ulVal = ulApplicationTimeHook() - SECS_FROM_1970_TILL_2000;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionClientIDTimeStamp" );
    /* Client ID - MAC Address */
    vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, ucDefaultMACAddress, ipMAC_ADDRESS_LENGTH_BYTES, "OptionClientIDMAC" );
    /* Call peek function to compare client ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadPeek, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ), "OptionClientIDpeek" );

    /* Option Server ID */
    usVal = DHCPv6_Option_Server_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionServerID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionServerIDLength" );
    /* Server ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionServerIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionServerIDHWType" );
    /* Server ID - remain ID */
    vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ), "OptionServerIDRemain" );

    /* Option List */
    usVal = DHCPv6_Option_Option_List;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionList" );
    usVal = 4U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionListLength" );
    usVal = DHCP6_OPTION_REQUEST_DNS;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionListDNS" );
    usVal = DHCP6_OPTION_REQUEST_DOMAIN_SEARCH_LIST;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionListDomainSearchList" );

    /* Option Elapsed Time */
    usVal = DHCPv6_Option_Elapsed_Time;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionElapsed" );
    usVal = 2U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionElapsedLength" );
    usVal = 0U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionElapsedValue" );

    /* Option IA_PD */
    usVal = DHCPv6_Option_IA_for_Prefix_Delegation;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_PD" );
    usVal = 41U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_PDLength" );
    ulVal = TEST_DHCPV6_IAID;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PDIAID" );
    ulVal = 3600U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PDT1" );
    ulVal = 5400U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PDT2" );

    /* Option IA_Prefix */
    usVal = DHCPv6_Option_IA_Prefix;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_Prefix" );
    usVal = 25U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_PrefixLength" );
    /* Preferred Life Time */
    ulVal = 4500U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PrefixPreferLifeTime" );
    /* Valid Life Time */
    ulVal = 7200U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PrefixValidLifeTime" );
    /* Prefix length */
    ucVal = 64U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite8, &ucVal, 1, "OptionIA_PrefixPrefixLength" );
    /* Prefix */
    vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, xDefaultNetPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS, "OptionIA_PrefixPrefixAddress" );

    /* Option IA_NA */
    usVal = DHCPv6_Option_NonTemporaryAddress;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_NA" );
    usVal = 12U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_NALength" );
    ulVal = TEST_DHCPV6_IAID;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_NAIAID" );
    /* T1 */
    ulVal = 4500U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_NAT1" );
    /* T2 */
    ulVal = 7200U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_NAT2" );

    /* Option DNS recursive name server */
    usVal = DHCPv6_Option_DNS_recursive_name_server;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionDNSRecursiveNameServer" );
    usVal = 0U;
    vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionDNSRecursiveNameServerValue" );
}

/**
 * @brief prvPrepareReply
 * Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReply()
{
    /* We hardcoded the option sequence in reply message.
     * 1. Client ID
     * 2. Server ID
     * 3. IA_NA
     *     - Sub-option IA Address
     * 4. Status Code
     * 5. Preference
     */
    uint8_t ucVal;
    uint16_t usVal;
    uint32_t ulVal;
    const uint8_t ucStatusCodeSuccess[] = "success";

    xBitConfig_init_Stub( xStubxBitConfig_init );
    pucBitConfig_peek_last_index_uc_Stub( xStubpucBitConfig_peek_last_index_uc );
    ucBitConfig_read_8_Stub( xStubucBitConfig_read_8 );
    xBitConfig_read_uc_Stub( xStubxBitConfig_read_uc );
    usBitConfig_read_16_Stub( xStubusBitConfig_read_16 );
    ulBitConfig_read_32_Stub( xStubulBitConfig_read_32 );
    vBitConfig_release_Ignore();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Reply;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "TypeReply" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );

    /* Option Client ID */
    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDLength" );
    /* Client ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDHWType" );
    /* Client ID - remain ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &ucTestDHCPv6OptionClientID[ 4 ], sizeof( ucTestDHCPv6OptionClientID ) - 4, "OptionClientIDRemain" );
    /* Call peek function to compare client ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadPeek, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ), "OptionClientIDPeek" );

    /* Option Server ID */
    usVal = DHCPv6_Option_Server_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDLength" );
    /* Server ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDHWType" );
    /* Server ID - remain ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ), "OptionServerIDRemain" );

    /* IA_NA */
    usVal = DHCPv6_Option_NonTemporaryAddress;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NA" );
    usVal = 40U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NALength" );
    ulVal = TEST_DHCPV6_IAID;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAIAID" );
    /* T1 */
    ulVal = 450U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAT1" );
    /* T2 */
    ulVal = 784U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAT2" );

    /* IA_NA sub-option IA Address */
    usVal = DHCPv6_Option_IA_Address;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAAddress" );
    usVal = 24U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAAddressLength" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS, "OptionIA_NASubIAAddressIP" );
    /* Preferred Life Time */
    ulVal = 900U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAAddressPreferLifeTime" );
    /* Valid Life Time */
    ulVal = 900U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAAddressValidLifeTime" );

    /* Option Status Code */
    usVal = DHCPv6_Option_Status_Code;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatus" );
    usVal = 9U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusLength" );
    usVal = 0U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusValue" );
    /* Status message */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucStatusCodeSuccess, sizeof( ucStatusCodeSuccess ), "OptionStatusmessage" );

    /* Option Preference */
    usVal = DHCPv6_Option_Preference;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionPreference" );
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionPreferenceLength" );
    /* Put 0 as preference value */
    ucVal = 0U;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "OptionPreferenceValue" );
}

/**
 * @brief prvPrepareUnknownMsgType
 * Prepare buffer content with known message type.
 */
static void prvPrepareUnknownMsgType()
{
    uint8_t ucVal;
    uint16_t usVal;
    uint32_t ulVal;

    xBitConfig_init_Stub( xStubxBitConfig_init );
    ucBitConfig_read_8_Stub( xStubucBitConfig_read_8 );
    xBitConfig_read_uc_Stub( xStubxBitConfig_read_uc );
    vBitConfig_release_Ignore();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = 0xEE;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "InvalidMessageType" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );
}

/**
 * @brief prvPrepareWrongTransactionID
 * Prepare buffer content with different transaction ID.
 */
static void prvPrepareWrongTransactionID()
{
    uint8_t ucVal;
    uint16_t usVal;
    uint32_t ulVal;
    uint8_t ucTestInvalidDHCPv6TransactionID[] = { 0x65, 0x43, 0x21 };

    xBitConfig_init_Stub( xStubxBitConfig_init );
    ucBitConfig_read_8_Stub( xStubucBitConfig_read_8 );
    xBitConfig_read_uc_Stub( xStubxBitConfig_read_uc );
    vBitConfig_release_Ignore();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Advertise;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "TypeAdvertise" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestInvalidDHCPv6TransactionID, 3, "InvalidTransactionID" );
}

/**
 * @brief prvPrepareErrorTransactionID
 * Prepare buffer content with transaction ID then set the error bit.
 */
static void prvPrepareErrorTransactionID()
{
    uint8_t ucVal;
    uint16_t usVal;
    uint32_t ulVal;

    xBitConfig_init_Stub( xStubxBitConfig_init );
    ucBitConfig_read_8_Stub( xStubucBitConfig_read_8 );
    xBitConfig_read_uc_Stub( xStubxBitConfig_read_uc );
    vBitConfig_release_Ignore();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Advertise;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "TypeAdvertise" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );
    vAddBitOperation( eTestDHCPv6BitOperationSetError, 0, 0, "SetError" );
}

/**
 * @brief prvPrepareErrorOption
 * Prepare operations for reading error on option.
 */
static void prvPrepareErrorOption()
{
    uint8_t ucVal;
    uint16_t usVal;
    uint32_t ulVal;

    xBitConfig_init_Stub( xStubxBitConfig_init );
    ucBitConfig_read_8_Stub( xStubucBitConfig_read_8 );
    usBitConfig_read_16_Stub( xStubusBitConfig_read_16 );
    xBitConfig_read_uc_Stub( xStubxBitConfig_read_uc );
    vBitConfig_release_Ignore();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Advertise;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "TypeAdvertise" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );
    /* Option Client ID */
    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDLength" );
    vAddBitOperation( eTestDHCPv6BitOperationSetError, 0, 0, "SetError" );
}

/**
 * @brief test_eGetDHCPv6State_happy_path
 * Check if eGetDHCPv6State can return DHCP state correctly.
 */
void test_eGetDHCPv6State_happy_path()
{
    NetworkEndPoint_t xEndPoint;
    eDHCPState_t eState = eInitialWait, eStateMax = eNotUsingLeasedAddress;
    eDHCPState_t eReturnState;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    for( eState = eInitialWait; eState <= eNotUsingLeasedAddress; eState++ )
    {
        xEndPoint.xDHCPData.eDHCPState = eState;
        eReturnState = eGetDHCPv6State( &xEndPoint );
        TEST_ASSERT_EQUAL( eState, eReturnState );
    }
}

/**
 * @brief test_eGetDHCPv6State_null
 * Check if eGetDHCPv6State trigger assertion when input is NULL.
 */
void test_eGetDHCPv6State_null()
{
    catch_assert( eGetDHCPv6State( NULL ) );
}

/**
 * @brief test_vDHCPv6Process_null
 * Check if vDHCPv6Process trigger assertion when input is NULL.
 */
void test_vDHCPv6Process_null()
{
    catch_assert( vDHCPv6Process( pdTRUE, NULL ) );
    catch_assert( vDHCPv6Process( pdFALSE, NULL ) );
}

/**
 * @brief test_vDHCPv6Process_reset_from_init
 * Check if vDHCPv6Process can reset successfully from eInitialWait.
 */
void test_vDHCPv6Process_reset_from_init()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    xEndPoint.xDHCPData.eDHCPState = eInitialWait;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xLocalDHCPv6Socket );
    xSocketValid_ExpectAndReturn( &xLocalDHCPv6Socket, pdTRUE );
    prvSetCheckerAndReturn_FreeRTOS_setsockopt( &xLocalDHCPv6Socket, sizeof( TickType_t ) );
    FreeRTOS_setsockopt_Stub( xStubFreeRTOS_setsockopt );
    prvSetCheckerAndReturn_vSocketBind( &xLocalDHCPv6Socket );
    vSocketBind_Stub( xStubvSocketBind );
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdTRUE, &xEndPoint );

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingSendFirstDiscover. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint.xDHCPData.eDHCPState );
    /* We should set 2 socket options (FREERTOS_SO_RCVTIMEO and FREERTOS_SO_SNDTIMEO). */
    TEST_ASSERT_EQUAL( ( 1 << FREERTOS_SO_RCVTIMEO | 1 << FREERTOS_SO_SNDTIMEO ), xStubFreeRTOS_setsockopt_lOptionName_BitMap );
}

/**
 * @brief test_vDHCPv6Process_reset_from_lease
 * Check if vDHCPv6Process can reset successfully from eLeasedAddress.
 */
void test_vDHCPv6Process_reset_from_lease()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xLocalDHCPv6Socket;
    const IPv6_Address_t xIPAddress = { 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    xEndPoint.xDHCPData.eDHCPState = eLeasedAddress;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xLocalDHCPv6Socket );
    xSocketValid_ExpectAndReturn( &xLocalDHCPv6Socket, pdTRUE );
    prvSetCheckerAndReturn_FreeRTOS_setsockopt( &xLocalDHCPv6Socket, sizeof( TickType_t ) );
    FreeRTOS_setsockopt_Stub( xStubFreeRTOS_setsockopt );
    prvSetCheckerAndReturn_vSocketBind( &xLocalDHCPv6Socket );
    vSocketBind_Stub( xStubvSocketBind );
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdTRUE, &xEndPoint );

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingSendFirstDiscover. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint.xDHCPData.eDHCPState );
    /* We should set 2 socket options (FREERTOS_SO_RCVTIMEO and FREERTOS_SO_SNDTIMEO). */
    TEST_ASSERT_EQUAL( ( 1 << FREERTOS_SO_RCVTIMEO | 1 << FREERTOS_SO_SNDTIMEO ), xStubFreeRTOS_setsockopt_lOptionName_BitMap );
}

/**
 * @brief test_vDHCPv6Process_continue_solicitation_happy_path
 * Check if vDHCPv6Process can continue from eWaitingSendFirstDiscover successfully.
 */
void test_vDHCPv6Process_continue_solicitation_happy_path()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    xEndPoint.xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    /* Prepare bit message for solicitation. */
    prvPrepareSolicitation();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingOffer. */
    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL( 0, xDHCPMessage.ulTimeStamp );
    TEST_ASSERT_EQUAL( TEST_DHCPV6_TRANSACTION_ID, xEndPoint.xDHCPData.ulTransactionId );
}

/**
 * @brief test_vDHCPv6Process_continue_advertise_happy_path
 * Check if vDHCPv6Process can continue from eWaitingOffer successfully.
 */
void test_vDHCPv6Process_continue_advertise_happy_path()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareAdvertise();

    prvPrepareRequest();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* The endpoint receives the DHCPv6 Advertise message from DHCPv6 server.
     * Then change the state to eWaitingAcknowledge. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief test_vDHCPv6Process_continue_reply_happy_path
 * Check if vDHCPv6Process can continue from eWaitingAcknowledge successfully.
 */
void test_vDHCPv6Process_continue_reply_happy_path()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 102 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReply();

    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpv6DEFAULT_LEASE_TIME );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* Check if the IP address provided in reply is set to endpoint properly. */
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPAddress.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief test_vDHCPv6Process_dhcp_lease
 * The address of endpoint is leased. Endpoint sends the DHCPv6 request to ask for renew.
 */
void test_vDHCPv6Process_dhcp_lease()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eLeasedAddress;
    xEndPoint.xDHCPData.eExpectedState = eLeasedAddress;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    xDHCPv6Socket = &xLocalDHCPv6Socket;
    /* Assume that DHCPv6 had got the advertise and sent request once. */
    xEndPoint.xDHCPData.xDHCPTxTime = pdMS_TO_TICKS( 0 );
    xEndPoint.xDHCPData.xDHCPTxPeriod = pdMS_TO_TICKS( 5000 );
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    /* Because we assume DHCPv6 got advertise, so we should set the server information in DHCP message. */
    xEndPoint.pxDHCPMessage = &xDHCPMessage;
    xDHCPMessage.xServerID.uxLength = 10U; /* 14 - 4 */
    xDHCPMessage.xServerID.usDUIDType = 1U;
    xDHCPMessage.xServerID.usHardwareType = 1U;
    memcpy( xDHCPMessage.xServerID.pucID, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ) );
    
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    prvPrepareRequest();
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* The address of endpoint is leased. Endpoint sends the DHCPv6 request to ask for renew.
     * Then change the state to eWaitingAcknowledge. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief test_vDHCPv6Process_giveup_when_socket_null
 * When the socket is failed on creation, we should use default setting as IP address.
 */
void test_vDHCPv6Process_giveup_when_socket_null()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_defaults.xIPAddress.ucBytes, &xDefaultIPAddress.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint.ipv6_defaults.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_defaults.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = NULL;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* When giving up, the state is set to eNotUsingLeasedAddress. Then using default setting as IPv6 address. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xEndPoint.xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPAddress.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief test_vDHCPv6Process_wait_reply_timeout
 * Check if vDHCPv6Process send another DHCPv6 reply when timeout triggered on waiting reply.
 * Then reset the state to initial when timeout period is out of bound.
 */
void test_vDHCPv6Process_wait_reply_timeout()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    /* Assume that DHCPv6 had got the advertise and sent request once. */
    xEndPoint.xDHCPData.xDHCPTxTime = pdMS_TO_TICKS( 0 );
    xEndPoint.xDHCPData.xDHCPTxPeriod = pdMS_TO_TICKS( 5000 );
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    /* Because we assume DHCPv6 got advertise, so we should set the server information in DHCP message. */
    xEndPoint.pxDHCPMessage = &xDHCPMessage;
    xDHCPMessage.xServerID.uxLength = 10U; /* 14 - 4 */
    xDHCPMessage.xServerID.usDUIDType = 1U;
    xDHCPMessage.xServerID.usHardwareType = 1U;
    memcpy( xDHCPMessage.xServerID.pucID, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ) );

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    /* 1st timeout at 5001ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) );
    /* Update tx time to 5001ms. And the tx period is updated to 10000ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) );
    /* 2nd timeout at 5001 + 10001 ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) + pdMS_TO_TICKS( 10001 ) );
    /* Update tx time to 5001ms + 10001 ms. And the tx period is updated to 20000ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) + pdMS_TO_TICKS( 10001 ) );
    /* 3rd timeout at 5001 + 10001 + 20001 ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) + pdMS_TO_TICKS( 10001 ) + pdMS_TO_TICKS( 20001 ) );
    /* Timeout triggered. Reset the DHCPv6 to initial state */

    prvPrepareRequest();
    prvPrepareRequest();

    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    /* 1st process to trigger 1st timeout. */
    vDHCPv6Process( pdFALSE, &xEndPoint );
    /* 2nd process to trigger 2nd timeout. */
    vDHCPv6Process( pdFALSE, &xEndPoint );
    /* 3rd process to trigger final timeout. */
    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eInitialWait, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief test_vDHCPv6Process_recv_unknown_msg_type
 * Check if vDHCPv6Process can drop packets with unknown message type.
 */
void test_vDHCPv6Process_recv_unknown_msg_type()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareUnknownMsgType();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief test_vDHCPv6Process_recv_wrong_transaction_ID
 * Check if vDHCPv6Process can drop packets with wrong transaction ID.
 */
void test_vDHCPv6Process_recv_wrong_transaction_ID()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareWrongTransactionID();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief test_vDHCPv6Process_recv_read_transaction_ID_error
 * Check if vDHCPv6Process can drop packets while error occured on bit configuration.
 */
void test_vDHCPv6Process_recv_read_transaction_ID_error()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareErrorTransactionID();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief test_vDHCPv6Process_recv_read_option_error
 * Check if vDHCPv6Process can drop packets while error occured on reading option.
 */
void test_vDHCPv6Process_recv_read_option_error()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareErrorOption();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief test_vDHCPv6Process_advertise_lack_server_ID
 * Check if vDHCPv6Process can drop packets while advertise message without server ID.
 */
void test_vDHCPv6Process_advertise_lack_server_ID()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 126 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareAdvertiseNoServerID();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief test_vDHCPv6Process_advertise_bit_config_init_error
 * Check if vDHCPv6Process can drop packets while failing on initialization of bit configuration.
 */
void test_vDHCPv6Process_advertise_bit_config_init_error()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 126 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    xBitConfig_init_IgnoreAndReturn( pdFAIL );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}
