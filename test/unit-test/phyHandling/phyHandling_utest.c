/*
 * FreeRTOS+TCP
 * Copyright (C) 2026 StitchLilo626
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

#include "unity.h"
#include "mock_task.h"
#include "FreeRTOS_IP.h"
#include "phyHandling.h"

#include <string.h>

#define testPHY_ADDRESS      3
#define testOTHER_ADDRESS    17
#define testBMCR             0x00U
#define testADVERTISE        0x04U
#define testPHYCR            0x19U
#define testRESET            0x8000U
#define testINITIAL_PHYCR    0xC123U

static uint32_t ulRegisters[ 32 ][ 32 ];
static uint32_t ulReads[ 32 ][ 32 ];
static uint32_t ulWrites[ 32 ][ 32 ];

void setUp( void )
{
    memset( ulRegisters, 0, sizeof( ulRegisters ) );
    memset( ulReads, 0, sizeof( ulReads ) );
    memset( ulWrites, 0, sizeof( ulWrites ) );
    vTaskDelay_Ignore();
    vTaskSetTimeOutState_Ignore();
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
}

void tearDown( void )
{
}

static BaseType_t prvRead( BaseType_t xAddress,
                           BaseType_t xRegister,
                           uint32_t * pulValue )
{
    TEST_ASSERT_TRUE( ( xAddress >= 0 ) && ( xAddress < 32 ) );
    TEST_ASSERT_TRUE( ( xRegister >= 0 ) && ( xRegister < 32 ) );
    ulReads[ xAddress ][ xRegister ]++;

    /* Model a PHY that completes reset immediately. */
    if( xRegister == testBMCR )
    {
        ulRegisters[ xAddress ][ xRegister ] &= ~testRESET;
    }

    *pulValue = ulRegisters[ xAddress ][ xRegister ];
    return 0;
}

static BaseType_t prvWrite( BaseType_t xAddress,
                            BaseType_t xRegister,
                            uint32_t ulValue )
{
    TEST_ASSERT_TRUE( ( xAddress >= 0 ) && ( xAddress < 32 ) );
    TEST_ASSERT_TRUE( ( xRegister >= 0 ) && ( xRegister < 32 ) );
    ulWrites[ xAddress ][ xRegister ]++;
    ulRegisters[ xAddress ][ xRegister ] = ulValue;
    return 0;
}

static void prvConfigure( uint32_t ulPhyID,
                          uint8_t ucMDIX,
                          BaseType_t xHasPHYCR )
{
    EthernetPhy_t xPhy;
    PhyProperties_t xProperties = { PHY_SPEED_AUTO, 0, PHY_DUPLEX_AUTO, 0 };
    uint32_t ulExpectedPHYCR = testINITIAL_PHYCR;

    xProperties.ucMDI_X = ucMDIX;
    ulRegisters[ testPHY_ADDRESS ][ testPHYCR ] = testINITIAL_PHYCR;
    vPhyInitialise( &xPhy, prvRead, prvWrite );
    xPhy.xPortCount = 1;
    xPhy.ucPhyIndexes[ 0 ] = testPHY_ADDRESS;
    xPhy.ulPhyIDs[ 0 ] = ulPhyID;

    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhy, &xProperties ) );

    /* Reset and standard advertisement still take place. */
    TEST_ASSERT_EQUAL_UINT32( 1, ulWrites[ testPHY_ADDRESS ][ testBMCR ] );
    TEST_ASSERT_EQUAL_UINT32( 1, ulWrites[ testPHY_ADDRESS ][ testADVERTISE ] );
    TEST_ASSERT_EQUAL_HEX32( 0x01E1U, ulRegisters[ testPHY_ADDRESS ][ testADVERTISE ] );
    TEST_ASSERT_EQUAL_HEX32( 0x3100U, xPhy.ulBCRValue );

    if( xHasPHYCR != pdFALSE )
    {
        TEST_ASSERT_EQUAL_UINT32( 1, ulReads[ testPHY_ADDRESS ][ testPHYCR ] );
        TEST_ASSERT_EQUAL_UINT32( 1, ulWrites[ testPHY_ADDRESS ][ testPHYCR ] );
        ulExpectedPHYCR &= ~0xC000U;

        if( ucMDIX == PHY_MDIX_AUTO )
        {
            ulExpectedPHYCR |= 0x8000U;
        }
        else if( ucMDIX == PHY_MDIX_DIRECT )
        {
            ulExpectedPHYCR |= 0x4000U;
        }
    }
    else
    {
        TEST_ASSERT_EQUAL_UINT32( 0, ulReads[ testPHY_ADDRESS ][ testPHYCR ] );
        TEST_ASSERT_EQUAL_UINT32( 0, ulWrites[ testPHY_ADDRESS ][ testPHYCR ] );
    }

    TEST_ASSERT_EQUAL_HEX32( ulExpectedPHYCR, ulRegisters[ testPHY_ADDRESS ][ testPHYCR ] );
}

void test_xPhyConfigure_LAN8742A_AutoMDIXDoesNotAccessTDR( void )
{
    prvConfigure( PHY_ID_LAN8742A, PHY_MDIX_AUTO, pdFALSE );
}

void test_xPhyConfigure_LAN8742A_DirectMDIXDoesNotAccessTDR( void )
{
    prvConfigure( PHY_ID_LAN8742A, PHY_MDIX_DIRECT, pdFALSE );
}

void test_xPhyConfigure_LAN8742A_CrossedMDIXDoesNotAccessTDR( void )
{
    prvConfigure( PHY_ID_LAN8742A, PHY_MDIX_CROSSED, pdFALSE );
}

void test_xPhyConfigure_LAN8720DoesNotAccessPHYCR( void )
{
    prvConfigure( PHY_ID_LAN8720, PHY_MDIX_AUTO, pdFALSE );
}

void test_xPhyConfigure_DP83848IRetainsPHYCRConfiguration( void )
{
    prvConfigure( PHY_ID_DP83848I, PHY_MDIX_AUTO, pdTRUE );
}

void test_xPhyConfigure_DP83822HFRetainsPHYCRConfiguration( void )
{
    prvConfigure( PHY_ID_DP83822HF, PHY_MDIX_DIRECT, pdTRUE );
}

void test_xPhyConfigure_TM4C129XRetainsPHYCRConfiguration( void )
{
    prvConfigure( PHY_ID_TM4C129X, PHY_MDIX_CROSSED, pdTRUE );
}

void test_xPhyConfigure_MixedPHYsOnlyAccessSupportedPHYCR( void )
{
    EthernetPhy_t xPhy;
    PhyProperties_t xProperties = { PHY_SPEED_AUTO, PHY_MDIX_AUTO, PHY_DUPLEX_AUTO, 0 };

    ulRegisters[ testPHY_ADDRESS ][ testPHYCR ] = testINITIAL_PHYCR;
    ulRegisters[ testOTHER_ADDRESS ][ testPHYCR ] = testINITIAL_PHYCR;
    vPhyInitialise( &xPhy, prvRead, prvWrite );
    xPhy.xPortCount = 2;
    xPhy.ucPhyIndexes[ 0 ] = testPHY_ADDRESS;
    xPhy.ucPhyIndexes[ 1 ] = testOTHER_ADDRESS;
    xPhy.ulPhyIDs[ 0 ] = PHY_ID_LAN8742A;
    xPhy.ulPhyIDs[ 1 ] = PHY_ID_DP83848I;

    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhy, &xProperties ) );
    TEST_ASSERT_EQUAL_UINT32( 0, ulReads[ testPHY_ADDRESS ][ testPHYCR ] );
    TEST_ASSERT_EQUAL_UINT32( 0, ulWrites[ testPHY_ADDRESS ][ testPHYCR ] );
    TEST_ASSERT_EQUAL_HEX32( testINITIAL_PHYCR, ulRegisters[ testPHY_ADDRESS ][ testPHYCR ] );
    TEST_ASSERT_EQUAL_UINT32( 1, ulReads[ testOTHER_ADDRESS ][ testPHYCR ] );
    TEST_ASSERT_EQUAL_UINT32( 1, ulWrites[ testOTHER_ADDRESS ][ testPHYCR ] );
    TEST_ASSERT_EQUAL_HEX32( 0x8123U, ulRegisters[ testOTHER_ADDRESS ][ testPHYCR ] );
    TEST_ASSERT_EQUAL_HEX32( 0x01E1U, ulRegisters[ testPHY_ADDRESS ][ testADVERTISE ] );
    TEST_ASSERT_EQUAL_HEX32( 0x01E1U, ulRegisters[ testOTHER_ADDRESS ][ testADVERTISE ] );
}
