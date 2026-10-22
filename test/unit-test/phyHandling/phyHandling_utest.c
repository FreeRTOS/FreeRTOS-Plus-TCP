/*
 * FreeRTOS+TCP
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 */

#include <stdint.h>
#include <string.h>

#include "unity.h"

#include "FreeRTOS.h"
#include "task.h"
#include "FreeRTOS_IP.h"
#include "phyHandling.h"

#define testPHY_ADDRESS                 1
#define testPHY_REGISTER_COUNT          32U
#define testPHY_REG_BMCR                0x00U
#define testPHY_REG_BMSR                0x01U
#define testPHY_REG_GBCR                0x09U
#define testPHY_REG_PHYCR               0x19U
#define testPHY_REG_PHYSR               0x1AU
#define testPHY_REG_SCSIR               0x1BU
#define testPHY_BMCR_RESET              0x8000U
#define testPHY_BMSR_LINK_STATUS        0x0004U
#define testPHY_BMSR_LINK_AND_AN_DONE   0x0024U
#define testPHY_GBCR_ADVERTISE_FULL     0x0200U
#define testPHY_RTL8211_1000_FULL       0x0028U
#define testPHY_RTL8211_100_FULL        0x0018U
#define testPHY_SCSIR_OVERRIDE          0x8000U
#define testPHY_SCSIR_AUTO              0x4000U
#define testPHY_SCSIR_STATE             0x2000U

static EthernetPhy_t xPhyObject;
static uint32_t ulPhyRegisters[ testPHY_REGISTER_COUNT ];
static BaseType_t xTaskCheckForTimeOutResult;
static BaseType_t xUseFirstBmsrReadValue;
static uint32_t ulFirstBmsrReadValue;
static size_t uxBmsrReadCount;
static BaseType_t xFailReadRegister;
static BaseType_t xFailWriteRegister;
static size_t uxWriteCount[ testPHY_REGISTER_COUNT ];

void vTaskSetTimeOutState( TimeOut_t * const pxTimeOut )
{
    ( void ) pxTimeOut;
}

BaseType_t xTaskCheckForTimeOut( TimeOut_t * const pxTimeOut,
                                 TickType_t * const pxTicksToWait )
{
    ( void ) pxTimeOut;
    ( void ) pxTicksToWait;
    return xTaskCheckForTimeOutResult;
}

void vTaskDelay( const TickType_t xTicksToDelay )
{
    ( void ) xTicksToDelay;
}

static BaseType_t prvPhyRead( BaseType_t xAddress,
                              BaseType_t xRegister,
                              uint32_t * pulValue )
{
    TEST_ASSERT_EQUAL( testPHY_ADDRESS, xAddress );
    TEST_ASSERT_LESS_THAN_UINT32( testPHY_REGISTER_COUNT, ( uint32_t ) xRegister );

    if( xRegister == xFailReadRegister )
    {
        /* A failed MDIO read leaves the output untouched. */
        return -1;
    }

    if( xRegister == testPHY_REG_BMSR )
    {
        uxBmsrReadCount++;

        if( ( xUseFirstBmsrReadValue != pdFALSE ) && ( uxBmsrReadCount == 1U ) )
        {
            *pulValue = ulFirstBmsrReadValue;
            return 0;
        }
    }

    *pulValue = ulPhyRegisters[ xRegister ];
    return 0;
}

static BaseType_t prvPhyWrite( BaseType_t xAddress,
                               BaseType_t xRegister,
                               uint32_t ulValue )
{
    TEST_ASSERT_EQUAL( testPHY_ADDRESS, xAddress );
    TEST_ASSERT_LESS_THAN_UINT32( testPHY_REGISTER_COUNT, ( uint32_t ) xRegister );

    uxWriteCount[ xRegister ]++;

    if( xRegister == xFailWriteRegister )
    {
        return -1;
    }

    if( xRegister == testPHY_REG_BMCR )
    {
        ulValue &= ~testPHY_BMCR_RESET;
    }

    ulPhyRegisters[ xRegister ] = ulValue;
    return 0;
}

void setUp( void )
{
    memset( &xPhyObject, 0, sizeof( xPhyObject ) );
    memset( ulPhyRegisters, 0, sizeof( ulPhyRegisters ) );
    xTaskCheckForTimeOutResult = pdFALSE;
    xUseFirstBmsrReadValue = pdFALSE;
    ulFirstBmsrReadValue = 0U;
    uxBmsrReadCount = 0U;
    xFailReadRegister = -1;
    xFailWriteRegister = -1;
    memset( uxWriteCount, 0, sizeof( uxWriteCount ) );

    vPhyInitialise( &xPhyObject, prvPhyRead, prvPhyWrite );
    xPhyObject.xPortCount = 1;
    xPhyObject.ucPhyIndexes[ 0 ] = testPHY_ADDRESS;
    xPhyObject.ulPhyIDs[ 0 ] = PHY_ID_RTL8211;
}

void tearDown( void )
{
}

void test_vPhyInitialise_DefaultsMaximumSpeedTo100Mbps( void )
{
    TEST_ASSERT_EQUAL_UINT8( PHY_SPEED_100, xPhyObject.ucMaxSpeed );
}

void test_xPhyIsLinkUp_ReflectsLinkStatusMask( void )
{
    TEST_ASSERT_EQUAL( pdFALSE, xPhyIsLinkUp( &xPhyObject ) );

    xPhyObject.ulLinkStatusMask = 1U;

    TEST_ASSERT_EQUAL( pdTRUE, xPhyIsLinkUp( &xPhyObject ) );
}

void test_xPhyConfigure_RTL8211ClearsGigabitAdvertisementFor100MbpsInterface( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_AUTO
    };

    ulPhyRegisters[ testPHY_REG_GBCR ] = 0x1F00U;

    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhyObject, &xProperties ) );
    TEST_ASSERT_EQUAL_HEX32( 0x1C00U, ulPhyRegisters[ testPHY_REG_GBCR ] );
    TEST_ASSERT_EQUAL_HEX32( 0U, xPhyObject.ulGCRValue );
}

void test_xPhyConfigure_RTL8211Advertises1000FullDuplexForGigabitInterface( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_AUTO
    };

    ulPhyRegisters[ testPHY_REG_GBCR ] = 0x1C00U;
    vPhySetMaxSpeed( &xPhyObject, PHY_SPEED_1000 );

    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhyObject, &xProperties ) );
    TEST_ASSERT_EQUAL_HEX32( 0x1E00U, ulPhyRegisters[ testPHY_REG_GBCR ] );
    TEST_ASSERT_EQUAL_HEX32( testPHY_GBCR_ADVERTISE_FULL, xPhyObject.ulGCRValue );
}

void test_xPhyConfigure_GigabitInterfaceRejectsUnsupportedPHY( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_AUTO
    };

    xPhyObject.ulPhyIDs[ 0 ] = PHY_ID_LAN8742A;
    vPhySetMaxSpeed( &xPhyObject, PHY_SPEED_1000 );

    TEST_ASSERT_EQUAL( -1, xPhyConfigure( &xPhyObject, &xProperties ) );
}

void test_xPhyConfigure_LAN8742UsesSCSIRForAutoMDIX( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_AUTO
    };

    xPhyObject.ulPhyIDs[ 0 ] = PHY_ID_LAN8742A;
    ulPhyRegisters[ testPHY_REG_PHYCR ] = 0xC601U;
    ulPhyRegisters[ testPHY_REG_SCSIR ] = 0xE810U;

    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhyObject, &xProperties ) );
    TEST_ASSERT_EQUAL_HEX32( 0xC601U, ulPhyRegisters[ testPHY_REG_PHYCR ] );
    TEST_ASSERT_EQUAL_HEX32( testPHY_SCSIR_OVERRIDE | testPHY_SCSIR_AUTO | 0x0810U,
                             ulPhyRegisters[ testPHY_REG_SCSIR ] );
}

void test_xPhyConfigure_LAN8742ForcesDirectLinkForCrossedCable( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_CROSSED
    };

    xPhyObject.ulPhyIDs[ 0 ] = PHY_ID_LAN8742A;
    ulPhyRegisters[ testPHY_REG_SCSIR ] = 0xE810U;

    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhyObject, &xProperties ) );
    TEST_ASSERT_EQUAL_HEX32( testPHY_SCSIR_OVERRIDE | 0x0810U,
                             ulPhyRegisters[ testPHY_REG_SCSIR ] );
}

void test_xPhyConfigure_LAN8742ForcesCrossedLinkForDirectCable( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_DIRECT
    };

    xPhyObject.ulPhyIDs[ 0 ] = PHY_ID_LAN8742A;
    ulPhyRegisters[ testPHY_REG_SCSIR ] = 0xE810U;

    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhyObject, &xProperties ) );
    TEST_ASSERT_EQUAL_HEX32( testPHY_SCSIR_OVERRIDE | testPHY_SCSIR_STATE | 0x0810U,
                             ulPhyRegisters[ testPHY_REG_SCSIR ] );
}

void test_xPhyConfigure_DP83848RetainsPHYCRAutoMDIXHandling( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_AUTO
    };

    xPhyObject.ulPhyIDs[ 0 ] = PHY_ID_DP83848I;
    ulPhyRegisters[ testPHY_REG_PHYCR ] = 0xC601U;

    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhyObject, &xProperties ) );
    TEST_ASSERT_EQUAL_HEX32( 0x8601U, ulPhyRegisters[ testPHY_REG_PHYCR ] );
}

void test_xPhyStartAutoNegotiation_RTL8211Resolves1000FullDuplex( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_AUTO
    };

    vPhySetMaxSpeed( &xPhyObject, PHY_SPEED_1000 );
    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhyObject, &xProperties ) );

    ulPhyRegisters[ testPHY_REG_GBCR ] &= ~testPHY_GBCR_ADVERTISE_FULL;
    ulPhyRegisters[ testPHY_REG_BMSR ] = testPHY_BMSR_LINK_AND_AN_DONE;
    ulPhyRegisters[ testPHY_REG_PHYSR ] = testPHY_RTL8211_1000_FULL;

    TEST_ASSERT_EQUAL( 0, xPhyStartAutoNegotiation( &xPhyObject, 1U ) );
    TEST_ASSERT_BITS_HIGH( testPHY_GBCR_ADVERTISE_FULL, ulPhyRegisters[ testPHY_REG_GBCR ] );
    TEST_ASSERT_EQUAL_UINT8( PHY_SPEED_1000, xPhyObject.xPhyProperties.ucSpeed );
    TEST_ASSERT_EQUAL_UINT8( PHY_DUPLEX_FULL, xPhyObject.xPhyProperties.ucDuplex );
    TEST_ASSERT_EQUAL_HEX32( 1U, xPhyObject.ulLinkStatusMask );
}

void test_xPhyStartAutoNegotiation_RTL8211Retains100MbpsFallback( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_AUTO
    };

    vPhySetMaxSpeed( &xPhyObject, PHY_SPEED_1000 );
    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhyObject, &xProperties ) );

    ulPhyRegisters[ testPHY_REG_BMSR ] = testPHY_BMSR_LINK_AND_AN_DONE;
    ulPhyRegisters[ testPHY_REG_PHYSR ] = testPHY_RTL8211_100_FULL;

    TEST_ASSERT_EQUAL( 0, xPhyStartAutoNegotiation( &xPhyObject, 1U ) );
    TEST_ASSERT_EQUAL_UINT8( PHY_SPEED_100, xPhyObject.xPhyProperties.ucSpeed );
    TEST_ASSERT_EQUAL_UINT8( PHY_DUPLEX_FULL, xPhyObject.xPhyProperties.ucDuplex );
}

void test_xPhyStartAutoNegotiation_RTL8211Retains10MbpsFallback( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_AUTO
    };

    vPhySetMaxSpeed( &xPhyObject, PHY_SPEED_1000 );
    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhyObject, &xProperties ) );

    ulPhyRegisters[ testPHY_REG_BMSR ] = testPHY_BMSR_LINK_AND_AN_DONE;
    ulPhyRegisters[ testPHY_REG_PHYSR ] = 0U;

    TEST_ASSERT_EQUAL( 0, xPhyStartAutoNegotiation( &xPhyObject, 1U ) );
    TEST_ASSERT_EQUAL_UINT8( PHY_SPEED_10, xPhyObject.xPhyProperties.ucSpeed );
    TEST_ASSERT_EQUAL_UINT8( PHY_DUPLEX_HALF, xPhyObject.xPhyProperties.ucDuplex );
}

void test_xPhyFixedValue_Rejects1000BaseTWithoutAutoNegotiation( void )
{
    xPhyObject.xPhyPreferences.ucSpeed = PHY_SPEED_1000;
    xPhyObject.xPhyPreferences.ucDuplex = PHY_DUPLEX_FULL;

    TEST_ASSERT_EQUAL( -1, xPhyFixedValue( &xPhyObject, 1U ) );
}

void test_xPhyCheckLinkStatus_PreservesBriefLinkLossAndResolvesNewSpeed( void )
{
    xTaskCheckForTimeOutResult = pdTRUE;
    xUseFirstBmsrReadValue = pdTRUE;
    ulFirstBmsrReadValue = 0U;
    ulPhyRegisters[ testPHY_REG_BMSR ] = testPHY_BMSR_LINK_STATUS;
    xPhyObject.ulLinkStatusMask = 1U;
    xPhyObject.xPhyProperties.ucSpeed = PHY_SPEED_100;
    xPhyObject.xPhyProperties.ucDuplex = PHY_DUPLEX_FULL;

    TEST_ASSERT_EQUAL( pdTRUE, xPhyCheckLinkStatus( &xPhyObject, pdFALSE ) );
    TEST_ASSERT_EQUAL_size_t( 1U, uxBmsrReadCount );
    TEST_ASSERT_EQUAL_HEX32( 0U, xPhyObject.ulLinkStatusMask );

    /* The next poll reports recovery so the MAC can refresh its mode. */
    TEST_ASSERT_EQUAL( pdTRUE, xPhyCheckLinkStatus( &xPhyObject, pdFALSE ) );
    TEST_ASSERT_EQUAL_HEX32( 1U, xPhyObject.ulLinkStatusMask );

    ulPhyRegisters[ testPHY_REG_BMSR ] = testPHY_BMSR_LINK_AND_AN_DONE;
    ulPhyRegisters[ testPHY_REG_PHYSR ] = testPHY_RTL8211_1000_FULL;
    TEST_ASSERT_EQUAL( 0, xPhyStartAutoNegotiation( &xPhyObject, 1U ) );
    TEST_ASSERT_EQUAL_UINT8( PHY_SPEED_1000, xPhyObject.xPhyProperties.ucSpeed );
    TEST_ASSERT_EQUAL_UINT8( PHY_DUPLEX_FULL, xPhyObject.xPhyProperties.ucDuplex );
}

void test_xPhyCheckLinkStatus_ClearsLatchedLowWhenAlreadyDown( void )
{
    xTaskCheckForTimeOutResult = pdTRUE;
    xUseFirstBmsrReadValue = pdTRUE;
    ulFirstBmsrReadValue = 0U;
    ulPhyRegisters[ testPHY_REG_BMSR ] = testPHY_BMSR_LINK_STATUS;

    TEST_ASSERT_EQUAL( pdTRUE, xPhyCheckLinkStatus( &xPhyObject, pdFALSE ) );
    TEST_ASSERT_EQUAL_size_t( 2U, uxBmsrReadCount );
    TEST_ASSERT_EQUAL_HEX32( 1U, xPhyObject.ulLinkStatusMask );
}

void test_xPhyCheckLinkStatus_StableUp( void )
{
    xTaskCheckForTimeOutResult = pdTRUE;
    ulPhyRegisters[ testPHY_REG_BMSR ] = testPHY_BMSR_LINK_STATUS;
    xPhyObject.ulLinkStatusMask = 1U;

    TEST_ASSERT_EQUAL( pdFALSE, xPhyCheckLinkStatus( &xPhyObject, pdFALSE ) );
    TEST_ASSERT_EQUAL_HEX32( 1U, xPhyObject.ulLinkStatusMask );
}

void test_xPhyCheckLinkStatus_StableDown( void )
{
    xTaskCheckForTimeOutResult = pdTRUE;

    TEST_ASSERT_EQUAL( pdFALSE, xPhyCheckLinkStatus( &xPhyObject, pdFALSE ) );
    TEST_ASSERT_EQUAL_HEX32( 0U, xPhyObject.ulLinkStatusMask );
}

void test_xPhyConfigure_GigabitReadFailureDoesNotWriteOrCacheAdvertisement( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_AUTO
    };

    vPhySetMaxSpeed( &xPhyObject, PHY_SPEED_1000 );
    xFailReadRegister = testPHY_REG_GBCR;

    TEST_ASSERT_EQUAL( -1, xPhyConfigure( &xPhyObject, &xProperties ) );
    TEST_ASSERT_EQUAL_size_t( 0U, uxWriteCount[ testPHY_REG_GBCR ] );
    TEST_ASSERT_EQUAL_HEX32( 0U, xPhyObject.ulGCRValue );
}

void test_xPhyConfigure_GigabitWriteFailureDoesNotCacheAdvertisement( void )
{
    const PhyProperties_t xProperties =
    {
        .ucSpeed = PHY_SPEED_AUTO,
        .ucDuplex = PHY_DUPLEX_AUTO,
        .ucMDI_X = PHY_MDIX_AUTO
    };

    vPhySetMaxSpeed( &xPhyObject, PHY_SPEED_1000 );
    xFailWriteRegister = testPHY_REG_GBCR;

    TEST_ASSERT_EQUAL( -1, xPhyConfigure( &xPhyObject, &xProperties ) );
    TEST_ASSERT_EQUAL_size_t( 1U, uxWriteCount[ testPHY_REG_GBCR ] );
    TEST_ASSERT_EQUAL_HEX32( 0U, xPhyObject.ulGCRValue );

    xFailWriteRegister = -1;
    TEST_ASSERT_EQUAL( 0, xPhyConfigure( &xPhyObject, &xProperties ) );
    TEST_ASSERT_EQUAL_HEX32( testPHY_GBCR_ADVERTISE_FULL, xPhyObject.ulGCRValue );
}

void test_xPhyStartAutoNegotiation_GigabitReadFailureDoesNotRestart( void )
{
    xFailReadRegister = testPHY_REG_GBCR;
    xTaskCheckForTimeOutResult = pdTRUE;
    xPhyObject.ulLinkStatusMask = 1U;

    TEST_ASSERT_EQUAL( -1, xPhyStartAutoNegotiation( &xPhyObject, 1U ) );
    TEST_ASSERT_EQUAL_size_t( 0U, uxWriteCount[ testPHY_REG_GBCR ] );
    TEST_ASSERT_EQUAL_size_t( 0U, uxWriteCount[ testPHY_REG_BMCR ] );
    TEST_ASSERT_EQUAL_HEX32( 0U, xPhyObject.ulLinkStatusMask );
}

void test_xPhyStartAutoNegotiation_GigabitWriteFailureDoesNotRestart( void )
{
    xFailWriteRegister = testPHY_REG_GBCR;
    xTaskCheckForTimeOutResult = pdTRUE;
    xPhyObject.ulLinkStatusMask = 1U;

    TEST_ASSERT_EQUAL( -1, xPhyStartAutoNegotiation( &xPhyObject, 1U ) );
    TEST_ASSERT_EQUAL_size_t( 1U, uxWriteCount[ testPHY_REG_GBCR ] );
    TEST_ASSERT_EQUAL_size_t( 0U, uxWriteCount[ testPHY_REG_BMCR ] );
    TEST_ASSERT_EQUAL_HEX32( 0U, xPhyObject.ulLinkStatusMask );
}

void test_xPhyStartAutoNegotiation_StatusReadFailurePreservesModeAndCanRetry( void )
{
    xFailReadRegister = testPHY_REG_PHYSR;
    xPhyObject.ulLinkStatusMask = 1U;
    xPhyObject.xPhyProperties.ucSpeed = PHY_SPEED_1000;
    xPhyObject.xPhyProperties.ucDuplex = PHY_DUPLEX_FULL;
    ulPhyRegisters[ testPHY_REG_BMSR ] = testPHY_BMSR_LINK_AND_AN_DONE;

    TEST_ASSERT_EQUAL( -1, xPhyStartAutoNegotiation( &xPhyObject, 1U ) );
    TEST_ASSERT_EQUAL_UINT8( PHY_SPEED_1000, xPhyObject.xPhyProperties.ucSpeed );
    TEST_ASSERT_EQUAL_UINT8( PHY_DUPLEX_FULL, xPhyObject.xPhyProperties.ucDuplex );
    TEST_ASSERT_EQUAL_HEX32( 0U, xPhyObject.ulLinkStatusMask );

    xFailReadRegister = -1;
    ulPhyRegisters[ testPHY_REG_PHYSR ] = testPHY_RTL8211_100_FULL;
    TEST_ASSERT_EQUAL( 0, xPhyStartAutoNegotiation( &xPhyObject, 1U ) );
    TEST_ASSERT_EQUAL_UINT8( PHY_SPEED_100, xPhyObject.xPhyProperties.ucSpeed );
    TEST_ASSERT_EQUAL_UINT8( PHY_DUPLEX_FULL, xPhyObject.xPhyProperties.ucDuplex );
    TEST_ASSERT_EQUAL_HEX32( 1U, xPhyObject.ulLinkStatusMask );
}
