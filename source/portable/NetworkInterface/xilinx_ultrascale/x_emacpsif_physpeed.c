/*
 * Copyright (c) 2007-2008, Advanced Micro Devices, Inc.
 *               All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *    * Redistributions of source code must retain the above copyright
 *      notice, this list of conditions and the following disclaimer.
 *    * Redistributions in binary form must reproduce the above copyright
 *      notice, this list of conditions and the following disclaimer in
 *      the documentation and/or other materials provided with the
 *      distribution.
 *    * Neither the name of Advanced Micro Devices, Inc. nor the names
 *      of its contributors may be used to endorse or promote products
 *      derived from this software without specific prior written
 *      permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * Some portions copyright (c) 2010-2013 Xilinx, Inc.  All rights reserved.
 *
 * Xilinx, Inc.
 * XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS" AS A
 * COURTESY TO YOU.  BY PROVIDING THIS DESIGN, CODE, OR INFORMATION AS
 * ONE POSSIBLE   IMPLEMENTATION OF THIS FEATURE, APPLICATION OR
 * STANDARD, XILINX IS MAKING NO REPRESENTATION THAT THIS IMPLEMENTATION
 * IS FREE FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE RESPONSIBLE
 * FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE FOR YOUR IMPLEMENTATION.
 * XILINX EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH RESPECT TO
 * THE ADEQUACY OF THE IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO
 * ANY WARRANTIES OR REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE
 * FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS FOR A PARTICULAR PURPOSE.
 *
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "x_emacpsif.h"
#include "x_emac_map.h"
#include "xparameters_ps.h"
#include "xparameters.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/*/ * FreeRTOS+TCP includes. * / */
/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Routing.h"
#include "NetworkBufferManagement.h"

#define phyMIN_PHY_ADDRESS    0
#define phyMAX_PHY_ADDRESS    31

#define MINIMUM_SLEEP_TIME    ( ( TickType_t ) 1 * configTICK_RATE_HZ )


uint32_t phy_detected[ 4 ];

/* Advertisement control register. */
#define ADVERTISE_10HALF      0x0020    /* Try for 10mbps half-duplex  */
#define ADVERTISE_10FULL      0x0040    /* Try for 10mbps full-duplex  */
#define ADVERTISE_100HALF     0x0080    /* Try for 100mbps half-duplex */
#define ADVERTISE_100FULL     0x0100    /* Try for 100mbps full-duplex */

#define ADVERTISE_1000FULL    0x0200
#define ADVERTISE_1000HALF    0x0100

#define ADVERTISE_100_AND_10                 \
    ( ADVERTISE_10FULL | ADVERTISE_100FULL | \
      ADVERTISE_10HALF | ADVERTISE_100HALF )
#define ADVERTISE_100         ( ADVERTISE_100FULL | ADVERTISE_100HALF )
#define ADVERTISE_10          ( ADVERTISE_10FULL | ADVERTISE_10HALF )

#define ADVERTISE_1000        0x0300

/*#define PHY_REG_00_BMCR            0x00 // Basic mode control register */
/*#define PHY_REG_01_BMSR            0x01 // Basic mode status register */
/*#define PHY_REG_02_PHYSID1         0x02 // PHYS ID 1 */
/*#define PHY_REG_03_PHYSID2         0x03 // PHYS ID 2 */
/*#define PHY_REG_04_ADVERTISE       0x04 // Advertisement control reg */

#define IEEE_CONTROL_REG_OFFSET                0
#define IEEE_STATUS_REG_OFFSET                 1
#define IEEE_AUTONEGO_ADVERTISE_REG            4
#define IEEE_PARTNER_ABILITIES_1_REG_OFFSET    5
#define IEEE_PARTNER_ABILITIES_2_REG_OFFSET    8
#define IEEE_PARTNER_ABILITIES_3_REG_OFFSET    10
#define IEEE_1000_ADVERTISE_REG_OFFSET         9
#define IEEE_MMD_ACCESS_CONTROL_REG            13
#define IEEE_MMD_ACCESS_ADDRESS_DATA_REG       14
#define IEEE_COPPER_SPECIFIC_CONTROL_REG       16
#define IEEE_SPECIFIC_STATUS_REG               17
#define IEEE_COPPER_SPECIFIC_STATUS_REG_2      19
#define IEEE_EXT_PHY_SPECIFIC_CONTROL_REG      20
#define IEEE_CONTROL_REG_MAC                   21
#define IEEE_PAGE_ADDRESS_REGISTER             22

#define IEEE_CTRL_1GBPS_LINKSPEED_MASK         0x2040
#define IEEE_CTRL_LINKSPEED_MASK               0x0040
#define IEEE_CTRL_LINKSPEED_1000M              0x0040
#define IEEE_CTRL_LINKSPEED_100M               0x2000
#define IEEE_CTRL_LINKSPEED_10M                0x0000
#define IEEE_CTRL_FULL_DUPLEX                  0x100
#define IEEE_CTRL_RESET_MASK                   0x8000
#define IEEE_CTRL_AUTONEGOTIATE_ENABLE         0x1000
#define IEEE_STAT_AUTONEGOTIATE_CAPABLE        0x0008
#define IEEE_STAT_AUTONEGOTIATE_COMPLETE       0x0020
#define IEEE_STAT_AUTONEGOTIATE_RESTART        0x0200
#define IEEE_STAT_LINK_STATUS                  0x0004
#define IEEE_STAT_1GBPS_EXTENSIONS             0x0100
#define IEEE_AN1_ABILITY_MASK                  0x1FE0
#define IEEE_AN3_ABILITY_MASK_1GBPS            0x0C00
#define IEEE_AN1_ABILITY_MASK_100MBPS          0x0380
#define IEEE_AN1_ABILITY_MASK_10MBPS           0x0060
#define IEEE_RGMII_TXRX_CLOCK_DELAYED_MASK     0x0030

#define IEEE_SPEED_MASK                        0xC000
#define IEEE_SPEED_1000                        0x8000
#define IEEE_SPEED_100                         0x4000

#define IEEE_ASYMMETRIC_PAUSE_MASK             0x0800
#define IEEE_PAUSE_MASK                        0x0400
#define IEEE_AUTONEG_ERROR_MASK                0x8000

#define IEEE_MMD_ACCESS_CTRL_DEVAD_MASK        0x1F
#define IEEE_MMD_ACCESS_CTRL_PIDEVAD_MASK      0x801F
#define IEEE_MMD_ACCESS_CTRL_NOPIDEVAD_MASK    0x401F

#define PHY_DETECT_REG                         1
#define PHY_IDENTIFIER_1_REG                   2
#define PHY_IDENTIFIER_2_REG                   3
#define PHY_DETECT_MASK                        0x1808
#define PHY_MARVELL_IDENTIFIER                 0x0141
#define PHY_TI_IDENTIFIER                      0x2000
#define PHY_REALTEK_IDENTIFIER                 0x001c
#define PHY_MICREL_IDENTIFIER                  0x0022
#define PHY_AR8035_IDENTIFIER                  0x004D
#define PHY_XILINX_PCS_PMA_ID1                 0x0174
#define PHY_XILINX_PCS_PMA_ID2                 0x0C00

#define XEMACPS_GMII2RGMII_SPEED1000_FD        0x140
#define XEMACPS_GMII2RGMII_SPEED100_FD         0x2100
#define XEMACPS_GMII2RGMII_SPEED10_FD          0x100
#define XEMACPS_GMII2RGMII_REG_NUM             0x10

#define PHY_REGCR                              0x0D
#define PHY_ADDAR                              0x0E
#define PHY_RGMIIDCTL                          0x86
#define PHY_RGMIICTL                           0x32
#define PHY_STS                                0x11
#define PHY_TI_CR                              0x10
#define PHY_TI_CFG4                            0x31

#define PHY_REGCR_ADDR                         0x001F
#define PHY_REGCR_DATA                         0x401F
#define PHY_TI_CRVAL                           0x5048
#define PHY_TI_CFG4RESVDBIT7                   0x80

#define CRL_APB_GEM0_REF_CTRL                  0xFF5E0050
#define CRL_APB_GEM1_REF_CTRL                  0xFF5E0054
#define CRL_APB_GEM2_REF_CTRL                  0xFF5E0058
#define CRL_APB_GEM3_REF_CTRL                  0xFF5E005C

#define CRL_APB_GEM_DIV0_MASK                  0x00003F00
#define CRL_APB_GEM_DIV0_SHIFT                 8
#define CRL_APB_GEM_DIV1_MASK                  0x003F0000
#define CRL_APB_GEM_DIV1_SHIFT                 16

#define VERSAL_EMACPS_0_BASEADDR               0xFF0C0000
#define VERSAL_EMACPS_1_BASEADDR               0xFF0D0000

#define VERSAL_CRL_GEM0_REF_CTRL               0xFF5E0118
#define VERSAL_CRL_GEM1_REF_CTRL               0xFF5E011C

#define VERSAL_CRL_GEM_DIV_MASK                0x0003FF00
#define VERSAL_CRL_APB_GEM_DIV_SHIFT           8


#define GEM_VERSION_ZYNQMP                     7
#define GEM_VERSION_VERSAL                     0x107


static uint16_t prvAR803x_debug_reg_write( XEmacPs * xemacpsp,
                                           uint32_t phy_addr,
                                           u16 reg,
                                           u16 value );
static void prvSET_AR803x_TX_Timing( XEmacPs * xemacpsp,
                                     uint32_t phy_addr );

uint32_t ulDetectPHY( XEmacPs * xemacpsp )
{
    u16 PhyReg1;
    u16 PhyReg2;
    u32 phy_addr;
    u32 Status;

    for( phy_addr = phyMIN_PHY_ADDRESS; phy_addr <= phyMAX_PHY_ADDRESS; phy_addr++ )
    {
        Status = XEmacPs_PhyRead( xemacpsp, phy_addr, PHY_IDENTIFIER_1_REG, &PhyReg1 );
        Status |= XEmacPs_PhyRead( xemacpsp, phy_addr, PHY_IDENTIFIER_2_REG, &PhyReg2 );

        if( ( Status == XST_SUCCESS ) &&
            ( PhyReg1 > 0x0000 ) && ( PhyReg1 < 0xffff ) &&
            ( PhyReg2 > 0x0000 ) && ( PhyReg2 < 0xffff ) )
        {
            /* Found a valid PHY address */
            break;
        }
    }

    return ( phy_addr <= phyMAX_PHY_ADDRESS ) ? phy_addr : ~0U;
}



unsigned configure_IEEE_phy_speed_US( XEmacPs * xemacpsp,
                                      unsigned speed,
                                      u32 phy_addr )
{
    u16 control;

    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_PAGE_ADDRESS_REGISTER, 2 );
    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_MAC, &control );
    control |= IEEE_RGMII_TXRX_CLOCK_DELAYED_MASK;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_MAC, control );

    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_PAGE_ADDRESS_REGISTER, 0 );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, &control );
    control |= IEEE_ASYMMETRIC_PAUSE_MASK;
    control |= IEEE_PAUSE_MASK;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );
    control &= ~IEEE_CTRL_LINKSPEED_1000M;
    control &= ~IEEE_CTRL_LINKSPEED_100M;
    control &= ~IEEE_CTRL_LINKSPEED_10M;

    if( speed == 1000 )
    {
        control |= IEEE_CTRL_LINKSPEED_1000M;
    }

    else if( speed == 100 )
    {
        control |= IEEE_CTRL_LINKSPEED_100M;
        /* Dont advertise PHY speed of 1000 Mbps */
        XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET, 0 );
        /* Dont advertise PHY speed of 10 Mbps */
        XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG,
                          ADVERTISE_100 );
    }

    else if( speed == 10 )
    {
        control |= IEEE_CTRL_LINKSPEED_10M;
        /* Dont advertise PHY speed of 1000 Mbps */
        XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET, 0 );
        /* Dont advertise PHY speed of 100 Mbps */
        XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG,
                          ADVERTISE_10 );
    }

    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET,
                      control | IEEE_CTRL_RESET_MASK );
    {
        volatile int wait;

        for( wait = 0; wait < 100000; wait++ )
        {
        }
    }
    return 0;
}

static uint32_t get_TI_phy_speed( XEmacPs * xemacpsp,
                                  uint32_t phy_addr )
{
    uint16_t control;
    uint16_t status;
    uint16_t status_speed;
    uint32_t timeout_counter = 0;
    uint32_t phyregtemp;
    int i;
    uint32_t RetStatus;

    XEmacPs_PhyRead( xemacpsp, phy_addr, 0x1F, ( uint16_t * ) &phyregtemp );
    phyregtemp |= 0x4000;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, 0x1F, phyregtemp );
    RetStatus = XEmacPs_PhyRead( xemacpsp, phy_addr, 0x1F, ( uint16_t * ) &phyregtemp );

    if( RetStatus != XST_SUCCESS )
    {
        FreeRTOS_printf( ( "Error during sw reset \n\r" ) );
        return XST_FAILURE;
    }

    XEmacPs_PhyRead( xemacpsp, phy_addr, 0, ( uint16_t * ) &phyregtemp );
    phyregtemp |= 0x8000;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, 0, phyregtemp );

    /*
     * Delay
     */
    for( i = 0; i < 1000000000; i++ )
    {
    }

    RetStatus = XEmacPs_PhyRead( xemacpsp, phy_addr, 0, ( uint16_t * ) &phyregtemp );

    if( RetStatus != XST_SUCCESS )
    {
        FreeRTOS_printf( ( "Error during reset \n\r" ) );
        return XST_FAILURE;
    }

    /* FIFO depth */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_TI_CR, PHY_TI_CRVAL );
    RetStatus = XEmacPs_PhyRead( xemacpsp, phy_addr, PHY_TI_CR, ( uint16_t * ) &phyregtemp );

    if( RetStatus != XST_SUCCESS )
    {
        FreeRTOS_printf( ( "Error writing to 0x10 \n\r" ) );
        return XST_FAILURE;
    }

    /* TX/RX tuning */
    /* Write to PHY_RGMIIDCTL */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_ADDR );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_ADDAR, PHY_RGMIIDCTL );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_DATA );
    RetStatus = XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_ADDAR, 0xA8 );

    if( RetStatus != XST_SUCCESS )
    {
        FreeRTOS_printf( ( "Error in tuning" ) );
        return XST_FAILURE;
    }

    /* Read PHY_RGMIIDCTL */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_ADDR );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_ADDAR, PHY_RGMIIDCTL );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_DATA );
    RetStatus = XEmacPs_PhyRead( xemacpsp, phy_addr, PHY_ADDAR, ( uint16_t * ) &phyregtemp );

    if( RetStatus != XST_SUCCESS )
    {
        FreeRTOS_printf( ( "Error in tuning" ) );
        return XST_FAILURE;
    }

    /* Write PHY_RGMIICTL */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_ADDR );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_ADDAR, PHY_RGMIICTL );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_DATA );
    RetStatus = XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_ADDAR, 0xD3 );

    if( RetStatus != XST_SUCCESS )
    {
        FreeRTOS_printf( ( "Error in tuning" ) );
        return XST_FAILURE;
    }

    /* Read PHY_RGMIICTL */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_ADDR );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_ADDAR, PHY_RGMIICTL );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_DATA );
    RetStatus = XEmacPs_PhyRead( xemacpsp, phy_addr, PHY_ADDAR, ( uint16_t * ) &phyregtemp );

    if( RetStatus != XST_SUCCESS )
    {
        FreeRTOS_printf( ( "Error in tuning" ) );
        return XST_FAILURE;
    }

    /* SW workaround for unstable link when RX_CTRL is not STRAP MODE 3 or 4 */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_ADDR );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_ADDAR, PHY_TI_CFG4 );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_DATA );
    RetStatus = XEmacPs_PhyRead( xemacpsp, phy_addr, PHY_ADDAR, ( uint16_t * ) &phyregtemp );
    phyregtemp &= ~( PHY_TI_CFG4RESVDBIT7 );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_ADDR );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_ADDAR, PHY_TI_CFG4 );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_REGCR, PHY_REGCR_DATA );
    RetStatus = XEmacPs_PhyWrite( xemacpsp, phy_addr, PHY_ADDAR, phyregtemp );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, &control );
    control |= IEEE_ASYMMETRIC_PAUSE_MASK;
    control |= IEEE_PAUSE_MASK;
    control |= ADVERTISE_100;
    control |= ADVERTISE_10;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET,
                     &control );
    control |= ADVERTISE_1000;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET,
                      control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );
    control |= IEEE_CTRL_AUTONEGOTIATE_ENABLE;
    control |= IEEE_STAT_AUTONEGOTIATE_RESTART;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );
    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET, &status );

    FreeRTOS_printf( ( "Waiting for PHY to complete autonegotiation.\n" ) );

    while( !( status & IEEE_STAT_AUTONEGOTIATE_COMPLETE ) )
    {
        vTaskDelay( MINIMUM_SLEEP_TIME );
        timeout_counter++;

        if( timeout_counter == 30 )
        {
            FreeRTOS_printf( ( "Auto negotiation error \n" ) );
            return XST_FAILURE;
        }

        XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET, &status );
    }

    FreeRTOS_printf( ( "autonegotiation complete \n" ) );

    XEmacPs_PhyRead( xemacpsp, phy_addr, PHY_STS, &status_speed );

    if( ( status_speed & 0xC000 ) == 0x8000 )
    {
        return 1000;
    }
    else if( ( status_speed & 0xC000 ) == 0x4000 )
    {
        return 100;
    }
    else
    {
        return 10;
    }

    return XST_SUCCESS;
}

static uint32_t get_Marvell_phy_speed( XEmacPs * xemacpsp,
                                       uint32_t phy_addr )
{
    uint16_t temp;
    uint16_t control;
    uint16_t status;
    uint16_t status_speed;
    uint32_t timeout_counter = 0;
    uint32_t temp_speed;

    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_PAGE_ADDRESS_REGISTER, 2 );
    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_MAC, &control );
    control |= IEEE_RGMII_TXRX_CLOCK_DELAYED_MASK;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_MAC, control );

    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_PAGE_ADDRESS_REGISTER, 0 );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, &control );
    control |= IEEE_ASYMMETRIC_PAUSE_MASK;
    control |= IEEE_PAUSE_MASK;
    control |= ADVERTISE_100;
    control |= ADVERTISE_10;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET,
                     &control );
    control |= ADVERTISE_1000;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET,
                      control );

    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_PAGE_ADDRESS_REGISTER, 0 );
    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_COPPER_SPECIFIC_CONTROL_REG,
                     &control );
    control |= ( 7 << 12 ); /* max number of gigabit attempts */
    control |= ( 1 << 11 ); /* enable downshift */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_COPPER_SPECIFIC_CONTROL_REG,
                      control );
    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );
    control |= IEEE_CTRL_AUTONEGOTIATE_ENABLE;
    control |= IEEE_STAT_AUTONEGOTIATE_RESTART;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );
    control |= IEEE_CTRL_RESET_MASK;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, control );

    while( 1 )
    {
        XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );

        if( control & IEEE_CTRL_RESET_MASK )
        {
            continue;
        }
        else
        {
            break;
        }
    }

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET, &status );

    FreeRTOS_printf( ( "Waiting for PHY to complete autonegotiation.\n" ) );

    while( !( status & IEEE_STAT_AUTONEGOTIATE_COMPLETE ) )
    {
        vTaskDelay( MINIMUM_SLEEP_TIME );
        XEmacPs_PhyRead( xemacpsp, phy_addr,
                         IEEE_COPPER_SPECIFIC_STATUS_REG_2, &temp );
        timeout_counter++;

        if( timeout_counter == 30 )
        {
            FreeRTOS_printf( ( "Auto negotiation error \n" ) );
            return XST_FAILURE;
        }

        XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET, &status );
    }

    FreeRTOS_printf( ( "autonegotiation complete \n" ) );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_SPECIFIC_STATUS_REG,
                     &status_speed );

    if( status_speed & 0x400 )
    {
        temp_speed = status_speed & IEEE_SPEED_MASK;

        if( temp_speed == IEEE_SPEED_1000 )
        {
            return 1000;
        }
        else if( temp_speed == IEEE_SPEED_100 )
        {
            return 100;
        }
        else
        {
            return 10;
        }
    }

    return XST_SUCCESS;
}

static uint32_t get_Realtek_phy_speed( XEmacPs * xemacpsp,
                                       uint32_t phy_addr )
{
    uint16_t control;
    uint16_t status;
    uint16_t status_speed;
    uint32_t timeout_counter = 0;
    uint32_t temp_speed;

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, &control );
    control |= IEEE_ASYMMETRIC_PAUSE_MASK;
    control |= IEEE_PAUSE_MASK;
    control |= ADVERTISE_100;
    control |= ADVERTISE_10;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET,
                     &control );
    control |= ADVERTISE_1000;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET,
                      control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );
    control |= IEEE_CTRL_AUTONEGOTIATE_ENABLE;
    control |= IEEE_STAT_AUTONEGOTIATE_RESTART;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );
    control |= IEEE_CTRL_RESET_MASK;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, control );

    while( 1 )
    {
        XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );

        if( control & IEEE_CTRL_RESET_MASK )
        {
            continue;
        }
        else
        {
            break;
        }
    }

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET, &status );

    FreeRTOS_printf( ( "Waiting for PHY to complete autonegotiation.\n" ) );

    while( !( status & IEEE_STAT_AUTONEGOTIATE_COMPLETE ) )
    {
        vTaskDelay( MINIMUM_SLEEP_TIME );
        timeout_counter++;

        if( timeout_counter == 30 )
        {
            FreeRTOS_printf( ( "Auto negotiation error \n" ) );
            return XST_FAILURE;
        }

        XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET, &status );
    }

    FreeRTOS_printf( ( "autonegotiation complete \n" ) );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_SPECIFIC_STATUS_REG,
                     &status_speed );

    if( status_speed & 0x400 )
    {
        temp_speed = status_speed & IEEE_SPEED_MASK;

        if( temp_speed == IEEE_SPEED_1000 )
        {
            return 1000;
        }
        else if( temp_speed == IEEE_SPEED_100 )
        {
            return 100;
        }
        else
        {
            return 10;
        }
    }

    return XST_FAILURE;
}

#define LPA_IEEE_1000        0x0800
#define LP5_IEEE_100         0x0100
#define LP5_IEEE_10          0x0040
#define MICREL_ID_KSZ9021    0x0161
#define MICREL_ID_KSZ9031    0x0162
#define MICREL_ID_KSZ9131    0x0164


static int set_Micrel_phy_delays( XEmacPs * EmacPsInstancePtr,
                                  uint32_t PhyAddr )
{
    int Status;
    uint16_t PhyType, PhyData;

    XEmacPs_PhyRead( EmacPsInstancePtr, PhyAddr, 0x3, ( u16 * ) &PhyData ); /* read value */
    PhyType = ( PhyData >> 4 );

    /* enabling RGMII delays */
    if( PhyType == MICREL_ID_KSZ9131 ) /* KSZ9131 */
    {
        FreeRTOS_printf( ( "Detected KSZ9131 Ethernet PHY\n\r" ) );
        /*Ctrl Delay */
        u16 RxCtrlDelay = 7;                                         /* 0..15, default 7 */
        u16 TxCtrlDelay = 7;                                         /* 0..15, default 7 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x0002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, 0x0004 ); /* Reg 0x4 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x4002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, ( TxCtrlDelay | ( RxCtrlDelay << 4 ) ) );
        /*Data Delay */
        u16 RxDataDelay = 7;                                         /* 0..15, default 7 */
        u16 TxDataDelay = 7;                                         /* 0..15, default 7 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x0002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, 0x0005 ); /* Reg 0x5 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x4002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, ( RxDataDelay | ( RxDataDelay << 4 ) | ( RxDataDelay << 8 ) | ( RxDataDelay << 12 ) ) );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x0002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, 0x0006 ); /* Reg 0x6 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x4002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, ( TxDataDelay | ( TxDataDelay << 4 ) | ( TxDataDelay << 8 ) | ( TxDataDelay << 12 ) ) );
        /*Clock Delay */
        u16 RxClockDelay = 31;                                       /* 0..31, default 15 */
        u16 TxClockDelay = 31;                                       /* 0..31, default 15 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x0002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, 0x0008 ); /* Reg 0x8 RGMII Clock Pad Skew */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x4002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, ( RxClockDelay | ( TxClockDelay << 5 ) ) );
    }
    else if( PhyType == MICREL_ID_KSZ9031 ) /* KSZ9031 */
    {
        FreeRTOS_printf( ( "Detected KSZ9031 Ethernet PHY\n\r" ) );
        /*Ctrl Delay */
        u16 RxCtrlDelay = 7;                                         /* 0..15, default 7 */
        u16 TxCtrlDelay = 7;                                         /* 0..15, default 7 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x0002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, 0x0004 ); /* Reg 0x4 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x4002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, ( TxCtrlDelay | ( RxCtrlDelay << 4 ) ) );
        /*Data Delay */
        u16 RxDataDelay = 7;                                         /* 0..15, default 7 */
        u16 TxDataDelay = 7;                                         /* 0..15, default 7 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x0002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, 0x0005 ); /* Reg 0x5 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x4002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, ( RxDataDelay | ( RxDataDelay << 4 ) | ( RxDataDelay << 8 ) | ( RxDataDelay << 12 ) ) );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x0002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, 0x0006 ); /* Reg 0x6 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x4002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, ( TxDataDelay | ( TxDataDelay << 4 ) | ( TxDataDelay << 8 ) | ( TxDataDelay << 12 ) ) );
        /*Clock Delay */
        u16 RxClockDelay = 31;                                       /* 0..31, default 15 */
        u16 TxClockDelay = 31;                                       /* 0..31, default 15 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x0002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, 0x0008 ); /* Reg 0x8 RGMII Clock Pad Skew */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xD, 0x4002 );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xE, ( RxClockDelay | ( TxClockDelay << 5 ) ) );
    }
    else if( PhyType == MICREL_ID_KSZ9021 ) /* KSZ9021 */
    {
        FreeRTOS_printf( ( "Detected KSZ9021 Ethernet PHY\n\r" ) );
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xB, 0x8104 ); /* write Reg 0x104 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xC, 0xF0F0 ); /* set write data */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xB, 0x8105 ); /* write Reg 0x105 */
        XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0xC, 0x0000 ); /* set write data */
    }

    /* Issue a reset to phy */
    Status = XEmacPs_PhyRead( EmacPsInstancePtr, PhyAddr, 0x0, &PhyData );
    PhyData |= 0x8000;
    Status = XEmacPs_PhyWrite( EmacPsInstancePtr, PhyAddr, 0x0, PhyData );
    vTaskDelay( 1 );
    Status |= XEmacPs_PhyRead( EmacPsInstancePtr, PhyAddr, 0x0, &PhyData );

    if( Status != XST_SUCCESS )
    {
        return Status;
    }

    return PhyType;
}

static uint32_t get_Micrel_phy_speed( XEmacPs * xemacpsp,
                                      uint32_t phy_addr )
{
    const char * name_ptr;
    uint16_t temp, phy_type;
    uint16_t control;
    uint16_t status;
    uint16_t status_speed;
    uint32_t timeout_counter = 0;

    /* Just to prevent compiler warnings about unused variables. */
    ( void ) name_ptr;


    FreeRTOS_printf( ( "Start Micrel PHY program delay\r\n" ) );

    if( ( phy_type = set_Micrel_phy_delays( xemacpsp, phy_addr ) ) != XST_FAILURE )
    {
        FreeRTOS_printf( ( "Delay Set Okay!\r\n" ) );
    }
    else
    {
        FreeRTOS_printf( ( "Delay Set Error!\r\n" ) );
    }

    switch( phy_type )
    {
        case MICREL_ID_KSZ9021:
            name_ptr = "KSZ9021";
            break;

        case MICREL_ID_KSZ9031:
            name_ptr = "KSZ9031";
            break;

        case MICREL_ID_KSZ9131:
            name_ptr = "KSZ9131";
            break;

        default:
            name_ptr = "!UNKNOWN!";
            break;
    }

    FreeRTOS_printf( ( "Start %s auto-negotiation\r\n", name_ptr ) );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, &control );
    control |= IEEE_ASYMMETRIC_PAUSE_MASK;
    control |= IEEE_PAUSE_MASK;
    control |= ADVERTISE_100;
    control |= ADVERTISE_10;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG, control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET, &control );
    control |= ADVERTISE_1000;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET, control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_COPPER_SPECIFIC_CONTROL_REG, &control );
    control |= ( 7 << 12 );
    control |= ( 1 << 11 );
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_COPPER_SPECIFIC_CONTROL_REG, control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );
    control |= IEEE_CTRL_AUTONEGOTIATE_ENABLE;
    control |= IEEE_STAT_AUTONEGOTIATE_RESTART;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, control );

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );
    control |= IEEE_CTRL_RESET_MASK;
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, control );

    while( 1 )
    {
        XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, &control );

        if( control & IEEE_CTRL_RESET_MASK )
        {
            continue;
        }
        else
        {
            break;
        }
    }

    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET, &status );

    FreeRTOS_printf( ( "Waiting for %s to complete Auto-negotiation.\r\n", name_ptr ) );

    while( !( status & IEEE_STAT_AUTONEGOTIATE_COMPLETE ) )
    {
        vTaskDelay( pdMS_TO_TICKS( 1000 ) );
        XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_COPPER_SPECIFIC_STATUS_REG_2, &temp );
        timeout_counter++;

        if( timeout_counter == 30 )
        {
            FreeRTOS_printf( ( "Auto negotiation error \r\n" ) );
            return XST_FAILURE;
        }

        XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_STATUS_REG_OFFSET, &status );
    }

    FreeRTOS_printf( ( "%s Completed Auto-negotiation\r\n", name_ptr ) );

    /* Check for high speed connection first */
    XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_PARTNER_ABILITIES_3_REG_OFFSET, &status_speed );

    if( status_speed & LPA_IEEE_1000 )
    {
        FreeRTOS_printf( ( "Micrel PHY %s speed 1000Mbps\r\n", name_ptr ) );
        return 1000;
    }
    else /* No high speed so check lows... */
    {
        XEmacPs_PhyRead( xemacpsp, phy_addr, IEEE_PARTNER_ABILITIES_1_REG_OFFSET, &status_speed );

        if( status_speed & LP5_IEEE_100 )
        {
            FreeRTOS_printf( ( "Micrel PHY %s speed 100Mbps\r\n", name_ptr ) );
            return 100;
        }

        if( status_speed & LP5_IEEE_10 )
        {
            FreeRTOS_printf( ( "Micrel PHY %s speed 10Mbps\r\n", name_ptr ) );
            return 10;
        }
    }

    return XST_FAILURE;
}

/* Here is a XEmacPs_PhyRead() that returns the value of a register. */
static uint16_t XEmacPs_PhyRead2( XEmacPs * InstancePtr,
                                  u32 PhyAddress,
                                  u32 RegisterNum )
{
    LONG lResult;
    uint16_t usReturn = 0U;

    lResult = XEmacPs_PhyRead( InstancePtr, PhyAddress, RegisterNum, &( usReturn ) );

    if( lResult != ( LONG ) ( XST_SUCCESS ) )
    {
        usReturn = 0U;
    }

    return usReturn;
}

static uint32_t ar8035CheckStatus( XEmacPs * xemacpsp,
                                   uint32_t phy_addr );

static void prvSET_AR803x_TX_Timing( XEmacPs * xemacpsp,
                                     uint32_t phy_addr )
{
/*
 *  rgmii_tx_clk_dly: tx clock delay control bit:
 *  1 =  rgmii tx clock delay enable  <<= this option
 *  0 =  rgmii tx clock delay disable.
 *
 *  Gtx_dly_val: select the delay of gtx_clk.
 *  00:0.25ns
 *  01:1.3ns  <<= this option
 *  10:2.4ns
 *  11:3.4ns
 */
    prvAR803x_debug_reg_write( xemacpsp, phy_addr, 0x5, 0x2d47 );
    prvAR803x_debug_reg_write( xemacpsp, phy_addr, 0xb, 0xbc20 );
}

static uint32_t get_AR8035_phy_speed( XEmacPs * xemacpsp,
                                      uint32_t phy_addr )
{
    uint32_t timeout_counter = 0;

    /*Reset PHY transceiver */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, IEEE_CTRL_RESET_MASK );

    /*Wait for the reset to complete */
    while( ( XEmacPs_PhyRead2( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET ) & IEEE_CTRL_RESET_MASK ) != 0U )
    {
    }

    /*Basic mode control register */
    /* IEEE_CTRL_LINKSPEED_100M,  also known as 'AR8035_BMCR_SPEED_SEL_LSB' */
    /* IEEE_STAT_1GBPS_EXTENSIONS also known as: AR8035_BMCR_DUPLEX_MODE' */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_CONTROL_REG_OFFSET, IEEE_CTRL_LINKSPEED_100M |
                      IEEE_CTRL_AUTONEGOTIATE_ENABLE | IEEE_STAT_1GBPS_EXTENSIONS );

#define AR8035_ANAR_SELECTOR_DEFAULT    0x0001

    /*Auto-negotiation advertisement register */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_AUTONEGO_ADVERTISE_REG,
                      IEEE_CTRL_AUTONEGOTIATE_ENABLE |
                      IEEE_ASYMMETRIC_PAUSE_MASK |
                      IEEE_PAUSE_MASK |
                      ADVERTISE_100FULL |
                      ADVERTISE_100HALF |
                      ADVERTISE_10FULL |
                      ADVERTISE_10HALF |
                      AR8035_ANAR_SELECTOR_DEFAULT );

    /*1000 BASE-T control register */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, IEEE_1000_ADVERTISE_REG_OFFSET, ADVERTISE_1000FULL );

#define AR8035_FUNC_CTRL                          0x10
#define AR8035_FUNC_CTRL_ASSERT_CRS_ON_TX         0x0800
#define AR8035_FUNC_CTRL_MDIX_MODE                0x0060
#define AR8035_FUNC_CTRL_MDIX_MODE_MANUAL_MDI     0x0000
#define AR8035_FUNC_CTRL_MDIX_MODE_MANUAL_MDIX    0x0020
#define AR8035_FUNC_CTRL_MDIX_MODE_AUTO           0x0060
#define AR8035_FUNC_CTRL_SQE_TEST                 0x0004
#define AR8035_FUNC_CTRL_POLARITY_REVERSAL        0x0002
#define AR8035_FUNC_CTRL_JABBER_DIS               0x0001

    /*Function control register */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, AR8035_FUNC_CTRL,
                      AR8035_FUNC_CTRL_ASSERT_CRS_ON_TX | AR8035_FUNC_CTRL_MDIX_MODE_AUTO |
                      AR8035_FUNC_CTRL_POLARITY_REVERSAL );

    /*Dump PHY registers for debugging purpose */
/*	ar8035DumpPhyReg(interface); */

#define AR8035_INT_EN                     0x12
#define AR8035_INT_STATUS_LINK_FAIL       0x0800
#define AR8035_INT_STATUS_LINK_SUCCESS    0x0400

    /*The PHY will generate interrupts when link status changes are detected */
    XEmacPs_PhyWrite( xemacpsp, phy_addr, AR8035_INT_EN, AR8035_INT_STATUS_LINK_FAIL |
                      AR8035_INT_STATUS_LINK_SUCCESS );

    while( pdTRUE )
    {
        uint32_t status;
        vTaskDelay( MINIMUM_SLEEP_TIME );

        timeout_counter++;

        if( timeout_counter == 30 )
        {
            FreeRTOS_printf( ( "Auto negotiation error \n" ) );
            return XST_FAILURE;
        }

        status = ar8035CheckStatus( xemacpsp, phy_addr );

        if( status > 10 )
        {
            prvSET_AR803x_TX_Timing( xemacpsp, phy_addr );
            return status;
        }
    }
}

#define AR803X_DEBUG_ADDR    0x1D
#define AR803X_DEBUG_DATA    0x1E
static uint16_t prvAR803x_debug_reg_write( XEmacPs * xemacpsp,
                                           uint32_t phy_addr,
                                           u16 reg,
                                           u16 value )
{
    XEmacPs_PhyWrite( xemacpsp, phy_addr, AR803X_DEBUG_ADDR, reg );

    return XEmacPs_PhyWrite( xemacpsp, phy_addr, AR803X_DEBUG_DATA, value );
}

static uint32_t ar8035CheckStatus( XEmacPs * xemacpsp,
                                   uint32_t phy_addr )
{
    uint16_t status;
    uint32_t linkSpeed = 0U;
    BaseType_t linkState = pdFALSE;

    /*Read status register to acknowledge the interrupt */
    status = XEmacPs_PhyRead2( xemacpsp, phy_addr, IEEE_COPPER_SPECIFIC_STATUS_REG_2 );

#define AR8035_INT_STATUS_LINK_FAIL       0x0800
#define AR8035_INT_STATUS_LINK_SUCCESS    0x0400

    /*Link status change? */
    if( status & ( AR8035_INT_STATUS_LINK_FAIL | AR8035_INT_STATUS_LINK_SUCCESS ) )
    {
        /*Read PHY status register */
        status = XEmacPs_PhyRead2( xemacpsp, phy_addr, IEEE_SPECIFIC_STATUS_REG );

#define AR8035_PHY_STATUS_LINK    0x0400

        /*Link is up? */
        if( status & AR8035_PHY_STATUS_LINK )
        {
#define AR8035_PHY_STATUS_SPEED             0xC000
#define AR8035_PHY_STATUS_SPEED_10MBPS      0x0000
#define AR8035_PHY_STATUS_SPEED_100MBPS     0x4000
#define AR8035_PHY_STATUS_SPEED_1000MBPS    0x8000

            /*Check current speed */
            switch( status & AR8035_PHY_STATUS_SPEED )
            {
                /*10BASE-T */
                case AR8035_PHY_STATUS_SPEED_10MBPS:
                    linkSpeed = 10;
                    break;

                /*100BASE-TX */
                case AR8035_PHY_STATUS_SPEED_100MBPS:
                    linkSpeed = 100;
                    break;

                /*1000BASE-T */
                case AR8035_PHY_STATUS_SPEED_1000MBPS:
                    linkSpeed = 1000;
                    break;

                /*Unknown speed */
                default:
                    /*Debug message */
                    FreeRTOS_printf( ( "Invalid speed ( status %04X )\n", status ) );
                    break;
            }

#define AR8035_PHY_STATUS_DUPLEX    0x2000

            /*Check current duplex mode */
            if( status & AR8035_PHY_STATUS_DUPLEX )
            {
                FreeRTOS_printf( ( "Full duplex\n" ) );
            }
            else
            {
                FreeRTOS_printf( ( "Half duplex\n" ) );
            }

            /*Update link state */
            linkState = TRUE;

            /*Adjust MAC configuration parameters for proper operation */
            /*interface->nicDriver->updateMacConfig(interface); */
        }
        else
        {
            /*Update link state */
            linkState = FALSE;
        }

        /*Process link state change event */
/*		nicNotifyLinkChange(interface); */
    }

    /* Just to prevent compiler warnings about unused variable. */
    ( void ) linkState;

    return linkSpeed;
}


static const char * pcGetPHIName( uint16_t usID )
{
    const char * pcReturn = "";
    static char pcName[ 32 ];

    switch( usID )
    {
        case PHY_TI_IDENTIFIER:
            pcReturn = "TI_dp83869hm";
            break;

        case PHY_REALTEK_IDENTIFIER:
            pcReturn = "Realtek RTL8212";
            break;

        case PHY_MICREL_IDENTIFIER:
            pcReturn = "MICREL PHY";
            break;

        case PHY_AR8035_IDENTIFIER:
            pcReturn = "Atheros_ar8035";
            break;

        case PHY_MARVELL_IDENTIFIER:
            pcReturn = "Marvell_88E1512";
            break;

        default:
            snprintf( pcName, sizeof pcName, "Unknown PHY %04X", usID );
            pcReturn = pcName;
            break;
    }

    return pcReturn;
}

static uint32_t get_IEEE_phy_speed_US( XEmacPs * xemacpsp,
                                       uint32_t phy_addr )
{
    uint16_t phy_identity;
    uint32_t RetStatus;

    XEmacPs_PhyRead( xemacpsp, phy_addr, PHY_IDENTIFIER_1_REG,
                     &phy_identity );

    const char * pcPHYName = pcGetPHIName( phy_identity );

    FreeRTOS_printf( ( "Start %s PHY autonegotiation. ID = 0x%04X\n", pcPHYName, phy_identity ) );

    /* Just to prevent compiler warnings about unused variables. */
    ( void ) pcPHYName;

    switch( phy_identity )
    {
        case PHY_TI_IDENTIFIER:
            RetStatus = get_TI_phy_speed( xemacpsp, phy_addr );
            break;

        case PHY_REALTEK_IDENTIFIER:
            RetStatus = get_Realtek_phy_speed( xemacpsp, phy_addr );
            break;

        case PHY_MARVELL_IDENTIFIER:
            RetStatus = get_Marvell_phy_speed( xemacpsp, phy_addr );
            break;

        case PHY_MICREL_IDENTIFIER:
            RetStatus = get_Micrel_phy_speed( xemacpsp, phy_addr );
            break;

        case PHY_AR8035_IDENTIFIER:
            RetStatus = get_AR8035_phy_speed( xemacpsp, phy_addr );
            prvSET_AR803x_TX_Timing( xemacpsp, phy_addr );
            break;

        default:
            FreeRTOS_printf( ( "Don't know how to handle PHY ID %04X\n", phy_identity ) );
            RetStatus = XST_FAILURE;
            break;
    }

    return RetStatus;
}

static void SetUpSLCRDivisors( u32 mac_baseaddr,
                               s32 speed )
{
    u32 gigeversion;
    volatile u32 CrlApbBaseAddr;
    u32 CrlApbDiv0 = 0;
    u32 CrlApbDiv1 = 0;
    u32 CrlApbGemCtrl;

    gigeversion = ( ( Xil_In32( mac_baseaddr + 0xFC ) ) >> 16 ) & 0xFFF;

    if( gigeversion == GEM_VERSION_ZYNQMP )
    {
        /* Setup divisors in CRL_APB for Zynq Ultrascale+ MPSoC */
        if( mac_baseaddr == ZYNQMP_EMACPS_0_BASEADDR )
        {
            CrlApbBaseAddr = CRL_APB_GEM0_REF_CTRL;
        }
        else if( mac_baseaddr == ZYNQMP_EMACPS_1_BASEADDR )
        {
            CrlApbBaseAddr = CRL_APB_GEM1_REF_CTRL;
        }
        else if( mac_baseaddr == ZYNQMP_EMACPS_2_BASEADDR )
        {
            CrlApbBaseAddr = CRL_APB_GEM2_REF_CTRL;
        }
        else if( mac_baseaddr == ZYNQMP_EMACPS_3_BASEADDR )
        {
            CrlApbBaseAddr = CRL_APB_GEM3_REF_CTRL;
        }

        if( speed == 1000 )
        {
            if( mac_baseaddr == ZYNQMP_EMACPS_0_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_0_ENET_SLCR_1000MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_0_ENET_SLCR_1000MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_0_ENET_SLCR_1000MBPS_DIV1;
                #endif
            }
            else if( mac_baseaddr == ZYNQMP_EMACPS_1_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_1_ENET_SLCR_1000MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_1_ENET_SLCR_1000MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_1_ENET_SLCR_1000MBPS_DIV1;
                #endif
            }
            else if( mac_baseaddr == ZYNQMP_EMACPS_2_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_2_ENET_SLCR_1000MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_2_ENET_SLCR_1000MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_2_ENET_SLCR_1000MBPS_DIV1;
                #endif
            }
            else if( mac_baseaddr == ZYNQMP_EMACPS_3_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_3_ENET_SLCR_1000MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_3_ENET_SLCR_1000MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_3_ENET_SLCR_1000MBPS_DIV1;
                #endif
            }
        }
        else if( speed == 100 )
        {
            if( mac_baseaddr == ZYNQMP_EMACPS_0_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_0_ENET_SLCR_100MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_0_ENET_SLCR_100MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_0_ENET_SLCR_100MBPS_DIV1;
                #endif
            }
            else if( mac_baseaddr == ZYNQMP_EMACPS_1_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_1_ENET_SLCR_100MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_1_ENET_SLCR_100MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_1_ENET_SLCR_100MBPS_DIV1;
                #endif
            }
            else if( mac_baseaddr == ZYNQMP_EMACPS_2_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_2_ENET_SLCR_100MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_2_ENET_SLCR_100MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_2_ENET_SLCR_100MBPS_DIV1;
                #endif
            }
            else if( mac_baseaddr == ZYNQMP_EMACPS_3_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_3_ENET_SLCR_100MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_3_ENET_SLCR_100MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_3_ENET_SLCR_100MBPS_DIV1;
                #endif
            }
        }
        else
        {
            if( mac_baseaddr == ZYNQMP_EMACPS_0_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_0_ENET_SLCR_10MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_0_ENET_SLCR_10MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_0_ENET_SLCR_10MBPS_DIV1;
                #endif
            }
            else if( mac_baseaddr == ZYNQMP_EMACPS_1_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_1_ENET_SLCR_10MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_1_ENET_SLCR_10MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_1_ENET_SLCR_10MBPS_DIV1;
                #endif
            }
            else if( mac_baseaddr == ZYNQMP_EMACPS_2_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_2_ENET_SLCR_10MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_2_ENET_SLCR_10MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_2_ENET_SLCR_10MBPS_DIV1;
                #endif
            }
            else if( mac_baseaddr == ZYNQMP_EMACPS_3_BASEADDR )
            {
                #ifdef XPAR_PSU_ETHERNET_3_ENET_SLCR_10MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSU_ETHERNET_3_ENET_SLCR_10MBPS_DIV0;
                    CrlApbDiv1 = XPAR_PSU_ETHERNET_3_ENET_SLCR_10MBPS_DIV1;
                #endif
            }
        }

        if( ( CrlApbDiv0 != 0 ) && ( CrlApbDiv1 != 0 ) )
        {
            #if EL1_NONSECURE
                XSmc_OutVar RegRead;
                RegRead = Xil_Smc( MMIO_READ_SMC_FID, ( u64 ) ( CrlApbBaseAddr ),
                                   0, 0, 0, 0, 0, 0 );
                CrlApbGemCtrl = RegRead.Arg0 >> 32;
            #else
                CrlApbGemCtrl = *( volatile u32 * ) ( UINTPTR ) ( CrlApbBaseAddr );
            #endif
            CrlApbGemCtrl &= ~CRL_APB_GEM_DIV0_MASK;
            CrlApbGemCtrl |= CrlApbDiv0 << CRL_APB_GEM_DIV0_SHIFT;
            CrlApbGemCtrl &= ~CRL_APB_GEM_DIV1_MASK;
            CrlApbGemCtrl |= CrlApbDiv1 << CRL_APB_GEM_DIV1_SHIFT;
            #if EL1_NONSECURE
                Xil_Smc( MMIO_WRITE_SMC_FID, ( u64 ) ( CrlApbBaseAddr ) | ( ( u64 ) ( 0xFFFFFFFF ) << 32 ),
                         ( u64 ) CrlApbGemCtrl, 0, 0, 0, 0, 0 );

                do
                {
                    RegRead = Xil_Smc( MMIO_READ_SMC_FID, ( u64 ) ( CrlApbBaseAddr ),
                                       0, 0, 0, 0, 0, 0 );
                } while( ( RegRead.Arg0 >> 32 ) != CrlApbGemCtrl );
            #else
                *( volatile u32 * ) ( UINTPTR ) ( CrlApbBaseAddr ) = CrlApbGemCtrl;
            #endif
        }
        else
        {
            FreeRTOS_printf( ( "Clock Divisors incorrect - Please check\n" ) );
        }
    }
    else if( gigeversion == GEM_VERSION_VERSAL )
    {
        /* Setup divisors in CRL for Versal */
        if( mac_baseaddr == VERSAL_EMACPS_0_BASEADDR )
        {
            CrlApbBaseAddr = VERSAL_CRL_GEM0_REF_CTRL;
            #if EL1_NONSECURE
                ClkId = CLK_GEM0_REF;
            #endif
        }
        else if( mac_baseaddr == VERSAL_EMACPS_1_BASEADDR )
        {
            CrlApbBaseAddr = VERSAL_CRL_GEM1_REF_CTRL;
            #if EL1_NONSECURE
                ClkId = CLK_GEM1_REF;
            #endif
        }

        if( speed == 1000 )
        {
            if( mac_baseaddr == VERSAL_EMACPS_0_BASEADDR )
            {
                #ifdef XPAR_PSV_ETHERNET_0_ENET_SLCR_1000MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSV_ETHERNET_0_ENET_SLCR_1000MBPS_DIV0;
                #endif
            }
            else if( mac_baseaddr == VERSAL_EMACPS_1_BASEADDR )
            {
                #ifdef XPAR_PSV_ETHERNET_1_ENET_SLCR_1000MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSV_ETHERNET_1_ENET_SLCR_1000MBPS_DIV0;
                #endif
            }
        }
        else if( speed == 100 )
        {
            if( mac_baseaddr == VERSAL_EMACPS_0_BASEADDR )
            {
                #ifdef XPAR_PSV_ETHERNET_0_ENET_SLCR_100MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSV_ETHERNET_0_ENET_SLCR_100MBPS_DIV0;
                #endif
            }
            else if( mac_baseaddr == VERSAL_EMACPS_1_BASEADDR )
            {
                #ifdef XPAR_PSV_ETHERNET_1_ENET_SLCR_100MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSV_ETHERNET_1_ENET_SLCR_100MBPS_DIV0;
                #endif
            }
        }
        else
        {
            if( mac_baseaddr == VERSAL_EMACPS_0_BASEADDR )
            {
                #ifdef XPAR_PSV_ETHERNET_0_ENET_SLCR_10MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSV_ETHERNET_0_ENET_SLCR_10MBPS_DIV0;
                #endif
            }
            else if( mac_baseaddr == VERSAL_EMACPS_1_BASEADDR )
            {
                #ifdef XPAR_PSV_ETHERNET_1_ENET_SLCR_10MBPS_DIV0
                    CrlApbDiv0 = XPAR_PSV_ETHERNET_1_ENET_SLCR_10MBPS_DIV0;
                #endif
            }
        }

        if( CrlApbDiv0 != 0 )
        {
            #if EL1_NONSECURE
                Xil_Smc( PM_SET_DIVIDER_SMC_FID, ( ( ( u64 ) CrlApbDiv0 << 32 ) | ClkId ), 0, 0, 0, 0, 0, 0 );
            #else
                CrlApbGemCtrl = Xil_In32( ( UINTPTR ) CrlApbBaseAddr );
                CrlApbGemCtrl &= ~VERSAL_CRL_GEM_DIV_MASK;
                CrlApbGemCtrl |= CrlApbDiv0 << VERSAL_CRL_APB_GEM_DIV_SHIFT;

                Xil_Out32( ( UINTPTR ) CrlApbBaseAddr, CrlApbGemCtrl );
            #endif
        }
        else
        {
            FreeRTOS_printf( ( "Clock Divisors incorrect - Please check\n" ) );
        }
    }
    else
    {
        FreeRTOS_printf( ( "Invalid GEM version %u \n", gigeversion ) );
        return;
    }
}

u32 Phy_Setup_US( XEmacPs * xemacpsp,
                  u32 phy_addr )
{
    u32 link_speed = 0;
    u32 conv_present = 0;
    u32 convspeeddupsetting = 0;
    u32 convphyaddr = 0;

    #ifdef XPAR_GMII2RGMIICON_0N_ETH0_ADDR
        convphyaddr = XPAR_GMII2RGMIICON_0N_ETH0_ADDR;
        conv_present = 1;
    #else
        #ifdef XPAR_GMII2RGMIICON_0N_ETH1_ADDR
            convphyaddr = XPAR_GMII2RGMIICON_0N_ETH1_ADDR;
            conv_present = 1;
        #endif
    #endif

    #ifdef  ipconfigNIC_LINKSPEED_AUTODETECT
        link_speed = get_IEEE_phy_speed_US( xemacpsp, phy_addr );

        if( link_speed == 1000 )
        {
            SetUpSLCRDivisors( xemacpsp->Config.BaseAddress, 1000 );
            convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED1000_FD;
        }
        else if( link_speed == 100 )
        {
            SetUpSLCRDivisors( xemacpsp->Config.BaseAddress, 100 );
            convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED100_FD;
        }
        else if( link_speed != XST_FAILURE )
        {
            SetUpSLCRDivisors( xemacpsp->Config.BaseAddress, 10 );
            convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED10_FD;
        }
        else
        {
            FreeRTOS_printf( ( "Phy setup error \n" ) );
            return XST_FAILURE;
        }
    #elif   defined( ipconfigNIC_LINKSPEED1000 )
        SetUpSLCRDivisors( xemacpsp->Config.BaseAddress, 1000, , phy_addr );
        link_speed = 1000;
        configure_IEEE_phy_speed_US( xemacpsp, link_speed );
        convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED1000_FD;
        vTaskDelay( MINIMUM_SLEEP_TIME );
    #elif   defined( ipconfigNIC_LINKSPEED100 )
        SetUpSLCRDivisors( xemacpsp->Config.BaseAddress, 100 );
        link_speed = 100;
        configure_IEEE_phy_speed_US( xemacpsp, link_speed, phy_addr );
        convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED100_FD;
        vTaskDelay( MINIMUM_SLEEP_TIME );
    #elif   defined( ipconfigNIC_LINKSPEED10 )
        SetUpSLCRDivisors( xemacpsp->Config.BaseAddress, 10 );
        link_speed = 10;
        configure_IEEE_phy_speed_US( xemacpsp, link_speed, , phy_addr );
        convspeeddupsetting = XEMACPS_GMII2RGMII_SPEED10_FD;
        vTaskDelay( MINIMUM_SLEEP_TIME );
    #endif /* ifdef  ipconfigNIC_LINKSPEED_AUTODETECT */

    if( conv_present )
    {
        XEmacPs_PhyWrite( xemacpsp, convphyaddr,
                          XEMACPS_GMII2RGMII_REG_NUM, convspeeddupsetting );
    }

    FreeRTOS_printf( ( "link speed: %d\n", link_speed ) );
    return link_speed;
}
