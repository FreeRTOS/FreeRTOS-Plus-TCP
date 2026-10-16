/* SPDX-License-Identifier: MIT */

#ifndef STM32F4XX_HAL_CONF_H
#define STM32F4XX_HAL_CONF_H

#define HAL_MODULE_ENABLED
#define HAL_ETH_MODULE_ENABLED
#define HAL_RCC_MODULE_ENABLED
#define HAL_CORTEX_MODULE_ENABLED
#define USE_HAL_ETH_REGISTER_CALLBACKS    0U
#define PHY_READ_TO                       0x0000FFFFU
#define PHY_WRITE_TO                      0x0000FFFFU

#include "stm32f4xx_hal_rcc.h"
#include "stm32f4xx_hal_cortex.h"
#include "stm32f4xx_hal_eth.h"

#define assert_param( expression )    ( ( void ) ( expression ) )

#endif /* STM32F4XX_HAL_CONF_H */
