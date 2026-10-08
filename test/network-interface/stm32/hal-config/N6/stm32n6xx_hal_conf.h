/* SPDX-License-Identifier: MIT */

#ifndef STM32N6XX_HAL_CONF_H
#define STM32N6XX_HAL_CONF_H

#define HAL_MODULE_ENABLED
#define HAL_ETH_MODULE_ENABLED
#define HAL_RCC_MODULE_ENABLED
#define HAL_CORTEX_MODULE_ENABLED
#define USE_HAL_ETH_REGISTER_CALLBACKS    0U

#include "stm32n6xx_hal_rcc.h"
#include "stm32n6xx_hal_cortex.h"
#include "stm32n6xx_hal_eth.h"

#define assert_param( expression )    ( ( void ) ( expression ) )

#endif /* STM32N6XX_HAL_CONF_H */
