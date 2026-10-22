/* SPDX-License-Identifier: MIT */

#ifndef STM32_NETWORK_INTERFACE_OVERRIDE_CONFIG_H
#define STM32_NETWORK_INTERFACE_OVERRIDE_CONFIG_H

#define ipconfigUSE_RMII                      0
#define ipconfigETHERNET_AN_ENABLE            0
#define ipconfigETHERNET_AUTO_CROSS_ENABLE    0
#define ipconfigETHERNET_CROSSED_LINK         0
#define ipconfigETHERNET_USE_100MB            0
#define ipconfigETHERNET_USE_FULL_DUPLEX      0

#define niEMAC_HANDLER_TASK_NAME              "EMAC_TEST"
#define niEMAC_HANDLER_TASK_PRIORITY          1U
#define niEMAC_HANDLER_TASK_STACK_SIZE        256U
#define niEMAC_TASK_MAX_BLOCK_TIME_MS         1U
#define niEMAC_TX_MAX_BLOCK_TIME_MS           2U
#define niEMAC_RX_MAX_BLOCK_TIME_MS           3U
#define niDESCRIPTOR_WAIT_TIME_MS             4U

#define niEMAC_TX_DESC_SECTION                ".TestTxDescriptors"
#define niEMAC_RX_DESC_SECTION                ".TestRxDescriptors"
#define niEMAC_BUFFERS_SECTION                ".TestEthBuffers"
#define niEMAC_USE_MPU                        0

#define ipconfigEMAC_TASK_HOOK()    do {} while( 0 )
#define iptraceSTM32_ETH_RX_DESC_USAGE( channel, descriptorsUsed ) \
        do {                                                               \
            ( void ) ( channel );                                          \
            ( void ) ( descriptorsUsed );                                  \
        } while( 0 )
#define iptraceSTM32_ETH_TX_DESC_USAGE( channel, descriptorsUsed ) \
        do {                                                               \
            ( void ) ( channel );                                          \
            ( void ) ( descriptorsUsed );                                  \
        } while( 0 )
#define iptraceSTM32_ETH_FATAL_ERROR( halError, dmaError, macError ) \
        do {                                                               \
            ( void ) ( halError );                                         \
            ( void ) ( dmaError );                                         \
            ( void ) ( macError );                                         \
        } while( 0 )

#endif /* STM32_NETWORK_INTERFACE_OVERRIDE_CONFIG_H */
