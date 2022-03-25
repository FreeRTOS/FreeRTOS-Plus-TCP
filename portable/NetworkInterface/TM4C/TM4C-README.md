# Ethernet Driver for TM4C129X MCUs
*JD Scott - jscott@hotstart.com*

This driver was written and tested using the Texas Instruments (TI) TM4C1294NCPDT microcontroller using version the TivaWare((C) TI) driver library. This MCU includes built-in MAC and PHY which this driver assumes is to be used.

This is a zero-copy driver uses the TivaWare ((C) TI) ROM function mapping macros, is intended for use with FreeRTOS+TCP BufferManagmeent_1, and is loosely modeled after the example lwIP Ethernet driver provided by TI in their TivaWare library. The driver utilizes the Ethernet (MAC) DMA engine.

## Known Issues
The configuration of vendor supplied tools and libraries used in this driver cause compiler warnings related to the Code Composer Studio ((C) TI) specific *pack_struct_start.h* and *pack_struct_end.h* port headers, though they appear to be benign. If there are suggestions for preventing these warnings, please let me know.

## Vendor Provided Version Numbers Used
The following versions for tools/libraries were used during development and testing of this driver:
- Code Composer Studio - 11.1.0.000111
- TI ARM Code Generation Tools ((C) Texas Instruments) (CGT) - 20.2.6.LTS
- TivaWare - 2.2.0.295
