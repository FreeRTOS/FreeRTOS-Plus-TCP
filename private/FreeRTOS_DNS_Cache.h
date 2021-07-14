#ifndef FREE_RTOS_DNS_CACHE_H
#define FREE_RTOS_DNS_CACHE_H

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"

/* Standard includes. */
#include <stdint.h>


uint32_t FreeRTOS_dnslookup( const char * pcHostName );

void FreeRTOS_dnsclear( void );

BaseType_t FreeRTOS_dns_update( const char * pcName,
                                uint32_t * pulIP,
                                uint32_t ulTTL);

BaseType_t FreeRTOS_ProcessDNSCache( const char * pcName,
                               uint32_t * pulIP,
                               uint32_t ulTTL,
                               BaseType_t xLookUp );
#if ( ipconfigUSE_DNS_CACHE == 1 ) || ( ipconfigDNS_USE_CALLBACKS == 1 )
size_t prvReadNameField( const uint8_t * pucByte,
                         size_t uxRemainingBytes,
                         char * pcName,
                         size_t uxDestLen );
#endif /* ipconfigUSE_DNS_CACHE || ipconfigDNS_USE_CALLBACKS */

#endif
