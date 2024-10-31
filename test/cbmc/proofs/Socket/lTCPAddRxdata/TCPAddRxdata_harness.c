/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"

/* CBMC includes. */
#include "memory_assignments.c"

/****************************************************************
* Signature of function under test
****************************************************************/

StreamBuffer_t * __CPROVER_file_local_FreeRTOS_Sockets_c_prvTCPCreateStream( FreeRTOS_Socket_t * pxSocket,
                                                                             BaseType_t xIsInputStream );


void __CPROVER_file_local_FreeRTOS_Sockets_c_vTCPAddRxdata_Callback( FreeRTOS_Socket_t * pxSocket,
                                                                     const uint8_t * pcData,
                                                                     uint32_t ulByteCount );

void __CPROVER_file_local_FreeRTOS_Sockets_c_vTCPAddRxdata_Stored( FreeRTOS_Socket_t * pxSocket );

/* Abstraction of this functions allocate and return xWantedSize data. */
void * pvPortMallocLarge( size_t xWantedSize )
{
    return safeMalloc( xWantedSize );
}

size_t uxStreamBufferFrontSpace( const StreamBuffer_t * const pxBuffer )
{
    size_t uxReturn;

    return uxReturn;
}

BaseType_t xSendEventToIPTask( eIPEvent_t eEvent )
{
    BaseType_t xReturn;

    __CPROVER_assume( ( xReturn == pdTRUE ) || ( xReturn == pdFALSE ) );

    return xReturn;
}

void vTCPStateChange( FreeRTOS_Socket_t * pxSocket,
                      enum eTCP_STATE eTCPState )
{
}

size_t uxStreamBufferAdd( StreamBuffer_t * const pxBuffer,
                          size_t uxOffset,
                          const uint8_t * const pucData,
                          size_t uxByteCount )
{
    size_t uxReturn;

    __CPROVER_assert( __CPROVER_r_ok( pucData, uxByteCount ), "Data pointer must be valid to read" );
    __CPROVER_assume( uxReturn <= uxByteCount );

    return uxReturn;
}

void harness()
{
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
    size_t uxOffset;
    const uint8_t * pcData = NULL;
    uint32_t ulByteCount;

    /* This function expect socket to be not NULL, as it has been validated previously */
    __CPROVER_assume( pxSocket != NULL );

    /* Assume size of streams to be in the range of maximum supported size.*/
    __CPROVER_assume( pxSocket->u.xTCP.uxRxStreamSize >= 0 && pxSocket->u.xTCP.uxRxStreamSize < ipconfigTCP_RX_BUFFER_LENGTH );
    __CPROVER_assume( pxSocket->u.xTCP.uxTxStreamSize >= 0 && pxSocket->u.xTCP.uxTxStreamSize < ipconfigTCP_TX_BUFFER_LENGTH );

    /* ipconfigTCP_MSS is guaranteed not less than tcpMINIMUM_SEGMENT_LENGTH by FreeRTOSIPConfigDefaults.h */
    __CPROVER_assume( pxSocket->u.xTCP.usMSS >= tcpMINIMUM_SEGMENT_LENGTH );

    __CPROVER_assume( ulByteCount > 0U );
    pcData = safeMalloc( ulByteCount );
    __CPROVER_assume( pcData != NULL );

    lTCPAddRxdata( pxSocket, uxOffset, pcData, ulByteCount );
}
