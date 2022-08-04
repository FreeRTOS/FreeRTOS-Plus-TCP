/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "list.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DNS_Parser.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"
#include "IPTraceMacroDefaults.h"

#include "cbmc.h"

/****************************************************************
* Signature of function under test
****************************************************************/

uint32_t DNS_ParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                            size_t xBufferLength,
                            struct freertos_addrinfo ** ppxAddressInfo,
                            BaseType_t xExpected,
                            uint16_t usPort );

/****************************************************************
* Abstraction of DNS_ReadNameField proved in DNS_ReadNameField
****************************************************************/

size_t DNS_ReadNameField( ParseSet_t * pxSet,
                          size_t uxDestLen )
{
    __CPROVER_assert( NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE,
                      "NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE" );
    __CPROVER_assert( NAME_SIZE < CBMC_MAX_OBJECT_SIZE,
                      "NAME_SIZE < CBMC_MAX_OBJECT_SIZE" );
    __CPROVER_assert( NAME_SIZE >= 4,
                      "NAME_SIZE >= 4 required for good coverage." );


    /* Preconditions */
    __CPROVER_assert( pxSet->uxSourceBytesRemaining < CBMC_MAX_OBJECT_SIZE,
                      "ReadNameField: pxSet->uxSourceBytesRemaining < CBMC_MAX_OBJECT_SIZE)" );
    __CPROVER_assert( uxDestLen < CBMC_MAX_OBJECT_SIZE,
                      "ReadNameField: uxDestLen < CBMC_MAX_OBJECT_SIZE)" );

    __CPROVER_assert( pxSet->uxSourceBytesRemaining <= NETWORK_BUFFER_SIZE,
                      "ReadNameField: pxSet->uxSourceBytesRemaining <= NETWORK_BUFFER_SIZE)" );

    /* This precondition in the function contract for DNS_ReadNameField
     * fails because prvCheckOptions called DNS_ReadNameField with the
     * constant value 254.
     * __CPROVER_assert(uxDestLen <= NAME_SIZE,
     *       "ReadNameField: uxDestLen <= NAME_SIZE)");
     */

    __CPROVER_assert( pxSet->pucByte != NULL,
                      "ReadNameField:  pxSetpucByte != NULL )" );
    __CPROVER_assert( pxSet->pcName != NULL,
                      "ReadNameField:  pxSet->pcName != NULL )" );

    __CPROVER_assert( uxDestLen > 0,
                      "ReadNameField: uxDestLen > 0)" );

    /* Return value */
    size_t index;

    /* Postconditions */
    __CPROVER_assume( index <= ( uxDestLen + 1U ) && index <= pxSet->uxSourceBytesRemaining );

    return index;
}

/****************************************************************
* Abstraction of usChar2u16
****************************************************************/
uint16_t usChar2u16( const uint8_t * pucPtr )
{
    uint16_t ret;

    return ret;
}

/****************************************************************
* Abstraction of pxNew_AddrInfo
****************************************************************/
struct freertos_addrinfo * pxNew_AddrInfo( const char * pcName,
                                           BaseType_t xFamily,
                                           const uint8_t * pucAddress )
{
    struct freertos_addrinfo * ret;

    return ret;
}

/****************************************************************
* Abstraction of pxUDPPayloadBuffer_to_NetworkBuffer
****************************************************************/
NetworkBufferDescriptor_t * pxUDPPayloadBuffer_to_NetworkBuffer( const void * pvBuffer )
{
    NetworkBufferDescriptor_t * ret;

    return ret;
}

/****************************************************************
* Abstraction of xApplicationDNSQueryHook
****************************************************************/
BaseType_t xApplicationDNSQueryHook( struct xNetworkEndPoint * pxEndPoint,
                                     const char * pcName )
{
    BaseType_t ret;

    return ret;
}

/****************************************************************
* Abstraction of uxIPHeaderSizePacket
****************************************************************/
size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    size_t ret;

    return ret;
}

/****************************************************************
* Abstraction of pxResizeNetworkBufferWithDescriptor
****************************************************************/
NetworkBufferDescriptor_t * pxResizeNetworkBufferWithDescriptor( NetworkBufferDescriptor_t * pxDescriptor,
                                                                 size_t xNewSizeBytes )
{
    NetworkBufferDescriptor_t * ret;

    return ret;
}

/****************************************************************
* Abstraction of vSetField16
****************************************************************/
void vSetField16helper( uint8_t * pucBase,
                        size_t uxOffset,
                        uint16_t usValue )
{
}

/****************************************************************
* Abstraction of vSetField16
****************************************************************/
void vSetField32helper( uint8_t * pucBase,
                        size_t uxOffset,
                        uint32_t ulValue )
{
}

/****************************************************************
* Proof of DNS_ParseDNSReply
****************************************************************/

void harness()
{
    size_t uxBufferLength;
    BaseType_t xExpected;
    uint8_t * pucUDPPayloadBuffer = malloc( uxBufferLength );

    __CPROVER_assert( NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE,
                      "NETWORK_BUFFER_SIZE < CBMC_MAX_OBJECT_SIZE" );

    __CPROVER_assume( uxBufferLength < CBMC_MAX_OBJECT_SIZE );
    __CPROVER_assume( uxBufferLength <= NETWORK_BUFFER_SIZE );
    __CPROVER_assume( pucUDPPayloadBuffer != NULL );

    uint32_t index = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                                        uxBufferLength,
                                        xExpected );
}
