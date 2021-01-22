/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DHCP.h"
#include "FreeRTOS_Routing.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "cbmc.h"

/****************************************************************
* We abstract:
*
*   All kernel task scheduling functions since we are doing
*   sequential verification and the sequential verification of these
*   sequential primitives is done elsewhere.
*
*   Many methods in the FreeRTOS TCP API in stubs/freertos_api.c
*
*   prvParseDNSReply proved memory safe elsewhere
*
*   prvCreateDNSMessage
*
* This proof assumes the length of pcHostName is bounded by
* MAX_HOSTNAME_LEN.  We have to bound this length because we have to
* bound the iterations of strcmp.
****************************************************************/

NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    __CPROVER_assert(
        xRequestedSizeBytes + ipBUFFER_PADDING < CBMC_MAX_OBJECT_SIZE,
        "pxGetNetworkBufferWithDescriptor: request too big" );

   NetworkBufferDescriptor_t * pxReturn = nondet_bool() ? NULL : malloc( sizeof( * pxReturn ) );

   if( pxReturn != NULL )
   {
       pxReturn->pucEthernetBuffer = malloc( xRequestedSizeBytes + ipBUFFER_PADDING );

       if( pxReturn->pucEthernetBuffer != NULL )
       {
           pxReturn->xDataLength = xRequestedSizeBytes;
           pxReturn->pucEthernetBuffer += ipBUFFER_PADDING;
       }
       else
       {
           free(pxReturn);
           pxReturn = NULL;
       }
   }

   return pxReturn;
}

void vReleaseNetworkBufferAndDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    __CPROVER_assert( pxNetworkBuffer != NULL,
                      "Precondition: pxNetworkBuffer != NULL" );

    if( pxNetworkBuffer->pucEthernetBuffer != NULL )
    {
        pxNetworkBuffer->pucEthernetBuffer -= ipBUFFER_PADDING;
        free( pxNetworkBuffer->pucEthernetBuffer );
    }

    free( pxNetworkBuffer );
}

/****************************************************************
* Abstract prvParseDNSReply proved memory save in ParseDNSReply.
*
* We stub out his function to fill the payload buffer with
* unconstrained data and return an unconstrained size.
*
* The function under test uses only the return value of this
* function.
****************************************************************/
uint32_t __CPROVER_file_local_FreeRTOS_DNS_c_prvParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                                                               size_t xBufferLength,
                                                               struct freertos_addrinfo ** ppxAddressInfo,
                                                               BaseType_t xExpected )
{
    uint32_t size;

    __CPROVER_havoc_object( pucUDPPayloadBuffer );
    return size;
}


/****************************************************************
* Abstract prvCreateDNSMessage
*
* This function writes a header, a hostname, and a constant amount of
* data into the payload buffer, and returns the amount of data
* written.  This abstraction just fills the entire buffer with
* unconstrained data and returns and unconstrained length.
****************************************************************/

size_t __CPROVER_file_local_FreeRTOS_DNS_c_prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                                                                const char * pcHostName,
                                                                TickType_t uxIdentifier,
                                                                UBaseType_t uxHostType )
{
    __CPROVER_havoc_object( pucUDPPayloadBuffer );
    size_t size;

    return size;
}


/** A list of all network end-points.  Each element has a next pointer. */
extern struct xNetworkEndPoint * pxNetworkEndPoints;

/** A list of all network interfaces: */
extern struct xNetworkInterface * pxNetworkInterfaces;

void harness()
{
    size_t len;

    __CPROVER_assume( len <= MAX_HOSTNAME_LEN );
    char * pcHostName = safeMalloc( len );

    /* Assume that the list of interfaces/endpoints is not initialized.
     * Note: These variables are defined in FreeRTOS_Routing.c in global scope.
     *       They serve as a list to the network interfaces and the corresponding
     *       endpoints respectively. And are defined as NULL initially. */
    __CPROVER_assume( pxNetworkInterfaces == NULL );
    __CPROVER_assume( pxNetworkEndPoints == NULL );

    __CPROVER_assume( len > 0 ); /* prvProcessDNSCache strcmp */
    __CPROVER_assume( pcHostName != NULL );
    pcHostName[ len - 1 ] = NULL;

    FreeRTOS_gethostbyname( pcHostName );
}
