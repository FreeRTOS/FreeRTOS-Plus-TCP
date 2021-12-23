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
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "cbmc.h"

uint32_t FreeRTOS_dnslookup( const char * pcHostName );
Socket_t DNS_CreateSocket( TickType_t uxReadTimeout_ticks );
void DNS_CloseSocket( Socket_t xDNSSocket );
void DNS_ReadReply( Socket_t xDNSSocket,
                    struct freertos_sockaddr * xAddress,
                    struct dns_buffer * pxDNSBuf );
uint32_t DNS_SendRequest( const char * hostname,
                          TickType_t uxIdentifier,
                          Socket_t xDNSSocket,
                          struct freertos_sockaddr * xAddress,
                          struct dns_buffer * pxDNSBuf );
uint32_t DNS_ParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                            size_t xBufferLength,
                            BaseType_t xExpected );

/****************************************************************
* We abstract:
*
*   All kernel task scheduling functions since we are doing
*   sequential verification and the sequential verification of these
*   sequential primitives is done elsewhere.
*
*   Many methods in the FreeRTOS TCP API in stubs/freertos_api.c
*
*   DNS_ParseDNSReply proved memory safe elsewhere
*
*   prvCreateDNSMessage
*
* This proof assumes the length of pcHostName is bounded by
* MAX_HOSTNAME_LEN.  We have to bound this length because we have to
* bound the iterations of strcmp.
****************************************************************/

/****************************************************************
* Abstract DNS_ParseDNSReply proved memory safe in ParseDNSReply.
*
* We stub out his function to fill the payload buffer with
* unconstrained data and return an unconstrained size.
*
* The function under test uses only the return value of this
* function.
****************************************************************/

uint32_t DNS_ParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                            size_t xBufferLength,
                            BaseType_t xExpected )
{
    uint32_t size;

    __CPROVER_havoc_object( pucUDPPayloadBuffer );
    return size;
}

/****************************************************************
* Abstract  DNS_SendRequest
*
* We stub out this function with return constraint of true or false
*
****************************************************************/
uint32_t DNS_SendRequest( const char * hostname,
                          TickType_t uxIdentifier,
                          Socket_t xDNSSocket,
                          struct freertos_sockaddr * xAddress,
                          struct dns_buffer * pxDNSBuf )
{
    uint32_t ret;

    __CPROVER_assume( ret >= 0 );
    __CPROVER_assume( ret <= 1 );

    return ret;
}

/****************************************************************
* Abstract DNS_ReadReply
*
* We stub out this function which returned a dns_buffer filled with random data
*
****************************************************************/
void DNS_ReadReply( Socket_t xDNSSocket,
                    struct freertos_sockaddr * xAddress,
                    struct dns_buffer * pxDNSBuf )
{
    int len;

    pxDNSBuf->pucPayloadBuffer = safeMalloc( len );

    pxDNSBuf->uxPayloadLength = len;

    __CPROVER_assume( len < CBMC_MAX_OBJECT_SIZE );
    __CPROVER_assume( pxDNSBuf->pucPayloadBuffer != NULL );

    __CPROVER_havoc_slice( pxDNSBuf->pucUDPPayloadBuffer, pxDNSBuf->ulSize );
}


void DNS_CloseSocket( Socket_t xDNSSocket )
{
}

Socket_t DNS_CreateSocket( TickType_t uxReadTimeout_ticks )
{
    Socket_t sock;

    return sock;
}

uint32_t FreeRTOS_dnslookup( const char * pcHostName )
{
    int ret;

    __CPROVER_assume( ret < 0xFFFF );
    __CPROVER_assume( ret > 0 );

    return ret;
}


/****************************************************************
* Abstract prvCreateDNSMessage
*
* This function writes a header, a hostname, and a constant amount of
* data into the payload buffer, and returns the amount of data
* written.  This abstraction just fills the entire buffer with
* unconstrained data and returns and unconstrained length.
****************************************************************/

size_t prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                            const char * pcHostName,
                            TickType_t uxIdentifier )
{
    __CPROVER_havoc_object( pucUDPPayloadBuffer );
    size_t size;

    return size;
}

/****************************************************************
* The proof for FreeRTOS_gethostbyname.
****************************************************************/

void harness()
{
    size_t len;

    __CPROVER_assume( len <= MAX_HOSTNAME_LEN );
    char * pcHostName = safeMalloc( len );

    __CPROVER_assume( len > 0 ); /* prvProcessDNSCache strcmp */
    __CPROVER_assume( pcHostName != NULL );
    pcHostName[ len - 1 ] = NULL;

    FreeRTOS_gethostbyname( pcHostName );
}
