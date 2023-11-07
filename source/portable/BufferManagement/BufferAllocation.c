/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"

/* The obtained network buffer must be large enough to hold a packet that might
 * replace the packet that was requested to be sent. */
#if ipconfigIS_ENABLED( ipconfigUSE_TCP )
    #define baMINIMAL_BUFFER_SIZE    TCP_PACKET_SIZE
#else
    #define baMINIMAL_BUFFER_SIZE    sizeof( ARPPacket_t )
#endif

/* Compile time assertion with zero runtime effects
 * it will assert on 'e' not being zero, as it tries to divide by it,
 * will also print the line where the error occurred in case of failure */
/* MISRA Ref 20.10.1 [Lack of sizeof operator and compile time error checking] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-2010 */
/* coverity[misra_c_2012_rule_20_10_violation] */
#if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES )
    #define ASSERT_CONCAT_( a, b )    a ## b
    #define ASSERT_CONCAT( a, b )     ASSERT_CONCAT_( a, b )
    #define STATIC_ASSERT( e ) \
    enum { ASSERT_CONCAT( assert_line_, __LINE__ ) = 1 / ( !!( e ) ) }

    STATIC_ASSERT( ipconfigETHERNET_MINIMUM_PACKET_BYTES <= baMINIMAL_BUFFER_SIZE );
#endif

#define baALIGNMENT_MASK    ( portBYTE_ALIGNMENT - 1U )
#define baADD_WILL_OVERFLOW( a, b ) ( ( a ) > ( SIZE_MAX - ( b ) ) )
#define baINTERRUPT_BUFFER_GET_THRESHOLD    ( 3 )

#if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE_CUSTOM_BUFFER_SIZE )
    #define BUFFER_SIZE ( ipTOTAL_ETHERNET_FRAME_SIZE + ipBUFFER_PADDING )
    #define BUFFER_SIZE_ALIGNED ( ( BUFFER_SIZE + portBYTE_ALIGNMENT ) & ~baALIGNMENT_MASK )
#endif

static NetworkBufferDescriptor_t xNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ];

static List_t xFreeBuffersList;

static UBaseType_t uxMinimumFreeNetworkBuffers = 0U;

static SemaphoreHandle_t xNetworkBufferSemaphore = NULL;

/*-----------------------------------------------------------*/

static BaseType_t xIsValidNetworkDescriptor( const NetworkBufferDescriptor_t * pxDesc )
{
    BaseType_t xReturn;

    const UBaseType_t offset = ( UBaseType_t ) ( ( ( const char * ) pxDesc ) - ( ( const char * ) xNetworkBuffers ) );
    const ptrdiff_t index = pxDesc - xNetworkBuffers;

    if( ( offset >= sizeof( xNetworkBuffers ) ) || ( ( offset % sizeof( xNetworkBuffers[ 0 ] ) ) != 0 ) )
    {
        xReturn = pdFALSE;
    }
    else if( ( index < 0 ) || ( ( UBaseType_t ) index > ( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 1 ) ) )
    {
    	xReturn = pdFALSE;
    }
    else
    {
    	xReturn = pdTRUE;
    }

    return xReturn;
}

/*-----------------------------------------------------------*/

static BaseType_t xIsFreeBuffer( const NetworkBufferDescriptor_t * pxDesc )
{
    return ( xIsValidNetworkDescriptor( pxDesc ) != pdFALSE ) && ( listIS_CONTAINED_WITHIN( &xFreeBuffersList, &( pxDesc->xBufferListItem ) ) != pdFALSE );
}

/*-----------------------------------------------------------*/

static NetworkBufferDescriptor_t * pxGetNetworkBuffer( void )
{
    NetworkBufferDescriptor_t * pxReturn = ( NetworkBufferDescriptor_t * ) listGET_OWNER_OF_HEAD_ENTRY( &xFreeBuffersList );

    if( xIsFreeBuffer( pxReturn ) != pdFALSE )
    {
        ( void ) uxListRemove( &( pxReturn->xBufferListItem ) );
    }
    else
    {
        pxReturn = NULL;
    }

    return pxReturn;
}

/*-----------------------------------------------------------*/

static BaseType_t xFreeNetworkBuffer( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    const BaseType_t xListItemAlreadyInFreeList = listIS_CONTAINED_WITHIN( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );

    if( xListItemAlreadyInFreeList == pdFALSE )
    {
        vListInsertEnd( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );
    }

    return xListItemAlreadyInFreeList;

}

/*-----------------------------------------------------------*/

static void vInitNetworkBuffer( NetworkBufferDescriptor_t * pxNetworkBuffer, size_t xRequestedSizeBytes )
{
    pxNetworkBuffer->xDataLength = xRequestedSizeBytes;
    pxNetworkBuffer->pxInterface = NULL;
    pxNetworkBuffer->pxEndPoint = NULL;

    #if ipconfigIS_ENABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE )
    {
        /* make sure the buffer is not linked */
        pxNetworkBuffer->pxNextBuffer = NULL;
    }
    #endif
}

/*-----------------------------------------------------------*/

static void vUpdateMinimumFreeNetworkBuffers( void )
{
    /* Reading UBaseType_t, no critical section needed. */
    const UBaseType_t uxCount = uxGetNumberOfFreeNetworkBuffers();

    /* For stats, latch the lowest number of network buffers since booting. */
    if( uxMinimumFreeNetworkBuffers > uxCount )
    {
        uxMinimumFreeNetworkBuffers = uxCount;
    }
}

/*-----------------------------------------------------------*/

UBaseType_t uxGetMinimumFreeNetworkBuffers( void )
{
    return uxMinimumFreeNetworkBuffers;
}

/*-----------------------------------------------------------*/

UBaseType_t uxGetNumberOfFreeNetworkBuffers( void )
{
    return listCURRENT_LIST_LENGTH( &xFreeBuffersList );
}

/*-----------------------------------------------------------*/

#if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE )

static uint8_t * pucGetNetworkBuffer( size_t * const pxRequestedSizeBytes )
{
    size_t xSize = *pxRequestedSizeBytes;

    if( xSize < baMINIMAL_BUFFER_SIZE )
    {
        /* Buffers must be at least large enough to hold a TCP-packet with
         * headers, or an ARP packet, in case TCP is not included. */
        xSize = baMINIMAL_BUFFER_SIZE;
    }

    BaseType_t xIntegerOverflowed = pdFALSE;

    /* Round up xSize to the nearest multiple of N bytes,
     * where N equals 'sizeof( size_t )'. */
    if( ( xSize & baALIGNMENT_MASK ) != 0U )
    {
        const size_t xBytesRequiredForAlignment = portBYTE_ALIGNMENT - ( xSize & baALIGNMENT_MASK );

        if( baADD_WILL_OVERFLOW( xSize, xBytesRequiredForAlignment ) == 0 )
        {
            xSize += xBytesRequiredForAlignment;
        }
        else
        {
            xIntegerOverflowed = pdTRUE;
        }
    }

    size_t xAllocatedBytes;

    if( baADD_WILL_OVERFLOW( xSize, ipBUFFER_PADDING ) == 0 )
    {
        xAllocatedBytes = xSize + ipBUFFER_PADDING;
    }
    else
    {
        xIntegerOverflowed = pdTRUE;
    }

    uint8_t * pucEthernetBuffer = NULL;

    if( ( xIntegerOverflowed == pdFALSE ) && ( xAllocatedBytes <= ( SIZE_MAX >> 1 ) ) )
    {
        *pxRequestedSizeBytes = xSize;

        /* Allocate a buffer large enough to store the requested Ethernet frame size
         * and a pointer to a network buffer structure (hence the addition of
         * ipBUFFER_PADDING bytes). */
        pucEthernetBuffer = ( uint8_t * ) pvPortMalloc( xAllocatedBytes );
        configASSERT( pucEthernetBuffer != NULL );

        if( pucEthernetBuffer != NULL )
        {
            /* Enough space is left at the start of the buffer to place a pointer to
             * the network buffer structure that references this Ethernet buffer.
             * Return a pointer to the start of the Ethernet buffer itself. */
            pucEthernetBuffer += ipBUFFER_PADDING;
        }
    }

    return pucEthernetBuffer;
}

#endif /* if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE ) */

/*-----------------------------------------------------------*/

#if ( ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE ) )

static void vReleaseNetworkBuffer( const uint8_t * const pucEthernetBuffer )
{
    /* There is space before the Ethernet buffer in which a pointer to the
     * network buffer that references this Ethernet buffer is stored.  Remove the
     * space before freeing the buffer. */
    if( pucEthernetBuffer != NULL )
    {
        const uint8_t * pucEthernetBufferCopy = pucEthernetBuffer - ipBUFFER_PADDING;
        vPortFree( ( void * ) pucEthernetBufferCopy );
    }
}

#endif /* if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE ) */

/*-----------------------------------------------------------*/

#if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE )

NetworkBufferDescriptor_t * pxResizeNetworkBufferWithDescriptor( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                                 size_t xNewSizeBytes )
{
    NetworkBufferDescriptor_t * pxNetworkBufferCopy = pxNetworkBuffer;
    size_t uxSizeBytes = xNewSizeBytes;

    if( baADD_WILL_OVERFLOW( uxSizeBytes, ipBUFFER_PADDING ) == 0 )
    {
        uxSizeBytes += ipBUFFER_PADDING;

        uint8_t * const pucBuffer = pucGetNetworkBuffer( &( uxSizeBytes ) );

        if( pucBuffer == NULL )
        {
            pxNetworkBufferCopy = NULL;
        }
        else
        {
            pxNetworkBufferCopy->xDataLength = uxSizeBytes;

            const size_t xOriginalLength = pxNetworkBufferCopy->xDataLength + ipBUFFER_PADDING;

            if( uxSizeBytes > xOriginalLength )
            {
                uxSizeBytes = xOriginalLength;
            }

            ( void ) memcpy( pucBuffer - ipBUFFER_PADDING,
                             pxNetworkBufferCopy->pucEthernetBuffer - ipBUFFER_PADDING,
                             uxSizeBytes );
            vReleaseNetworkBuffer( pxNetworkBufferCopy->pucEthernetBuffer );
            pxNetworkBufferCopy->pucEthernetBuffer = pucBuffer;
        }
    }
    else
    {
        pxNetworkBufferCopy = NULL;
    }

    return pxNetworkBufferCopy;
}

#endif /* if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE ) */

/*-----------------------------------------------------------*/

#if ipconfigIS_ENABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE ) && ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE_CUSTOM_ALLOCATE )

void vNetworkBufferAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    // __attribute__( ( section( ".EthBuffersSection" ), aligned( baALIGNMENT_BYTES ) ) );
    #if ipconfigIS_ENABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE_CUSTOM_BUFFER_SIZE )
        static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ uxBufferAllocFixedSize ] __attribute__( ( aligned( portBYTE_ALIGNMENT ) ) );
    #else
        static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ BUFFER_SIZE_ALIGNED ] __attribute__( ( aligned( portBYTE_ALIGNMENT ) ) );
    #endif

    for( size_t i = 0; i < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ++i )
    {
        pxNetworkBuffers[ i ].pucEthernetBuffer = &( ucNetworkPackets[ i ][ ipBUFFER_PADDING ] );
        *( ( uint32_t * ) &( ucNetworkPackets[ i ][ 0 ] ) ) = ( uint32_t ) ( &( pxNetworkBuffers[ i ] ) );
    }
}

#endif

/*-----------------------------------------------------------*/

BaseType_t xNetworkBuffersInitialise( void )
{
    BaseType_t xReturn = pdFAIL;

    if( xNetworkBufferSemaphore == NULL )
    {
        ipconfigBUFFER_ALLOC_INIT();

        #if ipconfigIS_ENABLED( configSUPPORT_STATIC_ALLOCATION )
        {
            static StaticSemaphore_t xNetworkBufferSemaphoreBuffer;
            xNetworkBufferSemaphore = xSemaphoreCreateCountingStatic(
                ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS,
                ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS,
                &xNetworkBufferSemaphoreBuffer );
        }
        #else
        {
            xNetworkBufferSemaphore = xSemaphoreCreateCounting(
                ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS,
                ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS );
        }
        #endif

        configASSERT( xNetworkBufferSemaphore != NULL );

        if( xNetworkBufferSemaphore != NULL )
        {
            #if ( configQUEUE_REGISTRY_SIZE > 0 )
            {
                vQueueAddToRegistry( xNetworkBufferSemaphore, "NetBufSem" );
            }
            #endif

            vListInitialise( &xFreeBuffersList );

            #if ipconfigIS_ENABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE )
            {
                vNetworkBufferAllocateRAMToBuffers( xNetworkBuffers );
            }
            #endif

            for( size_t i = 0U; i < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ++i )
            {
                NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffers[ i ];

                #if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE )
                {
                    pxNetworkBuffer->pucEthernetBuffer = NULL;
                }
                #endif

                ListItem_t * pxBufferListItem = &pxNetworkBuffer->xBufferListItem;
                vListInitialiseItem( pxBufferListItem );
                listSET_LIST_ITEM_OWNER( pxBufferListItem, pxNetworkBuffer );
                vListInsert( &xFreeBuffersList, pxBufferListItem );
            }

            uxMinimumFreeNetworkBuffers = ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;

            xReturn = pdPASS;
        }
    }

    return xReturn;
}

/*-----------------------------------------------------------*/

NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes, TickType_t xBlockTimeTicks )
{
    NetworkBufferDescriptor_t * pxReturn = NULL;

    #if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE )
        size_t xRequestedSizeBytesCopy = xRequestedSizeBytes;

        if( ( xRequestedSizeBytesCopy < ( size_t ) baMINIMAL_BUFFER_SIZE ) )
        {
            /* ARP packets can replace application packets, so the storage must be
             * at least large enough to hold an ARP. */
            xRequestedSizeBytesCopy = baMINIMAL_BUFFER_SIZE;
        }

        BaseType_t xIntegerOverflowed = pdFALSE;

        /* Add 2 bytes to xRequestedSizeBytesCopy and round up xRequestedSizeBytesCopy
         * to the nearest multiple of N bytes, where N equals 'sizeof( size_t )'. */
        if( baADD_WILL_OVERFLOW( xRequestedSizeBytesCopy, 2 ) == 0 )
        {
            xRequestedSizeBytesCopy += 2U;
        }
        else
        {
            xIntegerOverflowed = pdTRUE;
        }

        if( ( xRequestedSizeBytesCopy & baALIGNMENT_MASK ) != 0U )
        {
            const size_t xBytesRequiredForAlignment = portBYTE_ALIGNMENT - ( xRequestedSizeBytesCopy & baALIGNMENT_MASK );

            if( baADD_WILL_OVERFLOW( xRequestedSizeBytesCopy, xBytesRequiredForAlignment ) == 0 )
            {
                xRequestedSizeBytesCopy += xBytesRequiredForAlignment;
            }
            else
            {
                xIntegerOverflowed = pdTRUE;
            }
        }

        size_t xAllocatedBytes = 0;

        if( baADD_WILL_OVERFLOW( xRequestedSizeBytesCopy, ipBUFFER_PADDING ) == 0 )
        {
            xAllocatedBytes = xRequestedSizeBytesCopy + ipBUFFER_PADDING;
        }
        else
        {
            xIntegerOverflowed |= pdTRUE;
        }

        if( ( xIntegerOverflowed == pdFALSE ) && ( xAllocatedBytes <= ( SIZE_MAX >> 1 ) ) )
        {
    #endif /* if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE ) */

    if( xNetworkBufferSemaphore != NULL )
    {
        /* If there is a semaphore available, there is a network buffer available. */
        if( xSemaphoreTake( xNetworkBufferSemaphore, xBlockTimeTicks ) == pdPASS )
        {
            /* Protect the structure as it is accessed from tasks and interrupts. */
            ipconfigBUFFER_ALLOC_LOCK();
            {
                pxReturn = pxGetNetworkBuffer();
            }
            ipconfigBUFFER_ALLOC_UNLOCK();

            if( pxReturn != NULL )
            {
                vUpdateMinimumFreeNetworkBuffers();

                #if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE )
                {
                    configASSERT( pxReturn->pucEthernetBuffer == NULL );

                    if( xRequestedSizeBytesCopy > 0U )
                    {
                        /* Extra space is obtained so a pointer to the network buffer can
                        * be stored at the beginning of the buffer. */
                        pxReturn->pucEthernetBuffer = ( uint8_t * ) pvPortMalloc( xAllocatedBytes );

                        if( pxReturn->pucEthernetBuffer == NULL )
                        {
                            /* The attempt to allocate storage for the buffer payload failed,
                             * so the network buffer structure cannot be used and must be
                             * released. */
                            vReleaseNetworkBufferAndDescriptor( pxReturn );
                            pxReturn = NULL;
                        }
                        else
                        {
                            /* Store a pointer to the network buffer structure in the
                             * buffer storage area, then move the buffer pointer on past the
                             * stored pointer so the pointer value is not overwritten by the
                             * application when the buffer is used. */
                            /* MISRA Ref 11.3.1 [Misaligned access] */
                            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                            /* coverity[misra_c_2012_rule_11_3_violation] */
                            *( ( NetworkBufferDescriptor_t ** ) ( pxReturn->pucEthernetBuffer ) ) = pxReturn;
                            pxReturn->pucEthernetBuffer += ipBUFFER_PADDING;

                            /* Store the actual size of the allocated buffer, which may be
                             * greater than the original requested size. */
                            vInitNetworkBuffer( pxReturn, xRequestedSizeBytesCopy );
                        }
                    }
                }
                #else
                {
                    vInitNetworkBuffer( pxReturn, xRequestedSizeBytes );
                }
                #endif /* if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE ) */
            }
        }
    }

    #if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE )
        }
    #endif

    if( pxReturn == NULL )
    {
        iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER();
    }
    else
    {
        iptraceNETWORK_BUFFER_OBTAINED( pxReturn );
    }

    return pxReturn;
}

/*-----------------------------------------------------------*/

void vReleaseNetworkBufferAndDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    if( xIsValidNetworkDescriptor( pxNetworkBuffer ) != pdFALSE )
    {
        #if ipconfigIS_DISABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE )
        {
            /* Release the storage allocated to the buffer payload. */
            vReleaseNetworkBuffer( pxNetworkBuffer->pucEthernetBuffer );
            pxNetworkBuffer->pucEthernetBuffer = NULL;
            pxNetworkBuffer->xDataLength = 0U;
        }
        #endif

        BaseType_t xListItemAlreadyInFreeList;

        /* Ensure the buffer is returned to the list of free buffers before the
         * counting semaphore is 'given' to say a buffer is available. */
        ipconfigBUFFER_ALLOC_LOCK();
        {
            xListItemAlreadyInFreeList = xFreeNetworkBuffer( pxNetworkBuffer );
        }
        ipconfigBUFFER_ALLOC_UNLOCK();

        if( xListItemAlreadyInFreeList == pdFALSE )
        {
            if( xSemaphoreGive( xNetworkBufferSemaphore ) == pdPASS )
            {
                iptraceNETWORK_BUFFER_RELEASED( pxNetworkBuffer );
            }
        }
    }
}

/*-----------------------------------------------------------*/

#if ipconfigIS_ENABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE )

NetworkBufferDescriptor_t * pxNetworkBufferGetFromISR( size_t xRequestedSizeBytes )
{
    NetworkBufferDescriptor_t * pxReturn = NULL;

    if( xNetworkBufferSemaphore != NULL )
    {
        /* If there is a semaphore available then there is a buffer available, but,
         * as this is called from an interrupt, only take a buffer if there are at
         * least baINTERRUPT_BUFFER_GET_THRESHOLD buffers remaining.  This prevents,
         * to a certain degree at least, a rapidly executing interrupt exhausting
         * buffer and in so doing preventing tasks from continuing. */
        if( uxQueueMessagesWaitingFromISR( ( QueueHandle_t ) xNetworkBufferSemaphore ) > ( UBaseType_t ) baINTERRUPT_BUFFER_GET_THRESHOLD )
        {
            if( xSemaphoreTakeFromISR( xNetworkBufferSemaphore, NULL ) == pdPASS )
            {
                /* Protect the structure as it is accessed from tasks and interrupts. */
                ipconfigBUFFER_ALLOC_LOCK_FROM_ISR();
                {
                    pxReturn = pxGetNetworkBuffer();
                }
                ipconfigBUFFER_ALLOC_UNLOCK_FROM_ISR();

                if( pxReturn != NULL )
                {
                    vUpdateMinimumFreeNetworkBuffers();

                    vInitNetworkBuffer( pxReturn, xRequestedSizeBytes );
                }
            }
        }
    }

    if( pxReturn == NULL )
    {
        iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER_FROM_ISR();
    }
    else
    {
        iptraceNETWORK_BUFFER_OBTAINED_FROM_ISR( pxReturn );
    }

    return pxReturn;
}

#endif /* if ipconfigIS_ENABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE ) */

/*-----------------------------------------------------------*/

#if ipconfigIS_ENABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE )

BaseType_t xReleaseNetworkBufferFromISR( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    if( xIsValidNetworkDescriptor( pxNetworkBuffer ) != pdFALSE )
    {
        BaseType_t xListItemAlreadyInFreeList;

        /* Ensure the buffer is returned to the list of free buffers before the
         * counting semaphore is 'given' to say a buffer is available. */
        ipconfigBUFFER_ALLOC_LOCK_FROM_ISR();
        {
            xListItemAlreadyInFreeList = xFreeNetworkBuffer( pxNetworkBuffer );
        }
        ipconfigBUFFER_ALLOC_UNLOCK_FROM_ISR();

        if( xListItemAlreadyInFreeList == pdFALSE )
        {
            if( xSemaphoreGiveFromISR( xNetworkBufferSemaphore, &xHigherPriorityTaskWoken ) == pdPASS )
            {
                iptraceNETWORK_BUFFER_RELEASED( pxNetworkBuffer );
            }
        }
    }

    return xHigherPriorityTaskWoken;
}

#endif /* if ipconfigIS_ENABLED( ipconfigBUFFER_ALLOC_FIXED_SIZE ) */

/*-----------------------------------------------------------*/
