/* IPv4 multi-cast addresses range from 224.0.0.0.0 to 240.0.0.0. */
#define ipFIRST_MULTI_CAST_IPv4    0xE0000000UL
#define ipLAST_MULTI_CAST_IPv4     0xF0000000UL

/* The expected IP version and header length coded into the IP header itself. */
#define ipIP_VERSION_AND_HEADER_LENGTH_BYTE    ( ( uint8_t ) 0x45 )

void vTaskSetTimeOutState( TimeOut_t * const pxTimeOut )
{
}
/*-----------------------------------------------------------*/

BaseType_t xTaskCheckForTimeOut( TimeOut_t * const pxTimeOut,
                                 TickType_t * const pxTicksToWait )
{
    return pdTRUE;
}
/*-----------------------------------------------------------*/

void vTaskDelay( const TickType_t xTicksToDelay )
{
}
/*-----------------------------------------------------------*/

TickType_t xTaskGetTickCount( void )
{
    TickType_t xTicks;

    return xTicks;
}

/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t bReleaseAfterSend )
{
    return pdPASS;
}
/*-----------------------------------------------------------*/

NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    return NULL;
}
/*-----------------------------------------------------------*/

void vReleaseNetworkBufferAndDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
}
/*-----------------------------------------------------------*/
