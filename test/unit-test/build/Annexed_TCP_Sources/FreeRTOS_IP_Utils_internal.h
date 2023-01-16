NetworkBufferDescriptor_t * prvPacketBuffer_to_NetworkBuffer( const void * pvBuffer,
                                                                     size_t uxOffset );

uintptr_t void_ptr_to_uintptr( const void * pvPointer );

BaseType_t prvChecksumProtocolChecks( size_t uxBufferLength,
                                             struct xPacketSummary * pxSet );

BaseType_t prvChecksumProtocolMTUCheck( struct xPacketSummary * pxSet );

void prvChecksumProtocolCalculate( BaseType_t xOutgoingPacket,
                                          const uint8_t * pucEthernetBuffer,
                                          struct xPacketSummary * pxSet );

void prvChecksumProtocolSetChecksum( BaseType_t xOutgoingPacket,
                                            const uint8_t * pucEthernetBuffer,
                                            size_t uxBufferLength,
                                            const struct xPacketSummary * pxSet );


#if ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 );

/**
 * @brief Create a DHCP event.
 *
 * @return pdPASS or pdFAIL, depending on whether xSendEventStructToIPTask();
 *         succeeded.
 * @param pxEndPoint: The end-point that needs DHCP.
 */
    BaseType_t xSendDHCPEvent( struct xNetworkEndPoint * pxEndPoint );
        IPStackEvent_t xEventMessage;
        const TickType_t uxDontBlock = 0U;

        #if ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 );
            eDHCPState_t uxOption = eGetDHCPState( pxEndPoint );
        #endif

        xEventMessage.eEventType = eDHCPEvent;

        /* MISRA Ref 11.6.1 [DHCP events and conversion to void] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-116 */
        /* coverity[misra_c_2012_rule_11_6_violation] */
        xEventMessage.pvData = ( void * ) pxEndPoint;
        #if ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 );
                pxEndPoint->xDHCPData.eExpectedState = uxOption;
            }
        #endif

        return xSendEventStructToIPTask( &xEventMessage, uxDontBlock );
    }
#endif /* if ( ipconfigUSE_DHCPv6 == 1 ) || ( ipconfigUSE_DHCP == 1 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Duplicate the given network buffer descriptor with a modified length.
 *
 * @param[in] pxNetworkBuffer: The network buffer to be duplicated.
 * @param[in] uxNewLength: The length for the new buffer.
 *
 * @return If properly duplicated, then the duplicate network buffer or else, NULL.
 */
NetworkBufferDescriptor_t * pxDuplicateNetworkBufferWithDescriptor( const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                    size_t uxNewLength );
NetworkBufferDescriptor_t * prvPacketBuffer_to_NetworkBuffer( const void * pvBuffer,
                                                                     size_t uxOffset );
uintptr_t void_ptr_to_uintptr( const void * pvPointer );
BaseType_t prvChecksumProtocolChecks( size_t uxBufferLength,
                                             struct xPacketSummary * pxSet );
BaseType_t prvChecksumProtocolMTUCheck( struct xPacketSummary * pxSet );
void prvChecksumProtocolCalculate( BaseType_t xOutgoingPacket,
                                          const uint8_t * pucEthernetBuffer,
                                          struct xPacketSummary * pxSet );
void prvChecksumProtocolSetChecksum( BaseType_t xOutgoingPacket,
                                            const uint8_t * pucEthernetBuffer,
                                            size_t uxBufferLength,
                                            const struct xPacketSummary * pxSet );
