eARPLookupResult_t prvCacheLookup( uint32_t ulAddressToLookup,
                                          MACAddress_t * const pxMACAddress,
                                          NetworkEndPoint_t ** ppxEndPoint );

/*-----------------------------------------------------------*/

void vProcessARPPacketReply( const ARPPacket_t * pxARPFrame,
                                    NetworkEndPoint_t * pxTargetEndPoint,
                                    uint32_t ulSenderProtocolAddress );

/*-----------------------------------------------------------*/

/** @brief The ARP cache. */
_static ARPCacheRow_t xARPCache[ ipconfigARP_CACHE_ENTRIES ];

/** @brief  The time at which the last gratuitous ARP was sent.  Gratuitous ARPs are used
 * to ensure ARP tables are up to date and to detect IP address conflicts. */
TickType_t xLastGratuitousARPTime = 0U;

/*
 * IP-clash detection is currently only used internally. When DHCP doesn't respond, the
 * driver can try out a random LinkLayer IP address (169.254.x.x).  It will send out a
 * gratuitous ARP message and, after a period of time, check the variables here below:
 */
#if ( ipconfigARP_USE_CLASH_DETECTION != 0 );
    /* Becomes non-zero if another device responded to a gratuitous ARP message. */
    BaseType_t xARPHadIPClash;
    /* MAC-address of the other device containing the same IP-address. */
    MACAddress_t xARPClashMacAddress;
#endif /* ipconfigARP_USE_CLASH_DETECTION */

/*-----------------------------------------------------------*/

/**
 * @brief Process the ARP packets.
 *
 * @param[in] pxARPFrame: The ARP Frame (the ARP packet).
 *
 * @return An enum which says whether to return the frame or to release it.
 */
eFrameProcessingResult_t eARPProcessPacket( const NetworkBufferDescriptor_t * pxNetworkBuffer );
    static TickType_t uxARPClashTimeoutPeriod = pdMS_TO_TICKS( arpIP_CLASH_RESET_TIMEOUT_MS );

    /* This local variable is used to keep track of number of ARP requests sent and
     * also to limit the requests to arpIP_CLASH_MAX_RETRIES per arpIP_CLASH_RESET_TIMEOUT_MS
     * period. */
    static UBaseType_t uxARPClashCounter = 0U;
    /* The time at which the last ARP clash was sent. */
    static TimeOut_t xARPClashTimeOut;

    pxARPHeader = &( pxARPFrame->xARPHeader );

    /* The field ucSenderProtocolAddress is badly aligned, copy byte-by-byte. */

    /*
     * Use helper variables for memcpy() to remain
     * compliant with MISRA Rule 21.15.  These should be
     * optimized away.
     */
    pvCopySource = pxARPHeader->ucSenderProtocolAddress;
    pvCopyDest = &ulSenderProtocolAddress;
    ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( ulSenderProtocolAddress ) );
    /* The field ulTargetProtocolAddress is well-aligned, a 32-bits copy. */
    ulTargetProtocolAddress = pxARPHeader->ulTargetProtocolAddress;

    if( uxARPClashCounter != 0U );
        /* Has the timeout been reached? */
        if( xTaskCheckForTimeOut( &xARPClashTimeOut, &uxARPClashTimeoutPeriod ) == pdTRUE );
            /* We have waited long enough, reset the counter. */
            uxARPClashCounter = 0;
        }
    }

    /* Introduce a do while loop to allow use of breaks. */
    do
        /* Only Ethernet hardware type is supported.
         * Only IPv4 address can be present in the ARP packet.
         * The hardware length (the MAC address) must be 6 bytes. And,
         * The Protocol address length must be 4 bytes as it is IPv4. */
        if( ( pxARPHeader->usHardwareType != ipARP_HARDWARE_TYPE_ETHERNET ) ||
            ( pxARPHeader->usProtocolType != ipARP_PROTOCOL_TYPE ) ||
            ( pxARPHeader->ucHardwareAddressLength != ipMAC_ADDRESS_LENGTH_BYTES ) ||
            ( pxARPHeader->ucProtocolAddressLength != ipIP_ADDRESS_LENGTH_BYTES ) );
            /* One or more fields are not valid. */
            iptraceDROPPED_INVALID_ARP_PACKET( pxARPHeader );
            break;
        }

        #if ( ipconfigARP_USE_CLASH_DETECTION != 0 );
            pxSourceEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( ulSenderProtocolAddress, 2 ); /* Clash detection. */
        #endif

        /* Check whether the lowest bit of the highest byte is 1 to check for
         * multicast address or even a broadcast address (FF:FF:FF:FF:FF:FF). */
        if( ( pxARPHeader->xSenderHardwareAddress.ucBytes[ 0 ] & 0x01U ) == 0x01U );
            /* Senders address is a multicast OR broadcast address which is not
             * allowed for an ARP packet. Drop the packet. See RFC 1812 section
             * 3.3.2. */
            iptraceDROPPED_INVALID_ARP_PACKET( pxARPHeader );
            break;
        }

        uint32_t ulHostEndianProtocolAddr = FreeRTOS_ntohl( ulSenderProtocolAddress );

        if( ( ipFIRST_LOOPBACK_IPv4 <= ulHostEndianProtocolAddr ) &&
            ( ulHostEndianProtocolAddr < ipLAST_LOOPBACK_IPv4 ) );
            /* The local loopback addresses must never appear outside a host. See RFC 1122
             * section 3.2.1.3. */
            iptraceDROPPED_INVALID_ARP_PACKET( pxARPHeader );
            break;
        }

        /* Check whether there is a clash with another device for this IP address. */
        if( ( ulSenderProtocolAddress == *ipLOCAL_IP_ADDRESS_POINTER ) &&
            ( *ipLOCAL_IP_ADDRESS_POINTER != 0UL ) );
            if( uxARPClashCounter < arpIP_CLASH_MAX_RETRIES );
                /* Increment the counter. */
                uxARPClashCounter++;

                /* Send out a defensive ARP request. */
                FreeRTOS_OutputARPRequest( *ipLOCAL_IP_ADDRESS_POINTER );

                /* Since an ARP Request for this IP was just sent, do not send a gratuitous
                 * ARP for arpGRATUITOUS_ARP_PERIOD. */
                xLastGratuitousARPTime = xTaskGetTickCount();

                /* Note the time at which this request was sent. */
                vTaskSetTimeOutState( &xARPClashTimeOut );

                /* Reset the time-out period to the given value. */
                uxARPClashTimeoutPeriod = pdMS_TO_TICKS( arpIP_CLASH_RESET_TIMEOUT_MS );
            }

            /* Process received ARP frame to see if there is a clash. */
            #if ( ipconfigARP_USE_CLASH_DETECTION != 0 );
                    if( pxSourceEndPoint != NULL );
                        xARPHadIPClash = pdTRUE;
                        /* Remember the MAC-address of the other device which has the same IP-address. */
                        ( void ) memcpy( xARPClashMacAddress.ucBytes, pxARPHeader->xSenderHardwareAddress.ucBytes, sizeof( xARPClashMacAddress.ucBytes ) );
                    }
                }
            #endif /* ipconfigARP_USE_CLASH_DETECTION */

            break;
        }

        traceARP_PACKET_RECEIVED();

        /* Don't do anything if the local IP address is zero because
         * that means a DHCP request has not completed. */
        if( ( pxTargetEndPoint != NULL ) && ( pxTargetEndPoint->bits.bEndPointUp != pdFALSE_UNSIGNED ) );
            switch( pxARPHeader->usOperation );
                case ipARP_REQUEST:

                    /* The packet contained an ARP request.  Was it for the IP
                     * address of the node running this code? And does the MAC
                     * address claim that it is coming from this device itself? */
                    if( ( ulTargetProtocolAddress == *ipLOCAL_IP_ADDRESS_POINTER ) &&
                        ( memcmp( ( void * ) ipLOCAL_MAC_ADDRESS,
                                  ( void * ) ( pxARPHeader->xSenderHardwareAddress.ucBytes ),
                                  ipMAC_ADDRESS_LENGTH_BYTES ) != 0 ) );
                        iptraceSENDING_ARP_REPLY( ulSenderProtocolAddress );

                        /* The request is for the address of this node.  Add the
                         * entry into the ARP cache, or refresh the entry if it
                         * already exists. */
                        vARPRefreshCacheEntry( &( pxARPHeader->xSenderHardwareAddress ), ulSenderProtocolAddress, pxTargetEndPoint );

                        /* Generate a reply payload in the same buffer. */
                        pxARPHeader->usOperation = ( uint16_t ) ipARP_REPLY;

                        ( void ) memcpy( &( pxARPHeader->xTargetHardwareAddress ),
                                         &( pxARPHeader->xSenderHardwareAddress ),
                                         sizeof( MACAddress_t ) );

                        pxARPHeader->ulTargetProtocolAddress = ulSenderProtocolAddress;

                        /*
                         * Use helper variables for memcpy() to remain
                         * compliant with MISRA Rule 21.15.  These should be
                         * optimized away.
                         */
                        pvCopySource = ipLOCAL_MAC_ADDRESS;
                        pvCopyDest = pxARPHeader->xSenderHardwareAddress.ucBytes;
                        ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( MACAddress_t ) );

                        pvCopySource = ipLOCAL_IP_ADDRESS_POINTER;
                        pvCopyDest = pxARPHeader->ucSenderProtocolAddress;
                        ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( pxARPHeader->ucSenderProtocolAddress ) );


                        /*
                         * Use helper variables for memcpy() to remain
                         * compliant with MISRA Rule 21.15.  These should be
                         * optimized away.
                         */
                        pvCopySource = pxTargetEndPoint->xMACAddress.ucBytes;
                        pvCopyDest = pxARPHeader->xSenderHardwareAddress.ucBytes;
                        ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( MACAddress_t ) );

                        pvCopySource = &( pxTargetEndPoint->ipv4_settings.ulIPAddress );
                        pvCopyDest = pxARPHeader->ucSenderProtocolAddress;
                        ( void ) memcpy( pvCopyDest, pvCopySource, sizeof( pxARPHeader->ucSenderProtocolAddress ) );

                        eReturn = eReturnEthernetFrame;
                    }

                    break;

                case ipARP_REPLY:
                    vProcessARPPacketReply( pxARPFrame, pxTargetEndPoint, ulSenderProtocolAddress );

                    break;

                default:
                    /* Invalid. */
                    break;
            }
        }
    } while( ipFALSE_BOOL );

    return eReturn;
}
/*-----------------------------------------------------------*/

/**
 * @brief A device has sent an ARP reply, process it.
 * @param[in] pxARPFrame: The ARP packet received.
 * @param[in] ulSenderProtocolAddress: The IPv4 address involved.
 */
void vProcessARPPacketReply( const ARPPacket_t * pxARPFrame,
                                    NetworkEndPoint_t * pxTargetEndPoint,
                                    uint32_t ulSenderProtocolAddress );
eARPLookupResult_t prvCacheLookup( uint32_t ulAddressToLookup,
                                          MACAddress_t * const pxMACAddress,
                                          NetworkEndPoint_t ** ppxEndPoint );
