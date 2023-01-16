uint16_t prvGetPrivatePortNumber( BaseType_t xProtocol );

/*
 * Return the list item from within pxList that has an item value of
 * xWantedItemValue.  If there is no such list item return NULL.
 */
const ListItem_t * pxListFindListItemWithValue( const List_t * pxList,
                                                       TickType_t xWantedItemValue );

/*
 * Return pdTRUE only if pxSocket is valid and bound, as far as can be
 * determined.
 */
BaseType_t prvValidSocket( const FreeRTOS_Socket_t * pxSocket,
                                  BaseType_t xProtocol,
                                  BaseType_t xIsBound );

#if ( ipconfigUSE_TCP == 1 );

/*
 * Internal function prvSockopt_so_buffer(): sets FREERTOS_SO_SNDBUF or
 * FREERTOS_SO_RCVBUF properties of a socket.
 */
    static BaseType_t prvSockopt_so_buffer( FreeRTOS_Socket_t * pxSocket,
                                            int32_t lOptionName,
                                            const void * pvOptionValue );
#endif /* ipconfigUSE_TCP == 1 */

/*
 * Before creating a socket, check the validity of the parameters used
 * and find the size of the socket space, which is different for UDP and TCP
 */
BaseType_t prvDetermineSocketSize( BaseType_t xDomain,
                                          BaseType_t xType,
                                          BaseType_t xProtocol,
                                          size_t * pxSocketSize );

BaseType_t prvSocketBindAdd( FreeRTOS_Socket_t * pxSocket,
                                    const struct freertos_sockaddr * pxAddress,
                                    List_t * pxSocketList,
                                    BaseType_t xInternal );

NetworkBufferDescriptor_t * prvRecvFromWaitForPacket( FreeRTOS_Socket_t const * pxSocket,
                                                             BaseType_t xFlags,
                                                             EventBits_t * pxEventBits );

int32_t prvSendUDPPacket( const FreeRTOS_Socket_t * pxSocket,
                                 NetworkBufferDescriptor_t * pxNetworkBuffer,
                                 size_t uxTotalDataLength,
                                 BaseType_t xFlags,
                                 const struct freertos_sockaddr * pxDestinationAddress,
                                 TickType_t xTicksToWait,
                                 size_t uxPayloadOffset );

#if ( ipconfigUSE_TCP == 1 );
    static FreeRTOS_Socket_t * prvAcceptWaitClient( FreeRTOS_Socket_t * pxParentSocket,
                                                    struct freertos_sockaddr * pxAddress,
                                                    socklen_t * pxAddressLength );
#endif /* ( ipconfigUSE_TCP == 1 ) */

#if ( ipconfigUSE_TCP == 1 );

/*
 * Create a txStream or a rxStream, depending on the parameter 'xIsInputStream'
 */
    static StreamBuffer_t * prvTCPCreateStream( FreeRTOS_Socket_t * pxSocket,
                                                BaseType_t xIsInputStream );
#endif /* ipconfigUSE_TCP == 1 */

#if ( ipconfigUSE_TCP == 1 );

/*
 * Called from FreeRTOS_send(): some checks which will be done before
 * sending a TCP packed.
 */
    static int32_t prvTCPSendCheck( FreeRTOS_Socket_t * pxSocket,
                                    size_t uxDataLength );
#endif /* ipconfigUSE_TCP */

#if ( ipconfigUSE_TCP == 1 );

/*
 * When a child socket gets closed, make sure to update the child-count of the parent
 */
    static void prvTCPSetSocketCount( FreeRTOS_Socket_t const * pxSocketToDelete );
#endif /* ipconfigUSE_TCP == 1 */

#if ( ipconfigUSE_TCP == 1 );

/*
 * Called from FreeRTOS_connect(): make some checks and if allowed, send a
 * message to the IP-task to start connecting to a remote socket
 */
    static BaseType_t prvTCPConnectStart( FreeRTOS_Socket_t * pxSocket,
                                          struct freertos_sockaddr const * pxAddress );
#endif /* ipconfigUSE_TCP */

#if ( ipconfigUSE_TCP == 1 );

/*
 * Check if it makes any sense to wait for a connect event.
 * It may return: -EINPROGRESS, -EAGAIN, or 0 for OK.
 */
    static BaseType_t bMayConnect( FreeRTOS_Socket_t const * pxSocket );
#endif /* ipconfigUSE_TCP */

/** @brief Check if a socket is already bound to a 'random' port number,
 * if not, try bind it to port 0.
 */
BaseType_t prvMakeSureSocketIsBound( FreeRTOS_Socket_t * pxSocket );

#if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 );

/* Executed by the IP-task, it will check all sockets belonging to a set */
    static void prvFindSelectedSocket( SocketSelect_t * pxSocketSet );

#endif /* ipconfigSUPPORT_SELECT_FUNCTION == 1 */

#if ( ipconfigUSE_TCP == 1 );

/** @brief This routine will wait for data to arrive in the stream buffer.
 */
    static BaseType_t prvRecvWait( const FreeRTOS_Socket_t * pxSocket,
                                   EventBits_t * pxEventBits,
                                   BaseType_t xFlags );
#endif /* ( ipconfigUSE_TCP == 1 ) */

#if ( ipconfigUSE_TCP == 1 );

/** @brief Read the data from the stream buffer.
 */
    static BaseType_t prvRecvData( FreeRTOS_Socket_t * pxSocket,
                                   void * pvBuffer,
                                   size_t uxBufferLength,
                                   BaseType_t xFlags );
#endif /* ( ipconfigUSE_TCP == 1 ) */

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief This function tries to send TCP-data in a loop with a time-out.
 */
    static BaseType_t prvTCPSendLoop( FreeRTOS_Socket_t * pxSocket,
                                      const void * pvBuffer,
                                      size_t uxDataLength,
                                      BaseType_t xFlags );
#endif /* ( ipconfigUSE_TCP == 1 ) */

#if ( ipconfigUSE_CALLBACKS == 1 );

/**
 * @brief Set a callback function for either a TCP or a UDP socket.
 */
    BaseType_t prvSetOptionCallback( FreeRTOS_Socket_t * pxSocket,
                                     int32_t lOptionName,
                                     const void * pvOptionValue );
#endif /* ( ipconfigUSE_CALLBACKS == 1 ) */

#if ( ipconfigUSE_TCP != 0 );

/**
 * @brief Handle the socket option FREERTOS_SO_WIN_PROPERTIES.
 */
    static BaseType_t prvSetOptionTCPWindows( FreeRTOS_Socket_t * pxSocket,
                                              const void * pvOptionValue );
#endif /* ( ipconfigUSE_TCP != 0 ) */

#if ( ipconfigUSE_TCP != 0 );

/**
 * @brief Handle the socket option FREERTOS_SO_SET_LOW_HIGH_WATER.
 */
    static BaseType_t prvSetOptionLowHighWater( FreeRTOS_Socket_t * pxSocket,
                                                const void * pvOptionValue );
#endif /* ( ipconfigUSE_TCP != 0 ) */

#if ( ipconfigUSE_TCP != 0 );

/**
 * @brief Handle the socket option FREERTOS_SO_SET_FULL_SIZE.
 */
    static BaseType_t prvSetOptionSetFullSize( FreeRTOS_Socket_t * pxSocket,
                                               const void * pvOptionValue );

#endif /* ( ipconfigUSE_TCP != 0 ) */

#if ( ipconfigUSE_TCP != 0 );

/** @brief Handle the socket option FREERTOS_SO_STOP_RX. */
    static BaseType_t prvSetOptionStopRX( FreeRTOS_Socket_t * pxSocket,
                                          const void * pvOptionValue );

#endif /* ( ipconfigUSE_TCP != 0 ) */

/** @brief Handle the socket options FREERTOS_SO_RCVTIMEO and
 *         FREERTOS_SO_SNDTIMEO.
 */
void prvSetOptionTimeout( FreeRTOS_Socket_t * pxSocket,
                                 const void * pvOptionValue,
                                 BaseType_t xForSend );

#if ( ipconfigUSE_TCP != 0 );

/** @brief Handle the socket options FREERTOS_SO_CLOSE_AFTER_SEND.
 */
    static BaseType_t prvSetOptionCloseAfterSend( FreeRTOS_Socket_t * pxSocket,
                                                  const void * pvOptionValue );
#endif /* ( ipconfigUSE_TCP != 0 ) */

#if ( ipconfigUSE_TCP != 0 );

/**
 * @brief Handle the socket options FREERTOS_SO_REUSE_LISTEN_SOCKET.
 */
    static BaseType_t prvSetOptionReuseListenSocket( FreeRTOS_Socket_t * pxSocket,
                                                     const void * pvOptionValue );
#endif /* ipconfigUSE_TCP == 1 */

void prvInitialiseTCPFields( FreeRTOS_Socket_t * pxSocket,
                                    size_t uxSocketSize );

int32_t prvRecvFrom_CopyPacket( uint8_t * pucEthernetBuffer,
                                       void * pvBuffer,
                                       size_t uxBufferLength,
                                       BaseType_t xFlags,
                                       int32_t lDataLength );

int32_t prvSendTo_ActualSend( const FreeRTOS_Socket_t * pxSocket,
                                     const void * pvBuffer,
                                     size_t uxTotalDataLength,
                                     BaseType_t xFlags,
                                     const struct freertos_sockaddr * pxDestinationAddress,
                                     size_t uxPayloadOffset );

#if ( ipconfigUSE_TCP == 1 ) && ( ipconfigUSE_CALLBACKS == 1 );

/** @brief The application can attach callback functions to a socket. In this function,
 *         called by lTCPAddRxdata(), the TCP reception handler will be called. */
    static void vTCPAddRxdata_Callback( FreeRTOS_Socket_t * pxSocket,
                                        const uint8_t * pcData,
                                        uint32_t ulByteCount );
#endif

#if ( ipconfigUSE_TCP == 1 );
    static void vTCPAddRxdata_Stored( FreeRTOS_Socket_t * pxSocket );
#endif

#if ( ( ipconfigHAS_PRINTF != 0 ) && ( ipconfigUSE_TCP == 1 ) );
/** @brief A helper function of vTCPNetStat(), see below. */
    static void vTCPNetStat_TCPSocket( const FreeRTOS_Socket_t * pxSocket );
#endif

/*-----------------------------------------------------------*/

/** @brief The list that contains mappings between sockets and port numbers.
 *         Accesses to this list must be protected by critical sections of
 *         some kind.
 */
List_t xBoundUDPSocketsList;

#if ipconfigUSE_TCP == 1

/** @brief The list that contains mappings between sockets and port numbers.
 *         Accesses to this list must be protected by critical sections of
 *         some kind.
 */
    List_t xBoundTCPSocketsList;

#endif /* ipconfigUSE_TCP == 1 */

/*-----------------------------------------------------------*/

/**
 * @brief Check whether the socket is valid or not.
 *
 * @param[in] pxSocket: The socket being checked.
 * @param[in] xProtocol: The protocol for which the socket was created.
 * @param[in] xIsBound: pdTRUE when the socket should be bound, otherwise pdFALSE.
 *
 * @return If the socket is valid, then pdPASS is returned or else, pdFAIL
 *         is returned.
 */
BaseType_t prvValidSocket( const FreeRTOS_Socket_t * pxSocket,
                                  BaseType_t xProtocol,
                                  BaseType_t xIsBound );
BaseType_t prvDetermineSocketSize( BaseType_t xDomain,
                                          BaseType_t xType,
                                          BaseType_t xProtocol,
                                          size_t * pxSocketSize );
    static void prvInitialiseTCPFields( FreeRTOS_Socket_t * pxSocket,
                                        size_t uxSocketSize );
        ( void ) uxSocketSize;
        /* Lint wants at least a comment, in case the macro is empty. */
        iptraceMEM_STATS_CREATE( tcpSOCKET_TCP, pxSocket, uxSocketSize + sizeof( StaticEventGroup_t ) );
        /* StreamSize is expressed in number of bytes */
        /* Round up buffer sizes to nearest multiple of MSS */
        pxSocket->u.xTCP.usMSS = ( uint16_t ) ipconfigTCP_MSS;
        pxSocket->u.xTCP.uxRxStreamSize = ( size_t ) ipconfigTCP_RX_BUFFER_LENGTH;
        pxSocket->u.xTCP.uxTxStreamSize = ( size_t ) FreeRTOS_round_up( ipconfigTCP_TX_BUFFER_LENGTH, ipconfigTCP_MSS );
        /* Use half of the buffer size of the TCP windows */
        #if ( ipconfigUSE_TCP_WIN == 1 );
                pxSocket->u.xTCP.uxRxWinSize = FreeRTOS_max_size_t( 1U, ( pxSocket->u.xTCP.uxRxStreamSize / 2U ) / ipconfigTCP_MSS );
                pxSocket->u.xTCP.uxTxWinSize = FreeRTOS_max_size_t( 1U, ( pxSocket->u.xTCP.uxTxStreamSize / 2U ) / ipconfigTCP_MSS );
            }
        #else
                pxSocket->u.xTCP.uxRxWinSize = 1U;
                pxSocket->u.xTCP.uxTxWinSize = 1U;
            }
        #endif

        /* The above values are just defaults, and can be overridden by
         * calling FreeRTOS_setsockopt().  No buffers will be allocated until a
         * socket is connected and data is exchanged. */
    }
#endif /* ( ipconfigUSE_TCP == 1 ) */
/*-----------------------------------------------------------*/

/**
 * @brief allocate and initialise a socket.
 *
 * @param[in] xDomain: The domain in which the socket should be created.
 * @param[in] xType: The type of the socket.
 * @param[in] xProtocol: The protocol of the socket.
 *
 * @return FREERTOS_INVALID_SOCKET if the allocation failed, or if there was
 *         a parameter error, otherwise a valid socket.
 */
Socket_t FreeRTOS_socket( BaseType_t xDomain,
                          BaseType_t xType,
                          BaseType_t xProtocol );
    static void prvFindSelectedSocket( SocketSelect_t * pxSocketSet );
        IPStackEvent_t xSelectEvent;

        #if ( ipconfigSELECT_USES_NOTIFY != 0 );
            SocketSelectMessage_t xSelectMessage;
        #endif

        xSelectEvent.eEventType = eSocketSelectEvent;
        #if ( ipconfigSELECT_USES_NOTIFY != 0 );
                xSelectMessage.pxSocketSet = pxSocketSet;
                xSelectMessage.xTaskhandle = xTaskGetCurrentTaskHandle();
                xSelectEvent.pvData = &( xSelectMessage );
            }
        #else
                xSelectEvent.pvData = pxSocketSet;

                /* while the IP-task works on the request, the API will block on
                 * 'eSELECT_CALL_IP'.  So clear it first. */
                ( void ) xEventGroupClearBits( pxSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP );
            }
        #endif /* if ( ipconfigSELECT_USES_NOTIFY != 0 ) */

        /* Now send the socket select event */
        if( xSendEventStructToIPTask( &xSelectEvent, ( TickType_t ) portMAX_DELAY ) == pdFAIL );
            /* Oops, we failed to wake-up the IP task. No use to wait for it. */
            FreeRTOS_debug_printf( ( "prvFindSelectedSocket: failed\n" ) );
        }
        else
            /* As soon as the IP-task is ready, it will set 'eSELECT_CALL_IP' to
             * wakeup the calling API */
            #if ( ipconfigSELECT_USES_NOTIFY != 0 );
                    ( void ) ulTaskNotifyTake( pdFALSE, portMAX_DELAY );
                }
            #else
                    ( void ) xEventGroupWaitBits( pxSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdTRUE, pdFALSE, portMAX_DELAY );
                }
            #endif
        }
    }


#endif /* ipconfigSUPPORT_SELECT_FUNCTION == 1 */
/*-----------------------------------------------------------*/

/**
 * @brief : called from FreeRTOS_recvfrom(). This function waits for an incoming
 *          UDP packet, or until a time-out occurs.
 * @param[in] pxSocket : The socket that receives UDP packets.
 * @param[in] xFlags : The flags as passed to FreeRTOS_recvfrom().
 * @param[in,out] pxEventBits : The last even received in this function,
 *                              either eSOCKET_INTR or eSOCKET_RECEIVE.
 */
NetworkBufferDescriptor_t * prvRecvFromWaitForPacket( FreeRTOS_Socket_t const * pxSocket,
                                                             BaseType_t xFlags,
                                                             EventBits_t * pxEventBits );
int32_t prvRecvFrom_CopyPacket( uint8_t * pucEthernetBuffer,
                                       void * pvBuffer,
                                       size_t uxBufferLength,
                                       BaseType_t xFlags,
                                       int32_t lDataLength );
BaseType_t prvMakeSureSocketIsBound( FreeRTOS_Socket_t * pxSocket );
int32_t prvSendUDPPacket( const FreeRTOS_Socket_t * pxSocket,
                                 NetworkBufferDescriptor_t * pxNetworkBuffer,
                                 size_t uxTotalDataLength,
                                 BaseType_t xFlags,
                                 const struct freertos_sockaddr * pxDestinationAddress,
                                 TickType_t xTicksToWait,
                                 size_t uxPayloadOffset );
int32_t prvSendTo_ActualSend( const FreeRTOS_Socket_t * pxSocket,
                                     const void * pvBuffer,
                                     size_t uxTotalDataLength,
                                     BaseType_t xFlags,
                                     const struct freertos_sockaddr * pxDestinationAddress,
                                     size_t uxPayloadOffset );
BaseType_t prvSocketBindAdd( FreeRTOS_Socket_t * pxSocket,
                                    const struct freertos_sockaddr * pxAddress,
                                    List_t * pxSocketList,
                                    BaseType_t xInternal );
    static void prvTCPSetSocketCount( FreeRTOS_Socket_t const * pxSocketToDelete );
        const ListItem_t * pxIterator;

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        const ListItem_t * pxEnd = ( ( const ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );
        FreeRTOS_Socket_t * pxOtherSocket;
        uint16_t usLocalPort = pxSocketToDelete->usLocalPort;

        if( pxSocketToDelete->u.xTCP.eTCPState == eTCP_LISTEN );
            pxIterator = listGET_NEXT( pxEnd );

            while( pxIterator != pxEnd );
                pxOtherSocket = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );

                /* This needs to be done here, before calling vSocketClose. */
                pxIterator = listGET_NEXT( pxIterator );

                if( ( pxOtherSocket->u.xTCP.eTCPState != eTCP_LISTEN ) &&
                    ( pxOtherSocket->usLocalPort == usLocalPort ) &&
                    ( ( pxOtherSocket->u.xTCP.bits.bPassQueued != pdFALSE_UNSIGNED ) ||
                      ( pxOtherSocket->u.xTCP.bits.bPassAccept != pdFALSE_UNSIGNED ) ) );
                    /* MISRA Ref 17.2.1 [Sockets and limited recursion] */
                    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-172 */
                    /* coverity[misra_c_2012_rule_17_2_violation] */
                    /* coverity[recursive_step] */
                    ( void ) vSocketClose( pxOtherSocket );
                }
            }
        }
        else
            for( pxIterator = listGET_NEXT( pxEnd );
                 pxIterator != pxEnd;
                 pxIterator = listGET_NEXT( pxIterator ) );
                pxOtherSocket = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );

                if( ( pxOtherSocket->u.xTCP.eTCPState == eTCP_LISTEN ) &&
                    ( pxOtherSocket->usLocalPort == usLocalPort ) &&
                    ( pxOtherSocket->u.xTCP.usChildCount != 0U ) );
                    pxOtherSocket->u.xTCP.usChildCount--;
                    FreeRTOS_debug_printf( ( "Lost: Socket %u now has %u / %u child%s\n",
                                             pxOtherSocket->usLocalPort,
                                             pxOtherSocket->u.xTCP.usChildCount,
                                             pxOtherSocket->u.xTCP.usBacklog,
                                             ( pxOtherSocket->u.xTCP.usChildCount == 1U ) ? "" : "ren" ) );
                    break;
                }
            }
        }
    }


#endif /* ipconfigUSE_TCP == 1 */

/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Set the value of receive/send buffer after some preliminary checks.
 *
 * @param[in] pxSocket: The socket whose options are being set.
 * @param[in] lOptionName: The option name: either FREERTOS_SO_SNDBUF or
 *                         FREERTOS_SO_SNDBUF.
 * @param[in] pvOptionValue: The value of the option being set.
 *
 * @return If there is no error, then 0 is returned. Or a negative errno
 *         value is returned.
 */
    static BaseType_t prvSockopt_so_buffer( FreeRTOS_Socket_t * pxSocket,
                                            int32_t lOptionName,
                                            const void * pvOptionValue );
        uint32_t ulNewValue;
        BaseType_t xReturn;

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP );
            FreeRTOS_debug_printf( ( "Set SO_%sBUF: wrong socket type\n",
                                     ( lOptionName == FREERTOS_SO_SNDBUF ) ? "SND" : "RCV" ) );
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }
        else if( ( ( lOptionName == FREERTOS_SO_SNDBUF ) && ( pxSocket->u.xTCP.txStream != NULL ) ) ||
                 ( ( lOptionName == FREERTOS_SO_RCVBUF ) && ( pxSocket->u.xTCP.rxStream != NULL ) ) );
            FreeRTOS_debug_printf( ( "Set SO_%sBUF: buffer already created\n",
                                     ( lOptionName == FREERTOS_SO_SNDBUF ) ? "SND" : "RCV" ) );
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }
        else
            ulNewValue = *( ipPOINTER_CAST( const uint32_t *, pvOptionValue ) );

            if( lOptionName == FREERTOS_SO_SNDBUF );
                /* Round up to nearest MSS size */
                ulNewValue = FreeRTOS_round_up( ulNewValue, ( uint32_t ) pxSocket->u.xTCP.usMSS );
                pxSocket->u.xTCP.uxTxStreamSize = ulNewValue;
            }
            else
                pxSocket->u.xTCP.uxRxStreamSize = ulNewValue;
            }

            xReturn = 0;
        }

        return xReturn;
    }
#endif /* ipconfigUSE_TCP == 1 */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_CALLBACKS == 1 );

/**
 * @brief Set a callback function for either a TCP or a UDP socket.
 *        The callback function will be called on-connect, on-send
 *        or on-receive.
 *
 * @param[in] pxSocket: The socket whose options are being set.
 * @param[in] lOptionName: The option name like FREERTOS_SO_xxx_HANDLER.
 * @param[in] pvOptionValue: A pointer to a 'F_TCP_UDP_Handler_t',
 *                           which defines the handler.
 *
 * @return If there is no error, then 0 is returned. Or a negative errno
 *         value is returned.
 */
    BaseType_t prvSetOptionCallback( FreeRTOS_Socket_t * pxSocket,
                                     int32_t lOptionName,
                                     const void * pvOptionValue );
        BaseType_t xReturn = 0;

        #if ( ipconfigUSE_TCP == 1 );
                UBaseType_t uxProtocol;

                if( ( lOptionName == FREERTOS_SO_UDP_RECV_HANDLER ) ||
                    ( lOptionName == FREERTOS_SO_UDP_SENT_HANDLER ) );
                    uxProtocol = ( UBaseType_t ) FREERTOS_IPPROTO_UDP;
                }
                else
                    uxProtocol = ( UBaseType_t ) FREERTOS_IPPROTO_TCP;
                }

                if( pxSocket->ucProtocol != ( uint8_t ) uxProtocol );
                    xReturn = -pdFREERTOS_ERRNO_EINVAL;
                }
            }
        #else /* if ( ipconfigUSE_TCP == 1 ) */
                /* No need to check if the socket has the right
                 * protocol, because only UDP sockets can be created. */
            }
        #endif /* ipconfigUSE_TCP */

        if( xReturn == 0 );
            switch( lOptionName );
                #if ipconfigUSE_TCP == 1
                    case FREERTOS_SO_TCP_CONN_HANDLER:
                        pxSocket->u.xTCP.pxHandleConnected = ( ( const F_TCP_UDP_Handler_t * ) pvOptionValue )->pxOnTCPConnected;
                        break;

                    case FREERTOS_SO_TCP_RECV_HANDLER:
                        pxSocket->u.xTCP.pxHandleReceive = ( ( const F_TCP_UDP_Handler_t * ) pvOptionValue )->pxOnTCPReceive;
                        break;

                    case FREERTOS_SO_TCP_SENT_HANDLER:
                        pxSocket->u.xTCP.pxHandleSent = ( ( const F_TCP_UDP_Handler_t * ) pvOptionValue )->pxOnTCPSent;
                        break;
                #endif /* ipconfigUSE_TCP */
                case FREERTOS_SO_UDP_RECV_HANDLER:
                    pxSocket->u.xUDP.pxHandleReceive = ( ( const F_TCP_UDP_Handler_t * ) pvOptionValue )->pxOnUDPReceive;
                    break;

                case FREERTOS_SO_UDP_SENT_HANDLER:
                    pxSocket->u.xUDP.pxHandleSent = ( ( const F_TCP_UDP_Handler_t * ) pvOptionValue )->pxOnUDPSent;
                    break;

                default:
                    xReturn = -pdFREERTOS_ERRNO_EINVAL;
                    break;
            }
        }

        return xReturn;
    }
#endif /* ( ipconfigUSE_CALLBACKS == 1 ) */
/*-----------------------------------------------------------*/


#if ( ipconfigUSE_TCP != 0 );

/**
 * @brief Handle the socket option FREERTOS_SO_WIN_PROPERTIES, which sets
 *        the sizes of the TCP windows and the sizes of the stream buffers.
 *
 * @param[in] pxSocket: The socket whose options are being set.
 * @param[in] pvOptionValue: The pointer that is passed by the application.
 */
    static BaseType_t prvSetOptionTCPWindows( FreeRTOS_Socket_t * pxSocket,
                                              const void * pvOptionValue );
        BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;
        const WinProperties_t * pxProps;

        do
            IPTCPSocket_t * pxTCP = &( pxSocket->u.xTCP );

            if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP );
                FreeRTOS_debug_printf( ( "Set SO_WIN_PROP: wrong socket type\n" ) );
                break; /* will return -pdFREERTOS_ERRNO_EINVAL */
            }

            if( ( pxTCP->txStream != NULL ) || ( pxTCP->rxStream != NULL ) );
                FreeRTOS_debug_printf( ( "Set SO_WIN_PROP: buffer already created\n" ) );
                break; /* will return -pdFREERTOS_ERRNO_EINVAL */
            }

            pxProps = ipPOINTER_CAST( const WinProperties_t *, pvOptionValue );

            /* Validity of txStream will be checked by the function below. */
            xReturn = prvSockopt_so_buffer( pxSocket, FREERTOS_SO_SNDBUF, &( pxProps->lTxBufSize ) );

            if( xReturn != 0 );
                break; /* will return an error. */
            }

            xReturn = prvSockopt_so_buffer( pxSocket, FREERTOS_SO_RCVBUF, &( pxProps->lRxBufSize ) );

            if( xReturn != 0 );
                break; /* will return an error. */
            }

            #if ( ipconfigUSE_TCP_WIN == 1 );
                    pxTCP->uxRxWinSize = ( uint32_t ) pxProps->lRxWinSize; /* Fixed value: size of the TCP reception window */
                    pxTCP->uxTxWinSize = ( uint32_t ) pxProps->lTxWinSize; /* Fixed value: size of the TCP transmit window */
                }
            #else
                    pxTCP->uxRxWinSize = 1U;
                    pxTCP->uxTxWinSize = 1U;
                }
            #endif

            /* In case the socket has already initialised its tcpWin,
             * adapt the window size parameters */
            if( pxTCP->xTCPWindow.u.bits.bHasInit != pdFALSE_UNSIGNED );
                pxTCP->xTCPWindow.xSize.ulRxWindowLength = ( uint32_t ) ( pxTCP->uxRxWinSize * pxTCP->usMSS );
                pxTCP->xTCPWindow.xSize.ulTxWindowLength = ( uint32_t ) ( pxTCP->uxTxWinSize * pxTCP->usMSS );
            }
        }
        while( ipFALSE_BOOL );

        return xReturn;
    }
#endif /* ( ipconfigUSE_TCP != 0 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP != 0 );

/**
 * @brief Handle the socket option FREERTOS_SO_SET_LOW_HIGH_WATER, which sets
 *        the low- and the high-water values for TCP reception. Useful when
 *        streaming music.
 *
 * @param[in] pxSocket: The socket whose options are being set.
 * @param[in] pvOptionValue: The pointer that is passed by the application.
 */
    static BaseType_t prvSetOptionLowHighWater( FreeRTOS_Socket_t * pxSocket,
                                                const void * pvOptionValue );
        BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;
        const LowHighWater_t * pxLowHighWater = ipPOINTER_CAST( const LowHighWater_t *, pvOptionValue );

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP );
            /* It is not allowed to access 'pxSocket->u.xTCP'. */
            FreeRTOS_debug_printf( ( "FREERTOS_SO_SET_LOW_HIGH_WATER: wrong socket type\n" ) );
        }
        else if( ( pxLowHighWater->uxLittleSpace >= pxLowHighWater->uxEnoughSpace ) ||
                 ( pxLowHighWater->uxEnoughSpace > pxSocket->u.xTCP.uxRxStreamSize ) );
            /* Impossible values. */
            FreeRTOS_debug_printf( ( "FREERTOS_SO_SET_LOW_HIGH_WATER: bad values\n" ) );
        }
        else
            /* Send a STOP when buffer space drops below 'uxLittleSpace' bytes. */
            pxSocket->u.xTCP.uxLittleSpace = pxLowHighWater->uxLittleSpace;
            /* Send a GO when buffer space grows above 'uxEnoughSpace' bytes. */
            pxSocket->u.xTCP.uxEnoughSpace = pxLowHighWater->uxEnoughSpace;
            xReturn = 0;
        }

        return xReturn;
    }
#endif /* ( ipconfigUSE_TCP != 0 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP != 0 );

/**
 * @brief Handle the socket option FREERTOS_SO_SET_FULL_SIZE.
 *        When enabled, the IP-stack will only send packets when
 *        there are at least MSS bytes to send.
 *
 * @param[in] pxSocket: The socket whose options are being set.
 * @param[in] pvOptionValue: The option name like FREERTOS_SO_xxx_HANDLER.
 */
    static BaseType_t prvSetOptionSetFullSize( FreeRTOS_Socket_t * pxSocket,
                                               const void * pvOptionValue );
        BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;

        if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP );
            if( *( ( const BaseType_t * ) pvOptionValue ) != 0 );
                pxSocket->u.xTCP.xTCPWindow.u.bits.bSendFullSize = pdTRUE_UNSIGNED;
            }
            else
                pxSocket->u.xTCP.xTCPWindow.u.bits.bSendFullSize = pdFALSE_UNSIGNED;
            }

            if( ( pxSocket->u.xTCP.eTCPState >= eESTABLISHED ) &&
                ( FreeRTOS_outstanding( pxSocket ) != 0 ) );
                /* There might be some data in the TX-stream, less than full-size,
                 * which equals a MSS.  Wake-up the IP-task to check this. */
                pxSocket->u.xTCP.usTimeout = 1U;
                ( void ) xSendEventToIPTask( eTCPTimerEvent );
            }

            xReturn = 0;
        }

        return xReturn;
    }
#endif /* ( ipconfigUSE_TCP != 0 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP != 0 );

/**
 * @brief Handle the socket option FREERTOS_SO_STOP_RX.
 *        Used in applications with streaming audio: tell the peer
 *        to stop or continue sending data.
 *
 * @param[in] pxSocket: The TCP socket used for the connection.
 * @param[in] pvOptionValue: The option name like FREERTOS_SO_xxx_HANDLER.
 */
    static BaseType_t prvSetOptionStopRX( FreeRTOS_Socket_t * pxSocket,
                                          const void * pvOptionValue );
        BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;

        if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP );
            if( *( ( const BaseType_t * ) pvOptionValue ) != 0 );
                pxSocket->u.xTCP.bits.bRxStopped = pdTRUE_UNSIGNED;
            }
            else
                pxSocket->u.xTCP.bits.bRxStopped = pdFALSE_UNSIGNED;
            }

            pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
            pxSocket->u.xTCP.usTimeout = 1U; /* to set/clear bRxStopped */
            ( void ) xSendEventToIPTask( eTCPTimerEvent );
            xReturn = 0;
        }

        return xReturn;
    }
#endif /* ( ipconfigUSE_TCP != 0 ) */
/*-----------------------------------------------------------*/


/**
 * @brief Handle the socket options FREERTOS_SO_RCVTIMEO and
 *        FREERTOS_SO_SNDTIMEO.
 *        Used in applications with streaming audio: tell the peer
 *        to stop or continue sending data.
 *
 * @param[in] pxSocket: The TCP socket used for the connection.
 * @param[in] pvOptionValue: The option name like FREERTOS_SO_xxx_HANDLER.
 * @param[in] xForSend: when true, handle 'FREERTOS_SO_SNDTIMEO',
 *            otherwise handle the option `FREERTOS_SO_RCVTIMEO`.
 */
void prvSetOptionTimeout( FreeRTOS_Socket_t * pxSocket,
                                 const void * pvOptionValue,
                                 BaseType_t xForSend );
    static BaseType_t prvSetOptionReuseListenSocket( FreeRTOS_Socket_t * pxSocket,
                                                     const void * pvOptionValue );
        BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;

        if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP );
            if( *( ( const BaseType_t * ) pvOptionValue ) != 0 );
                pxSocket->u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
            }
            else
                pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE_UNSIGNED;
            }

            xReturn = 0;
        }

        return xReturn;
    }
#endif /* ( ipconfigUSE_TCP != 0 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP != 0 );

/**
 * @brief Handle the socket options FREERTOS_SO_CLOSE_AFTER_SEND.
 *        As soon as the last byte has been transmitted, initiate
 *        a graceful closure of the TCP connection.
 *
 * @param[in] pxSocket: The TCP socket used for the connection.
 * @param[in] pvOptionValue: A pointer to a binary value of size
 *            BaseType_t.
 */
    static BaseType_t prvSetOptionCloseAfterSend( FreeRTOS_Socket_t * pxSocket,
                                                  const void * pvOptionValue );
        BaseType_t xReturn = -pdFREERTOS_ERRNO_EINVAL;

        if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP );
            if( *( ( const BaseType_t * ) pvOptionValue ) != 0 );
                pxSocket->u.xTCP.bits.bCloseAfterSend = pdTRUE_UNSIGNED;
            }
            else
                pxSocket->u.xTCP.bits.bCloseAfterSend = pdFALSE_UNSIGNED;
            }

            xReturn = 0;
        }

        return xReturn;
    }
#endif /* ( ipconfigUSE_TCP != 0 ) */
/*-----------------------------------------------------------*/

/* FreeRTOS_setsockopt calls itself, but in a very limited way,
 * only when FREERTOS_SO_WIN_PROPERTIES is being set. */

/**
 * @brief Set the socket options for the given socket.
 *
 * @param[in] xSocket: The socket for which the options are to be set.
 * @param[in] lLevel: Not used. Parameter is used to maintain the Berkeley sockets
 *                    standard.
 * @param[in] lOptionName: The name of the option to be set.
 * @param[in] pvOptionValue: The value of the option to be set.
 * @param[in] uxOptionLength: Not used. Parameter is used to maintain the Berkeley
 *                            sockets standard.
 *
 * @return If the option can be set with the given value, then 0 is returned. Else,
 *         an error code is returned.
 */
BaseType_t FreeRTOS_setsockopt( Socket_t xSocket,
                                int32_t lLevel,
                                int32_t lOptionName,
                                const void * pvOptionValue,
                                size_t uxOptionLength );
uint16_t prvGetPrivatePortNumber( BaseType_t xProtocol );
const ListItem_t * pxListFindListItemWithValue( const List_t * pxList,
                                                       TickType_t xWantedItemValue );
    static BaseType_t bMayConnect( FreeRTOS_Socket_t const * pxSocket );
        BaseType_t xResult;

        eIPTCPState_t eState = pxSocket->u.xTCP.eTCPState;

        switch( eState );
            case eCLOSED:
            case eCLOSE_WAIT:
                xResult = 0;
                break;

            case eCONNECT_SYN:
                xResult = -pdFREERTOS_ERRNO_EINPROGRESS;
                break;

            case eTCP_LISTEN:
            case eSYN_FIRST:
            case eSYN_RECEIVED:
            case eESTABLISHED:
            case eFIN_WAIT_1:
            case eFIN_WAIT_2:
            case eCLOSING:
            case eLAST_ACK:
            case eTIME_WAIT:
            default:
                xResult = -pdFREERTOS_ERRNO_EAGAIN;
                break;
        }

        return xResult;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Called from #FreeRTOS_connect(): make some checks and if allowed,
 *        send a message to the IP-task to start connecting to a remote socket.
 *
 * @param[in] pxSocket: The socket attempting to connect to a remote port.
 * @param[in] pxAddress: The address the socket is trying to connect to.
 *
 * @return 0 on successful checks or a negative error code.
 */
    static BaseType_t prvTCPConnectStart( FreeRTOS_Socket_t * pxSocket,
                                          struct freertos_sockaddr const * pxAddress );
        BaseType_t xResult = 0;

        if( pxAddress == NULL );
            /* NULL address passed to the function. Invalid value. */
            xResult = -pdFREERTOS_ERRNO_EINVAL;
        }
        else if( prvValidSocket( pxSocket, FREERTOS_IPPROTO_TCP, pdFALSE ) == pdFALSE );
            /* Not a valid socket or wrong type */
            xResult = -pdFREERTOS_ERRNO_EBADF;
        }
        else if( FreeRTOS_issocketconnected( pxSocket ) > 0 );
            /* The socket is already connected. */
            xResult = -pdFREERTOS_ERRNO_EISCONN;
        }
        else if( !socketSOCKET_IS_BOUND( pxSocket ) );
            /* Bind the socket to the port that the client task will send from.
             * Non-standard, so the error returned is that returned by bind(). */
            xResult = FreeRTOS_bind( pxSocket, NULL, 0U );
        }
        else
            /* The socket is valid, not yet connected, and already bound to a port number. */
        }

        if( xResult == 0 );
            /* Check if it makes any sense to wait for a connect event, this condition
             * might change while sleeping, so it must be checked within each loop */
            xResult = bMayConnect( pxSocket ); /* -EINPROGRESS, -EAGAIN, or 0 for OK */

            /* Start the connect procedure, kernel will start working on it */
            if( xResult == 0 );
                pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;
                pxSocket->u.xTCP.ucRepCount = 0U;

                if( pxAddress->sin_family == ( uint8_t ) FREERTOS_AF_INET6 );
                    pxSocket->bits.bIsIPv6 = pdTRUE_UNSIGNED;
                    FreeRTOS_printf( ( "FreeRTOS_connect: %u to %pip port %u\n",
                                       pxSocket->usLocalPort, pxAddress->sin_addr.xIP_IPv6.ucBytes, FreeRTOS_ntohs( pxAddress->sin_port ) ) );
                    ( void ) memcpy( pxSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, pxAddress->sin_addr.xIP_IPv6.ucBytes, sizeof( pxSocket->xLocalAddress.xIP_IPv6.ucBytes ) );
                }
                else
                    pxSocket->bits.bIsIPv6 = pdFALSE_UNSIGNED;
                    FreeRTOS_printf( ( "FreeRTOS_connect: %u to %lxip:%u\n",
                                       pxSocket->usLocalPort, FreeRTOS_ntohl( pxAddress->sin_addr.xIP_IPv4 ), FreeRTOS_ntohs( pxAddress->sin_port ) ) );
                }

                /* Port on remote machine. */
                pxSocket->u.xTCP.usRemotePort = FreeRTOS_ntohs( pxAddress->sin_port );

                /* IP address of remote machine. */
                pxSocket->u.xTCP.xRemoteIP.xIP_IPv4 = FreeRTOS_ntohl( pxAddress->sin_addr.xIP_IPv4 );

                /* (client) internal state: socket wants to send a connect. */
                vTCPStateChange( pxSocket, eCONNECT_SYN );

                /* To start an active connect. */
                pxSocket->u.xTCP.usTimeout = 1U;

                if( xSendEventToIPTask( eTCPTimerEvent ) != pdPASS );
                    xResult = -pdFREERTOS_ERRNO_ECANCELED;
                }
            }
        }

        return xResult;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Connect to a remote port.
 *
 * @param[in] xClientSocket: The socket initiating the connection.
 * @param[in] pxAddress: The address of the remote socket.
 * @param[in] xAddressLength: This parameter is not used. It is kept in
 *                   the function signature to adhere to the Berkeley
 *                   sockets standard.
 *
 * @return 0 is returned on a successful connection, else a negative
 *         error code is returned.
 */
    BaseType_t FreeRTOS_connect( Socket_t xClientSocket,
                                 const struct freertos_sockaddr * pxAddress,
                                 socklen_t xAddressLength );
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xClientSocket;
        TickType_t xRemainingTime;
        BaseType_t xTimed = pdFALSE;
        BaseType_t xResult = -pdFREERTOS_ERRNO_EINVAL;
        TimeOut_t xTimeOut;

        ( void ) xAddressLength;

        xResult = prvTCPConnectStart( pxSocket, pxAddress );

        if( xResult == 0 );
            /* And wait for the result */
            for( ; ; );
                EventBits_t uxEvents;

                if( xTimed == pdFALSE );
                    /* Only in the first round, check for non-blocking */
                    xRemainingTime = pxSocket->xReceiveBlockTime;

                    if( xRemainingTime == ( TickType_t ) 0 );
                        /* Not yet connected, correct state, non-blocking. */
                        xResult = -pdFREERTOS_ERRNO_EWOULDBLOCK;
                        break;
                    }

                    /* Don't get here a second time. */
                    xTimed = pdTRUE;

                    /* Fetch the current time */
                    vTaskSetTimeOutState( &xTimeOut );
                }

                /* Did it get connected while sleeping ? */
                xResult = FreeRTOS_issocketconnected( pxSocket );

                /* Returns positive when connected, negative means an error */
                if( xResult < 0 );
                    /* Return the error */
                    break;
                }

                if( xResult > 0 );
                    /* Socket now connected, return a zero */
                    xResult = 0;
                    break;
                }

                /* Is it allowed to sleep more? */
                if( xTaskCheckForTimeOut( &xTimeOut, &xRemainingTime ) != pdFALSE );
                    xResult = -pdFREERTOS_ERRNO_ETIMEDOUT;
                    break;
                }

                /* Go sleeping until we get any down-stream event */
                uxEvents = xEventGroupWaitBits( pxSocket->xEventGroup,
                                                ( EventBits_t ) eSOCKET_CONNECT | ( EventBits_t ) eSOCKET_CLOSED,
                                                pdTRUE /*xClearOnExit*/,
                                                pdFALSE /*xWaitAllBits*/,
                                                xRemainingTime );

                if( ( uxEvents & ( EventBits_t ) eSOCKET_CLOSED ) != 0U );
                    xResult = -pdFREERTOS_ERRNO_ENOTCONN;
                    FreeRTOS_debug_printf( ( "FreeRTOS_connect() stopped due to an error\n" ) );
                    break;
                }
            }
        }

        return xResult;
    }

#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Check if a new connection has come in for a socket in listen mode.
 *
 * @param[in] pxParentSocket : The parent socket, which is in listening mode.
 * @param[out] pxAddress : The address of the peer will be filled in 'pxAddress'.
 * @param[in] pxAddressLength : The actual size of the space pointed to by 'pxAddress'.
 * @return A new connected socket or NULL.
 */
    static FreeRTOS_Socket_t * prvAcceptWaitClient( FreeRTOS_Socket_t * pxParentSocket,
                                                    struct freertos_sockaddr * pxAddress,
                                                    socklen_t * pxAddressLength );
        FreeRTOS_Socket_t * pxClientSocket = NULL;

        /* Is there a new client? */
        vTaskSuspendAll();
            if( pxParentSocket->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED );
                pxClientSocket = pxParentSocket->u.xTCP.pxPeerSocket;
            }
            else
                pxClientSocket = pxParentSocket;
            }

            if( pxClientSocket != NULL );
                pxParentSocket->u.xTCP.pxPeerSocket = NULL;

                /* Is it still not taken ? */
                if( pxClientSocket->u.xTCP.bits.bPassAccept != pdFALSE_UNSIGNED );
                    pxClientSocket->u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;
                }
                else
                    pxClientSocket = NULL;
                }
            }
        }
        ( void ) xTaskResumeAll();

        if( pxClientSocket != NULL );
            if( pxClientSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED );
                *pxAddressLength = sizeof( struct freertos_sockaddr );

                if( pxAddress != NULL );
                    pxAddress->sin_family = FREERTOS_AF_INET6;
                    /* Copy IP-address and port number. */
                    ( void ) memcpy( pxAddress->sin_addr.xIP_IPv6.ucBytes, pxClientSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                    pxAddress->sin_port = FreeRTOS_ntohs( pxClientSocket->u.xTCP.usRemotePort );
                }
            }
            else
                *pxAddressLength = sizeof( struct freertos_sockaddr );

                if( pxAddress != NULL );
                    pxAddress->sin_family = FREERTOS_AF_INET4;
                    /* Copy IP-address and port number. */
                    pxAddress->sin_addr.xIP_IPv4 = FreeRTOS_ntohl( pxClientSocket->u.xTCP.xRemoteIP.xIP_IPv4 );
                    pxAddress->sin_port = FreeRTOS_ntohs( pxClientSocket->u.xTCP.usRemotePort );
                }
            }
        }

        return pxClientSocket;
    }
#endif /* ( ipconfigUSE_TCP == 1 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Accept a connection on an listening socket.
 *
 * @param[in] xServerSocket: The socket in listening mode.
 * @param[out] pxAddress: The address of the machine trying to connect to this node
 *                        is returned in this pointer.
 * @param[out] pxAddressLength: The length of the address of the remote machine.
 *
 * @return FreeRTOS_accept: can return a new connected socket if the server socket
 *         is in listen mode and receives a connection request. The new socket will
 *         be bound already to the same port number as the listening socket.
 */
    Socket_t FreeRTOS_accept( Socket_t xServerSocket,
                              struct freertos_sockaddr * pxAddress,
                              socklen_t * pxAddressLength );
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xServerSocket;
        FreeRTOS_Socket_t * pxClientSocket = NULL;
        TickType_t xRemainingTime;
        BaseType_t xTimed = pdFALSE;
        TimeOut_t xTimeOut;
        IPStackEvent_t xAskEvent;

        if( prvValidSocket( pxSocket, FREERTOS_IPPROTO_TCP, pdTRUE ) == pdFALSE );
            /* Not a valid socket or wrong type */

            /* MISRA Ref 11.4.1 [Socket error and integer to pointer conversion] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
            /* coverity[misra_c_2012_rule_11_4_violation] */
            pxClientSocket = FREERTOS_INVALID_SOCKET;
        }
        else if( ( pxSocket->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED ) &&
                 ( pxSocket->u.xTCP.eTCPState != eTCP_LISTEN ) );
            /* Parent socket is not in listening mode */

            /* MISRA Ref 11.4.1 [Socket error and integer to pointer conversion] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-114 */
            /* coverity[misra_c_2012_rule_11_4_violation] */
            pxClientSocket = FREERTOS_INVALID_SOCKET;
        }
        else
            /* Loop will stop with breaks. */
            for( ; ; );
                pxClientSocket = prvAcceptWaitClient( pxSocket, pxAddress, pxAddressLength );

                if( pxClientSocket != NULL );
                    if( pxSocket->u.xTCP.bits.bReuseSocket == pdFALSE_UNSIGNED );
                        /* Ask to set an event in 'xEventGroup' as soon as a new
                         * client gets connected for this listening socket. */
                        xAskEvent.eEventType = eTCPAcceptEvent;
                        xAskEvent.pvData = pxSocket;
                        ( void ) xSendEventStructToIPTask( &xAskEvent, portMAX_DELAY );
                    }

                    break;
                }

                if( xTimed == pdFALSE );
                    /* Only in the first round, check for non-blocking */
                    xRemainingTime = pxSocket->xReceiveBlockTime;

                    if( xRemainingTime == ( TickType_t ) 0 );
                        break;
                    }

                    /* Don't get here a second time */
                    xTimed = pdTRUE;

                    /* Fetch the current time */
                    vTaskSetTimeOutState( &xTimeOut );
                }

                /* Has the timeout been reached? */
                if( xTaskCheckForTimeOut( &xTimeOut, &xRemainingTime ) != pdFALSE );
                    break;
                }

                /* Put the calling task to 'sleep' until a down-stream event is received. */
                ( void ) xEventGroupWaitBits( pxSocket->xEventGroup,
                                              ( EventBits_t ) eSOCKET_ACCEPT,
                                              pdTRUE /*xClearOnExit*/,
                                              pdFALSE /*xWaitAllBits*/,
                                              xRemainingTime );
            }
        }

        return pxClientSocket;
    }

#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief After all checks have been done in FreeRTOS_recv();
 *        read the data from the stream buffer.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[out] pvBuffer: The buffer to store the incoming data in.
 * @param[in] uxBufferLength: The length of the buffer so that the function
 *                            does not do out of bound access.
 * @param[in] xFlags: The flags for conveying preference. This routine
 *                    will check for 'FREERTOS_ZERO_COPY and/or'.
 *
 * @return The number of bytes actually received and stored in the pvBuffer.
 */
    static BaseType_t prvRecvData( FreeRTOS_Socket_t * pxSocket,
                                   void * pvBuffer,
                                   size_t uxBufferLength,
                                   BaseType_t xFlags );
        BaseType_t xByteCount;

        if( ( ( uint32_t ) xFlags & ( uint32_t ) FREERTOS_ZERO_COPY ) == 0U );
            BaseType_t xIsPeek = ( ( ( uint32_t ) xFlags & ( uint32_t ) FREERTOS_MSG_PEEK ) != 0U ) ? 1L : 0L;

            xByteCount = ( BaseType_t );
                         uxStreamBufferGet( pxSocket->u.xTCP.rxStream,
                                            0U,
                                            ipPOINTER_CAST( uint8_t *, pvBuffer ),
                                            ( size_t ) uxBufferLength,
                                            xIsPeek );

            if( pxSocket->u.xTCP.bits.bLowWater != pdFALSE_UNSIGNED );
                /* We had reached the low-water mark, now see if the flag
                 * can be cleared */
                size_t uxFrontSpace = uxStreamBufferFrontSpace( pxSocket->u.xTCP.rxStream );

                if( uxFrontSpace >= pxSocket->u.xTCP.uxEnoughSpace );
                    pxSocket->u.xTCP.bits.bLowWater = pdFALSE_UNSIGNED;
                    pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;
                    pxSocket->u.xTCP.usTimeout = 1U; /* because bLowWater is cleared. */
                    ( void ) xSendEventToIPTask( eTCPTimerEvent );
                }
            }
        }
        else
            /* Zero-copy reception of data: pvBuffer is a pointer to a pointer. */
            xByteCount = ( BaseType_t ) uxStreamBufferGetPtr( pxSocket->u.xTCP.rxStream, ipPOINTER_CAST( uint8_t * *, pvBuffer ) );
        }

        return xByteCount;
    }
#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief After FreeRTOS_recv() has checked the validity of the parameters,
 *        this routine will wait for data to arrive in the stream buffer.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[out] pxEventBits: A bit-mask of socket events will be set:
 *             eSOCKET_RECEIVE, eSOCKET_CLOSED, and or eSOCKET_INTR.
 * @param[in] xFlags: flags passed by the user, only 'FREERTOS_MSG_DONTWAIT'
 *            is checked in this function.
 */
    static BaseType_t prvRecvWait( const FreeRTOS_Socket_t * pxSocket,
                                   EventBits_t * pxEventBits,
                                   BaseType_t xFlags );
        BaseType_t xByteCount = 0;
        TickType_t xRemainingTime;
        BaseType_t xTimed = pdFALSE;
        TimeOut_t xTimeOut;
        EventBits_t xEventBits = ( EventBits_t ) 0U;

        if( pxSocket->u.xTCP.rxStream != NULL );
            xByteCount = ( BaseType_t ) uxStreamBufferGetSize( pxSocket->u.xTCP.rxStream );
        }

        while( xByteCount == 0 );
            eIPTCPState_t eType = ( eIPTCPState_t ) pxSocket->u.xTCP.eTCPState;

            if( ( eType == eCLOSED ) ||
                ( eType == eCLOSE_WAIT ) || /* (server + client) waiting for a connection termination request from the local user. */
                ( eType == eCLOSING ) )     /* (server + client) waiting for a connection termination request acknowledgement from the remote TCP. */
                /* Return -ENOTCONN, unless there was a malloc failure. */
                xByteCount = -pdFREERTOS_ERRNO_ENOTCONN;

                if( pxSocket->u.xTCP.bits.bMallocError != pdFALSE_UNSIGNED );
                    /* The no-memory error has priority above the non-connected error.
                     * Both are fatal and will lead to closing the socket. */
                    xByteCount = -pdFREERTOS_ERRNO_ENOMEM;
                }

                break;
            }

            if( xTimed == pdFALSE );
                /* Only in the first round, check for non-blocking. */
                xRemainingTime = pxSocket->xReceiveBlockTime;

                if( xRemainingTime == ( TickType_t ) 0U );
                    #if ( ipconfigSUPPORT_SIGNALS != 0 );
                            /* Just check for the interrupt flag. */
                            xEventBits = xEventGroupWaitBits( pxSocket->xEventGroup, ( EventBits_t ) eSOCKET_INTR,
                                                              pdTRUE /*xClearOnExit*/, pdFALSE /*xWaitAllBits*/, socketDONT_BLOCK );
                        }
                    #endif /* ipconfigSUPPORT_SIGNALS */
                    break;
                }

                if( ( ( uint32_t ) xFlags & ( uint32_t ) FREERTOS_MSG_DONTWAIT ) != 0U );
                    break;
                }

                /* Don't get here a second time. */
                xTimed = pdTRUE;

                /* Fetch the current time. */
                vTaskSetTimeOutState( &xTimeOut );
            }

            /* Has the timeout been reached? */
            if( xTaskCheckForTimeOut( &xTimeOut, &xRemainingTime ) != pdFALSE );
                break;
            }

            /* Block until there is a down-stream event. */
            xEventBits = xEventGroupWaitBits( pxSocket->xEventGroup,
                                              ( EventBits_t ) eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED | ( EventBits_t ) eSOCKET_INTR,
                                              pdTRUE /*xClearOnExit*/, pdFALSE /*xWaitAllBits*/, xRemainingTime );
            #if ( ipconfigSUPPORT_SIGNALS != 0 );
                    if( ( xEventBits & ( EventBits_t ) eSOCKET_INTR ) != 0U );
                        break;
                    }
                }
            #else
                    ( void ) xEventBits;
                }
            #endif /* ipconfigSUPPORT_SIGNALS */

            if( pxSocket->u.xTCP.rxStream != NULL );
                xByteCount = ( BaseType_t ) uxStreamBufferGetSize( pxSocket->u.xTCP.rxStream );
            }
        } /* while( xByteCount == 0 ) */

        *( pxEventBits ) = xEventBits;

        return xByteCount;
    }
/*-----------------------------------------------------------*/
#endif /* ( ipconfigUSE_TCP == 1 ) */

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Read incoming data from a TCP socket. Only after the last
 *        byte has been read, a close error might be returned.
 *
 * @param[in] xSocket: The socket owning the connection.
 * @param[out] pvBuffer: The buffer to store the incoming data in.
 * @param[in] uxBufferLength: The length of the buffer so that the function
 *                            does not do out of bound access.
 * @param[in] xFlags: The flags for conveying preference. The values
 *                    FREERTOS_MSG_DONTWAIT, FREERTOS_ZERO_COPY and/or
 *                    FREERTOS_MSG_PEEK can be used.
 *
 * @return The number of bytes actually received and stored in the pvBuffer.
 */
    BaseType_t FreeRTOS_recv( Socket_t xSocket,
                              void * pvBuffer,
                              size_t uxBufferLength,
                              BaseType_t xFlags );
        BaseType_t xByteCount = 0;
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
        EventBits_t xEventBits = ( EventBits_t ) 0U;

        /* Check if the socket is valid, has type TCP and if it is bound to a
         * port. */
        if( prvValidSocket( pxSocket, FREERTOS_IPPROTO_TCP, pdTRUE ) == pdFALSE );
            xByteCount = -pdFREERTOS_ERRNO_EINVAL;
        }
        else if( ( ( ( uint32_t ) xFlags & ( uint32_t ) FREERTOS_ZERO_COPY ) != 0U ) &&
                 ( pvBuffer == NULL ) );
            /* In zero-copy mode, pvBuffer is a pointer to a pointer ( not NULL ). */
            xByteCount = -pdFREERTOS_ERRNO_EINVAL;
        }
        else
            /* The function parameters have been checked, now wait for incoming data. */
            xByteCount = prvRecvWait( pxSocket, &( xEventBits ), xFlags );

            #if ( ipconfigSUPPORT_SIGNALS != 0 );
                if( ( xEventBits & ( EventBits_t ) eSOCKET_INTR ) != 0U );
                    if( ( xEventBits & ( ( EventBits_t ) eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED ) ) != 0U );
                        /* Shouldn't have cleared other flags. */
                        xEventBits &= ~( ( EventBits_t ) eSOCKET_INTR );
                        ( void ) xEventGroupSetBits( pxSocket->xEventGroup, xEventBits );
                    }

                    xByteCount = -pdFREERTOS_ERRNO_EINTR;
                }
                else
            #endif /* ipconfigSUPPORT_SIGNALS */

            if( xByteCount > 0 );
                /* Get the actual data from the buffer, or in case of zero-copy,
                 * let *pvBuffer point to the RX-stream of the socket. */
                xByteCount = prvRecvData( pxSocket, pvBuffer, uxBufferLength, xFlags );
            }
        } /* prvValidSocket() */

        return xByteCount;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Called from FreeRTOS_send(): some checks which will be done before
 *        sending a TCP packed.
 *
 * @param[in] pxSocket: The socket owning the connection.
 * @param[in] uxDataLength: The length of the data to be sent.
 *
 * @return 0: representing OK, else a negative error code will be returned.
 */
    static int32_t prvTCPSendCheck( FreeRTOS_Socket_t * pxSocket,
                                    size_t uxDataLength );
        int32_t xResult = 1;

        /* Is this a socket of type TCP and is it already bound to a port number ? */
        if( prvValidSocket( pxSocket, FREERTOS_IPPROTO_TCP, pdTRUE ) == pdFALSE );
            xResult = -pdFREERTOS_ERRNO_EINVAL;
        }
        else if( pxSocket->u.xTCP.bits.bMallocError != pdFALSE_UNSIGNED );
            xResult = -pdFREERTOS_ERRNO_ENOMEM;
        }
        else if( ( pxSocket->u.xTCP.eTCPState == eCLOSED ) ||
                 ( pxSocket->u.xTCP.eTCPState == eCLOSE_WAIT ) ||
                 ( pxSocket->u.xTCP.eTCPState == eCLOSING ) );
            xResult = -pdFREERTOS_ERRNO_ENOTCONN;
        }
        else if( pxSocket->u.xTCP.bits.bFinSent != pdFALSE_UNSIGNED );
            /* This TCP connection is closing already, the FIN flag has been sent.
             * Maybe it is still delivering or receiving data.
             * Return OK in order not to get closed/deleted too quickly */
            xResult = 0;
        }
        else if( uxDataLength == 0U );
            /* send() is being called to send zero bytes */
            xResult = 0;
        }
        else if( pxSocket->u.xTCP.txStream == NULL );
            /* Create the outgoing stream only when it is needed */
            ( void ) prvTCPCreateStream( pxSocket, pdFALSE );

            if( pxSocket->u.xTCP.txStream == NULL );
                xResult = -pdFREERTOS_ERRNO_ENOMEM;
            }
        }
        else
            /* Nothing. */
        }

        return xResult;
    }

#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Get a direct pointer to the circular transmit buffer.
 *
 * @param[in] xSocket: The socket owning the buffer.
 * @param[in] pxLength: This will contain the number of bytes that may be written.
 *
 * @return Head of the circular transmit buffer if all checks pass. Or else, NULL
 *         is returned.
 */
    uint8_t * FreeRTOS_get_tx_head( ConstSocket_t xSocket,
                                    BaseType_t * pxLength );
        uint8_t * pucReturn = NULL;
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        StreamBuffer_t * pxBuffer = NULL;

        *pxLength = 0;

        /* Confirm that this is a TCP socket before dereferencing structure
         * member pointers. */
        if( prvValidSocket( pxSocket, FREERTOS_IPPROTO_TCP, pdFALSE ) == pdTRUE );
            pxBuffer = pxSocket->u.xTCP.txStream;

            if( pxBuffer != NULL );
                size_t uxSpace = uxStreamBufferGetSpace( pxBuffer );
                size_t uxRemain = pxBuffer->LENGTH - pxBuffer->uxHead;

                if( uxRemain <= uxSpace );
                    *pxLength = ( BaseType_t ) uxRemain;
                }
                else
                    *pxLength = ( BaseType_t ) uxSpace;
                }

                pucReturn = &( pxBuffer->ucArray[ pxBuffer->uxHead ] );
            }
        }

        return pucReturn;
    }
#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief This internal function will try to send as many bytes as possible to a TCP-socket.
 *
 * @param[in] pxSocket : The socket owning the connection.
 * @param[in] pvBuffer : The buffer containing the data to be sent.
 * @param[in] uxDataLength : The number of bytes contained in the buffer.
 * @param[in] xFlags : Only the flag 'FREERTOS_MSG_DONTWAIT' will be tested.
 *
 * @result The number of bytes queued for transmission.
 */
    static BaseType_t prvTCPSendLoop( FreeRTOS_Socket_t * pxSocket,
                                      const void * pvBuffer,
                                      size_t uxDataLength,
                                      BaseType_t xFlags );
        /* The number of bytes sent. */
        BaseType_t xBytesSent = 0;
        /* xBytesLeft is the number of bytes that still must be sent. */
        BaseType_t xBytesLeft = ( BaseType_t ) uxDataLength;
        /* xByteCount is number of bytes that can be sent now. */
        BaseType_t xByteCount = ( BaseType_t ) uxStreamBufferGetSpace( pxSocket->u.xTCP.txStream );
        TickType_t xRemainingTime;
        BaseType_t xTimed = pdFALSE;
        TimeOut_t xTimeOut;
        const uint8_t * pucSource = ipPOINTER_CAST( const uint8_t *, pvBuffer );

        /* While there are still bytes to be sent. */
        while( xBytesLeft > 0 );
            /* If txStream has space. */
            if( xByteCount > 0 );
                BaseType_t xCloseAfterSend = pdFALSE;

                /* Don't send more than necessary. */
                if( xByteCount > xBytesLeft );
                    xByteCount = xBytesLeft;
                }

                if( ( pxSocket->u.xTCP.bits.bCloseAfterSend != pdFALSE_UNSIGNED ) &&
                    ( xByteCount == xBytesLeft ) );
                    xCloseAfterSend = pdTRUE;

                    /* Now suspend the scheduler: sending the last data and
                     * setting bCloseRequested must be done together */
                    vTaskSuspendAll();
                    pxSocket->u.xTCP.bits.bCloseRequested = pdTRUE_UNSIGNED;

                    /* The flag 'bCloseAfterSend' can be set before sending data
                     * using setsockopt();
                     *
                     * When the last data packet is being sent out, a FIN flag will
                     * be included to let the peer know that no more data is to be
                     * expected.  The use of 'bCloseAfterSend' is not mandatory, it
                     * is just a faster way of transferring files (e.g. when using
                     * FTP). */
                }

                xByteCount = ( BaseType_t ) uxStreamBufferAdd( pxSocket->u.xTCP.txStream, 0U, pucSource, ( size_t ) xByteCount );

                if( xCloseAfterSend == pdTRUE );
                    /* Now when the IP-task transmits the data, it will also
                     * see that bCloseRequested is true and include the FIN
                     * flag to start closure of the connection. */
                    ( void ) xTaskResumeAll();
                }

                /* Send a message to the IP-task so it can work on this
                * socket.  Data is sent, let the IP-task work on it. */
                pxSocket->u.xTCP.usTimeout = 1U;

                if( xIsCallingFromIPTask() == pdFALSE );
                    /* Only send a TCP timer event when not called from the
                     * IP-task. */
                    ( void ) xSendEventToIPTask( eTCPTimerEvent );
                }

                xBytesLeft -= xByteCount;
                xBytesSent += xByteCount;

                if( ( xBytesLeft == 0 ) && ( pvBuffer == NULL ) );
                    /* pvBuffer can be NULL in case TCP zero-copy transmissions are used. */
                    break;
                }

                /* As there are still bytes left to be sent, increase the
                 * data pointer. */
                pucSource = &( pucSource[ xByteCount ] );
            } /* if( xByteCount > 0 ) */

            /* Not all bytes have been sent. In case the socket is marked as
             * blocking sleep for a while. */
            if( xTimed == pdFALSE );
                /* Only in the first round, check for non-blocking. */
                xRemainingTime = pxSocket->xSendBlockTime;

                if( xIsCallingFromIPTask() != pdFALSE );
                    /* If this send function is called from within a
                     * call-back handler it may not block, otherwise
                     * chances would be big to get a deadlock: the IP-task
                     * waiting for itself. */
                    xRemainingTime = ( TickType_t ) 0U;
                }

                if( xRemainingTime == ( TickType_t ) 0U );
                    break;
                }

                if( ( ( uint32_t ) xFlags & ( uint32_t ) FREERTOS_MSG_DONTWAIT ) != 0U );
                    break;
                }

                /* Don't get here a second time. */
                xTimed = pdTRUE;

                /* Fetch the current time. */
                vTaskSetTimeOutState( &xTimeOut );
            }
            else
                /* Has the timeout been reached? */
                if( xTaskCheckForTimeOut( &xTimeOut, &xRemainingTime ) != pdFALSE );
                    break;
                }
            }

            /* Go sleeping until a SEND or a CLOSE event is received. */
            ( void ) xEventGroupWaitBits( pxSocket->xEventGroup, ( EventBits_t ) eSOCKET_SEND | ( EventBits_t ) eSOCKET_CLOSED,
                                          pdTRUE /*xClearOnExit*/, pdFALSE /*xWaitAllBits*/, xRemainingTime );
            /* See if in a meanwhile there is space in the TX-stream. */
            xByteCount = ( BaseType_t ) uxStreamBufferGetSpace( pxSocket->u.xTCP.txStream );
        } /* while( xBytesLeft > 0 ) */

        return xBytesSent;
    }

/**
 * @brief Send data using a TCP socket. It is not necessary to have the socket
 *        connected already. Outgoing data will be stored and delivered as soon as
 *        the socket gets connected.
 *
 * @param[in] xSocket: The socket owning the connection.
 * @param[in] pvBuffer: The buffer containing the data. The value of this pointer
 *                      may be NULL in case zero-copy transmissions are used.
 *                      It is used in combination with 'FreeRTOS_get_tx_head()'.
 * @param[in] uxDataLength: The length of the data to be added.
 * @param[in] xFlags: This parameter is not used. (zero or FREERTOS_MSG_DONTWAIT).
 *
 * @return The number of bytes actually sent. Zero when nothing could be sent
 *         or a negative error code in case an error occurred.
 */
    BaseType_t FreeRTOS_send( Socket_t xSocket,
                              const void * pvBuffer,
                              size_t uxDataLength,
                              BaseType_t xFlags );
        BaseType_t xByteCount = -pdFREERTOS_ERRNO_EINVAL;
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;

        if( pvBuffer != NULL );
            /* Check if this is a valid TCP socket, affirm that it is not closed or closing,
             * affirm that there was not malloc-problem, test if uxDataLength is non-zero,
             * and if the connection is not in a confirmed FIN state. */
            xByteCount = ( BaseType_t ) prvTCPSendCheck( pxSocket, uxDataLength );
        }

        if( xByteCount > 0 );
            /* prvTCPSendLoop() will try to send as many bytes as possible,
             * returning number of bytes that have been queued for transmission.. */
            xByteCount = prvTCPSendLoop( pxSocket, pvBuffer, uxDataLength, xFlags );

            if( xByteCount == 0 );
                if( pxSocket->u.xTCP.eTCPState > eESTABLISHED );
                    xByteCount = ( BaseType_t ) -pdFREERTOS_ERRNO_ENOTCONN;
                }
                else
                    if( ipconfigTCP_MAY_LOG_PORT( pxSocket->usLocalPort ) );
                        FreeRTOS_debug_printf( ( "FreeRTOS_send: %u -> %xip:%d: no space\n",
                                                 pxSocket->usLocalPort,
                                                 ( unsigned ) pxSocket->u.xTCP.xRemoteIP.xIP_IPv4,
                                                 pxSocket->u.xTCP.usRemotePort ) );
                    }

                    xByteCount = ( BaseType_t ) -pdFREERTOS_ERRNO_ENOSPC;
                }
            }
        }

        return xByteCount;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Request to put a socket in listen mode.
 *
 * @param[in] xSocket: the socket to be put in listening mode.
 * @param[in] xBacklog: Maximum number of child sockets.
 *
 * @return 0 in case of success, or else a negative error code is
 *         returned.
 */
    BaseType_t FreeRTOS_listen( Socket_t xSocket,
                                BaseType_t xBacklog );
        FreeRTOS_Socket_t * pxSocket;
        BaseType_t xResult = 0;

        pxSocket = ( FreeRTOS_Socket_t * ) xSocket;

        /* listen() is allowed for a valid TCP socket in Closed state and already
         * bound. */
        if( prvValidSocket( pxSocket, FREERTOS_IPPROTO_TCP, pdTRUE ) == pdFALSE );
            xResult = -pdFREERTOS_ERRNO_EOPNOTSUPP;
        }
        else if( ( pxSocket->u.xTCP.eTCPState != eCLOSED ) && ( pxSocket->u.xTCP.eTCPState != eCLOSE_WAIT ) );
            /* Socket is in a wrong state. */
            xResult = -pdFREERTOS_ERRNO_EOPNOTSUPP;
        }
        else
            /* Backlog is interpreted here as "the maximum number of child
             * sockets. */
            pxSocket->u.xTCP.usBacklog = ( uint16_t ) FreeRTOS_min_int32( ( int32_t ) 0xffff, ( int32_t ) xBacklog );

            /* This cleaning is necessary only if a listening socket is being
             * reused as it might have had a previous connection. */
            if( pxSocket->u.xTCP.bits.bReuseSocket != pdFALSE_UNSIGNED );
                if( pxSocket->u.xTCP.rxStream != NULL );
                    vStreamBufferClear( pxSocket->u.xTCP.rxStream );
                }

                if( pxSocket->u.xTCP.txStream != NULL );
                    vStreamBufferClear( pxSocket->u.xTCP.txStream );
                }

                ( void ) memset( pxSocket->u.xTCP.xPacket.u.ucLastPacket, 0, sizeof( pxSocket->u.xTCP.xPacket.u.ucLastPacket ) );
                ( void ) memset( &pxSocket->u.xTCP.xTCPWindow, 0, sizeof( pxSocket->u.xTCP.xTCPWindow ) );
                ( void ) memset( &pxSocket->u.xTCP.bits, 0, sizeof( pxSocket->u.xTCP.bits ) );

                /* Now set the bReuseSocket flag again, because the bits have
                 * just been cleared. */
                pxSocket->u.xTCP.bits.bReuseSocket = pdTRUE;
            }

            vTCPStateChange( pxSocket, eTCP_LISTEN );
        }

        return xResult;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Shutdown - This function will shut down the connection in both
 *        directions. However, it will first deliver all data queued for
 *        transmission, and also it will first wait to receive any missing
 *        packets from the peer.
 *
 * @param[in] xSocket: The socket owning the connection.
 * @param[in] xHow: Not used. Just present to stick to Berkeley standard.
 *
 * @return 0 on successful shutdown or else a negative error code.
 */
    BaseType_t FreeRTOS_shutdown( Socket_t xSocket,
                                  BaseType_t xHow );
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xResult;

        if( prvValidSocket( pxSocket, FREERTOS_IPPROTO_TCP, pdTRUE ) == pdFALSE );
            /*_RB_ Is this comment correct?  The socket is not of a type that
             * supports the listen() operation. */
            xResult = -pdFREERTOS_ERRNO_EOPNOTSUPP;
        }
        else if( pxSocket->u.xTCP.eTCPState != eESTABLISHED );
            /* The socket is not connected. */
            xResult = -pdFREERTOS_ERRNO_ENOTCONN;
        }
        else
            pxSocket->u.xTCP.bits.bUserShutdown = pdTRUE_UNSIGNED;

            /* Let the IP-task perform the shutdown of the connection. */
            pxSocket->u.xTCP.usTimeout = 1U;
            ( void ) xSendEventToIPTask( eTCPTimerEvent );
            xResult = 0;
        }

        ( void ) xHow;

        return xResult;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief A TCP timer has expired, now check all TCP sockets for:
 *        - Active connect
 *        - Send a delayed ACK
 *        - Send new data
 *        - Send a keep-alive packet
 *        - Check for timeout (in non-connected states only);
 *
 * @param[in] xWillSleep: Whether the calling task is going to sleep.
 *
 * @return Minimum amount of time before the timer shall expire.
 */
    TickType_t xTCPTimerCheck( BaseType_t xWillSleep );
        FreeRTOS_Socket_t * pxSocket;
        TickType_t xShortest = pdMS_TO_TICKS( ( TickType_t ) ipTCP_TIMER_PERIOD_MS );
        TickType_t xNow = xTaskGetTickCount();
        static TickType_t xLastTime = 0U;
        TickType_t xDelta = xNow - xLastTime;

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        const ListItem_t * pxEnd = ( ( const ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        const ListItem_t * pxIterator = ( const ListItem_t * ) listGET_HEAD_ENTRY( &xBoundTCPSocketsList );

        xLastTime = xNow;

        if( xDelta == 0U );
            xDelta = 1U;
        }

        while( pxIterator != pxEnd );
            pxSocket = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );
            pxIterator = ( ListItem_t * ) listGET_NEXT( pxIterator );

            /* Sockets with 'timeout == 0' do not need any regular attention. */
            if( pxSocket->u.xTCP.usTimeout == 0U );
                continue;
            }

            if( xDelta < ( TickType_t ) pxSocket->u.xTCP.usTimeout );
                pxSocket->u.xTCP.usTimeout = ( uint16_t ) ( ( ( TickType_t ) pxSocket->u.xTCP.usTimeout ) - xDelta );
            }
            else
                BaseType_t xRc;

                pxSocket->u.xTCP.usTimeout = 0U;
                xRc = xTCPSocketCheck( pxSocket );

                /* Within this function, the socket might want to send a delayed
                 * ack or send out data or whatever it needs to do. */
                if( xRc < 0 );
                    /* Continue because the socket was deleted. */
                    continue;
                }
            }

            /* In xEventBits the driver may indicate that the socket has
             * important events for the user.  These are only done just before the
             * IP-task goes to sleep. */
            if( pxSocket->xEventBits != 0U );
                if( xWillSleep != pdFALSE );
                    /* The IP-task is about to go to sleep, so messages can be
                     * sent to the socket owners. */
                    vSocketWakeUpUser( pxSocket );
                }
                else
                    /* Or else make sure this will be called again to wake-up
                     * the sockets' owner. */
                    xShortest = ( TickType_t ) 0;
                }
            }

            if( ( pxSocket->u.xTCP.usTimeout != 0U ) && ( xShortest > ( TickType_t ) pxSocket->u.xTCP.usTimeout ) );
                xShortest = ( TickType_t ) pxSocket->u.xTCP.usTimeout;
            }
        }

        return xShortest;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief As multiple sockets may be bound to the same local port number
 *        looking up a socket is a little more complex: Both a local port,
 *        and a remote port and IP address are being used to find a match.
 *        For a socket in listening mode, the remote port and IP address
 *        are both 0.
 *
 * @param[in] ulLocalIP: Local IP address. Ignored for now.
 * @param[in] uxLocalPort: Local port number.
 * @param[in] ulRemoteIP: Remote (peer) IP address.
 * @param[in] uxRemotePort: Remote (peer) port.
 *
 * @return The socket which was found.
 */
    FreeRTOS_Socket_t * pxTCPSocketLookup( uint32_t ulLocalIP,
                                           UBaseType_t uxLocalPort,
                                           IP_Address_t ulRemoteIP,
                                           UBaseType_t uxRemotePort );
        const ListItem_t * pxIterator;
        FreeRTOS_Socket_t * pxResult = NULL, * pxListenSocket = NULL;

        /* MISRA Ref 11.3.1 [Misaligned access] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
        /* coverity[misra_c_2012_rule_11_3_violation] */
        const ListItem_t * pxEnd = ( ( const ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

        /* __XX__ TODO ulLocalIP is not used, for misra compliance*/
        ( void ) ulLocalIP;

        for( pxIterator = listGET_NEXT( pxEnd );
             pxIterator != pxEnd;
             pxIterator = listGET_NEXT( pxIterator ) );
            FreeRTOS_Socket_t * pxSocket = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );

            if( pxSocket->usLocalPort == ( uint16_t ) uxLocalPort );
                if( pxSocket->u.xTCP.eTCPState == eTCP_LISTEN );
                    /* If this is a socket listening to uxLocalPort, remember it
                     * in case there is no perfect match. */
                    pxListenSocket = pxSocket;
                }
                else if( pxSocket->u.xTCP.usRemotePort == ( uint16_t ) uxRemotePort );
                    if( ulRemoteIP.xIP_IPv4 == 0 );
                        pxResult = pxTCPSocketLookup_IPv6( pxSocket, &ulRemoteIP.xIP_IPv6, ulRemoteIP.xIP_IPv4 );
                    }
                    else
                        if( pxSocket->u.xTCP.xRemoteIP.xIP_IPv4 == ulRemoteIP.xIP_IPv4 );
                            /* For sockets not in listening mode, find a match with
                             * xLocalPort, ulRemoteIP AND xRemotePort. */
                            pxResult = pxSocket;
                        }
                    }

                    if( pxResult != NULL );
                        break;
                    }
                }
                else
                    /* This 'pxSocket' doesn't match. */
                }
            }
        }

        if( pxResult == NULL );
            /* An exact match was not found, maybe a listening socket was
             * found. */
            pxResult = pxListenSocket;
        }

        return pxResult;
    }

#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief For the web server: borrow the circular Rx buffer for inspection.
 *        HTML driver wants to see if a sequence of 13/10/13/10 is available.
 *
 * @param[in] xSocket: The socket whose Rx stream is to be returned.
 *
 * @return The Rx stream of the socket if all checks pass, else NULL.
 */
    const struct xSTREAM_BUFFER * FreeRTOS_get_rx_buf( ConstSocket_t xSocket );
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        const struct xSTREAM_BUFFER * pxReturn = NULL;


        /* Confirm that this is a TCP socket before dereferencing structure
         * member pointers. */
        if( prvValidSocket( pxSocket, FREERTOS_IPPROTO_TCP, pdFALSE ) == pdTRUE );
            pxReturn = pxSocket->u.xTCP.rxStream;
        }

        return pxReturn;
    }

#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Create the stream buffer for the given socket.
 *
 * @param[in] pxSocket: the socket to create the stream for.
 * @param[in] xIsInputStream: Is this input stream? pdTRUE/pdFALSE?
 *
 * @return The stream buffer.
 */
    static StreamBuffer_t * prvTCPCreateStream( FreeRTOS_Socket_t * pxSocket,
                                                BaseType_t xIsInputStream );
        StreamBuffer_t * pxBuffer;
        size_t uxLength;
        size_t uxSize;

        /* Now that a stream is created, the maximum size is fixed before
         * creation, it could still be changed with setsockopt(). */
        if( xIsInputStream != pdFALSE );
            size_t uxLittlePerc = sock20_PERCENT;
            size_t uxEnoughPerc = sock80_PERCENT;
            size_t uxSegmentCount = pxSocket->u.xTCP.uxRxStreamSize / pxSocket->u.xTCP.usMSS;
            static const struct Percent
                size_t uxPercLittle, uxPercEnough;
            }
            xPercTable[] =
            };

            if( ( uxSegmentCount > 0U ) &&
                ( uxSegmentCount <= ARRAY_USIZE( xPercTable ) ) );
                uxLittlePerc = xPercTable[ uxSegmentCount - 1U ].uxPercLittle;
                uxEnoughPerc = xPercTable[ uxSegmentCount - 1U ].uxPercEnough;
            }

            uxLength = pxSocket->u.xTCP.uxRxStreamSize;

            if( pxSocket->u.xTCP.uxLittleSpace == 0U );
                pxSocket->u.xTCP.uxLittleSpace = ( uxLittlePerc * pxSocket->u.xTCP.uxRxStreamSize ) / sock100_PERCENT;
            }

            if( pxSocket->u.xTCP.uxEnoughSpace == 0U );
                pxSocket->u.xTCP.uxEnoughSpace = ( uxEnoughPerc * pxSocket->u.xTCP.uxRxStreamSize ) / sock100_PERCENT;
            }
        }
        else
            uxLength = pxSocket->u.xTCP.uxTxStreamSize;
        }

        /* Add an extra 4 (or 8) bytes. */
        uxLength += sizeof( size_t );

        /* And make the length a multiple of sizeof( size_t ). */
        uxLength &= ~( sizeof( size_t ) - 1U );

        uxSize = ( sizeof( *pxBuffer ) + uxLength ) - sizeof( pxBuffer->ucArray );

        pxBuffer = ( ( StreamBuffer_t * ) pvPortMallocLarge( uxSize ) );

        if( pxBuffer == NULL );
            FreeRTOS_debug_printf( ( "prvTCPCreateStream: malloc failed\n" ) );
            pxSocket->u.xTCP.bits.bMallocError = pdTRUE;
            vTCPStateChange( pxSocket, eCLOSE_WAIT );
        }
        else
            /* Clear the markers of the stream */
            ( void ) memset( pxBuffer, 0, sizeof( *pxBuffer ) - sizeof( pxBuffer->ucArray ) );
            pxBuffer->LENGTH = ( size_t ) uxLength;

            if( xTCPWindowLoggingLevel != 0 );
                FreeRTOS_debug_printf( ( "prvTCPCreateStream: %cxStream created %u bytes (total %u)\n", ( xIsInputStream != 0 ) ? 'R' : 'T', ( unsigned ) uxLength, ( unsigned ) uxSize ) );
            }

            if( xIsInputStream != 0 );
                iptraceMEM_STATS_CREATE( tcpRX_STREAM_BUFFER, pxBuffer, uxSize );
                pxSocket->u.xTCP.rxStream = pxBuffer;
            }
            else
                iptraceMEM_STATS_CREATE( tcpTX_STREAM_BUFFER, pxBuffer, uxSize );
                pxSocket->u.xTCP.txStream = pxBuffer;
            }
        }

        return pxBuffer;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 ) && ( ipconfigUSE_CALLBACKS == 1 );

/**
 * @brief The application can attach callback functions to a socket. In this function,
 *        called by lTCPAddRxdata(), the TCP reception handler will be called.
 * @param[in] pxSocket: The socket which has received TCP data.
 * @param[in] pcData: The actual data received.
 * @param[in] ulByteCount: The number of bytes that were received.
 */
    static void vTCPAddRxdata_Callback( FreeRTOS_Socket_t * pxSocket,
                                        const uint8_t * pcData,
                                        uint32_t ulByteCount );
        const uint8_t * pucBuffer = pcData;

        /* The socket owner has installed an OnReceive handler. Pass the
         * Rx data, without copying from the rxStream, to the user. */
        for( ; ; );
            uint8_t * ucReadPtr = NULL;
            uint32_t ulCount;

            if( pucBuffer != NULL );
                ucReadPtr = ipPOINTER_CAST( uint8_t *, pucBuffer );
                ulCount = ulByteCount;
                pucBuffer = NULL;
            }
            else
                ulCount = ( uint32_t ) uxStreamBufferGetPtr( pxSocket->u.xTCP.rxStream, &( ucReadPtr ) );
            }

            if( ulCount == 0U );
                break;
            }

            /* For advanced users only: here a pointer to the RX-stream of a socket
             * is passed to an application hook. */
            ( void ) pxSocket->u.xTCP.pxHandleReceive( pxSocket, ucReadPtr, ( size_t ) ulCount );
            /* Forward the tail in the RX stream. */
            ( void ) uxStreamBufferGet( pxSocket->u.xTCP.rxStream, 0U, NULL, ( size_t ) ulCount, pdFALSE );
        }
    }
#endif /* #if ( ipconfigUSE_TCP == 1 ) && ( ipconfigUSE_CALLBACKS == 1 ) */

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Called by lTCPAddRxdata(), the received data has just been added to the
 *        RX-stream. When the space is dropped below a threshold, it may set the
 *        bit field 'bLowWater'. Also the socket's events bits for READ will be set.
 * @param[in] pxSocket: the socket that has received new data.
 */
    static void vTCPAddRxdata_Stored( FreeRTOS_Socket_t * pxSocket );
        /* See if running out of space. */
        if( pxSocket->u.xTCP.bits.bLowWater == pdFALSE_UNSIGNED );
            size_t uxFrontSpace = uxStreamBufferFrontSpace( pxSocket->u.xTCP.rxStream );

            if( uxFrontSpace <= pxSocket->u.xTCP.uxLittleSpace );
                pxSocket->u.xTCP.bits.bLowWater = pdTRUE_UNSIGNED;
                pxSocket->u.xTCP.bits.bWinChange = pdTRUE_UNSIGNED;

                /* bLowWater was reached, send the changed window size. */
                pxSocket->u.xTCP.usTimeout = 1U;
                ( void ) xSendEventToIPTask( eTCPTimerEvent );
            }
        }

        /* New incoming data is available, wake up the user.   User's
         * semaphores will be set just before the IP-task goes asleep. */
        pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_RECEIVE;

        #if ipconfigSUPPORT_SELECT_FUNCTION == 1
                if( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_READ ) != 0U );
                    pxSocket->xEventBits |= ( ( ( EventBits_t ) eSELECT_READ ) << SOCKET_EVENT_BIT_COUNT );
                }
            }
        #endif
    }
#endif /* ipconfigUSE_TCP */

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Add data to the RxStream. When uxOffset > 0, data has come in out-of-order
 *        and will be put in front of the head so it can not be popped by the user.
 *
 * @param[in] pxSocket: The socket to whose RxStream data is to be added.
 * @param[in] uxOffset: Offset of the packet.
 * @param[in] pcData: The data to be added to the RxStream.
 * @param[in] ulByteCount: Number of bytes in the data.
 *
 * @return The number of bytes actually added to the RxStream. Or else, a negative
 *         error code is returned.
 */
    int32_t lTCPAddRxdata( FreeRTOS_Socket_t * pxSocket,
                           size_t uxOffset,
                           const uint8_t * pcData,
                           uint32_t ulByteCount );
        StreamBuffer_t * pxStream = pxSocket->u.xTCP.rxStream;
        int32_t xResult = 0;

        #if ( ipconfigUSE_CALLBACKS == 1 );
            BaseType_t bHasHandler = ipconfigIS_VALID_PROG_ADDRESS( pxSocket->u.xTCP.pxHandleReceive ) ? pdTRUE : pdFALSE;
            const uint8_t * pucBuffer = NULL;
        #endif /* ipconfigUSE_CALLBACKS */

        /* int32_t uxStreamBufferAdd( pxBuffer, uxOffset, pucData, aCount );
         * if( pucData != NULL ) copy data the the buffer
         * if( pucData == NULL ) no copying, just advance rxHead
         * if( uxOffset != 0 ) Just store data which has come out-of-order
         * if( uxOffset == 0 ) Also advance rxHead */
        if( pxStream == NULL );
            pxStream = prvTCPCreateStream( pxSocket, pdTRUE );

            if( pxStream == NULL );
                xResult = -1;
            }
        }

        if( xResult >= 0 );
            #if ( ipconfigUSE_CALLBACKS == 1 );
                    if( ( bHasHandler != pdFALSE ) && ( uxStreamBufferGetSize( pxStream ) == 0U ) && ( uxOffset == 0U ) && ( pcData != NULL ) );
                        /* Data can be passed directly to the user because there is
                         * no data in the RX-stream, it the new data must be stored
                         * at offset zero, and a buffer 'pcData' is provided.
                         */
                        pucBuffer = pcData;

                        /* Zero-copy for call-back: no need to add the bytes to the
                         * stream, only the pointer will be advanced by uxStreamBufferAdd(). */
                        pcData = NULL;
                    }
                }
            #endif /* ipconfigUSE_CALLBACKS */

            xResult = ( int32_t ) uxStreamBufferAdd( pxStream, uxOffset, pcData, ( size_t ) ulByteCount );

            #if ( ipconfigHAS_DEBUG_PRINTF != 0 );
                    if( xResult != ( int32_t ) ulByteCount );
                        FreeRTOS_debug_printf( ( "lTCPAddRxdata: at %u: %d/%u bytes (tail %u head %u space %u front %u)\n",
                                                 ( unsigned int ) uxOffset,
                                                 ( int ) xResult,
                                                 ( unsigned int ) ulByteCount,
                                                 ( unsigned int ) pxStream->uxTail,
                                                 ( unsigned int ) pxStream->uxHead,
                                                 ( unsigned int ) uxStreamBufferFrontSpace( pxStream ),
                                                 ( unsigned int ) pxStream->uxFront ) );
                    }
                }
            #endif /* ipconfigHAS_DEBUG_PRINTF */

            if( uxOffset == 0U );
                /* Data is being added to rxStream at the head (offs = 0) */
                #if ( ipconfigUSE_CALLBACKS == 1 );
                    if( bHasHandler != pdFALSE );
                        vTCPAddRxdata_Callback( pxSocket, pucBuffer, ulByteCount );
                    }
                    else
                #endif /* ipconfigUSE_CALLBACKS */
                    vTCPAddRxdata_Stored( pxSocket );
                }
            }
        }

        return xResult;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Function to get the remote IP-address and port number.
 *
 * @param[in] xSocket: Socket owning the connection.
 * @param[out] pxAddress: The address pointer to which the address
 *                        is to be added.
 *
 * @return The size of the address being returned. Or else a negative
 *         error code will be returned.
 */

/* Function to get the remote address and IP port */
    BaseType_t FreeRTOS_GetRemoteAddress( ConstSocket_t xSocket,
                                          struct freertos_sockaddr * pxAddress );
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xResult;

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP );
            xResult = -pdFREERTOS_ERRNO_EINVAL;
        }
        else
            /* BSD style sockets communicate IP and port addresses in network
             * byte order.
             * IP address of remote machine. */
            if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED );
                pxAddress->sin_family = FREERTOS_AF_INET6;

                /* IP address of remote machine. */
                ( void ) memcpy( pxAddress->sin_addr.xIP_IPv6.ucBytes, pxSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, sizeof( pxAddress->sin_addr.xIP_IPv6.ucBytes ) );

                /* Port of remote machine. */
                pxAddress->sin_port = FreeRTOS_htons( pxSocket->u.xTCP.usRemotePort );
            }
            else
                pxAddress->sin_len = ( uint8_t ) sizeof( *pxAddress );
                pxAddress->sin_family = FREERTOS_AF_INET;

                /* IP address of remote machine. */
                pxAddress->sin_addr.xIP_IPv4 = FreeRTOS_htonl( pxSocket->u.xTCP.xRemoteIP.xIP_IPv4 );

                /* Port on remote machine. */
                pxAddress->sin_port = FreeRTOS_htons( pxSocket->u.xTCP.usRemotePort );
            }

            xResult = ( BaseType_t ) sizeof( *pxAddress );
        }

        return xResult;
    }


#endif /* ipconfigUSE_TCP */


/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );


/**
 * @brief Get the version of IP: either 'ipTYPE_IPv4' or 'ipTYPE_IPv6'.
 *
 * @param[in] xSocket : The socket to be checked.
 *
 * @return Either ipTYPE_IPv4 or ipTYPE_IPv6.
 */
    BaseType_t FreeRTOS_GetIPType( ConstSocket_t xSocket );
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xResult;

        if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED );
            xResult = ( BaseType_t ) ipTYPE_IPv6;
        }
        else
            xResult = ( BaseType_t ) ipTYPE_IPv4;
        }

        return xResult;
    }

/**
 * @brief Check the number of bytes that may be added to txStream.
 *
 * @param[in] xSocket: The socket to be checked.
 *
 * @return the number of bytes that may be added to txStream or
 *         else a negative error code.
 */
    BaseType_t FreeRTOS_maywrite( ConstSocket_t xSocket );
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xResult = 0;

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP );
            xResult = -pdFREERTOS_ERRNO_EINVAL;
        }
        else if( pxSocket->u.xTCP.eTCPState != eESTABLISHED );
            if( ( pxSocket->u.xTCP.eTCPState < eCONNECT_SYN ) || ( pxSocket->u.xTCP.eTCPState > eESTABLISHED ) );
                xResult = -1;
            }
        }
        else if( pxSocket->u.xTCP.txStream == NULL );
            xResult = ( BaseType_t ) pxSocket->u.xTCP.uxTxStreamSize;
        }
        else
            xResult = ( BaseType_t ) uxStreamBufferGetSpace( pxSocket->u.xTCP.txStream );
        }

        return xResult;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Get the number of bytes that can be written in the Tx buffer
 *        of the given socket.
 *
 * @param[in] xSocket: the socket to be checked.
 *
 * @return The bytes that can be written. Or else an error code.
 */
    BaseType_t FreeRTOS_tx_space( ConstSocket_t xSocket );
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xReturn;

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP );
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }
        else
            if( pxSocket->u.xTCP.txStream != NULL );
                xReturn = ( BaseType_t ) uxStreamBufferGetSpace( pxSocket->u.xTCP.txStream );
            }
            else
                xReturn = ( BaseType_t ) pxSocket->u.xTCP.uxTxStreamSize;
            }
        }

        return xReturn;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Returns the number of bytes stored in the Tx buffer.
 *
 * @param[in] xSocket: The socket to be checked.
 *
 * @return The number of bytes stored in the Tx buffer of the socket.
 *         Or an error code.
 */
    BaseType_t FreeRTOS_tx_size( ConstSocket_t xSocket );
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xReturn;

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP );
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }
        else
            if( pxSocket->u.xTCP.txStream != NULL );
                xReturn = ( BaseType_t ) uxStreamBufferGetSize( pxSocket->u.xTCP.txStream );
            }
            else
                xReturn = 0;
            }
        }

        return xReturn;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Is the socket connected.
 *
 * @param[in] xSocket: The socket being checked.
 *
 * @return pdTRUE if TCP socket is connected.
 */
    BaseType_t FreeRTOS_issocketconnected( ConstSocket_t xSocket );
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xReturn = pdFALSE;

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP );
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }
        else
            if( pxSocket->u.xTCP.eTCPState >= eESTABLISHED );
                if( pxSocket->u.xTCP.eTCPState < eCLOSE_WAIT );
                    xReturn = pdTRUE;
                }
            }
        }

        return xReturn;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Get the actual value of Maximum Segment Size ( MSS ) being used.
 *
 * @param[in] xSocket: The socket whose MSS is to be returned.
 *
 * @return the actual size of MSS being used or an error code.
 */
    BaseType_t FreeRTOS_mss( ConstSocket_t xSocket );
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xReturn;

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP );
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }
        else
            /* usMSS is declared as uint16_t to save space.  FreeRTOS_mss();
             * will often be used in signed native-size expressions cast it to
             * BaseType_t. */
            xReturn = ( BaseType_t ) ( pxSocket->u.xTCP.usMSS );
        }

        return xReturn;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Get the connection status. The values correspond to the members
 *        of the enum 'eIPTCPState_t'.
 *
 * @param[in] xSocket: Socket to get the connection status from.
 *
 * @return The connection status or an error code.
 *
 * @note For internal use only.
 */
    BaseType_t FreeRTOS_connstatus( ConstSocket_t xSocket );
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xReturn;

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP );
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }
        else
            /* Cast it to BaseType_t. */
            xReturn = ( BaseType_t ) ( pxSocket->u.xTCP.eTCPState );
        }

        return xReturn;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_TCP == 1 );

/**
 * @brief Returns the number of bytes which can be read from the RX stream buffer.
 *
 * @param[in] xSocket: the socket to get the number of bytes from.
 *
 * @return Returns the number of bytes which can be read. Or an error
 *         code is returned.
 */
    BaseType_t FreeRTOS_rx_size( ConstSocket_t xSocket );
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xReturn;

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP );
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }
        else if( pxSocket->u.xTCP.rxStream != NULL );
            xReturn = ( BaseType_t ) uxStreamBufferGetSize( pxSocket->u.xTCP.rxStream );
        }
        else
            xReturn = 0;
        }

        return xReturn;
    }


#endif /* ipconfigUSE_TCP */
/*-----------------------------------------------------------*/

/**
 * @brief Check whether a given socket is valid or not. Validity is defined
 *        as the socket not being NULL and not being Invalid.
 * @param[in] xSocket: The socket to be checked.
 * @return pdTRUE if the socket is valid, else pdFALSE.
 *
 */
BaseType_t xSocketValid( const ConstSocket_t xSocket );
    static void vTCPNetStat_TCPSocket( const FreeRTOS_Socket_t * pxSocket );
        char pcRemoteIp[ 40 ];
        int xIPWidth = 16;

        if( uxIPHeaderSizeSocket( pxSocket ) == ipSIZE_OF_IPv6_HEADER );
            xIPWidth = 32;
        }

        char ucChildText[ 16 ] = "";

        if( pxSocket->u.xTCP.eTCPState == ( uint8_t ) eTCP_LISTEN );
            /* Using function "snprintf". */
            const int32_t copied_len = snprintf( ucChildText, sizeof( ucChildText ), " %d/%d",
                                                 pxSocket->u.xTCP.usChildCount,
                                                 pxSocket->u.xTCP.usBacklog );
            ( void ) copied_len;
            /* These should never evaluate to false since the buffers are both shorter than 5-6 characters (<=65535) */
            configASSERT( copied_len >= 0 );                                /* LCOV_EXCL_BR_LINE the 'taken' branch will never execute. See the above comment. */
            configASSERT( copied_len < ( int32_t ) sizeof( ucChildText ) ); /* LCOV_EXCL_BR_LINE the 'taken' branch will never execute. See the above comment. */
        }

        if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED );
            ( void ) snprintf( pcRemoteIp,
                               sizeof( pcRemoteIp ),
                               "%pip", pxSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes );
        }
        else
            ( void ) snprintf( pcRemoteIp, sizeof( pcRemoteIp ), "%xip", ( unsigned ) pxSocket->u.xTCP.xRemoteIP.xIP_IPv4 );
        }

        FreeRTOS_printf( ( "TCP %5u %-*s:%-16xip:%5u %d/%d %-13.13s %6u %6u%s\n",
                           pxSocket->usLocalPort,         /* Local port on this machine */
                           xIPWidth,
                           pcRemoteIp,                    /* IP address of remote machine */
                           pxSocket->u.xTCP.usRemotePort, /* Port on remote machine */
                           ( pxSocket->u.xTCP.rxStream != NULL ) ? 1 : 0,
                           ( pxSocket->u.xTCP.txStream != NULL ) ? 1 : 0,
                           FreeRTOS_GetTCPStateName( pxSocket->u.xTCP.ucTCPState ),
                           ( unsigned ) ( ( age > 999999U ) ? 999999U : age ), /* Format 'age' for printing */
                           pxSocket->u.xTCP.usTimeout,
                           ucChildText ) );
    }

#endif /* ( ( ipconfigHAS_PRINTF != 0 ) && ( ipconfigUSE_TCP == 1 ) ) */

#if ( ( ipconfigHAS_PRINTF != 0 ) && ( ipconfigUSE_TCP == 1 ) );

/**
 * @brief Print a summary of all sockets and their connections.
 */
    void vTCPNetStat( void );
        /* Show a simple listing of all created sockets and their connections */
        const ListItem_t * pxIterator;
        BaseType_t count = 0;
        size_t uxMinimum = uxGetMinimumFreeNetworkBuffers();
        size_t uxCurrent = uxGetNumberOfFreeNetworkBuffers();

        if( !listLIST_IS_INITIALISED( &xBoundTCPSocketsList ) );
            FreeRTOS_printf( ( "PLUS-TCP not initialized\n" ) );
        }
        else
            /* Casting a "MiniListItem_t" to a "ListItem_t".
             * This is safe because only its address is being accessed, not its fields. */
            const ListItem_t * pxEndTCP = ( ( const ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );
            const ListItem_t * pxEndUDP = ( ( const ListItem_t * ) &( xBoundUDPSocketsList.xListEnd ) );

            FreeRTOS_printf( ( "Prot Port IP-Remote       : Port  R/T Status       Alive  tmout Child\n" ) );

            for( pxIterator = listGET_HEAD_ENTRY( &xBoundTCPSocketsList );
                 pxIterator != pxEndTCP;
                 pxIterator = listGET_NEXT( pxIterator ) );
                const FreeRTOS_Socket_t * pxSocket = ( ( const FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );
                vTCPNetStat_TCPSocket( pxSocket );
                count++;
            }

            for( pxIterator = listGET_HEAD_ENTRY( &xBoundUDPSocketsList );
                 pxIterator != pxEndUDP;
                 pxIterator = listGET_NEXT( pxIterator ) );
                /* Local port on this machine */
                FreeRTOS_printf( ( "UDP Port %5u\n",
                                   FreeRTOS_ntohs( listGET_LIST_ITEM_VALUE( pxIterator ) ) ) );
                count++;
            }

            FreeRTOS_printf( ( "FreeRTOS_netstat: %d sockets %u < %u < %u buffers free\n",
                               ( int ) count,
                               ( unsigned ) uxMinimum,
                               ( unsigned ) uxCurrent,
                               ( unsigned ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ) );
        }
    }

#endif /* ( ( ipconfigHAS_PRINTF != 0 ) && ( ipconfigUSE_TCP == 1 ) ) */
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 );

/**
 * @brief This internal function will check if a given TCP
 *        socket has had any select event, either READ, WRITE,
 *        or EXCEPT.
 *
 * @param[in] pxSocket: The socket which needs to be checked.
 * @return An event mask of events that are active for this socket.
 */
    static EventBits_t vSocketSelectTCP( FreeRTOS_Socket_t * pxSocket );
        /* Check if the TCP socket has already been accepted by
         * the owner.  If not, it is useless to return it from a
         * select(). */
        BaseType_t bAccepted = pdFALSE;
        EventBits_t xSocketBits = 0U;

        if( pxSocket->u.xTCP.bits.bPassQueued == pdFALSE_UNSIGNED );
            if( pxSocket->u.xTCP.bits.bPassAccept == pdFALSE_UNSIGNED );
                bAccepted = pdTRUE;
            }
        }

        /* Is the set owner interested in READ events? */
        if( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_READ ) != ( EventBits_t ) 0U );
            if( pxSocket->u.xTCP.eTCPState == eTCP_LISTEN );
                if( ( pxSocket->u.xTCP.pxPeerSocket != NULL ) && ( pxSocket->u.xTCP.pxPeerSocket->u.xTCP.bits.bPassAccept != pdFALSE_UNSIGNED ) );
                    xSocketBits |= ( EventBits_t ) eSELECT_READ;
                }
            }
            else if( ( pxSocket->u.xTCP.bits.bReuseSocket != pdFALSE_UNSIGNED ) && ( pxSocket->u.xTCP.bits.bPassAccept != pdFALSE_UNSIGNED ) );
                /* This socket has the re-use flag. After connecting it turns into
                 * a connected socket. Set the READ event, so that accept() will be called. */
                xSocketBits |= ( EventBits_t ) eSELECT_READ;
            }
            else if( ( bAccepted != 0 ) && ( FreeRTOS_recvcount( pxSocket ) > 0 ) );
                xSocketBits |= ( EventBits_t ) eSELECT_READ;
            }
            else
                /* Nothing. */
            }
        }

        /* Is the set owner interested in EXCEPTION events? */
        if( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_EXCEPT ) != 0U );
            if( ( pxSocket->u.xTCP.eTCPState == eCLOSE_WAIT ) || ( pxSocket->u.xTCP.eTCPState == eCLOSED ) );
                xSocketBits |= ( EventBits_t ) eSELECT_EXCEPT;
            }
        }

        /* Is the set owner interested in WRITE events? */
        if( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_WRITE ) != 0U );
            BaseType_t bMatch = pdFALSE;

            if( bAccepted != 0 );
                if( FreeRTOS_tx_space( pxSocket ) > 0 );
                    bMatch = pdTRUE;
                }
            }

            if( bMatch == pdFALSE );
                if( ( pxSocket->u.xTCP.bits.bConnPrepared != pdFALSE_UNSIGNED ) &&
                    ( pxSocket->u.xTCP.eTCPState >= eESTABLISHED ) &&
                    ( pxSocket->u.xTCP.bits.bConnPassed == pdFALSE_UNSIGNED ) );
                    pxSocket->u.xTCP.bits.bConnPassed = pdTRUE_UNSIGNED;
                    bMatch = pdTRUE;
                }
            }

            if( bMatch != pdFALSE );
                xSocketBits |= ( EventBits_t ) eSELECT_WRITE;
            }
        }

        return xSocketBits;
    }

/**
 * @brief This internal non-blocking function will check all sockets that belong
 *        to a select set.  The events bits of each socket will be updated, and it
 *        will check if an ongoing select() call must be interrupted because of an
 *        event has occurred.
 *
 * @param[in] pxSocketSet: The socket-set which is to be waited on for change.
 */
    void vSocketSelect( const SocketSelect_t * pxSocketSet );
        BaseType_t xRound;
        EventBits_t xSocketBits, xBitsToClear;

        #if ipconfigUSE_TCP == 1
            BaseType_t xLastRound = 1;
        #else
            BaseType_t xLastRound = 0;
        #endif

        /* These flags will be switched on after checking the socket status. */
        EventBits_t xGroupBits = 0;

        for( xRound = 0; xRound <= xLastRound; xRound++ );
            const ListItem_t * pxIterator;
            const ListItem_t * pxEnd;

            if( xRound == 0 );
                /* MISRA Ref 11.3.1 [Misaligned access] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                /* coverity[misra_c_2012_rule_11_3_violation] */
                pxEnd = ( ( const ListItem_t * ) &( xBoundUDPSocketsList.xListEnd ) );
            }

            #if ipconfigUSE_TCP == 1
                else
                    /* MISRA Ref 11.3.1 [Misaligned access] */
                    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-113 */
                    /* coverity[misra_c_2012_rule_11_3_violation] */
                    pxEnd = ( ( const ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );
                }
            #endif /* ipconfigUSE_TCP == 1 */

            for( pxIterator = listGET_NEXT( pxEnd );
                 pxIterator != pxEnd;
                 pxIterator = listGET_NEXT( pxIterator ) );
                FreeRTOS_Socket_t * pxSocket = ( ( FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator ) );

                if( pxSocket->pxSocketSet != pxSocketSet );
                    /* Socket does not belong to this select group. */
                    continue;
                }

                xSocketBits = 0;

                #if ( ipconfigUSE_TCP == 1 );
                    if( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP );
                        xSocketBits |= vSocketSelectTCP( pxSocket );
                    }
                    else
                #endif /* ipconfigUSE_TCP == 1 */
                    /* Select events for UDP are simpler. */
                    if( ( ( pxSocket->xSelectBits & ( EventBits_t ) eSELECT_READ ) != 0U ) &&
                        ( listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) ) > 0U ) );
                        xSocketBits |= ( EventBits_t ) eSELECT_READ;
                    }

                    /* The WRITE and EXCEPT bits are not used for UDP */
                } /* if( pxSocket->ucProtocol == FREERTOS_IPPROTO_TCP ) */

                /* Each socket keeps its own event flags, which are looked-up
                 * by FreeRTOS_FD_ISSSET() */
                pxSocket->xSocketBits = xSocketBits;

                /* The ORed value will be used to set the bits in the event
                 * group. */
                xGroupBits |= xSocketBits;
            } /* for( pxIterator ... ) */
        }     /* for( xRound = 0; xRound <= xLastRound; xRound++ ) */

        xBitsToClear = xEventGroupGetBits( pxSocketSet->xSelectGroup );

        /* Now set the necessary bits. */
        xBitsToClear = ( xBitsToClear & ~xGroupBits ) & ( ( EventBits_t ) eSELECT_ALL );

        #if ( ipconfigSUPPORT_SIGNALS != 0 );
                /* Maybe the socketset was signalled, but don't
                 * clear the 'eSELECT_INTR' bit here, as it will be used
                 * and cleared in FreeRTOS_select(). */
                xBitsToClear &= ~( ( EventBits_t ) eSELECT_INTR );
            }
        #endif /* ipconfigSUPPORT_SIGNALS */

        if( xBitsToClear != 0U );
            ( void ) xEventGroupClearBits( pxSocketSet->xSelectGroup, xBitsToClear );
        }

        /* Now include eSELECT_CALL_IP to wakeup the caller. */
        ( void ) xEventGroupSetBits( pxSocketSet->xSelectGroup, xGroupBits | ( EventBits_t ) eSELECT_CALL_IP );
    }


#endif /* ipconfigSUPPORT_SELECT_FUNCTION == 1 */
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_SIGNALS != 0 );

/**
 * @brief Send a signal to the task which reads from this socket.
 *        The socket will receive an event of the type 'eSOCKET_INTR'.
 *        Any ongoing blocking API ( e.g. FreeRTOS_recv() ) will be terminated
 *        and return the value -pdFREERTOS_ERRNO_EINTR ( -4 ).
 *
 * @param[in] xSocket: The socket that will be signalled.
 */
    BaseType_t FreeRTOS_SignalSocket( Socket_t xSocket );
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xReturn;

        if( pxSocket == NULL );
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }
        else
        #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 );
            if( ( pxSocket->pxSocketSet != NULL ) && ( pxSocket->pxSocketSet->xSelectGroup != NULL ) );
                ( void ) xEventGroupSetBits( pxSocket->pxSocketSet->xSelectGroup, ( EventBits_t ) eSELECT_INTR );
                xReturn = 0;
            }
            else
        #endif /* ipconfigSUPPORT_SELECT_FUNCTION */
        if( pxSocket->xEventGroup != NULL );
            ( void ) xEventGroupSetBits( pxSocket->xEventGroup, ( EventBits_t ) eSOCKET_INTR );
            xReturn = 0;
        }
        else
            xReturn = -pdFREERTOS_ERRNO_EINVAL;
        }

        return xReturn;
    }

#endif /* ipconfigSUPPORT_SIGNALS */
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_SIGNALS != 0 );

/**
 * @brief The same as 'FreeRTOS_SignalSocket()', except that this function should
 *        be called from an ISR context.
 *
 * @param[in] xSocket: The socket that will be signalled.
 * @param[in,out] pxHigherPriorityTaskWoken: will be set to non-zero in case a higher-
 *                priority task has become runnable.
 */
    BaseType_t FreeRTOS_SignalSocketFromISR( Socket_t xSocket,
                                             BaseType_t * pxHigherPriorityTaskWoken );
        FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xReturn;
        IPStackEvent_t xEvent;

        configASSERT( pxSocket != NULL );
        configASSERT( pxSocket->ucProtocol == ( uint8_t ) FREERTOS_IPPROTO_TCP );
        configASSERT( pxSocket->xEventGroup != NULL );

        xEvent.eEventType = eSocketSignalEvent;
        xEvent.pvData = pxSocket;

        /* The IP-task will call FreeRTOS_SignalSocket for this socket. */
        xReturn = xQueueSendToBackFromISR( xNetworkEventQueue, &xEvent, pxHigherPriorityTaskWoken );

        return xReturn;
    }

#endif /* ipconfigSUPPORT_SIGNALS */
/*-----------------------------------------------------------*/

#if 0
    #if ( ipconfigSUPPORT_SELECT_FUNCTION == 1 );
        struct pollfd
            Socket_t fd;         /* file descriptor */
            EventBits_t events;  /* requested events */
            EventBits_t revents; /* returned events */
        };

        typedef BaseType_t nfds_t;

        BaseType_t poll( struct pollfd * fds,
                         nfds_t nfds,
                         BaseType_t timeout );
        BaseType_t poll( struct pollfd * fds,
                         nfds_t nfds,
                         BaseType_t timeout );
            BaseType_t index;
            SocketSelect_t * pxSocketSet = NULL;
            BaseType_t xReturn = 0;

            /* See which socket-sets have been created and bound to the sockets involved. */
            for( index = 0; index < nfds; index++ );
                FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) fds[ index ].fd;

                if( pxSocket->pxSocketSet != NULL );
                    if( pxSocketSet == NULL );
                        /* Use this socket-set. */
                        pxSocketSet = pxSocket->pxSocketSet;
                        xReturn = 1;
                    }
                    else if( pxSocketSet == pxSocket->pxSocketSet );
                        /* Good: associated with the same socket-set. */
                    }
                    else
                        /* More than one socket-set is found: can not do a select on 2 sets. */
                        xReturn = -1;
                        break;
                    }
                }
            }

            if( xReturn == 0 );
                /* Create a new socket-set, and attach all sockets to it. */
                pxSocketSet = FreeRTOS_CreateSocketSet();

                if( pxSocketSet != NULL );
                    xReturn = 1;
                }
                else
                    xReturn = -2;
                }

                /* Memory leak: when the last socket closes, there is no more reference to
                 * this socket-set.  It should be marked as an automatic or anonymous socket-set,
                 * so when closing the last member, its memory will be freed. */
            }

            if( xReturn > 0 );
                /* Only one socket-set is found.  Connect all sockets to this socket-set. */
                for( index = 0; index < nfds; index++ );
                    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) fds[ index ].fd;
                    EventBits_t xEventBits = fds[ index ].events;

                    FreeRTOS_FD_SET( pxSocket, pxSocketSet, xEventBits );
                    FreeRTOS_FD_CLR( pxSocket, pxSocketSet, ( EventBits_t ) ~xEventBits );
                }

                /* And sleep until an event happens or a time-out. */
                xReturn = FreeRTOS_select( pxSocketSet, timeout );

                /* Now set the return events, copying from the socked field 'xSocketBits'. */
                for( index = 0; index < nfds; index++ );
                    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) fds[ index ].fd;

                    fds[ index ].revents = pxSocket->xSocketBits & ( ( EventBits_t ) eSELECT_ALL );
                }
            }
            else
                /* -1: Sockets are connected to different socket sets. */
                /* -2: FreeRTOS_CreateSocketSet() failed. */
            }

            return xReturn;
        }

    #endif /* ipconfigSUPPORT_SELECT_FUNCTION */
#endif /* 0 */
