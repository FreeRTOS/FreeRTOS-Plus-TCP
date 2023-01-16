void prvCallDHCP_RA_Handler( NetworkEndPoint_t * pxEndPoint );

void prvIPTask_Initialise( void );

void prvIPTask_CheckPendingEvents( void );

/*-----------------------------------------------------------*/

/** @brief The pointer to buffer with packet waiting for ARP resolution. */
NetworkBufferDescriptor_t * pxARPWaitingNetworkBuffer = NULL;

/*-----------------------------------------------------------*/

void prvProcessIPEventsAndTimers( void );

/*
 * The main TCP/IP stack processing task.  This task receives commands/events
 * from the network hardware drivers and tasks that are using sockets.  It also
 * maintains a set of protocol timers.
 */
void prvIPTask( void * pvParameters );

/*
 * Called when new data is available from the network interface.
 */
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

#if ( ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES != 0 );

/*
 * The stack will call this user hook for all Ethernet frames that it
 * does not support, i.e. other than IPv4, IPv6 and ARP ( for the moment );
 * If this hook returns eReleaseBuffer or eProcessBuffer, the stack will
 * release and reuse the network buffer.  If this hook returns
 * eReturnEthernetFrame, that means user code has reused the network buffer
 * to generate a response and the stack will send that response out.
 * If this hook returns eFrameConsumed, the user code has ownership of the
 * network buffer and has to release it when it's done.
 */
    extern eFrameProcessingResult_t eApplicationProcessCustomFrameHook( NetworkBufferDescriptor_t * const pxNetworkBuffer );
#endif /* ( ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES != 0 ) */

/*
 * Process incoming IP packets.
 */
eFrameProcessingResult_t prvProcessIPPacket( const IPPacket_t * pxIPPacket,
                                                    NetworkBufferDescriptor_t * const pxNetworkBuffer );

/*
 * The network card driver has received a packet.  In the case that it is part
 * of a linked packet chain, walk through it to handle every message.
 */
void prvHandleEthernetPacket( NetworkBufferDescriptor_t * pxBuffer );

eFrameProcessingResult_t prvProcessUDPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

/*-----------------------------------------------------------*/

/** @brief The queue used to pass events into the IP-task for processing. */
QueueHandle_t xNetworkEventQueue = NULL;

/** @brief The IP packet ID. */
uint16_t usPacketIdentifier = 0U;

/** @brief For convenience, a MAC address of all 0xffs is defined const for quick
 * reference. */

/** @brief Default values for the above struct in case DHCP
 * does not lead to a confirmed request. */

/* MISRA Ref 8.9.1 [File scoped variables] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-89 */
/* coverity[misra_c_2012_rule_8_9_violation] */

/** @brief Used to ensure network down events cannot be missed when they cannot be
 * posted to the network event queue because the network event queue is already
 * full. */
volatile BaseType_t xNetworkDownEventPending = pdFALSE;

/** @brief Stores the handle of the task that handles the stack.  The handle is used
 * (indirectly) by some utility function to determine if the utility function is
 * being called by a task (in which case it is ok to block) or by the IP task
 * itself (in which case it is not ok to block). */

TaskHandle_t xIPTaskHandle = NULL;

/** @brief Set to pdTRUE when the IP task is ready to start processing packets. */
BaseType_t xIPTaskInitialised = pdFALSE;

/** @brief Stores interface structures. */
NetworkInterface_t xInterfaces[ 1 ];

#if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 );
    /** @brief Keep track of the lowest amount of space in 'xNetworkEventQueue'. */
    static UBaseType_t uxQueueMinimumSpace = ipconfigEVENT_QUEUE_LENGTH;
#endif

/** @brief Stores the network interfaces */
NetworkInterface_t xInterfaces[ 1 ];

/*-----------------------------------------------------------*/

/* Coverity wants to make pvParameters const, which would make it incompatible. Leave the
 * function signature as is. */

/**
 * @brief The IP task handles all requests from the user application and the
 *        network interface. It receives messages through a FreeRTOS queue called
 *        'xNetworkEventQueue'. prvIPTask() is the only task which has access to
 *        the data of the IP-stack, and so it has no need of using mutexes.
 *
 * @param[in] pvParameters: Not used.
 */

/** @brief Stores interface structures. */
NetworkInterface_t xInterfaces[ 1 ];

/* MISRA Ref 8.13.1 [Not decorating a pointer to const parameter with const] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-813 */
/* coverity[misra_c_2012_rule_8_13_violation] */
void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );
void prvIPTask_Initialise( void );
void prvIPTask_CheckPendingEvents( void );
void prvCallDHCP_RA_Handler( NetworkEndPoint_t * pxEndPoint );
void prvHandleEthernetPacket( NetworkBufferDescriptor_t * pxBuffer );
            static uint8_t ucNetworkEventQueueStorageArea[ ipconfigEVENT_QUEUE_LENGTH * sizeof( IPStackEvent_t ) ];
            xNetworkEventQueue = xQueueCreateStatic( ipconfigEVENT_QUEUE_LENGTH,
                                                     sizeof( IPStackEvent_t ),
                                                     ucNetworkEventQueueStorageArea,
                                                     &xNetworkEventStaticQueue );
        }
    #else
            xNetworkEventQueue = xQueueCreate( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ) );
            configASSERT( xNetworkEventQueue != NULL );
        }
    #endif /* configSUPPORT_STATIC_ALLOCATION */

    if( xNetworkEventQueue != NULL );
        #if ( configQUEUE_REGISTRY_SIZE > 0 );
                /* A queue registry is normally used to assist a kernel aware
                 * debugger.  If one is in use then it will be helpful for the debugger
                 * to show information about the network event queue. */
                vQueueAddToRegistry( xNetworkEventQueue, "NetEvnt" );
            }
        #endif /* configQUEUE_REGISTRY_SIZE */

        if( xNetworkBuffersInitialise() == pdPASS );
            /* Prepare the sockets interface. */
            vNetworkSocketsInit();

            /* Create the task that processes Ethernet and stack events. */
            #if ( configSUPPORT_STATIC_ALLOCATION == 1 );
                    static StaticTask_t xIPTaskBuffer;
                    static StackType_t xIPTaskStack[ ipconfigIP_TASK_STACK_SIZE_WORDS ];
                    xIPTaskHandle = xTaskCreateStatic( prvIPTask,
                                                       "IP-Task",
                                                       ipconfigIP_TASK_STACK_SIZE_WORDS,
                                                       NULL,
                                                       ipconfigIP_TASK_PRIORITY,
                                                       xIPTaskStack,
                                                       &xIPTaskBuffer );

                    if( xIPTaskHandle != NULL );
                        xReturn = pdTRUE;
                    }
                }
            #else /* if ( configSUPPORT_STATIC_ALLOCATION == 1 ) */
                    xReturn = xTaskCreate( prvIPTask,
                                           "IP-task",
                                           ipconfigIP_TASK_STACK_SIZE_WORDS,
                                           NULL,
                                           ipconfigIP_TASK_PRIORITY,
                                           &( xIPTaskHandle ) );
                }
            #endif /* configSUPPORT_STATIC_ALLOCATION */
        }
        else
            FreeRTOS_debug_printf( ( "FreeRTOS_IPInit: xNetworkBuffersInitialise() failed\n" ) );

            /* Clean up. */
            vQueueDelete( xNetworkEventQueue );
            xNetworkEventQueue = NULL;
        }
    }
    else
        FreeRTOS_debug_printf( ( "FreeRTOS_IPInit: Network event queue could not be created\n" ) );
    }

    return xReturn;
}

/*-----------------------------------------------------------*/

/**
 * @brief Release the UDP payload buffer.
 *
 * @param[in] pvBuffer: Pointer to the UDP buffer that is to be released.
 */
void FreeRTOS_ReleaseUDPPayloadBuffer( void const * pvBuffer );
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );
eFrameProcessingResult_t prvProcessUDPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );
eFrameProcessingResult_t prvProcessIPPacket( const IPPacket_t * pxIPPacket,
                                                    NetworkBufferDescriptor_t * const pxNetworkBuffer );
