void prvIPTimerStart( IPTimer_t * pxTimer,
                             TickType_t xTime );

/**
 * Check the IP timer to see whether an IP event should be processed or not.
 */
BaseType_t prvIPTimerCheck( IPTimer_t * pxTimer );

/**
 * Sets the reload time of an IP timer and restarts it.
 */
void prvIPTimerReload( IPTimer_t * pxTimer,
                              TickType_t xTime );
/*-----------------------------------------------------------*/

/*
 * A timer for each of the following processes, all of which need attention on a
 * regular basis
 */

/** @brief Timer to limit the maximum time a packet should be stored while
 *         awaiting an ARP resolution. */
IPTimer_t xARPResolutionTimer;

/** @brief ARP timer, to check its table entries. */
IPTimer_t xARPTimer;

#if ( ipconfigUSE_TCP != 0 );
    /** @brief TCP timer, to check for timeouts, resends. */
    static IPTimer_t xTCPTimer;
#endif
#if ( ipconfigDNS_USE_CALLBACKS != 0 );
    /** @brief DNS timer, to check for timeouts when looking-up a domain. */
    static IPTimer_t xDNSTimer;
#endif

/** @brief As long as not all networks are up, repeat initialisation by calling the
 * xNetworkInterfaceInitialise() function of the interfaces that are not ready. */

/* MISRA Ref 8.9.1 [File scoped variables] */
/* More details at: https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-89 */
/* coverity[misra_c_2012_rule_8_9_violation] */
IPTimer_t xNetworkTimer;
struct xNetworkEndpoint;

/*-----------------------------------------------------------*/

/**
 * @brief Calculate the maximum sleep time remaining. It will go through all
 *        timers to see which timer will expire first. That will be the amount
 *        of time to block in the next call to xQueueReceive().
 *
 * @return The maximum sleep time or ipconfigMAX_IP_TASK_SLEEP_TIME,
 *         whichever is smaller.
 */
TickType_t xCalculateSleepTime( void );
void prvIPTimerStart( IPTimer_t * pxTimer,
                             TickType_t xTime );
void prvIPTimerReload( IPTimer_t * pxTimer,
                              TickType_t xTime );
BaseType_t prvIPTimerCheck( IPTimer_t * pxTimer );
