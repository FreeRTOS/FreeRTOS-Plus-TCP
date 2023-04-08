/*
 * eventlogging.h
 */

#if !defined( __EVENTLOGGING_H__ )

    #ifndef LOG_EVENT_NAME_LEN
        #define LOG_EVENT_NAME_LEN    32
    #endif

    #ifndef LOG_EVENT_COUNT
        #define LOG_EVENT_COUNT    1024
    #endif

    #define __EVENTLOGGING_H__

    #ifndef EVENT_MAY_WRAP
        #define EVENT_MAY_WRAP    1
    #endif

    #ifndef USE_LOG_EVENT
        #define USE_LOG_EVENT    0
    #endif

    #if USE_LOG_EVENT

        typedef struct _SLogEvent
        {
            unsigned ullTimestamp;
            char pcMessage[ LOG_EVENT_NAME_LEN ];
        } SLogEvent;

        typedef struct _SEventLogging
        {
            unsigned
                hasInit : 1,
                initOk : 1,
                onhold : 1,
                delayedHold : 1;
            int delayCount;
            int wrapped;
            int writeIndex;
            SLogEvent * events;
        } SEventLogging;

        extern SEventLogging xEventLogs;

    #endif /* USE_LOG_EVENT */

    #ifdef __cplusplus
        extern "C" {
    #endif

    #if USE_LOG_EVENT
        int iEventLogInit( void );
        int iEventLogClear( void );
        #ifdef WIN32
            void eventLogAdd( const char * apFmt,
                              ... );
        #else
            void eventLogAdd( const char * apFmt,
                              ... ) __attribute__( ( format( __printf__, 1, 2 ) ) );
        #endif
        const char * eventLogLast();

        void eventLogDump( void );
        void eventFreeze( void );
        void startDelayedFreeze( BaseType_t xEventCount );
    #else /* if USE_LOG_EVENT */
        static __inline int iEventLogInit( void )
        {
            return 1;
        }
        static __inline void iEventLogClear( void )
        {
        }
        static __inline void eventLogAdd( const char * apFmt,
                                          ... )
        #ifndef WIN32
            __attribute__( ( format( __printf__, 1, 2 ) ) );
        #else
            ;
        #endif
        static __inline void eventLogAdd( const char * apFmt,
                                          ... )
        {
            if( apFmt )
            {
            }
        }
        static __inline const char * eventLogLast( void )
        {
            return "";
        }
        static __inline void eventLogDump( void )
        {
        }

        static __inline void eventFreeze( void )
        {
        }
    #endif /* USE_LOG_EVENT */

    #ifdef __cplusplus
        } /* extern "C" */
    #endif

#endif /* __EVENTLOGGING_H__ */
