/*
 * plus_tcp_demo_cli.h
 *
 * This module will handle a set of commands that help with integration testing.
 */

#ifndef PLUS_TCP_DEMO_CLI_H

    #if __cplusplus
        extern "C" {
    #endif

/*
 * Handle a CLI command.
 * Returns zero when the command was recognised and handled.
 */
    BaseType_t xHandleTestingCommand( char * pcBuffer,
                                      size_t uxBufferSize );

/*
 * Do the regular checks.
 */
    void xHandleTesting( void );

    #if ( ipconfigMULTI_INTERFACE != 0 )

/*
 * Show all properties of an end-point.
 */
        void showEndPoint( NetworkEndPoint_t * pxEndPoint );
    #endif

/*/ * 'xServerSemaphore' should be declared in main.c * / */
/*extern SemaphoreHandle_t xServerSemaphore; */

    #if __cplusplus
        } /* extern "C" */
    #endif

    extern int verboseLevel;

#endif /* PLUS_TCP_DEMO_CLI_H */
