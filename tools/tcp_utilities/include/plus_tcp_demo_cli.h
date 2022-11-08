/*
 * plus_tcp_demo_cli.h
 *
 * This module will handle a set of commands that help with integration testing.
 */

#ifndef PLUS_TCP_DEMO_CLI_H

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
 * Show all properties of all end-points.
 */
    void showEndPoints( NetworkInterface_t * pxInterface );

#endif

extern int verboseLevel;

/*/ * 'xServerSemaphore' should be declared in main.c * / */
/*extern SemaphoreHandle_t xServerSemaphore; */

#endif /* PLUS_TCP_DEMO_CLI_H */
