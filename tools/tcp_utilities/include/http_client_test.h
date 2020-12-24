/*
 *  FreeRTOS V8.2.2 - Copyright (C) 2015 Real Time Engineers Ltd.
 *  All rights reserved
 */

#ifndef HTTP_CLIENT_TEST_H
#define HTTP_CLIENT_TEST_H

/* Wake-up a HTTP client task. aIndex */
void wakeupHTTPClient( size_t uxIndex,
                       const char * pcHost,
                       const char * pcFileName,
                       BaseType_t xIPType );

/*
 * Create the TCP (HTTP) echo client tasks.
 */
void vStartHTTPClientTest( uint16_t usTaskStackSize,
                           UBaseType_t uxTaskPriority );
BaseType_t xAreSingleTaskTCPEchoClientsStillRunning( void );

#endif /* HTTP_CLIENT_TEST_H */
