/*
 * FreeRTOS+TCP V2.3.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */


#ifndef DDOS_TESETING_H

/*
 * ddos 1 2 30000   A 30-second UDP attack, using delays of 2 ms between packet.
 * ddos 1 0 120000  A 2-minute attack, no delays between packets.
 * ddos 0           Stop the DDoS UDP attack
 * ddos 2           Show some logging ( number of packs ).
 */
void vDDoSCommand( char * pcCommand );

/*
 * server 32002  Create an echoserver on port 32002
 */
void vTCPServerCommand( char * pcCommand );

/*
 * client 192.168.2.5 300000000  Exchange 300000000 bytes with an echo server on 192.168.2.5
 */
void vTCPClientCommand( char * pcCommand );

/*
 * buffer 80 10000    Let 80% of the buffer allocation succeed for 10 seconds
 * buffer 0 20000     Let all buffer allocations fail for 20 seconds
 */
void vBufferCommand( char * pcCommand );

#endif /* ifndef DDOS_TESETING_H */
