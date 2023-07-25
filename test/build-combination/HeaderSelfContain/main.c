/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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

/**
 * @file main.c
 * @brief Implements the main function.
 */

/* FreeRTOS include. */
#include <FreeRTOS.h>

/* System application includes. */
#if defined TEST_HEADER_INC_ONLY_DHCP
    #include "FreeRTOS_DHCP.h"
#elif defined TEST_HEADER_INC_ONLY_DNS
    #include "FreeRTOS_DNS.h"
#elif defined TEST_HEADER_INC_ONLY_IP
    #include "FreeRTOS_IP.h"
#elif defined TEST_HEADER_INC_ONLY_ND
    #include "FreeRTOS_ND.h"
#elif defined TEST_HEADER_INC_ONLY_ROUTING
    #include "FreeRTOS_Routing.h"
#elif defined TEST_HEADER_INC_ONLY_SOCKETS
    #include "FreeRTOS_Sockets.h"
#elif defined TEST_HEADER_INC_ONLY_NETWORKBUFFERMANAGEMENT
    #include "NetworkBufferManagement.h"
#elif defined TEST_HEADER_INC_ONLY_NETWORKINTERFACE
    #include "NetworkInterface.h"
#endif /* if defined TEST_HEADER_INC_ONLY_DHCP */

/*-----------------------------------------------------------*/
int main( void )
{
    return 0;
}
