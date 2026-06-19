/*
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 */

/*
 * How to catch an assert:
 * - save a jump buffer where execution will resume after the assert
 * - setup a handler for the abort signal, call longjmp within
 * - optional - close stderr ( fd 2 ) to discard the assert message
 *
 * Unity also does a longjmp within its TEST_ASSERT* macros,
 * so the macro below restores stderr and the prior abort handler
 * before calling the Unity macro.
 */

#ifndef CATCH_ASSERT_H_
#define CATCH_ASSERT_H_

#include <setjmp.h>
#include <signal.h>
#include <unistd.h>

/* Global state apology: Sigaction offers no context. */
static sigjmp_buf catch_waypoint;

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-function"
static void catch_rollBack( int signal )
{
    siglongjmp( catch_waypoint, signal );
}
static void catch_setSigabrtHandler(void)
{
    struct sigaction sa = { 0 };
    sa.sa_handler = catch_rollBack;
    sigaction( SIGABRT, &sa, NULL );
}
static int catch_saveStderr()
{
    int savedStderr = dup( 2 );
    close( 2 );
    return savedStderr;
}
static void catch_restoreStderr(int savedStderr)
{
    dup2( savedStderr, 2 );
    close( savedStderr );
}
#pragma GCC diagnostic pop

#define catch_assert( x )                                  \
    do {                                                   \
        int catch_stderr = catch_saveStderr();             \
        int catch_signal = sigsetjmp( catch_waypoint, 1 ); \
        if( catch_signal == 0 )                            \
        {                                                  \
            catch_setSigabrtHandler();                     \
            x;                                             \
        }                                                  \
        catch_restoreStderr( catch_stderr );               \
        TEST_ASSERT_EQUAL( SIGABRT, catch_signal );        \
    } while( 0 )

#endif /* ifndef CATCH_ASSERT_H_ */
