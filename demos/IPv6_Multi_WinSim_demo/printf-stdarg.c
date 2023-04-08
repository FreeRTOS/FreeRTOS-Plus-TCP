/*
 *  Copyright 2001, 2002 Georges Menie (www.menie.org)
 *  stdarg version contributed by Christian Ettinger
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  Changes for the FreeRTOS ports:
 *
 *  - The dot in "%-8.8s"
 *  - The specifiers 'l' (long) and 'L' (int64_t)
 *  - The specifier 'u' for unsigned
 *  - Dot notation for IP addresses:
 *    sprintf("IP = %xip\n", 0xC0A80164);
 *    will produce "IP = 192.168.1.100\n"
 *    sprintf("IP = %pip\n", pxIPv6_Address);
 */

#include <stdarg.h>
#include <stdio.h>

#include <stdlib.h>
#include <string.h>

#if ( USE_FREERTOS != 0 )
    #include "FreeRTOS.h"
#else
    #include <stdint.h>
    typedef int        BaseType_t;
    typedef uint32_t   TickType_t;
    #define pdTRUE     1
    #define pdFALSE    0
    #define pdMS_TO_TICKS( x )    ( x )
#endif

int sprintf( char * apBuf,
             const char * apFmt,
             ... );

/*
 * Return 1 for readable, 2 for writeable, 3 for both.
 * Function must be provided by the application.
 */
extern BaseType_t xApplicationMemoryPermissions( uint32_t aAddress );
extern void vOutputChar( const char cChar,
                         const TickType_t xTicksToWait );

#ifdef __GNUC__

    __attribute__( ( weak ) ) BaseType_t xApplicationMemoryPermissions( uint32_t aAddress )
    {
        ( void ) aAddress;
        /* Return 1 for readable, 2 for writeable, 3 for both. */
        return 0x03;
    }


    __attribute__( ( weak ) ) void vOutputChar( const char cChar,
                                                const TickType_t xTicksToWait )
    {
        ( void ) cChar;
        ( void ) xTicksToWait;
        /* Do nothing. */
    }

#endif /* __GNUC__ */

static const TickType_t xTicksToWait = pdMS_TO_TICKS( 20 );

int tiny_printf( const char * format,
                 ... );

/* Defined here: write a large amount as GB, MB, KB or bytes */
const char * mkSize( uint64_t aSize,
                     char * apBuf,
                     int aLen );

typedef union
{
    uint8_t ucBytes[ 4 ];
    uint16_t ucShorts[ 2 ];
    uint32_t ulWords[ 1 ];
} _U32;

struct xPrintFlags
{
    int base;       /**< The number should be printed as either decimal (10), hexdecimal (16) or octal (8). */
    int width;      /**< The total width of the thing to be printed, padded with a '0' or a space when needed. */
    int printLimit; /**< Total width of a number, will get leading zero's. */
    unsigned
        letBase : 8,
        pad_zero : 1,  /**< Use '0', not a space for padding. */
        pad_right : 1, /**< Padding: right adjusted. */
        isSigned : 1,  /**< The number is signed. */
        isNumber : 1,  /**< A numeric value is to be printed. */
        long32 : 1,    /**< Not used as long is the same as unsigned. */
        long64 : 1;    /**< The number is 64-bits. */
};

struct SStringBuf
{
    char * str;               /**< Points to the location where the next byte can be written. */
    const char * orgStr;      /**< Points to the buffer supplied by the caller. */
    const char * nulPos;      /**< Points to the last location that may be written, will be nulled */
    int curLen;               /**< The number of bytes that have been written so far. */
    struct xPrintFlags flags; /**< Some flags that indicate how a value shall be written. */
};

#ifdef __GNUC__
    static const _U32 u32 =
    {
        ucBytes : { 0, 1, 2, 3 }
    };
#else
    static const _U32 u32 = { 0, 1, 2, 3 };
#endif

static void strbuf_init( struct SStringBuf * apStr,
                         char * apBuf,
                         const char * apMaxStr )
{
    apStr->str = apBuf;
    apStr->orgStr = apBuf;
    apStr->nulPos = apMaxStr - 1;
    apStr->curLen = 0;

    memset( &apStr->flags, '\0', sizeof apStr->flags );
}
/*-----------------------------------------------------------*/

static BaseType_t strbuf_printchar( struct SStringBuf * apStr,
                                    int c )
{
    if( apStr->str == NULL )
    {
        /* There is no str pointer: printing to stdout. */
        vOutputChar( ( char ) c, xTicksToWait );
        apStr->curLen++;
        return pdTRUE;
    }

    if( apStr->str < apStr->nulPos )
    {
        /* There is space for this character. */
        *( apStr->str++ ) = c;
        apStr->curLen++;
        return pdTRUE;
    }

    if( apStr->str == apStr->nulPos )
    {
        /* nulPos is the last writeable character, zero it. */
        *( apStr->str++ ) = '\0';
    }

    return pdFALSE;
}
/*-----------------------------------------------------------*/

static __inline BaseType_t strbuf_printchar_inline( struct SStringBuf * apStr,
                                                    int c )
{
    if( apStr->str == NULL )
    {
        vOutputChar( ( char ) c, xTicksToWait );

        if( c == 0 )
        {
            return pdFALSE;
        }

        apStr->curLen++;
        return pdTRUE;
    }

    if( apStr->str < apStr->nulPos )
    {
        *( apStr->str++ ) = c;

        if( c == 0 )
        {
            return pdFALSE;
        }

        apStr->curLen++;
        return pdTRUE;
    }

    if( apStr->str == apStr->nulPos )
    {
        *( apStr->str++ ) = '\0';
    }

    return pdFALSE;
}
/*-----------------------------------------------------------*/

static __inline int i2hex( int aCh )
{
    int iResult;

    if( aCh < 10 )
    {
        iResult = '0' + aCh;
    }
    else
    {
        iResult = 'A' + aCh - 10;
    }

    return iResult;
}
/*-----------------------------------------------------------*/

static BaseType_t prints( struct SStringBuf * apBuf,
                          const char * apString )
{
    register int padchar = ' ';
    int i, len;

    if( xApplicationMemoryPermissions( ( uint32_t ) apString ) == 0 )
    {
        /* The user has probably made a mistake with the parameter
         * for '%s', the memory is not readbale. */
        apString = "INV_MEM";
    }

    if( apBuf->flags.width > 0 )
    {
        register int count = 0;
        register const char * ptr;

        for( ptr = apString; *ptr; ++ptr )
        {
            ++count;
        }

        if( count >= apBuf->flags.width )
        {
            apBuf->flags.width = 0;
        }
        else
        {
            apBuf->flags.width -= count;
        }

        if( apBuf->flags.pad_zero != 0U )
        {
            padchar = '0';
        }
    }

    if( apBuf->flags.pad_right == 0U )
    {
        for( ; apBuf->flags.width > 0; --apBuf->flags.width )
        {
            if( strbuf_printchar( apBuf, padchar ) == 0 )
            {
                return pdFALSE;
            }
        }
    }

    if( ( apBuf->flags.isNumber == pdTRUE ) &&
        ( apBuf->flags.pad_zero == pdTRUE ) &&
        ( apBuf->flags.pad_right == pdFALSE ) )
    {
        /* The string to print represents an integer number.
         * In this case, printLimit is the min number of digits to print
         * If the length of the number to print is less than the minimal
         * number of digits to display, we add 0 before printing the number
         */
        len = strlen( apString );

        if( len < apBuf->flags.printLimit )
        {
            i = apBuf->flags.printLimit - len;

            for( ; i; i-- )
            {
                if( strbuf_printchar( apBuf, '0' ) == 0 )
                {
                    return pdFALSE;
                }
            }
        }
    }

    /* The string to print is not the result of a number conversion to ascii.
     * For a string, printLimit is the max number of characters to display
     */
    for( ; apBuf->flags.printLimit && *apString; ++apString, --apBuf->flags.printLimit )
    {
        if( !strbuf_printchar( apBuf, *apString ) )
        {
            return pdFALSE;
        }
    }

    for( ; apBuf->flags.width > 0; --apBuf->flags.width )
    {
        if( !strbuf_printchar( apBuf, padchar ) )
        {
            return pdFALSE;
        }
    }

    return pdTRUE;
}
/*-----------------------------------------------------------*/

/* the following should be enough for 32 bit int */
#define PRINT_BUF_LEN    12 /* to print 4294967296 */

#if SPRINTF_LONG_LONG

/* Add an unsigned version of 'lldiv()'.
 * In an earlier version, the signed lldiv() was used,
 * which led to corrupted output. */

    typedef struct xlldiv_t
    {
        uint64_t quot; /* quotient */
        uint64_t rem;  /* remainder */
    }
    uns_lldiv_t;

    static uns_lldiv_t uns_lldiv( uint64_t number,
                                  uint64_t denom )
    {
        uns_lldiv_t rc;

        /* e.g. 10 / 4 = 2 */
        rc.quot = number / denom;
        /* e.g. 10 - 2 x 4 = 2 */
        rc.rem = number - rc.quot * denom;
        return rc;
    }

/*  #warning 64-bit libraries will be included as well. */
    static BaseType_t printll( struct SStringBuf * apBuf,
                               int64_t i )
    {
        char print_buf[ 2 * PRINT_BUF_LEN ];
        register char * s;
        register unsigned t, neg;
        register uint64_t u;
        uns_lldiv_t lldiv_result;

        apBuf->flags.isNumber = pdTRUE; /* Parameter for prints */

        if( i == 0 )
        {
            /* The number zero. */
            print_buf[ 0 ] = '0';
            print_buf[ 1 ] = '\0';
            return prints( apBuf, print_buf );
        }

        if( ( apBuf->flags.isSigned == pdTRUE ) && ( apBuf->flags.base == 10 ) && ( i < 0 ) )
        {
            neg = 1;
            u = ( uint64_t ) -i;
        }
        else
        {
            neg = 0;
            u = ( uint64_t ) i;
        }

        /* Numbers are written from right to left. */
        s = print_buf + sizeof print_buf - 1;

        *s = '\0';

        /* Biggest 64-bit number 18446744073709551615 */
        while( u != 0 )
        {
            lldiv_result = uns_lldiv( u, ( uint64_t ) apBuf->flags.base );
            t = lldiv_result.rem;

            if( t < 10 )
            {
                /* '0' to '9' */
                *( --s ) = t + '0';
            }
            else if( t < apBuf->flags.base )
            {
                /* 'A' to 'F' */
                *( --s ) = t - 10 + apBuf->flags.letBase;
            }
            else
            {
                /* Unexpected: the remainder is larger than the divisor. */
            }

            u = lldiv_result.quot;
        }

        if( neg != 0 )
        {
            if( ( apBuf->flags.width != 0 ) && ( apBuf->flags.pad_zero != 0U ) )
            {
                if( !strbuf_printchar( apBuf, '-' ) )
                {
                    return pdFALSE;
                }

                --apBuf->flags.width;
            }
            else
            {
                *( --s ) = '-';
            }
        }

        return prints( apBuf, s );
    }
#endif /* SPRINTF_LONG_LONG */
/*-----------------------------------------------------------*/

static BaseType_t printi( struct SStringBuf * apBuf,
                          int i )
{
    char print_buf[ PRINT_BUF_LEN ];
    register char * s;
    register int t, neg = 0;
    register unsigned int u = i;
    register unsigned base = apBuf->flags.base;

    apBuf->flags.isNumber = pdTRUE; /* Parameter for prints */

    if( i == 0 )
    {
        print_buf[ 0 ] = '0';
        print_buf[ 1 ] = '\0';
        return prints( apBuf, print_buf );
    }

    if( ( apBuf->flags.isSigned == pdTRUE ) && ( base == 10 ) && ( i < 0 ) )
    {
        neg = 1;
        u = -i;
    }

    s = print_buf + sizeof print_buf - 1;

    *s = '\0';

    switch( base )
    {
        case 16:

            while( u != 0 )
            {
                t = u & 0xF;

                if( t >= 10 )
                {
                    t += apBuf->flags.letBase - '0' - 10;
                }

                *( --s ) = t + '0';
                u >>= 4;
            }

            break;

        case 8:
        case 10:

            /* GCC compiles very efficient */
            while( u )
            {
                t = u % base;
                *( --s ) = t + '0';
                u /= base;
            }

            break;

/*
 *  // The generic case, not yet in use
 *  default:
 *      while( u )
 *      {
 *          t = u % base;
 *          if( t >= 10)
 *          {
 *              t += apBuf->flags.letBase - '0' - 10;
 *          }
 *( --s ) = t + '0';
 *          u /= base;
 *      }
 *      break;
 */
    }

    if( neg != 0 )
    {
        if( apBuf->flags.width && ( apBuf->flags.pad_zero != 0U ) )
        {
            if( strbuf_printchar( apBuf, '-' ) == 0 )
            {
                return pdFALSE;
            }

            --apBuf->flags.width;
        }
        else
        {
            *( --s ) = '-';
        }
    }

    return prints( apBuf, s );
}
/*-----------------------------------------------------------*/

static BaseType_t printIpNr( struct SStringBuf * apBuf,
                           unsigned i )
{
    apBuf->flags.printLimit = 3;
    return printi( apBuf, i );
}

static BaseType_t printIp( struct SStringBuf * apBuf,
                           unsigned uIPAddress )
{
    BaseType_t xResult = pdFALSE;

    memset( &( apBuf->flags ), 0, sizeof apBuf->flags );
    apBuf->flags.base = 10;

    if( printIpNr( apBuf, uIPAddress >> 24 ) && strbuf_printchar( apBuf, '.' ) &&
        printIpNr( apBuf, ( uIPAddress >> 16 ) & 0xff ) && strbuf_printchar( apBuf, '.' ) &&
        printIpNr( apBuf, ( uIPAddress >> 8 ) & 0xff ) && strbuf_printchar( apBuf, '.' ) &&
        printIpNr( apBuf, uIPAddress & 0xff ) )
    {
        xResult = pdTRUE;
    }

    return xResult;
}
/*-----------------------------------------------------------*/

static uint16_t usNetToHost( uint16_t usValue )
{
    if( u32.ulWords[ 0 ] == 0x00010203 )
    {
        return usValue;
    }
    else
    {
        return ( usValue << 8 ) | ( usValue >> 8 );
    }
}

static BaseType_t printIPv6( struct SStringBuf * apBuf,
                             uint16_t * pusAddress )
{
    int iIndex = 0;           /* The index in the IPv6 address: 0..7. */
    int iZeroStart = -1;      /* Default: when iZeroStart is negative, it won't match with any xIndex. */
    int iZeroLength = 0;
    int iCurStart = 0;        /* The position of the first zero found so far. */
    int iCurLength = 0;       /* The number of zero's seen so far. */
    const int xShortCount = 8; /* An IPv6 address consists of 8 shorts. */

    for( iIndex = 0; iIndex < 8; iIndex++ )
    {
        uint16_t usValue = pusAddress[ iIndex ];

        if( usValue == 0 )
        {
            if( iCurLength == 0 )
            {
                iCurStart = iIndex;
            }

            /* Count consecutive zeros. */
            iCurLength++;
        }

        if( ( usValue != 0 ) || ( iIndex == ( xShortCount - 1 ) ) )
        {
            if( ( iCurLength > 1 ) && ( iZeroLength < iCurLength ) )
            {
                /* Remember the number of consecutive zeros. */
                iZeroLength = iCurLength;
                /* Remember the index of the first zero found. */
                iZeroStart = iCurStart;
            }

            iCurLength = 0;
        }
    }

    apBuf->flags.base = 16;
    apBuf->flags.letBase = 'a'; /* use lower-case letters 'a' to 'f' */

    for( iIndex = 0; iIndex < 8; iIndex++ )
    {
        if( iIndex == iZeroStart )
        {
            iIndex += iZeroLength - 1;
            strbuf_printchar( apBuf, ':' );

            if( iIndex == 7 )
            {
                strbuf_printchar( apBuf, ':' );
            }
        }
        else
        {
            if( iIndex > 0 )
            {
                strbuf_printchar( apBuf, ':' );
            }

            printi( apBuf, ( int ) ( ( uint32_t ) usNetToHost( pusAddress[ iIndex ] ) ) );
        }
    }

    return pdTRUE;
}
/*-----------------------------------------------------------*/

static void tiny_print( struct SStringBuf * apBuf,
                        const char * format,
                        va_list args )
{
    char scr[ 2 ];

    for( ; ; )
    {
        int ch = *( format++ );

        if( ch != '%' )
        {
            do
            {
                /* Put the most like flow in a small loop */
                if( strbuf_printchar_inline( apBuf, ch ) == 0 )
                {
                    return;
                }

                ch = *( format++ );
            } while( ch != '%' );
        }

        ch = *( format++ );
        /* Now ch has character after '%', format pointing to next */

        if( ch == '\0' )
        {
            break;
        }

        if( ch == '%' )
        {
            if( strbuf_printchar( apBuf, ch ) == 0 )
            {
                return;
            }

            continue;
        }

        memset( &apBuf->flags, '\0', sizeof apBuf->flags );

        if( ch == '-' )
        {
            ch = *( format++ );
            apBuf->flags.pad_right = 1U;
        }

        while( ch == '0' )
        {
            ch = *( format++ );
            apBuf->flags.pad_zero = 1U;
        }

        if( ch == '*' )
        {
            ch = *( format++ );
            apBuf->flags.width = va_arg( args, int );
        }
        else
        {
            while( ch >= '0' && ch <= '9' )
            {
                apBuf->flags.width *= 10;
                apBuf->flags.width += ch - '0';
                ch = *( format++ );
            }
        }

        if( ch == '.' )
        {
            ch = *( format++ );

            if( ch == '*' )
            {
                apBuf->flags.printLimit = va_arg( args, int );
                ch = *( format++ );
            }
            else
            {
                while( ch >= '0' && ch <= '9' )
                {
                    apBuf->flags.printLimit *= 10;
                    apBuf->flags.printLimit += ch - '0';
                    ch = *( format++ );
                }
            }
        }

        if( apBuf->flags.printLimit == 0 )
        {
            apBuf->flags.printLimit--; /* -1: make it unlimited */
        }

        if( ch == 'p' )
        {
            if( ( format[ 0 ] == 'i' ) && ( format[ 1 ] == 'p' ) )
            {
                format += 2; /* eat the "pi" of "pip" */

                /* Print a IPv6 address */
                if( printIPv6( apBuf, va_arg( args, uint16_t * ) ) == 0 )
                {
                    break;
                }

                continue;
            }
        }

        if( ch == 's' )
        {
            register char * s = ( char * ) va_arg( args, int );

            if( prints( apBuf, s ? s : "(null)" ) == 0 )
            {
                break;
            }

            continue;
        }

        if( ch == 'c' )
        {
            /* char are converted to int then pushed on the stack */
            scr[ 0 ] = ( char ) va_arg( args, int );

            if( strbuf_printchar( apBuf, scr[ 0 ] ) == 0 )
            {
                return;
            }

            continue;
        }

        if( ch == 'l' )
        {
            ch = *( format++ );

            if( ch != 'l' )
            {
                /* A format like "%lu". */
            apBuf->flags.long32 = 1;
            }
            else
            {
                /* A format like "%llu". */
                ch = *( format++ );
                apBuf->flags.long64 = 1;
            }
        }

        if( ch == 'L' )
        {
            /* A format like "%Lu". */
            ch = *( format++ );
            apBuf->flags.long64 = 1;
        }

        apBuf->flags.base = 10;
        apBuf->flags.letBase = 'a';

        if( ( ch == 'd' ) || ( ch == 'u' ) )
        {
            apBuf->flags.isSigned = ( ch == 'd' );
            #if SPRINTF_LONG_LONG
                if( apBuf->flags.long64 != pdFALSE )
                {
                    if( printll( apBuf, va_arg( args, int64_t ) ) == 0 )
                    {
                        break;
                    }
                }
                else
            #endif /* SPRINTF_LONG_LONG */

            if( printi( apBuf, va_arg( args, int ) ) == 0 )
            {
                break;
            }

            continue;
        }

        apBuf->flags.base = 16; /* From here all hexadecimal */

        if( ( ch == 'x' ) && ( format[ 0 ] == 'i' ) && ( format[ 1 ] == 'p' ) )
        {
            format += 2; /* eat the "xi" of "xip" */

            /* Will use base 10 again */
            if( printIp( apBuf, va_arg( args, int ) ) == 0 )
            {
                break;
            }

            continue;
        }

        if( ( ch == 'x' ) || ( ch == 'X' ) || ( ch == 'p' ) || ( ch == 'o' ) )
        {
            if( ch == 'X' )
            {
                apBuf->flags.letBase = 'A';
            }
            else if( ch == 'o' )
            {
                apBuf->flags.base = 8;
            }

            #if SPRINTF_LONG_LONG
                if( apBuf->flags.long64 != pdFALSE )
                {
                    if( printll( apBuf, va_arg( args, int64_t ) ) == 0 )
                    {
                        break;
                    }
                }
                else
            #endif /* SPRINTF_LONG_LONG */

            if( printi( apBuf, va_arg( args, int ) ) == 0 )
            {
                break;
            }

            continue;
        }
    }

    strbuf_printchar( apBuf, '\0' );
}
/*-----------------------------------------------------------*/

int tiny_printf( const char * format,
                 ... )
{
    va_list args;

    va_start( args, format );
    struct SStringBuf strBuf;
    strbuf_init( &strBuf, NULL, ( const char * ) NULL );
    tiny_print( &strBuf, format, args );
    va_end( args );

    return strBuf.curLen;
}
/*-----------------------------------------------------------*/

int vsnprintf( char * apBuf,
               size_t aMaxLen,
               const char * apFmt,
               va_list args )
{
    struct SStringBuf strBuf;

    strbuf_init( &strBuf, apBuf, ( const char * ) apBuf + aMaxLen );
    tiny_print( &strBuf, apFmt, args );

    return strBuf.curLen;
}
/*-----------------------------------------------------------*/

int snprintf( char * apBuf,
              size_t aMaxLen,
              const char * apFmt,
              ... )
{
    va_list args;

    va_start( args, apFmt );
    struct SStringBuf strBuf;
    strbuf_init( &strBuf, apBuf, ( const char * ) apBuf + aMaxLen );
    tiny_print( &strBuf, apFmt, args );
    va_end( args );

    return strBuf.curLen;
}
/*-----------------------------------------------------------*/

int sprintf( char * apBuf,
             const char * apFmt,
             ... )
{
    va_list args;

    va_start( args, apFmt );
    struct SStringBuf strBuf;
    strbuf_init( &strBuf, apBuf, ( const char * ) apBuf + 1024 );
    tiny_print( &strBuf, apFmt, args );
    va_end( args );

    return strBuf.curLen;
}
/*-----------------------------------------------------------*/

int vsprintf( char * apBuf,
              const char * apFmt,
              va_list args )
{
    struct SStringBuf strBuf;

    strbuf_init( &strBuf, apBuf, ( const char * ) apBuf + 1024 );
    tiny_print( &strBuf, apFmt, args );

    return strBuf.curLen;
}
/*-----------------------------------------------------------*/

const char * mkSize( uint64_t aSize,
                     char * apBuf,
                     int aLen )
{
    /* Must be static because it might be returned. */
    static char retString[ 33 ];
    size_t gb, mb, kb, sb;

    if( apBuf == NULL )
    {
        apBuf = retString;
        aLen = sizeof retString;
    }

    gb = aSize / ( 1024 * 1024 * 1024 );
    aSize -= gb * ( 1024 * 1024 * 1024 );
    mb = aSize / ( 1024 * 1024 );
    aSize -= mb * ( 1024 * 1024 );
    kb = aSize / ( 1024 );
    aSize -= kb * ( 1024 );
    sb = aSize;

    if( gb )
    {
        snprintf( apBuf, aLen, "%u.%02u GB", ( unsigned ) gb, ( unsigned ) ( ( 100 * mb ) / 1024ul ) );
    }
    else if( mb )
    {
        snprintf( apBuf, aLen, "%u.%02u MB", ( unsigned ) mb, ( unsigned ) ( ( 100 * kb ) / 1024ul ) );
    }
    else if( kb != 0ul )
    {
        snprintf( apBuf, aLen, "%u.%02u KB", ( unsigned ) kb, ( unsigned ) ( ( 100 * sb ) / 1024ul ) );
    }
    else
    {
        snprintf( apBuf, aLen, "%u bytes", ( unsigned ) sb );
    }

    return apBuf;
}

const char * mkTime( unsigned aTime,
                     char * apBuf,
                     int aLen )                             /* Argument in uS */
{
    /* Must be static because it might be returned. */
    static char mySprintfRetString[ 33 ];

    if( apBuf == NULL )
    {
        apBuf = mySprintfRetString;
        aLen = sizeof mySprintfRetString;
    }

    unsigned sec = aTime / ( 1000 * 1000 );
    aTime -= sec * ( 1000 * 1000 );
    unsigned ms = aTime / ( 1000 );
    aTime -= ms * ( 1000 );
    unsigned us = aTime;

    if( sec )
    {
        snprintf( apBuf, aLen, "%u.%02u S", ( unsigned ) sec, ( unsigned ) ( ( 100 * ms ) / 1000 ) );
    }
    else if( ms )
    {
        snprintf( apBuf, aLen, "%u.%02u mS", ( unsigned ) ms, ( unsigned ) ( ( 100 * us ) / 1000 ) );
    }
    else
    {
        snprintf( apBuf, aLen, "%u uS", ( unsigned ) us );
    }

    return apBuf;
}

#ifdef _MSC_VER

    #if defined( _NO_CRT_STDIO_INLINE )

        int printf( char const * const _Format,
                    ... )
        {
            int _Result;
            va_list _ArgList;

            __crt_va_start( _ArgList, _Format );
            _Result = _vfprintf_l( stdout, _Format, NULL, _ArgList );
            __crt_va_end( _ArgList );
            return _Result;
        }

    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

    #if defined( _NO_CRT_STDIO_INLINE )

        int sscanf( char const * const _Buffer,
                    char const * const _Format,
                    ... )
        {
            int _Result;
            va_list _ArgList;

            __crt_va_start( _ArgList, _Format );
            _Result = _vsscanf_l( _Buffer, _Format, NULL, _ArgList );
            __crt_va_end( _ArgList );
            return _Result;
        }

    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

    #if defined( _NO_CRT_STDIO_INLINE )

        int _vfprintf_l( FILE * const _Stream,
                         char const * const _Format,
                         _locale_t const _Locale,
                         va_list _ArgList )
        {
            return __stdio_common_vfprintf( _CRT_INTERNAL_LOCAL_PRINTF_OPTIONS, _Stream, _Format, _Locale, _ArgList );
        }

    #endif

    #if defined( _NO_CRT_STDIO_INLINE )

        int _vsscanf_l( char const * const _Buffer,
                        char const * const _Format,
                        _locale_t const _Locale,
                        va_list _ArgList )
        {
            return __stdio_common_vsscanf(
                _CRT_INTERNAL_LOCAL_SCANF_OPTIONS,
                _Buffer, ( size_t ) -1, _Format, _Locale, _ArgList );
        }

    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

    #if defined( _NO_CRT_STDIO_INLINE )
        int scanf( char const * const _Format,
                   ... )
        {
            int _Result;
            va_list _ArgList;

            __crt_va_start( _ArgList, _Format );
            _Result = _vfscanf_l( stdin, _Format, NULL, _ArgList );
            __crt_va_end( _ArgList );
            return _Result;
        }
    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

    #if defined( _NO_CRT_STDIO_INLINE )
        int _vfscanf_l( _Inout_ FILE * const _Stream,
                        char const * const _Format,
                        const _Locale,
                        va_list _ArgList )
        {
            return __stdio_common_vfscanf(
                _CRT_INTERNAL_LOCAL_SCANF_OPTIONS,
                _Stream, _Format, _Locale, _ArgList );
        }

    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */


    #if defined( _NO_CRT_STDIO_INLINE )
        int vsnprintf_s( char * const _Buffer,
                         size_t const _BufferCount,
                         size_t const _MaxCount,
                         char const * const _Format,
                         va_list _ArgList )
        {
            return _vsnprintf_s_l( _Buffer, _BufferCount, _MaxCount, _Format, NULL, _ArgList );
        }
        int _vsnprintf_s( char * const _Buffer,
                          size_t const _BufferCount,
                          size_t const _MaxCount,
                          char const * const _Format,
                          va_list _ArgList )
        {
            return _vsnprintf_s_l( _Buffer, _BufferCount, _MaxCount, _Format, NULL, _ArgList );
        }

    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

    #if defined( _NO_CRT_STDIO_INLINE )
        int _vsnprintf_s_l( char * const _Buffer,
                            size_t const _BufferCount,
                            size_t const _MaxCount,
                            char const * const _Format,
                            _locale_t const _Locale,
                            va_list _ArgList )
        {
            int const _Result = __stdio_common_vsnprintf_s(
                _CRT_INTERNAL_LOCAL_PRINTF_OPTIONS,
                _Buffer, _BufferCount, _MaxCount, _Format, _Locale, _ArgList );

            return _Result < 0 ? -1 : _Result;
        }
    #endif /* if defined( _NO_CRT_STDIO_INLINE ) */

#endif /* __WIN32__ */
