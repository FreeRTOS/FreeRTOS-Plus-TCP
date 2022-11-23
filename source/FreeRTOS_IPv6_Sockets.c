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
 * @file FreeRTOS_Sockets_IPv6.c
 * @brief Implements the Sockets API based on Berkeley sockets for the FreeRTOS+TCP network stack.
 *        Sockets are used by the application processes to interact with the IP-task which in turn
 *        interacts with the hardware.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IPv6_Sockets.h"



#if ( ipconfigUSE_TCP == 1 )

/**
 * @brief Called by pxTCPSocketLookup(), this function will check if a socket
 *        is connected to a remote IP-address. It will be called from a loop
 *        iterating through all sockets.
 * @param[in] pxSocket: The socket to be inspected.
 * @param[in] pxAddress_IPv6: The IPv6 address, or NULL if the peer has a IPv4 address.
 * @param[in] ulRemoteIP: The IPv4 address
 * @return The socket in case it is connected to the remote IP-address
 */
    FreeRTOS_Socket_t * pxTCPSocketLookup_IPv6( FreeRTOS_Socket_t * pxSocket,
                                                       IPv6_Address_t * pxAddress_IPv6,
                                                       uint32_t ulRemoteIP )
    {
        FreeRTOS_Socket_t * pxResult = NULL;

        if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
        {
            if( pxAddress_IPv6 != NULL )
            {
                if( memcmp( pxSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, pxAddress_IPv6->ucBytes, ipSIZE_OF_IPv6_ADDRESS ) == 0 )
                {
                    /* For sockets not in listening mode, find a match with
                     * uxLocalPort, ulRemoteIP AND uxRemotePort. */
                    pxResult = pxSocket;
                }
            }
        }
        else
        {
            if( pxAddress_IPv6 == NULL )
            {
                if( pxSocket->u.xTCP.xRemoteIP.xIP_IPv4 == ulRemoteIP )
                {
                    /* For sockets not in listening mode, find a match with
                     * uxLocalPort, ulRemoteIP AND uxRemotePort. */
                    pxResult = pxSocket;
                }
            }
        }

        return pxResult;
    }
#endif /* if ( ( ipconfigUSE_TCP == 1 ) */

#if ( ipconfigUSE_TCP == 1 )
/**
 * @brief Get the version of IP: either 'ipTYPE_IPv4' or 'ipTYPE_IPv6'.
 *
 * @param[in] xSocket : The socket to be checked.
 *
 * @return Either ipTYPE_IPv4 or ipTYPE_IPv6.
 */
    BaseType_t FreeRTOS_GetIPType( ConstSocket_t xSocket )
    {
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xResult;

        if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
        {
            xResult = ( BaseType_t ) ipTYPE_IPv6;
        }
        else
        {
            xResult = ( BaseType_t ) ipTYPE_IPv4;
        }

        return xResult;
    }
#endif /* if ( ( ipconfigUSE_TCP == 1 ) */

/**
 * @brief Converts a hex value to a readable hex character, e.g. 14 becomes 'e'.
 * @param usValue : The value to be converted, must be between 0 and 15.
 * @return The character, between '0' and '9', or between 'a' and 'f'.
 */
    static char cHexToChar( unsigned short usValue )
    {
        char cReturn = '0';

        if( usValue <= 9U )
        {
            cReturn += usValue;
        }
        else if( usValue <= 15U )
        {
            cReturn = 'a';
            cReturn += ( usValue - 10U );
        }
        else
        {
            /* The value passed to 'usValue' has been and-ed with 0x0f,
             * so this else clause should never be reached. */
            configASSERT( 0 == 1 );
        }

        return cReturn;
    }

/*-----------------------------------------------------------*/

/**
 * @brief Convert a short numeric value to a hex string of at most 4 characters.
 *        The resulting string is **not** null-terminated. The resulting string
 *        will not have leading zero's, except when 'usValue' equals zero.
 * @param pcBuffer[in] : The buffer to which the string is written.
 * @param uxBufferSize[in] : The size of the buffer pointed to by 'pcBuffer'.
 * @param usValue[in] : The 16-bit value to be converted.
 * @return The number of bytes written to 'pcBuffer'.
 */
    static socklen_t uxHexPrintShort( char * pcBuffer,
                                      size_t uxBufferSize,
                                      uint16_t usValue )
    {
        const size_t uxNibbleCount = 4U;
        size_t uxNibble;
        size_t uxIndex = 0U;
        uint16_t usShifter = usValue;
        BaseType_t xHadNonZero = pdFALSE;

        for( uxNibble = 0; uxNibble < uxNibbleCount; uxNibble++ )
        {
            uint16_t usNibble = ( usShifter >> 12 ) & 0x0FU;

            if( usNibble != 0U )
            {
                xHadNonZero = pdTRUE;
            }

            if( ( xHadNonZero != pdFALSE ) || ( uxNibble == ( uxNibbleCount - 1U ) ) )
            {
                if( uxIndex >= ( uxBufferSize - 1U ) )
                {
                    break;
                }

                pcBuffer[ uxIndex ] = cHexToChar( usNibble );
                uxIndex++;
            }

            usShifter <<= 4;
        }

        return uxIndex;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Scan the binary IPv6 address and find the longest train of consecutive zero's.
 *        The result of this search will be stored in 'xZeroStart' and 'xZeroLength'.
 * @param pxSet: the set of parameters as used by FreeRTOS_inet_ntop6().
 */
    static void prv_ntop6_search_zeros( struct sNTOP6_Set * pxSet )
    {
        BaseType_t xIndex = 0;            /* The index in the IPv6 address: 0..7. */
        BaseType_t xCurStart = 0;         /* The position of the first zero found so far. */
        BaseType_t xCurLength = 0;        /* The number of zero's seen so far. */
        const BaseType_t xShortCount = 8; /* An IPv6 address consists of 8 shorts. */

        /* Default: when xZeroStart is negative, it won't match with any xIndex. */
        pxSet->xZeroStart = -1;

        /* Look for the longest train of zero's 0:0:0:... */
        for( ; xIndex < xShortCount; xIndex++ )
        {
            uint16_t usValue = pxSet->pusAddress[ xIndex ];

            if( usValue == 0U )
            {
                if( xCurLength == 0 )
                {
                    /* Remember the position of the first zero. */
                    xCurStart = xIndex;
                }

                /* Count consecutive zeros. */
                xCurLength++;
            }

            if( ( usValue != 0U ) || ( xIndex == ( xShortCount - 1 ) ) )
            {
                /* Has a longer train of zero's been found? */
                if( ( xCurLength > 1 ) && ( pxSet->xZeroLength < xCurLength ) )
                {
                    /* Remember the number of consecutive zeros. */
                    pxSet->xZeroLength = xCurLength;
                    /* Remember the index of the first zero found. */
                    pxSet->xZeroStart = xCurStart;
                }

                /* Reset the counter of consecutive zeros. */
                xCurLength = 0;
            }
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief The location is now at the longest train of zero's. Two colons have to
 *        be printed without a numeric value, e.g. "ff02::1".
 * @param pcDestination: the output buffer where the colons will be printed.
 * @param uxSize: the remaining length of the output buffer.
 * @param pxSet: the set of parameters as used by FreeRTOS_inet_ntop6().
 * @return pdPASS in case the output buffer is big enough to contain the colons.
 * @note uxSize must be at least 2, enough to print "::". The string will get
 *       null-terminated later on.
 */
    static BaseType_t prv_ntop6_write_zeros( char * pcDestination,
                                             size_t uxSize,
                                             struct sNTOP6_Set * pxSet )
    {
        BaseType_t xReturn = pdPASS;
        const BaseType_t xShortCount = 8; /* An IPv6 address consists of 8 shorts. */

        if( pxSet->uxTargetIndex <= ( uxSize - 1U ) )
        {
            pcDestination[ pxSet->uxTargetIndex ] = ':';
            pxSet->uxTargetIndex++;

            if( ( pxSet->xIndex + pxSet->xZeroLength ) == xShortCount )
            {
                /* Reached the last index, write a second ";". */
                if( pxSet->uxTargetIndex <= ( uxSize - 1U ) )
                {
                    pcDestination[ pxSet->uxTargetIndex ] = ':';
                    pxSet->uxTargetIndex++;
                }
                else
                {
                    /* Can not write the second colon. */
                    xReturn = pdFAIL;
                }
            }
            else
            {
                /* Otherwise the function prv_ntop6_write_short() will places the second colon. */
            }
        }
        else
        {
            /* Can not write the first colon. */
            xReturn = pdFAIL;
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Write a short value, as a hex number with at most 4 characters. E.g. the
 *        value 15 will be printed as "f".
 * @param pcDestination: the output buffer where the hex number is to be printed.
 * @param uxSize: the remaining length of the output buffer.
 * @param pxSet: the set of parameters as used by FreeRTOS_inet_ntop6().
 * @return pdPASS in case the output buffer is big enough to contain the string.
 * @note uxSize must be at least 4, enough to print "abcd". The string will get
 *       null-terminated later on.
 */
    static BaseType_t prv_ntop6_write_short( char * pcDestination,
                                             size_t uxSize,
                                             struct sNTOP6_Set * pxSet )
    {
        socklen_t uxLength;
        BaseType_t xReturn = pdPASS;
        const size_t uxBytesPerShortValue = 4U;

        if( pxSet->xIndex > 0 )
        {
            if( pxSet->uxTargetIndex >= ( uxSize - 1U ) )
            {
                xReturn = pdFAIL;
            }
            else
            {
                pcDestination[ pxSet->uxTargetIndex ] = ':';
                pxSet->uxTargetIndex++;
            }
        }

        if( xReturn == pdPASS )
        {
            /* If there is enough space to write a short. */
            if( pxSet->uxTargetIndex <= ( uxSize - uxBytesPerShortValue ) )
            {
                /* Write hex value of short. at most 4 + 1 bytes. */
                uxLength = uxHexPrintShort( &( pcDestination[ pxSet->uxTargetIndex ] ),
                                            uxBytesPerShortValue + 1U,
                                            FreeRTOS_ntohs( pxSet->pusAddress[ pxSet->xIndex ] ) );

                if( uxLength <= 0U )
                {
                    xReturn = pdFAIL;
                }
                else
                {
                    pxSet->uxTargetIndex += uxLength;
                }
            }
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief This function converts a binary IPv6 address to a human readable notation.
 *
 * @param[in] pcSource: The binary address, 16 bytes long..
 * @param[out] pvDestination: The human-readable ( hexadecimal ) notation of the
 *                            address.
 * @param[in] uxSize: The size of pvDestination. A value of 40 is recommended.
 *
 * @return pdPASS if the translation was successful or else pdFAIL.
 */
    const char * FreeRTOS_inet_ntop6( const void * pvSource,
                                      char * pcDestination,
                                      socklen_t uxSize )
    {
        const char * pcReturn;  /* The return value, which is either 'pcDestination' or NULL. */
        struct sNTOP6_Set xSet; /* A set of values for easy exchange with the helper functions prv_ntop6_xxx(). */

        ( void ) memset( &( xSet ), 0, sizeof( xSet ) );

        xSet.pusAddress = pvSource;

        if( uxSize < 3U )
        {
            /* Can not even print :: */
        }
        else
        {
            prv_ntop6_search_zeros( &( xSet ) );

            while( xSet.xIndex < 8 )
            {
                if( xSet.xIndex == xSet.xZeroStart )
                {
                    if( prv_ntop6_write_zeros( pcDestination, uxSize, &( xSet ) ) == pdFAIL )
                    {
                        break;
                    }

                    xSet.xIndex += xSet.xZeroLength;
                }
                else
                {
                    if( prv_ntop6_write_short( pcDestination, uxSize, &( xSet ) ) == pdFAIL )
                    {
                        break;
                    }

                    xSet.xIndex++;
                }
            }
        }

        if( xSet.xIndex < 8 )
        {
            /* Didn't reach the last nibble: clear the string. */
            pcReturn = NULL;
        }
	else
        {
            pcDestination[ xSet.uxTargetIndex ] = '\0';
            pcReturn = pcDestination;
        }

        return pcReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Converting a readable IPv6 address to its binary form, add one nibble.
 *
 * @param[in] pxSet : A set of variables describing the conversion.
 * @param[in] ucNew : The hex value, between 0 and 15
 * @param[in] ch : The character, such as '5', 'f', or ':'.
 *
 * @return pdTRUE when the nibble was added, otherwise pdFALSE.
 */
    static BaseType_t prv_inet_pton6_add_nibble( struct sPTON6_Set * pxSet,
                                                 uint8_t ucNew,
                                                 char ch )
    {
        BaseType_t xReturn = pdPASS;

        if( ucNew != ( uint8_t ) socketINVALID_HEX_CHAR )
        {
            /* Shift in 4 bits. */
            pxSet->ulValue <<= 4;
            pxSet->ulValue |= ( uint32_t ) ucNew;

            /* Remember that ulValue is valid now. */
            pxSet->xHadDigit = pdTRUE;

            /* Check if the number is not becoming larger than 16 bits. */
            if( pxSet->ulValue > 0xffffU )
            {
                /* The highest nibble has already been set,
                 * an overflow would occur.  Break out of the for-loop. */
                xReturn = pdFAIL;
            }
        }
        else if( ch == ':' )
        {
            if( pxSet->xHadDigit == pdFALSE )
            {
                /* A "::" sequence has been received. Check if it is not a third colon. */
                if( pxSet->xColon >= 0 )
                {
                    xReturn = pdFAIL;
                }
                else
                {
                    /* Two or more zero's are expected, starting at position 'xColon'. */
                    pxSet->xColon = pxSet->xTargetIndex;
                }
            }
            else
            {
                if( pxSet->xTargetIndex <= pxSet->xHighestIndex )
                {
                    /* Store a short value at position 'xTargetIndex'. */
                    pxSet->pucTarget[ pxSet->xTargetIndex ] = ( uint8_t ) ( ( pxSet->ulValue >> 8 ) & 0xffU );
                    pxSet->pucTarget[ pxSet->xTargetIndex + 1 ] = ( uint8_t ) ( pxSet->ulValue & 0xffU );
                    pxSet->xTargetIndex += 2;
                    pxSet->xHadDigit = pdFALSE;
                    pxSet->ulValue = 0U;
                }
                else
                {
                    xReturn = pdFAIL;
                }
            }
        }
        else
        {
            /* When an IPv4 address or rubbish is provided, this statement will be reached. */
            xReturn = pdFAIL;
        }

        return xReturn;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Convert an ASCII character to its corresponding hexadecimal value.
 *        Accepted characters are 0-9, a-f, and A-F.
 *
 * @param[in] cChar: The character to be converted.
 *
 * @return The hexadecimal value, between 0 and 15.
 *         When the character is not valid, socketINVALID_HEX_CHAR will be returned.
 */
uint8_t ucASCIIToHex( char cChar )
{
    char cValue = cChar;
    uint8_t ucNew;

    if( ( cValue >= '0' ) && ( cValue <= '9' ) )
    {
        cValue -= ( char ) '0';
        /* The value will be between 0 and 9. */
        ucNew = ( uint8_t ) cValue;
    }
    else if( ( cValue >= 'a' ) && ( cValue <= 'f' ) )
    {
        cValue -= ( char ) 'a';
        ucNew = ( uint8_t ) cValue;
        /* The value will be between 10 and 15. */
        ucNew += ( uint8_t ) 10;
    }
    else if( ( cValue >= 'A' ) && ( cValue <= 'F' ) )
    {
        cValue -= ( char ) 'A';
        ucNew = ( uint8_t ) cValue;
        /* The value will be between 10 and 15. */
        ucNew += ( uint8_t ) 10;
    }
    else
    {
        /* The character does not represent a valid hex number, return 255. */
        ucNew = ( uint8_t ) socketINVALID_HEX_CHAR;
    }

    return ucNew;
}
/*-----------------------------------------------------------*/

/**
 * @brief Convert an ASCII character to its corresponding hexadecimal value.
 *        A :: block was found, now fill in the zero's.
 * @param[in] pxSet : A set of variables describing the conversion.
 */
    static void prv_inet_pton6_set_zeros( struct sPTON6_Set * pxSet )
    {
        /* The number of bytes that were written after the :: */
        const BaseType_t xCount = pxSet->xTargetIndex - pxSet->xColon;
        const BaseType_t xTopIndex = ( BaseType_t ) ipSIZE_OF_IPv6_ADDRESS;
        BaseType_t xIndex;
        BaseType_t xTarget = xTopIndex - 1;
        BaseType_t xSource = pxSet->xColon + ( xCount - 1 );

        /* Inserting 'xCount' zero's. */
        for( xIndex = 0; xIndex < xCount; xIndex++ )
        {
            pxSet->pucTarget[ xTarget ] = pxSet->pucTarget[ xSource ];
            pxSet->pucTarget[ xSource ] = 0;
            xTarget--;
            xSource--;
        }

        pxSet->xTargetIndex = ( BaseType_t ) ipSIZE_OF_IPv6_ADDRESS;
    }
/*-----------------------------------------------------------*/

/**
 * @brief Convert an IPv6 address in hexadecimal notation to a binary format of 16 bytes.
 *
 * @param[in] pcSource: The address in hexadecimal notation.
 * @param[out] pvDestination: The address in binary format, 16 bytes long.
 *
 * @return The 32-bit representation of IP(v4) address.
 */
    BaseType_t FreeRTOS_inet_pton6( const char * pcSource,
                                    void * pvDestination )
    {
        char ch;
        uint8_t ucNew;
        BaseType_t xResult;
        struct sPTON6_Set xSet;

        const char * pcIterator = pcSource;

        ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
        xSet.xColon = -1;
        xSet.pucTarget = pvDestination;

        ( void ) memset( xSet.pucTarget, 0, ipSIZE_OF_IPv6_ADDRESS );

        xResult = 0;

        /* Leading :: requires some special handling. */
        if( strcmp( pcIterator, "::" ) == 0 )
        {
            xResult = 1;
        }
        else
        {
            if( pcIterator[ 0 ] == ':' )
            {
                pcIterator++;
            }

            /* The last bytes will be written at position 14 and 15. */
            xSet.xHighestIndex = ( BaseType_t ) ipSIZE_OF_IPv6_ADDRESS;
            xSet.xHighestIndex -= ( BaseType_t ) sizeof( uint16_t );

            /* The value in ulValue is not yet valid. */
            xSet.xHadDigit = pdFALSE;
            xSet.ulValue = 0U;

            for( ; ; )
            {
                ch = *( pcIterator++ );

                if( ch == ( char ) '\0' )
                {
                    /* The string is parsed now.
                     * Store the last short, if present. */
                    if( ( xSet.xHadDigit != pdFALSE ) &&
                        ( xSet.xTargetIndex <= xSet.xHighestIndex ) )
                    {
                        /* Add the last value seen, network byte order ( MSB first ). */
                        xSet.pucTarget[ xSet.xTargetIndex ] = ( uint8_t ) ( ( xSet.ulValue >> 8 ) & 0xffU );
                        xSet.pucTarget[ xSet.xTargetIndex + 1 ] = ( uint8_t ) ( xSet.ulValue & 0xffU );
                        xSet.xTargetIndex += 2;
                    }

                    /* Break out of the for-ever loop. */
                    break;
                }

                /* Convert from a readable character to a hex value. */
                ucNew = ucASCIIToHex( ch );
                /* See if this is a digit or a colon. */
                xResult = prv_inet_pton6_add_nibble( &( xSet ), ucNew, ch );

                if( xResult == pdFALSE )
                {
                    /* The new character was not accepted. */
                    break;
                }
            } /* for( ;; ) */

            if( xSet.xColon >= 0 )
            {
                /* The address contains a block of zero. */
                prv_inet_pton6_set_zeros( &( xSet ) );
            }

            if( xSet.xTargetIndex == ( BaseType_t ) ipSIZE_OF_IPv6_ADDRESS )
            {
                xResult = 1;
            }
        }

        if( xResult != 1 )
        {
            xSet.pucTarget = ( uint8_t * ) pvDestination;
            ( void ) memset( xSet.pucTarget, 0, ipSIZE_OF_IPv6_ADDRESS );
        }

        return xResult;
    }

/*-----------------------------------------------------------*/

/**
 * @brief Function to get the local address and IP port of the given socket.
 *
 * @param[in] xSocket: Socket whose port is to be added to the pxAddress.
 * @param[out] pxAddress: Structure in which the IP address and the port number
 *                        is returned.
 *
 * @return Size of the freertos_sockaddr structure.
 */
    size_t FreeRTOS_GetLocalAddressv6( ConstSocket_t xSocket,
                                     struct freertos_sockaddr6 * pxAddress6 )
{
    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;

    #if ( ipconfigUSE_IPV6 != 0 )
        struct freertos_sockaddr * pxAddress = ( ( sockaddr4_t * ) pxAddress6 );
        if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
        {
            pxAddress6->sin_family = FREERTOS_AF_INET6;
            /* IP address of local machine. */
            ( void ) memcpy( pxAddress6->sin_addrv6.ucBytes, pxSocket->xLocalAddress.xIP_IPv6.ucBytes, sizeof( pxAddress6->sin_addrv6.ucBytes ) );
            /* Local port on this machine. */
            pxAddress6->sin_port = FreeRTOS_htons( pxSocket->usLocalPort );
        }
        else
    #endif
    {
        pxAddress->sin_family = FREERTOS_AF_INET;
        pxAddress->sin_len = ( uint8_t ) sizeof( *pxAddress );
        /* IP address of local machine. */
        pxAddress->sin_addr = FreeRTOS_htonl( pxSocket->xLocalAddress.xIP_IPv4 );

        /* Local port on this machine. */
        pxAddress->sin_port = FreeRTOS_htons( pxSocket->usLocalPort );
    }

    return sizeof( *pxAddress );
}

/*-----------------------------------------------------------*/
#if ( ipconfigUSE_TCP == 1 )

/**
 * @brief Function to get the remote IPv6-address and port number.
 *
 * @param[in] xSocket: Socket owning the connection.
 * @param[out] pxAddress: The IPv6 address pointer to which the address
 *                        is to be added.
 *
 * @return The size of the address being returned. Or else a negative
 *         error code will be returned.
 */

/* Function to get the remote address and IP port */
    BaseType_t FreeRTOS_GetRemoteAddress6( ConstSocket_t xSocket,
                                              struct freertos_sockaddr6 * pxAddress )
    {
        const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) xSocket;
        BaseType_t xResult;

        if( pxSocket->ucProtocol != ( uint8_t ) FREERTOS_IPPROTO_TCP )
        {
            xResult = -pdFREERTOS_ERRNO_EINVAL;
        }
        else
        {
            /* BSD style sockets communicate IP and port addresses in network
             * byte order.
             * IP address of remote machine. */
            
            if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
                {
                    pxAddress->sin_family = FREERTOS_AF_INET6;

                    /* IP address of remote machine. */
                    ( void ) memcpy( pxAddress->sin_addrv6.ucBytes, pxSocket->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, sizeof( pxAddress->sin_addrv6.ucBytes ) );

                    /* Port of remote machine. */
                    pxAddress->sin_port = FreeRTOS_htons( pxSocket->u.xTCP.usRemotePort );
                }

            xResult = ( BaseType_t ) sizeof( *pxAddress );
        }

        return xResult;
    }


#endif /* ipconfigUSE_TCP */
