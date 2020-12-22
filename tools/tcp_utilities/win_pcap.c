/*
 * PCAP for embedded applications.
 */

#include <direct.h>
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

#if ipconfigUSE_PCAP

    #include "win_pcap.h"

    #define MAGIC_BE                   0xa1b2c3d4UL
    #define MAGIC_LE                   0xd4c3b2a1UL

    #define PCAP_MAGIC_ID              MAGIC_BE

    #define PCAP_MAX_PACKRET_LENGTH    1514U

    typedef struct _SCapData
    {
        char le_convert;
        FILE * fp;
    } SCapData;

    typedef struct pcap_hdr_s
    {
        uint32_t magic_number;  /* magic number */
        uint16_t version_major; /* major version number */
        uint16_t version_minor; /* minor version number */
        int32_t thiszone;       /* GMT to local correction */
        uint32_t sigfigs;       /* accuracy of timestamps */
        uint32_t snaplen;       /* max length of captured packets, in octets */
        uint32_t network;       /* data link type */
    } pcap_hdr_t;

    typedef struct pcaprec_hdr_s
    {
        uint32_t ts_sec;   /* timestamp seconds */
        uint32_t ts_usec;  /* timestamp microseconds */
        uint32_t incl_len; /* number of octets of packet saved in file */
        uint32_t orig_len; /* actual length of packet */
    } pcaprec_hdr_t;

    static const pcap_hdr_t pcap_header =
    {
        PCAP_MAGIC_ID,           /* magic number. */
        2U,                      /* major version number. */
        4U,                      /* minor version number. */
        0U,                      /* GMT to local correction in seconds. */
        0U,                      /* accuracy of timestamps. */
        PCAP_MAX_PACKRET_LENGTH, /* max length of captured packets, in octets. */
        1U                       /* data link type. */
    };

/* Get the time in micro seconds. */
    static void pcap_checkTime( SPcap * apThis );

/*-----------------------------------------------------------*/

    static uint32_t swap32( uint32_t ulValue )
    {
        return ( ( ( ( uint32_t ) ( ulValue ) ) ) << 24 ) |
               ( ( ( ( uint32_t ) ( ulValue ) ) & 0x0000ff00UL ) << 8 ) |
               ( ( ( ( uint32_t ) ( ulValue ) ) & 0x00ff0000UL ) >> 8 ) |
               ( ( ( ( uint32_t ) ( ulValue ) ) ) >> 24 );
    }
/*-----------------------------------------------------------*/

    uint64_t getSystemTime()
    {
        FILETIME ft;
        uint64_t tt;

        GetSystemTimeAsFileTime( &( ft ) );
        tt = ft.dwHighDateTime;
        tt <<= 32ULL;
        tt |= ft.dwLowDateTime;
        tt /= 10ULL;
        tt -= 11644473600000000ULL;

        return tt;
    }
/*-----------------------------------------------------------*/

/*
 *
 ######    ####    ###   ######       #     #           #
 #    #  #    #  #   #   #    #      #     #           #     #
 #    # #     # #     #  #    #      #     #                 #
 #    # #       #     #  #    #      #  #  # ### ##  ###   ######  ####
 #####  #       #     #  #####       #  #  #  # #  #   #     #    #    #
 #      #       #######  #           #  #  #  ##   #   #     #    ######
 #      #     # #     #  #            ## ##   #        #     #    #
 #       #    # #     #  #            ## ##   #        #     # ## #   ##
 ####      ####  #     # ####          ## ##  ####    #####    ##   ####
 ####
 */

    int pcap_init( SPcap * apThis,
                   size_t aSize )
    {
        int xResult = pdFALSE;

        if( apThis->data != NULL )
        {
            pcap_clear( apThis );
        }

        /* Make sure that the structures are aligned as expected. */

        configASSERT( sizeof( pcap_hdr_t ) == 24 );
        configASSERT( sizeof( pcaprec_hdr_t ) == 16 );

        uint8_t * ptr = ( uint8_t * ) malloc( aSize );

        if( ptr == NULL )
        {
            printf( "pcap_init: malloc %u failed\n", aSize );
        }
        else
        {
            apThis->xCurrentLength = sizeof pcap_header;
            apThis->uxMaxLength = aSize;

            /*
             * apThis->startTime = ( uint64_t ) 1000ull * xTaskGetTickCount();
             */
            apThis->startTime = getSystemTime();

            memcpy( ptr, &pcap_header, sizeof pcap_header );

            printf( "pcap_init: Malloc %u ok\n", aSize );
            /* As another thread will start filling the buffer, this is the last statement: */
            apThis->data = ptr;
            xResult = pdTRUE;
        }

        return xResult;
    }
/*-----------------------------------------------------------*/

    size_t pcap_has_space( SPcap * apThis )
	{
		size_t uxResult = 0;

		if( ( apThis->data != NULL ) &&
            ( apThis->uxMaxLength > 0U ) &&
            ( apThis->uxMaxLength > apThis->xCurrentLength ) )
		{
			uxResult = apThis->uxMaxLength - apThis->xCurrentLength;
		}
		
		return uxResult;
	}
/*-----------------------------------------------------------*/

    int pcap_write( SPcap * apThis,
                    const uint8_t * pucData,
                    int aLength )
    {
        if( !apThis->data )
        {
            /* Buffer not allocated. */
            return 0;
        }

        if( ( aLength < 40 ) || ( aLength > PCAP_MAX_PACKRET_LENGTH ) )
        {
            /* Unexpected packet length. */
            return 0;
        }

        if( apThis->xCurrentLength + sizeof( pcaprec_hdr_t ) + aLength > apThis->uxMaxLength )
        {
            /* Buffer is full. */
            return 0;
        }

        #ifdef _MSC_VER
            /*	showPacket(pucData, aLength); */
        #endif

        {
            uint8_t * target;
            pcaprec_hdr_t dataHeader;
            /* Fetch the current time in seconds + micro-seconds. */
            pcap_checkTime( apThis );

            target = &( apThis->data[ apThis->xCurrentLength ] );

            dataHeader.ts_sec = apThis->curSecs;  /* timestamp seconds. */
            dataHeader.ts_usec = apThis->curUsec; /* timestamp microseconds. */
            dataHeader.incl_len = aLength;        /* number of octets of packet saved in file. */
            dataHeader.orig_len = aLength;        /* actual length of packet. */

            /* printf("PCAP write %08x:%08x length %08x:%08x \n", dataHeader.ts_sec, dataHeader.ts_usec, dataHeader.incl_len, dataHeader.orig_len); */

            /* Copy the packet hreader plus the packet data to the buffer. */
            memcpy( &( target[ 0 ] ), &( dataHeader ), sizeof dataHeader );
            memcpy( &( target[ sizeof dataHeader ] ), pucData, aLength );

            apThis->xCurrentLength += sizeof dataHeader + aLength;
        }

        return aLength;
    }
/*-----------------------------------------------------------*/

    int32_t pcap_toFile( SPcap * apThis,
                         const char * pcFname )
    {
        int32_t iResult;

        if( apThis->data == NULL )
        {
            printf( "pcap_toFile: No buffer was allocated.\n" );
            iResult = -1;
        }
        else if( apThis->xCurrentLength == 0U )
        {
            printf( "pcap_toFile: nothing to write\n" );
            iResult = 0;
        }
        else
        {
            FILE * writeHandle;
            {
                /* Make sure the path leading to the file is created. */
                char fname[ MAX_PATH ];
                char * ptr;

                snprintf( fname, sizeof fname, "%s", pcFname );
                ptr = strrchr( fname, '/' );

                if( ptr == NULL )
                {
                    ptr = strrchr( fname, '\\' );
                }

                if( ptr != NULL )
                {
                    *ptr = '\0';
                    _mkdir( fname );
                }
            }
            writeHandle = fopen( pcFname, "wb" );

            if( writeHandle == NULL )
            {
                printf( "pcap_toFile: create %s failed: %s\n", pcFname, strerror( errno ) );
                iResult = -errno;
            }
            else
            {
                iResult = ( int32_t ) fwrite( apThis->data, 1, apThis->xCurrentLength, writeHandle );

                if( iResult < 0 )
                {
                    printf( "pcap_toFile: Write error: %s\n", strerror( errno ) );
                }
                else
                {
                    printf( "pcap_toFile: %d bytes written to %s\n", iResult, pcFname );
                }

                fclose( writeHandle );
            }
        }

        return iResult;
    }
/*-----------------------------------------------------------*/

    static void pcap_checkTime( SPcap * apThis ) /* Get the time in micro seconds. */
    {
/*	uint64_t now = ( uint64_t ) 1000ull * xTaskGetTickCount(); */
        uint64_t now = getSystemTime();
        uint64_t timeDiff = now - apThis->startTime;

        apThis->curSecs = ( uint32_t ) ( timeDiff / 1000000ul );
        apThis->curUsec = ( uint32_t ) ( timeDiff % 1000000ul );
    }
/*-----------------------------------------------------------*/

/*            1         2         3         4         5         6         7         8
 *  012345678901234567890123456789012345678901234567890123456789012345678901234567890
 *  0090   6D 62 65 72 20 34 34 35 35 27 0A 31 33 36 2E 37  mber 4455'.136.7
 */
    #define pcapSHOW_PACKET_MAX_COLUMN_COUNT    32

    void vShowPacket( const uint8_t * apPacket,
                      int aLen,
                      int aWidth )
    {
        char str[ 4 * pcapSHOW_PACKET_MAX_COLUMN_COUNT + 7 + 2 + 1 ];

        int iByteCount = 0;

        if( aWidth > pcapSHOW_PACKET_MAX_COLUMN_COUNT )
        {
            aWidth = pcapSHOW_PACKET_MAX_COLUMN_COUNT;
        }

        const uint8_t * source = apPacket;
        unsigned index = 0;
        char * pcPosition = str + 7 + 3 * aWidth + 2;
        char * charPtr = pcPosition;
        char * hexPtr = str;

        while( aLen-- )
        {
            uint8_t ch = *( source++ );

            if( iByteCount == 0 )
            {
                sprintf( hexPtr, "%04X   ", index & 0xffff );
                hexPtr += 7;
            }

            sprintf( hexPtr, "%02X ", ch );
            hexPtr += 3;

            if( ( ch >= 32 ) && ( ch < 128 ) )
            {
                *( charPtr++ ) = ch;
            }
            else
            {
                *( charPtr++ ) = '.';
            }

            if( ( ++iByteCount >= aWidth ) || ( aLen == 0 ) )
            {
                while( hexPtr < pcPosition )
                {
                    *( hexPtr ) = ' ';
                    hexPtr++;
                }

                *charPtr = 0;
                printf( "%s\n", str );
                hexPtr = str;
                charPtr = pcPosition;
                iByteCount = 0;
            }

            index++;
        }
    }
/*-----------------------------------------------------------*/

    void pcap_clear( SPcap * apThis )
    {
        if( apThis->data )
        {
            uint8_t * ptr = apThis->data;
            apThis->data = NULL;
            free( ptr );
        }
    }
/*-----------------------------------------------------------*/


/*
 *
 ######    ####    ###   ######       ######                    ###
 #    #  #    #  #   #   #    #       #    #                     #
 #    # #     # #     #  #    #       #    #                     #
 #    # #       #     #  #    #       #    #  ####   ####    #####
 #####  #       #     #  #####        ###### #    #      #  #    #
 #      #       #######  #            #  ##  ######  #####  #    #
 #      #     # #     #  #            #   #  #      #    #  #    #
 #       #    # #     #  #            #    # #   ## #    #  #    #
 ####      ####  #     # ####         ###  ##  ####   ### ##  ### ##
 ####
 */

    int pcapfile_open( CPcapFile * apThis,
                       const char * pcFname )
    {
        int32_t iResult = -1;

        if( apThis->data == NULL )
        {
            apThis->data = ( SCapData * ) malloc( sizeof( SCapData ) );
        }

        if( apThis->data == NULL )
        {
            printf( "pcapfile_open: malloc fail\n" );
        }
        else if( apThis->data != NULL )
        {
            memset( apThis->data, 0, sizeof *apThis->data );
            apThis->data->fp = fopen( pcFname, "rb" );

            if( apThis->data->fp == NULL )
            {
                printf( "pcapfile_open: %s: %s\n", pcFname, strerror( errno ) );
                iResult = -errno;
            }
            else
            {
                struct pcap_hdr_s header;
                int rc = fread( ( char * ) &header, 1, sizeof header, apThis->data->fp );

                if( rc != sizeof header )
                {
                    printf( "pcapfile_open: Read %d bytes, expected %d\n", rc, sizeof header );
                }
                else if( ( header.magic_number != MAGIC_BE ) && ( header.magic_number != MAGIC_LE ) )
                {
                    printf( "pcapfile_open: bad magic %X\n", header.magic_number );
                }
                else
                {
                    apThis->data->le_convert = ( header.magic_number == PCAP_MAGIC_ID ) ? 0 : 1;
                    printf( "pcapfile_open: magic %X expect %X convert = %d\n", header.magic_number, PCAP_MAGIC_ID, apThis->data->le_convert );
                    iResult = 1;
                }

                if( iResult < 1 )
                {
                    pcapfile_close( apThis );
                }
            }
        }

        return iResult;
    }

    int pcapfile_read( CPcapFile * apThis,
                       char * apBuf,
                       size_t aMaxLen )
    {
        pcaprec_hdr_t lineHeader;

        if( ( apThis->data == NULL ) || ( apThis->data->fp == NULL ) )
        {
            return 0;
        }

        int rc = ( int ) fread( ( char * ) &( lineHeader ), 1, sizeof lineHeader, apThis->data->fp );

        if( rc != ( int ) sizeof lineHeader )
        {
            pcapfile_close( apThis );
            return -1;
        }

        if( apThis->data->le_convert != 0 )
        {
            lineHeader.incl_len = swap32( lineHeader.incl_len );
        }

        if( aMaxLen < ( size_t ) lineHeader.incl_len )
        {
            printf( "pcapfile_read: buffer too small: %u < %u\n", aMaxLen, lineHeader.incl_len );
            pcapfile_close( apThis );
            rc = -1;
        }
        else
        {
            rc = ( int ) fread( ( char * ) apBuf, 1, lineHeader.incl_len, apThis->data->fp );

            if( lineHeader.incl_len != ( uint32_t ) rc )
            {
                pcapfile_close( apThis );
                rc = -1;
            }
        }

        return rc;
    }

    void pcapfile_close( CPcapFile * apThis )
    {
        if( apThis->data != NULL )
        {
            if( apThis->data->fp != NULL )
            {
                fclose( apThis->data->fp );
                apThis->data->fp = NULL;
            }
        }
    }

#endif /* ipconfig */
