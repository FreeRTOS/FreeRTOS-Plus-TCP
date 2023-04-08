/*
 * PCAP for embedded
 *
 * Writes a wireshark-compatible PCAP file
 */

#ifndef __PCAP_H__

    #define __PCAP_H__

    #include <stdlib.h>
    #include <stdio.h>
    #include <string.h>

    #ifdef __cplusplus
        extern "C" {
    #endif

    #ifdef USE_PCAP
        #error USE_PCAP is now valled ipconfigUSE_PCAP
    #endif

    #if ipconfigUSE_PCAP

        typedef struct _SPcap
        {
            uint8_t * data;
            volatile size_t xCurrentLength;
            size_t uxMaxLength;
            uint64_t startTime;
            uint32_t curSecs;
            uint32_t curUsec;
        } SPcap;

/* Initialise a PCAP struct. The field 'data' must either be allocated, or have the value NULL. */
        extern int pcap_init( SPcap * apThis,
                              size_t aSize );

/* Write an Ethernet packet to the buffer. */
        extern int pcap_write( SPcap * apThis,
                               const uint8_t * pucData,
                               int aLength );

/* Returns the number of packet bytes that can still be stored. */
        extern size_t pcap_has_space( SPcap * apThis );

/* Write the buffer with Ethernet packets to a file. */
        extern int32_t pcap_toFile( SPcap * apThis,
                                    const char * pcFname );

/* Free the space used by 'data'. */
        extern void pcap_clear( SPcap * apThis );

/* Fetch the current time in micro seconds. */
        extern void pcap_checkTime( SPcap * apThis );

        static __inline int pcap_hasData( SPcap * apThis )
        {
            /* Return true if there is at least one Ethernet packet recorded. */
            return ( apThis->data != NULL ) && ( apThis->xCurrentLength > 44 );
        }

/* Introduce an acstract struct that is used while reading a PCAP file. */
        struct _SCapData;

        typedef struct _CPcapFile
        {
            struct _SCapData * data;
        } CPcapFile;

/* Open a PACP file and check the header. */
        extern int pcapfile_open( CPcapFile * apThis,
                                  const char * pcFname );
        /* Read one packet from the file and returns the length of the packet. */
        extern int pcapfile_read( CPcapFile * apThis,
                                  char * apBuf,
                                  size_t aMaxLen );
        /* Close the file handle. */
        extern void pcapfile_close( CPcapFile * apThis );

    #endif /* defined(ipconfigUSE_PCAP) */

    #if ipconfigUSE_PCAP
        int uipCapAddPacket( const uint8_t * pucData,
                             int aLen );
        void uipCapCheckTime( void );
    #else
        static inline int uipCapAddPacket( const uint8_t * pucData,
                                           int aLen )
        {
            return 1;
        }
        static inline void uipCapCheckTime()
        {
        }
    #endif /* if ipconfigUSE_PCAP */

/* Printf a hexdump of data to stdout. */
    extern void vShowPacket( const uint8_t * apPacket,
                             int aLen,
                             int aWidth );

    #ifdef __cplusplus
        } /* extern "C" */
    #endif

#endif /* __PCAP_H__ */
