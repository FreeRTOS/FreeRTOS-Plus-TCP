The module win_pcap.c allows to create and read raw PCAP files.
Here below a few lines of code that show how a file can be created, and how it can be read.

    #include "win_pcap.h"
    static SPcap xMyPCAP;
    static BaseType_t xPCAP_Ok = pdFALSE;
    
        xPCAP_Ok = pcap_init( &( MyPCAP ), 10240000U );
    
        for( ;; )
        {
            if( xPCAP_Ok == pdTRUE )
            {
                pcap_write( &( MyPCAP ), pcBuffer, xActualCount );
                if( pcap_has_space( &( MyPCAP ) ) < 1514 )
                {
					/* No more space in the buffer. */
                    pcap_toFile( &( MyPCAP ), PCAP_FILE_NAME );
                    xPCAP_Ok = pdFALSE;
                }
            }
        }
    
        int rc;
        uint8_t packet_buffer[ 1514 ];
    
        CPcapFile xPcapFile;
        memset( &( xPcapFile ), 0, sizeof xPcapFile );
        rc = pcapfile_open( &( xPcapFile ), PCAP_FILE_NAME );
        while( rc > 0 )
        {
            rc = pcapfile_read( &( xPcapFile ), packet_buffer, sizeof( packet_buffer ) );
            if( rc > 0 )
            {
                vShowPacket( packet_buffer, rc, 16 );
            }
        }
