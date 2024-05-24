## FreeRTOS+TCP: Multi priority software queues


FreeRTOS+TCP now provides (feature in dev/tsn branch) support for multi priority software queues that can prioritize traffic based on the priority and budget allocated to each priority. The priority of each queue is assigned at compile time and all the network events that have to be processed in a given priority are sent to their respective priority queues. The number of queues can be configured at compile time. The IP-Task of the +TCP stack now has an event scheduler. The aim of the event scheduler is to process the events sent to the different event queues in the order of the queue priority and budget allotted to each priority.


### Configuration

Enabling multi priority software queues is done through the following macros that can be configured in the FreeRTOSIPConfig.h:

* `ipconfigEVENT_QUEUES` - Governs the number of software queues used. By default its defined to 1, meaning there is a single software queue for handling all events in the IP task.
* `ipconfigEVENT_PRIORITIES` - Defines the number of priorities supported. Should be less than or equal to `ipconfigEVENT_QUEUES` . By default its defined to 1 if `ipconfigEVENT_QUEUES` is 1.
* `ipconfigBUDGET_MAPPING` - An array of size `ipconfigEVENT_QUEUES`. Each value in the array specifies the number of events that will be processed continuously for a queue of that index in the array. The budget is inclusive of TX or RX events in queues.
* `ipconfigPACKET_PRIORITY_QUEUE_MAPPING` - An array of size `ipconfigEVENT_PRIORITIES`, that defines the queue to which events of a given priority (index of the array) are mapped. When an event of particular priority is ready its put to the queue thats mapped to that priority.
* `ipconfig_DEFAULT_EVENT_PRIORITY` - Default priority of network packets or sockets when they are created. 


NOTE: When network packets are received on the device, since the FreeRTOS+TCP AM243x network interface is not updated to handle the VLAN tags the priority is not decoded so all the RX packets are handled with same priority for now.


### Usage

For application writers advantages of multi priority software queues can be leveraged by setting priorities to the different sockets used in the application. Sockets can have any priority from 0 to `ipconfigEVENT_PRIORITIES`. With logically higher priority means higher numerical value (lower logical priority means lower numeric value). The socket priority can be updated via `FreeRTOS_setsockopt`, with option `FREERTOS_SO_SOCKET_PRIORITY` accpeting an `uint8_t` type priority value:

``` c
FreeRTOS_setsockopt(xListeningSocket, 0, FREERTOS_SO_SOCKET_PRIORITY, &ucPrio, sizeof( uint8_t ) );
```


### Example UDP echo server task

The following example demonstrates usage of socket priority on a UDP server socket:

``` c
typedef struct EchoTaskParams
{
    uint8_t priority;
    uint32_t port;
} EchoTaskParams_t;

static void prvSimpleSimpleServerTask( void *pvParameters )
{
    int32_t lBytes;
    uint8_t cReceivedString[ 512 ];
    struct freertos_sockaddr xClient, xBindAddress;
    uint32_t xClientLength = sizeof( xClient );
    Socket_t xListeningSocket;

    EchoTaskParams_t * task_params = ( EchoTaskParams_t * ) pvParameters;

    /* Attempt to open the socket. */
    xListeningSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
    configASSERT( xListeningSocket != FREERTOS_INVALID_SOCKET );

    /* This test receives data sent from a different port on the same IP
    address.  Configure the freertos_sockaddr structure with the address being
    bound to.  The strange casting is to try and remove    compiler warnings on 32
    bit machines.  Note that this task is only created after the network is up,
    so the IP address is valid here. */
    xBindAddress.sin_port = ( uint16_t ) ( ( uint32_t ) task_params->port ) & 0xffffUL;
    xBindAddress.sin_port = FreeRTOS_htons( xBindAddress.sin_port );
    xBindAddress.sin_family = FREERTOS_AF_INET;

    /* Set socket priority by setting FREERTOS_SO_SOCKET_PRIORITY socket option*/
    FreeRTOS_setsockopt(xListeningSocket, 0, FREERTOS_SO_SOCKET_PRIORITY, &( task_params->priority ), sizeof( task_params->priority ) );

    /* Bind the socket to the port that the client task will send to. */
    FreeRTOS_bind( xListeningSocket, &xBindAddress, sizeof( xBindAddress ) );

    FreeRTOS_printf(("********* UDP ECHO ***********\n"));

    for( ;; )
    {
        lBytes = 0;
        /* Zero out the receive array so there is NULL at the end of the string
        when it is printed out. */
        memset( cReceivedString, 0x00, sizeof( cReceivedString ) );

        /* Receive data on the socket.  ulFlags is zero, so the zero copy option
        is not set and the received data is copied into the buffer pointed to by
        cReceivedString.  By default the block time is portMAX_DELAY.
        xClientLength is not actually used by FreeRTOS_recvfrom(), but is set
        appropriately in case future versions do use it. */
        lBytes = FreeRTOS_recvfrom( xListeningSocket, cReceivedString, sizeof( cReceivedString ), 0, &xClient, &xClientLength );

        if (lBytes > 0)
        {
            FreeRTOS_sendto(xListeningSocket, cReceivedString, lBytes, 0, &xClient, xClientLength );
        }
    }
}
```
