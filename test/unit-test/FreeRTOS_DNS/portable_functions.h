void * pvPortMalloc( size_t xSize );
void vPortFree( void * pv );
void vPortInitialiseBlocks( void );
size_t xPortGetFreeHeapSize( void );
size_t xPortGetMinimumEverFreeHeapSize( void );
