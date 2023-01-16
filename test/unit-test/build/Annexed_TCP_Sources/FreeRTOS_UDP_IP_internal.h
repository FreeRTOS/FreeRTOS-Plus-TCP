eARPLookupResult_t prvLookupIPInCache( NetworkBufferDescriptor_t * const pxNetworkBuffer );
void prvFindIPv4Endpoint( NetworkBufferDescriptor_t * const pxNetworkBuffer );
eARPLookupResult_t prvStartLookup( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                          BaseType_t * pxLostBuffer );
