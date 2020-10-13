<?xml version='1.0' encoding='UTF-8' standalone='yes' ?>
<tagfile doxygen_version="1.8.20" doxygen_gitid="f246dd2f1c58eea39ea3f50c108019e4d4137bd5">
  <compound kind="file">
    <name>FreeRTOS_ARP.c</name>
    <path>/root/Desktop/AddDoxygen/</path>
    <filename>_free_r_t_o_s___a_r_p_8c.html</filename>
    <member kind="define">
      <type>#define</type>
      <name>arpMAX_ARP_AGE_BEFORE_NEW_ARP_REQUEST</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>a22f53fd4d5218d841f6176b29603a955</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>arpGRATUITOUS_ARP_PERIOD</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>a7b4eb297ab0d35cfe95b1879495a3d7f</anchor>
      <arglist></arglist>
    </member>
    <member kind="function" static="yes">
      <type>static eARPLookupResult_t</type>
      <name>prvCacheLookup</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>a78b76b83a58bdb609db07f2949b39dcb</anchor>
      <arglist>(uint32_t ulAddressToLookup, MACAddress_t *const pxMACAddress)</arglist>
    </member>
    <member kind="function">
      <type>eFrameProcessingResult_t</type>
      <name>eARPProcessPacket</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>aa06d3a8a2d409547e12b4825ebc885b5</anchor>
      <arglist>(ARPPacket_t *const pxARPFrame)</arglist>
    </member>
    <member kind="function">
      <type>void</type>
      <name>vARPRefreshCacheEntry</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>aa9740bba27acb79ac417f9b187630e3b</anchor>
      <arglist>(const MACAddress_t *pxMACAddress, const uint32_t ulIPAddress)</arglist>
    </member>
    <member kind="function">
      <type>eARPLookupResult_t</type>
      <name>eARPGetCacheEntry</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>a1ee3377f9c286506135c17be1962d8d6</anchor>
      <arglist>(uint32_t *pulIPAddress, MACAddress_t *const pxMACAddress)</arglist>
    </member>
    <member kind="function">
      <type>void</type>
      <name>vARPAgeCache</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>a3d3934dd27e4d024ab7a14ed0c80b3cc</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function">
      <type>void</type>
      <name>vARPSendGratuitous</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>aa96d87a3e4505229094bf3d81330c2f4</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function">
      <type>void</type>
      <name>FreeRTOS_OutputARPRequest</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>a87ebc2f32c8cda6cdc24a265df2388c0</anchor>
      <arglist>(uint32_t ulIPAddress)</arglist>
    </member>
    <member kind="function">
      <type>void</type>
      <name>vARPGenerateRequestPacket</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>a27861e019fb0f3c1d5579f6806f75b4c</anchor>
      <arglist>(NetworkBufferDescriptor_t *const pxNetworkBuffer)</arglist>
    </member>
    <member kind="function">
      <type>void</type>
      <name>FreeRTOS_ClearARP</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>a7ad41b60042629fc57086d4990fc6347</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function">
      <type>BaseType_t</type>
      <name>xCheckLoopback</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>a0927214ffe1d8b142d6e49fc26430339</anchor>
      <arglist>(NetworkBufferDescriptor_t *const pxDescriptor, BaseType_t bReleaseAfterSend)</arglist>
    </member>
    <member kind="variable">
      <type>_static ARPCacheRow_t</type>
      <name>xARPCache</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>afdc43c741d35db756e9a4ca5cd064bf1</anchor>
      <arglist>[ipconfigARP_CACHE_ENTRIES]</arglist>
    </member>
    <member kind="variable" static="yes">
      <type>static TickType_t</type>
      <name>xLastGratuitousARPTime</name>
      <anchorfile>_free_r_t_o_s___a_r_p_8c.html</anchorfile>
      <anchor>aa9c3721b546b6d8021730dbc1d49c263</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="file">
    <name>FreeRTOS_DHCP.c</name>
    <path>/root/Desktop/AddDoxygen/</path>
    <filename>_free_r_t_o_s___d_h_c_p_8c.html</filename>
    <class kind="struct">struct</class>
    <member kind="define">
      <type>#define</type>
      <name>dhcpCLIENT_HARDWARE_ADDRESS_LENGTH</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a9dfdebcc673e74887f8512868fa361ef</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpSERVER_HOST_NAME_LENGTH</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a3460ffc5d7a95ff76742f7dc24a60fd8</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpBOOT_FILE_NAME_LENGTH</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a525076903bc0e6179e9f18f11067018a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpINITIAL_TIMER_PERIOD</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a7e77d690aa573e19c016d4bab59a51b7</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpINITIAL_DHCP_TX_PERIOD</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>ae21108aea9e8f67970c05f03ae882832</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpIPv4_ZERO_PAD_OPTION_CODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a8c7929e27cfef12a81737179f4844eec</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpIPv4_SUBNET_MASK_OPTION_CODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a9b5e6f35b4d3c21e7339fd864b2eb083</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpIPv4_GATEWAY_OPTION_CODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a4c597e1ce55a624d96d679c7905ce68a</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpIPv4_DNS_SERVER_OPTIONS_CODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a152cd2137919e452b5329615b580f263</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpIPv4_DNS_HOSTNAME_OPTIONS_CODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a0e26813b27eb5216e4b4a69190f0e2a2</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpIPv4_REQUEST_IP_ADDRESS_OPTION_CODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a199afb602e62b7b4a8264ca6b4ce3d39</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpIPv4_LEASE_TIME_OPTION_CODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>aee62afab740f4b806fcb62947799bf22</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpIPv4_MESSAGE_TYPE_OPTION_CODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a2dfbd401c9846f500668864b7fb2710c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a1ae323b48e61a9cd0f8ea6d6f96bd9bb</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpIPv4_PARAMETER_REQUEST_OPTION_CODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>ab0415fe448ea9cf9bd3978ab4a5a2db4</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpIPv4_CLIENT_IDENTIFIER_OPTION_CODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>ae5814df2d0f5ab149f9528a8cec3ff89</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpMESSAGE_TYPE_DISCOVER</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a2e24721bd39e17d9b183e2125687d62d</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpMESSAGE_TYPE_OFFER</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a62c031313a09d86b89496ba6a9cae006</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpMESSAGE_TYPE_REQUEST</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a869e3c5f0c92896e6cb35e3e655b46b9</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpMESSAGE_TYPE_ACK</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a775354bab8931849febdbe263c58d1d0</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpMESSAGE_TYPE_NACK</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a6b165aa67cc11f56afbf388e7ac97264</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpCLIENT_IDENTIFIER_OFFSET</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a4ceff5f0da2ce1cb99569c34fef4d681</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpREQUESTED_IP_ADDRESS_OFFSET</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a25caf50e4ba7269beaf6c6075fd46464</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpDHCP_SERVER_IP_ADDRESS_OFFSET</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>aeb87759824da5d6e8f7f89ed9319258c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpREQUEST_OPCODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a73c6f002510653b02300a1c673f72c9d</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpREPLY_OPCODE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a3024e6e8ac856f362aa981ee5a8b9135</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpADDRESS_TYPE_ETHERNET</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>aa0d773d9ec08477bcad8103f5a38c3a4</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpETHERNET_ADDRESS_LENGTH</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a2767c2133228aee9dfb336269332dabc</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>EP_DHCPData</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>adfb2f90932de3ba1166a8ae0e22cfa16</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>EP_IPv4_SETTINGS</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a7855dad00c2e1354eaafb18a0ec8d999</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpDEFAULT_LEASE_TIME</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a10e722aeaae4c7083c3e373361e4289c</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpMINIMUM_LEASE_TIME</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>ab94b8bccbab25d280da8ccdaf4455d57</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpOPTION_END_BYTE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>af99f3d8cdc1153ec6629288600a967f7</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpFIRST_OPTION_BYTE_OFFSET</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a91ced274d25f700a12f7c520388e2fdf</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpCLIENT_PORT_IPv4</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a6314ef4310bb7e7b007fc8f8bd7caa64</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpSERVER_PORT_IPv4</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a8312231f5161d99c7b8b752fde8cb030</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpCOOKIE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a9c0d01ea72440e996e7cf6599efa518e</anchor>
      <arglist></arglist>
    </member>
    <member kind="define">
      <type>#define</type>
      <name>dhcpBROADCAST</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a399a2cda3f448f8b5c56fa4708ee4793</anchor>
      <arglist></arglist>
    </member>
    <member kind="function" static="yes">
      <type>static portINLINE</type>
      <name>ipDECL_CAST_PTR_FUNC_FOR_TYPE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a828bde991d7f730cc44a775b504d85f8</anchor>
      <arglist>(DHCPMessage_IPv4_t)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static portINLINE</type>
      <name>ipDECL_CAST_CONST_PTR_FUNC_FOR_TYPE</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a83261d43472efe09f8f0d99c8a4c14d4</anchor>
      <arglist>(DHCPMessage_IPv4_t)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>prvSendDHCPDiscover</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a751fb09098c8c93997f7a122c8f02f4f</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function">
      <type>_static BaseType_t</type>
      <name>prvProcessDHCPReplies</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a03acd9164ad584eb639fd70356794366</anchor>
      <arglist>(BaseType_t xExpectedMessageType)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>prvSendDHCPRequest</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>ad4a2682a52bc640066ca0528dbc33c18</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>prvInitialiseDHCP</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a0b627c523231206cd31f2bb46372e44e</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static uint8_t *</type>
      <name>prvCreatePartDHCPMessage</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a8d2f4ae9d52b68d32dae4991f3cb3229</anchor>
      <arglist>(struct freertos_sockaddr *pxAddress, BaseType_t xOpcode, const uint8_t *const pucOptionsArray, size_t *pxOptionsArraySize)</arglist>
    </member>
    <member kind="function">
      <type>_static void</type>
      <name>prvCreateDHCPSocket</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>aaff6679eef687e2c208ac49d368eabff</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function" static="yes">
      <type>static void</type>
      <name>prvCloseDHCPSocket</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a9d09a6b3e592978816bf2d7fdd98b699</anchor>
      <arglist>(void)</arglist>
    </member>
    <member kind="function">
      <type>BaseType_t</type>
      <name>xIsDHCPSocket</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>aed005283591e5af559f10afb9090eae0</anchor>
      <arglist>(Socket_t xSocket)</arglist>
    </member>
    <member kind="function">
      <type>void</type>
      <name>vDHCPProcess</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a513cb227506fa5ca324c1270b347fde3</anchor>
      <arglist>(BaseType_t xReset)</arglist>
    </member>
    <member kind="variable">
      <type>_static Socket_t</type>
      <name>xDHCPSocket</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>aea41a17995bc1183eb373bf376e90ae5</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>_static DHCPData_t</type>
      <name>xDHCPData</name>
      <anchorfile>_free_r_t_o_s___d_h_c_p_8c.html</anchorfile>
      <anchor>a501856edb97370508c912a8b49dbf3cb</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>ARPCacheRow_t</name>
    <filename>struct_a_r_p_cache_row__t.html</filename>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulIPAddress</name>
      <anchorfile>struct_a_r_p_cache_row__t.html</anchorfile>
      <anchor>ad7e6f78fbdbf7496f71897b831ee9e19</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>MACAddress_t</type>
      <name>xMACAddress</name>
      <anchorfile>struct_a_r_p_cache_row__t.html</anchorfile>
      <anchor>acb75c73fe317ae0ad35275551f4c4041</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucAge</name>
      <anchorfile>struct_a_r_p_cache_row__t.html</anchorfile>
      <anchor>a62d48e7f8d847def3e252b48abc201e1</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucValid</name>
      <anchorfile>struct_a_r_p_cache_row__t.html</anchorfile>
      <anchor>a3097622f9ccba0e9b82e1d4b5e317606</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>xDHCP_DATA</name>
    <filename>structx_d_h_c_p___d_a_t_a.html</filename>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulTransactionId</name>
      <anchorfile>structx_d_h_c_p___d_a_t_a.html</anchorfile>
      <anchor>adbc2b6c978a64237b21501d47b4a68a4</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulOfferedIPAddress</name>
      <anchorfile>structx_d_h_c_p___d_a_t_a.html</anchorfile>
      <anchor>a7744ff1fe929ff7419929e3482daa9ed</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulDHCPServerAddress</name>
      <anchorfile>structx_d_h_c_p___d_a_t_a.html</anchorfile>
      <anchor>a04c9aadfb84a9f0c128ccd3cace59d26</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulLeaseTime</name>
      <anchorfile>structx_d_h_c_p___d_a_t_a.html</anchorfile>
      <anchor>a7b77339ff6e3d172bb8541ae4af31002</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TickType_t</type>
      <name>xDHCPTxTime</name>
      <anchorfile>structx_d_h_c_p___d_a_t_a.html</anchorfile>
      <anchor>a62eb4df9377176103366608f89cde773</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TickType_t</type>
      <name>xDHCPTxPeriod</name>
      <anchorfile>structx_d_h_c_p___d_a_t_a.html</anchorfile>
      <anchor>a67d277497631a2be9c5d2b1cd5458cb0</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>BaseType_t</type>
      <name>xUseBroadcast</name>
      <anchorfile>structx_d_h_c_p___d_a_t_a.html</anchorfile>
      <anchor>a57b735613f051927ed9e82f07256d3cd</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>eDHCPState_t</type>
      <name>eDHCPState</name>
      <anchorfile>structx_d_h_c_p___d_a_t_a.html</anchorfile>
      <anchor>a5dd7a3139a5d159a65c6604a44afe5fc</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>DumpEntries_t</name>
    <filename>struct_dump_entries__t.html</filename>
    <member kind="variable">
      <type>size_t</type>
      <name>uxEntryCount</name>
      <anchorfile>struct_dump_entries__t.html</anchorfile>
      <anchor>a57b3b6be25147d0deb91b4f01c840494</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>DumpEntry_t</type>
      <name>xEntries</name>
      <anchorfile>struct_dump_entries__t.html</anchorfile>
      <anchor>a904e6c5b00dec0c3540289a60f123060</anchor>
      <arglist>[dumpMAX_DUMP_ENTRIES]</arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>DumpEntry_t</name>
    <filename>struct_dump_entry__t.html</filename>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulMask</name>
      <anchorfile>struct_dump_entry__t.html</anchorfile>
      <anchor>a88e54409181b654c82db72bc8d936b4c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>uxMax</name>
      <anchorfile>struct_dump_entry__t.html</anchorfile>
      <anchor>a6e87af1c71200d507f547dd8d576be0f</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>uxCount</name>
      <anchorfile>struct_dump_entry__t.html</anchorfile>
      <anchor>aabe799376c65c699c6854fd987b84375</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>freertos_sockaddr</name>
    <filename>structfreertos__sockaddr.html</filename>
    <member kind="variable">
      <type>uint8_t</type>
      <name>sin_len</name>
      <anchorfile>structfreertos__sockaddr.html</anchorfile>
      <anchor>ae3dd93b37bd98e67a7eee205880fab42</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>sin_family</name>
      <anchorfile>structfreertos__sockaddr.html</anchorfile>
      <anchor>a825766c52957d63bcf215bbf042e7edd</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>sin_port</name>
      <anchorfile>structfreertos__sockaddr.html</anchorfile>
      <anchor>a7bdc446dabdc9f6a4ddf3f75fa80bcb1</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>sin_addr</name>
      <anchorfile>structfreertos__sockaddr.html</anchorfile>
      <anchor>a71e5f78f1f8f5260b0b21f82b182f0f0</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>FreeRTOS_Socket_t</name>
    <filename>struct_free_r_t_o_s___socket__t.html</filename>
    <member kind="variable">
      <type>EventBits_t</type>
      <name>xEventBits</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>ac537b7cd7c67cb72ee80539a3ec86615</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>EventGroupHandle_t</type>
      <name>xEventGroup</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>a1087ecfb6310a094c37199bb74ee552d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>ListItem_t</type>
      <name>xBoundSocketListItem</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>a81f7fb13eb2eb7e9d3dd6d53d1b62fc6</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TickType_t</type>
      <name>xReceiveBlockTime</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>a11b6b2c460bed74b44982db42571f18c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TickType_t</type>
      <name>xSendBlockTime</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>a62980b673e34f3d860d28291e8368dc5</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usLocalPort</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>a0823b422673d39a0777f782e5b228924</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucSocketOptions</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>a5c58826d6de231ea85fbd8232d483e73</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucProtocol</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>a4957f47b13a4cab656e3394af700dea8</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>IPUDPSocket_t</type>
      <name>xUDP</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>af7d20b59a58392c60e90742d7e05f9eb</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>IPTCPSocket_t</type>
      <name>xTCP</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>ad7b0c1a2abd13c300e256223cfdb8861</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint64_t</type>
      <name>ullTCPAlignment</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>a218ef7bb881b6f6cca87d328758d7eee</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>union FreeRTOS_Socket_t::@3</type>
      <name>u</name>
      <anchorfile>struct_free_r_t_o_s___socket__t.html</anchorfile>
      <anchor>af45d92a8fd3ac7bbe14eb37eb769079b</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>IPStackEvent_t</name>
    <filename>struct_i_p_stack_event__t.html</filename>
    <member kind="variable">
      <type>eIPEvent_t</type>
      <name>eEventType</name>
      <anchorfile>struct_i_p_stack_event__t.html</anchorfile>
      <anchor>a3c79cf0368a1c276db07326c04d2f48c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>void *</type>
      <name>pvData</name>
      <anchorfile>struct_i_p_stack_event__t.html</anchorfile>
      <anchor>a74a2b43a698e7b1f80af6cbe7ba766f0</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>IPTCPSocket_t</name>
    <filename>struct_i_p_t_c_p_socket__t.html</filename>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulRemoteIP</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a32ed7eb620f15975b202bafaae98033b</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usRemotePort</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a242d2f450863eb04051d067b1f9a65e8</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bMssChange</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>ae2e1b69ff7626e60490dfce5c4e4b49e</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bPassAccept</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a4fbfbc25d2999a94283498c287e948c4</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bPassQueued</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>aefabd205c12a912148f520bc7331bda3</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bReuseSocket</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a67e3b0df6d2efac1d3c7479160b03a09</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bCloseAfterSend</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a7955b5826284647786ec3d76738b5c60</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bUserShutdown</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>aed89f4457684a9741063ebdd0055615c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bCloseRequested</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>ad3f84b87d8c3ad0d534ccf7636759aea</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bLowWater</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a1b1283ba1e84b4194f16e27884ab6e56</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bWinChange</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a3266106030dfdc10c6cce5cd729e8753</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bSendKeepAlive</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a0797356381128d67f9446c98b178a3fd</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bWaitKeepAlive</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a950472303383c1403beb0c4f8730c13c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bConnPrepared</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>af610864692c1bb9612186b6124399381</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bFinAccepted</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>ab54b8e386f194f485fb248924d8fbfbb</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bFinSent</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a6e595043eea244df0d3276d709347aaa</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bFinRecv</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a7a3a0e7d85826d93bca3ecbedc8b790b</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bFinAcked</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>af48a9f4d51b0eb0d9050ddb9f29af026</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bFinLast</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a71a1bd7622b0355b0da95a015c199f9d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bRxStopped</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a684da3bb496f67b256d4d5d3653e1b3d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bMallocError</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a084d5462a8ac914e1295bb9841a9d9b1</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bWinScaling</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a108ad4e95847749be6d17617368fa88a</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>struct IPTCPSocket_t::@2</type>
      <name>bits</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a65e5019837336ac80d144aa1c91028e8</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulHighestRxAllowed</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a8558cd1bc60e6ec1a490fb0627a8a90e</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usTimeout</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a6af07b9c7a0e7a73bf52c11ea4657b64</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usCurMSS</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a327fd7be334ed970068b0ba825453376</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usInitMSS</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a12363ab6c5cdac8495864a358c4a0d5d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usChildCount</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>ab9c9a21ca5f0a92fe267bf054d905bbe</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usBacklog</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a3faa3e47f0f9024e6544317387f5257d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucRepCount</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a114f05ceb8efdc0552608a6adb6d46db</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucTCPState</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>ad8bcdb186864a071efa65791fbea737c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>struct xSOCKET *</type>
      <name>pxPeerSocket</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>afa792ed5525eb9c9f2190ed3b6319ba1</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TickType_t</type>
      <name>xLastActTime</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>ad0f826d4ed758787daef5d0c938bcdf9</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>uxLittleSpace</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a2790d23e492ae2e72115f524518eae79</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>uxEnoughSpace</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a08e862a831d0c8ccce04281b2a4f99dd</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>uxRxStreamSize</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>adae0a2e945eb93b7197fe4d1db9ff502</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>uxTxStreamSize</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>ab8fb5fcab4fb96ef8d5074624d886926</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>StreamBuffer_t *</type>
      <name>rxStream</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>acc0e922869614b29dfacbaaca87a8fd7</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>StreamBuffer_t *</type>
      <name>txStream</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a0f8ca18cd9438cbb3ff4b81df888c2f7</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>NetworkBufferDescriptor_t *</type>
      <name>pxAckMessage</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a2684031d3344d337d00783af8c7834d5</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>LastTCPPacket_t</type>
      <name>xPacket</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a825906211789ffb7e900020e3a700d2a</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>tcpflags</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a88f867efcc4b3e6de5994f2ec8a43489</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucMyWinScaleFactor</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>ab8f19ca09df246571c4503d26184882a</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucPeerWinScaleFactor</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a9af40a7697b7ea5a2fbd9e34a108f9de</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulWindowSize</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a397e9d9a6b7fe660b0603a0933c82652</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>uxRxWinSize</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a3a237318fc4107062470fe9523f67bc0</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>uxTxWinSize</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a7d77b6dadf986bbb813da8b9fca7fa15</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TCPWindow_t</type>
      <name>xTCPWindow</name>
      <anchorfile>struct_i_p_t_c_p_socket__t.html</anchorfile>
      <anchor>a50eccf22fc5189e7710be4271d4fb740</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>IPTimer_t</name>
    <filename>struct_i_p_timer__t.html</filename>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bActive</name>
      <anchorfile>struct_i_p_timer__t.html</anchorfile>
      <anchor>a5d4b2f7d9479bad52891214655c91d05</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bExpired</name>
      <anchorfile>struct_i_p_timer__t.html</anchorfile>
      <anchor>a7244df48107f28b502e0482d80d5ed79</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TimeOut_t</type>
      <name>xTimeOut</name>
      <anchorfile>struct_i_p_timer__t.html</anchorfile>
      <anchor>a1fbb967ea7d847861fcdc91fac46f664</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TickType_t</type>
      <name>ulRemainingTime</name>
      <anchorfile>struct_i_p_timer__t.html</anchorfile>
      <anchor>a12d360ad42cfca0fb6e9e1fe02c89130</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TickType_t</type>
      <name>ulReloadTime</name>
      <anchorfile>struct_i_p_timer__t.html</anchorfile>
      <anchor>aec37c3212367cf4478cd02b26cb9fdb9</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>IPUDPSocket_t</name>
    <filename>struct_i_p_u_d_p_socket__t.html</filename>
    <member kind="variable">
      <type>List_t</type>
      <name>xWaitingPacketsList</name>
      <anchorfile>struct_i_p_u_d_p_socket__t.html</anchorfile>
      <anchor>a75d281c062cef5f3ac4ba623f57cff9d</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="union">
    <name>LastTCPPacket_t</name>
    <filename>union_last_t_c_p_packet__t.html</filename>
    <member kind="variable">
      <type>uint64_t</type>
      <name>ullAlignmentWord</name>
      <anchorfile>union_last_t_c_p_packet__t.html</anchorfile>
      <anchor>acac0b536fd23d0549090a14fee75c2f9</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>struct LastTCPPacket_t::@0</type>
      <name>a</name>
      <anchorfile>union_last_t_c_p_packet__t.html</anchorfile>
      <anchor>a0c7565d1dcdd4b49f66993a07aed2b49</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>struct LastTCPPacket_t::@1</type>
      <name>u</name>
      <anchorfile>union_last_t_c_p_packet__t.html</anchorfile>
      <anchor>a52e1ac85c8c531d827d8919dc5a10d6d</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>LowHighWater_t</name>
    <filename>struct_low_high_water__t.html</filename>
    <member kind="variable">
      <type>size_t</type>
      <name>uxLittleSpace</name>
      <anchorfile>struct_low_high_water__t.html</anchorfile>
      <anchor>ad06f5b9357359dd6d4fe360b27d58576</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>uxEnoughSpace</name>
      <anchorfile>struct_low_high_water__t.html</anchorfile>
      <anchor>ab46bf12f20f5b1b8b4f20b56be2799e8</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>NetworkAddressingParameters_t</name>
    <filename>struct_network_addressing_parameters__t.html</filename>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulDefaultIPAddress</name>
      <anchorfile>struct_network_addressing_parameters__t.html</anchorfile>
      <anchor>ae045d16fa68bfe73642742a5f31e2c37</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulNetMask</name>
      <anchorfile>struct_network_addressing_parameters__t.html</anchorfile>
      <anchor>a22fbe93b74fb20da191c622797d3df81</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulGatewayAddress</name>
      <anchorfile>struct_network_addressing_parameters__t.html</anchorfile>
      <anchor>a9d71a84b99c03d5b7ba7a8bd4a83eaed</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulDNSServerAddress</name>
      <anchorfile>struct_network_addressing_parameters__t.html</anchorfile>
      <anchor>aa67e87c2631d5ec4b4521ce60fce0c13</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulBroadcastAddress</name>
      <anchorfile>struct_network_addressing_parameters__t.html</anchorfile>
      <anchor>ad73e26c68c4bb9f768ddee1c509097ba</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>NetworkBufferDescriptor_t</name>
    <filename>struct_network_buffer_descriptor__t.html</filename>
    <member kind="variable">
      <type>ListItem_t</type>
      <name>xBufferListItem</name>
      <anchorfile>struct_network_buffer_descriptor__t.html</anchorfile>
      <anchor>a2686bee348dfc8652b3d533d8f3fc834</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulIPAddress</name>
      <anchorfile>struct_network_buffer_descriptor__t.html</anchorfile>
      <anchor>ae5ab9a79f989beec2c8a5f20b6507f1b</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t *</type>
      <name>pucEthernetBuffer</name>
      <anchorfile>struct_network_buffer_descriptor__t.html</anchorfile>
      <anchor>abf478d3a5f40ee8fcff38b60d40d3ad9</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>xDataLength</name>
      <anchorfile>struct_network_buffer_descriptor__t.html</anchorfile>
      <anchor>a8f99bd5f37c30f0479c46ef33edbbbef</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usPort</name>
      <anchorfile>struct_network_buffer_descriptor__t.html</anchorfile>
      <anchor>a7c33c718263189dfb7e5d69faed2acd6</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usBoundPort</name>
      <anchorfile>struct_network_buffer_descriptor__t.html</anchorfile>
      <anchor>a03acb46a1d606b0a1fa383fd29e3ba2e</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="union">
    <name>ProtocolHeaders_t</name>
    <filename>union_protocol_headers__t.html</filename>
    <member kind="variable">
      <type>ICMPHeader_t</type>
      <name>xICMPHeader</name>
      <anchorfile>union_protocol_headers__t.html</anchorfile>
      <anchor>a34fa07a31297737bff19d733c6b89437</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>UDPHeader_t</type>
      <name>xUDPHeader</name>
      <anchorfile>union_protocol_headers__t.html</anchorfile>
      <anchor>a340de9e523d1acc9d2f74bc2aa68c623</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TCPHeader_t</type>
      <name>xTCPHeader</name>
      <anchorfile>union_protocol_headers__t.html</anchorfile>
      <anchor>a4ea5af3581d9234f7eebf3f3191cc04a</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="union">
    <name>ProtocolPacket_t</name>
    <filename>union_protocol_packet__t.html</filename>
    <member kind="variable">
      <type>ARPPacket_t</type>
      <name>xARPPacket</name>
      <anchorfile>union_protocol_packet__t.html</anchorfile>
      <anchor>aad27f9018b835568291e438814538985</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TCPPacket_t</type>
      <name>xTCPPacket</name>
      <anchorfile>union_protocol_packet__t.html</anchorfile>
      <anchor>a06b806c78329b262b110ae28acf4b248</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>UDPPacket_t</type>
      <name>xUDPPacket</name>
      <anchorfile>union_protocol_packet__t.html</anchorfile>
      <anchor>a361b2c5467713271312045f01a9b4b0c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>ICMPPacket_t</type>
      <name>xICMPPacket</name>
      <anchorfile>union_protocol_packet__t.html</anchorfile>
      <anchor>abf91797faa0b5541232bbe007fd5c358</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>StreamBuffer_t</name>
    <filename>struct_stream_buffer__t.html</filename>
    <member kind="variable">
      <type>volatile size_t</type>
      <name>uxTail</name>
      <anchorfile>struct_stream_buffer__t.html</anchorfile>
      <anchor>ab4b51182188e1d42c49918d10d939785</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>volatile size_t</type>
      <name>uxMid</name>
      <anchorfile>struct_stream_buffer__t.html</anchorfile>
      <anchor>ab3f03b76564f83ef2e040aaf14ca1330</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>volatile size_t</type>
      <name>uxHead</name>
      <anchorfile>struct_stream_buffer__t.html</anchorfile>
      <anchor>ae29b53069e0afd6e117f77d43e4c68a5</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>volatile size_t</type>
      <name>uxFront</name>
      <anchorfile>struct_stream_buffer__t.html</anchorfile>
      <anchor>a4f2a7a3c3a1098a77e74df26d78b92de</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>size_t</type>
      <name>LENGTH</name>
      <anchorfile>struct_stream_buffer__t.html</anchorfile>
      <anchor>a68ae1bd7578a1851412320d4e234c00f</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucArray</name>
      <anchorfile>struct_stream_buffer__t.html</anchorfile>
      <anchor>a1db2d6ef9f4266a540d86097a4051cdf</anchor>
      <arglist>[sizeof(size_t)]</arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>struct</name>
    <filename>structstruct.html</filename>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucOpcode</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>ad884a11402ccadd1b88ca8f9394ce0fc</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucAddressType</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>abfa2426341ed766152ea7edfcd30ad7b</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucAddressLength</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a14e877b0915020479dfd71609dd6f60b</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucHops</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a0c8d8fde35ef807181a3af28302931e9</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulTransactionID</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>ade137bb75fbc6cf8b3076fd707de4807</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usElapsedTime</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>ab65dc4a8cd915d8a3123f4452679930a</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usFlags</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a9ca7c93121ebde17c241c6090c313f93</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulClientIPAddress_ciaddr</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a4eecb7fd87bcbac3b01d61207829c585</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulYourIPAddress_yiaddr</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>ae058b7eaa364f8fcf38ee855b8fb648c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulServerIPAddress_siaddr</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a0a54655dc8374e96f97de34aafa9d409</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulRelayAgentIPAddress_giaddr</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a1da36384572e810902bc854cd28f00b0</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucClientHardwareAddress</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a13ee27d7a1edfa18cf81cc9b91272487</anchor>
      <arglist>[dhcpCLIENT_HARDWARE_ADDRESS_LENGTH]</arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucServerHostName</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>aee417fad4b56e93f970d8dc2c258452a</anchor>
      <arglist>[dhcpSERVER_HOST_NAME_LENGTH]</arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucBootFileName</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>ab24e7f933bf7a8f0282e440be4e5ff78</anchor>
      <arglist>[dhcpBOOT_FILE_NAME_LENGTH]</arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulDHCPCookie</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a1d3d088b7f2d720efef9773d8ba4c3bc</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucBytes</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a42f7aefbd34c2b9c513a9d7cb8d289aa</anchor>
      <arglist>[ipMAC_ADDRESS_LENGTH_BYTES]</arglist>
    </member>
    <member kind="variable">
      <type>MACAddress_t</type>
      <name>xDestinationAddress</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>ade7fc0f7222ea6079955b2cdcb6408a0</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>MACAddress_t</type>
      <name>xSourceAddress</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>af203141196c89d5f1a90af29dd077212</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usFrameType</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>ac2294956ef25abf79b292eae53ca0d97</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usHardwareType</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a1f9dc6989d16e650f0b15b646fc502b0</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usProtocolType</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a499848689c664a20ef209c0d22b42223</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucHardwareAddressLength</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>aaff67273a3b66f2d23759c1479025bae</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucProtocolAddressLength</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a654eb61393780f5a5d5cfb93a31579f1</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usOperation</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a76d52ece3a066bebc7f18ac933f9a956</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>MACAddress_t</type>
      <name>xSenderHardwareAddress</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>af5cfb48d31b8d85652a9da0821582606</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucSenderProtocolAddress</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a9318bcd50bdd8448215145252f182139</anchor>
      <arglist>[4]</arglist>
    </member>
    <member kind="variable">
      <type>MACAddress_t</type>
      <name>xTargetHardwareAddress</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a37eed545b17af44cc19f5ef63335aa4d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulTargetProtocolAddress</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a3fcf3a4c59e190915b0d09718269c5c6</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucVersionHeaderLength</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a54ef7e602f84f2b3476cd10efef96720</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucDifferentiatedServicesCode</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a0ddd590409edd968cefb18ededaefc4e</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usLength</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a5e26363013a5761eb3d0796d35b7f71d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usIdentification</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>ad4acebb8f4e30bae0506558e18be1538</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usFragmentOffset</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>aa3955126880a21beccb06bfa72f05b60</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucTimeToLive</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a5bfe2de234be9e3342e60e8fa9c09e11</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucProtocol</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>acd2508a55e01fa8fa55a65b9febc7e2a</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usHeaderChecksum</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a78614faa161325bbc6e5f1edd43d1f32</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulSourceIPAddress</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a70f5e64b15e32ce8d87ec4c2afe7fafc</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulDestinationIPAddress</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a12f4a589751b2c6ac6181f585cceb3d1</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucTypeOfMessage</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>adf99ac0dc4ef8a20834574a8d06dbe48</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucTypeOfService</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a8dc4f9048189a6571fbb64cae047e3fc</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usChecksum</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>af1e30c3a15d68c6692928407fc26d225</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usIdentifier</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>af96f1fbbc84c6ac1c3719857392f8597</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usSequenceNumber</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a4188a123470f3f59e17107bfb3a533e2</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usSourcePort</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>ade05608e9ba9d8391b1ed07dbdd260fb</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usDestinationPort</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a8eec861cc2d2845acdb21d45f244169b</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulSequenceNumber</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>aa407a89e2e8b38f3ce62e8da06b4dfbd</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulAckNr</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a3c191068c88c577058c4ef882321a1b7</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucTCPOffset</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a083a955bb7ee558067570a394179e5f7</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucTCPFlags</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a915becd2b5be617372864ba45febfaec</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usWindow</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a8b27bc8a1b97fddab32d51ad373c018d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usUrgent</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a2d74d4b3d045fe40aa1a26f345e2473c</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucOptdata</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>af10dade2e3ca23ad86b3f24fec92e00c</anchor>
      <arglist>[ipSIZE_TCP_OPTIONS]</arglist>
    </member>
    <member kind="variable">
      <type>EthernetHeader_t</type>
      <name>xEthernetHeader</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>ade289b8c53e649fa2559f1cee4766a40</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>ARPHeader_t</type>
      <name>xARPHeader</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a27b6bfc4e4db6aa1ff10e08bdd13dcda</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>IPHeader_t</type>
      <name>xIPHeader</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>ad73143081d8c065e2fed17fbff3d7fbf</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>ICMPHeader_t</type>
      <name>xICMPHeader</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>aff9b7d7a7806207eb441d9d0ed36a808</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>UDPHeader_t</type>
      <name>xUDPHeader</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a2943ee8413c4b5e44adad8a970db6977</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TCPHeader_t</type>
      <name>xTCPHeader</name>
      <anchorfile>structstruct.html</anchorfile>
      <anchor>a3c5bfce97918a23030d84a5ea120a988</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>TCPSegment_t</name>
    <filename>struct_t_c_p_segment__t.html</filename>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulSequenceNumber</name>
      <anchorfile>struct_t_c_p_segment__t.html</anchorfile>
      <anchor>a8b4011e5bbe6f229a6f47c072a3d8297</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>lMaxLength</name>
      <anchorfile>struct_t_c_p_segment__t.html</anchorfile>
      <anchor>acfdf465e8083ecc8f0370b7bc9328b11</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>lDataLength</name>
      <anchorfile>struct_t_c_p_segment__t.html</anchorfile>
      <anchor>af4be27b695914f3035e0320c19346d05</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>lStreamPos</name>
      <anchorfile>struct_t_c_p_segment__t.html</anchorfile>
      <anchor>ad3c4fa986c17a6076142594ab3c4f67f</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TCPTimer_t</type>
      <name>xTransmitTimer</name>
      <anchorfile>struct_t_c_p_segment__t.html</anchorfile>
      <anchor>a57ed94ff6a304cd5e90ae0a96c253f56</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ucTransmitCount</name>
      <anchorfile>struct_t_c_p_segment__t.html</anchorfile>
      <anchor>a15cd5a913a70812749c6ca24f9e34cd8</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ucDupAckCount</name>
      <anchorfile>struct_t_c_p_segment__t.html</anchorfile>
      <anchor>aad2e3391e82c9783740bd991cf1359d1</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bOutstanding</name>
      <anchorfile>struct_t_c_p_segment__t.html</anchorfile>
      <anchor>a56f492387b0815a3cb07720268e5e043</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bAcked</name>
      <anchorfile>struct_t_c_p_segment__t.html</anchorfile>
      <anchor>a37fbd53c8c14464983fdb9e4bc32ba98</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bIsForRx</name>
      <anchorfile>struct_t_c_p_segment__t.html</anchorfile>
      <anchor>ab8ea887b001f6304c98e402b32574b13</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>union TCPSegment_t::@0</type>
      <name>u</name>
      <anchorfile>struct_t_c_p_segment__t.html</anchorfile>
      <anchor>aef340f8dbb522ad2c08a73f25ab02ab0</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>TCPTimer_t</name>
    <filename>struct_t_c_p_timer__t.html</filename>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulBorn</name>
      <anchorfile>struct_t_c_p_timer__t.html</anchorfile>
      <anchor>a9fe34b13c92967053a2f5d89a3d71ac5</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>TCPWindow_t</name>
    <filename>struct_t_c_p_window__t.html</filename>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bHasInit</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>acd7249d799b345cd92c97e3bfb12933b</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bSendFullSize</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a97000733d08ecc2dce73e544ad7b9213</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>bTimeStamps</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>aee1b76d9af1c92e55dc5137e547bc2fb</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>struct TCPWindow_t::@2::@4</type>
      <name>bits</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>ab59743e01decca912282d7aa1bc6bc02</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>union TCPWindow_t::@2</type>
      <name>u</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>aedd191b7a89cbe074db56c5eaf24b8e3</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TCPWinSize_t</type>
      <name>xSize</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a0e1bb052b5e4f97b77761c917ced73aa</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulFirstSequenceNumber</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a1e468229cce59ab0dc1599f648b2c667</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulCurrentSequenceNumber</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a4d9da94474f534f21e773aaf056ae9b4</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulFINSequenceNumber</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a8be59622f0a92e22d48b9cb3886109a6</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulHighestSequenceNumber</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a8e161ce8c71ddf5509b057d81451a03e</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>struct TCPWindow_t::@3</type>
      <name>rx</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a945d3c0c8c41e9ac4f6b985ac4109717</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>struct TCPWindow_t::@3</type>
      <name>tx</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a64453840d05a73a465d7a166652a5676</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulOurSequenceNumber</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a5bfdac42880e5ae6ef7ac77c1374f4e8</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulUserDataLength</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>ae6f1dd8e9d4a66a7797bcec120f059d3</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulNextTxSequenceNumber</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a070811b69e87c61e47c59ff50e29dadc</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>lSRTT</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>acdf5efc1b38f7bc4fdd3cfbe874af180</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucOptionLength</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a6bde9c3ebe7f805aa99cccc49e0527b5</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>TCPSegment_t</type>
      <name>xTxSegment</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a6be255a8d90e388ea48cc395c76592c7</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usOurPortNumber</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>af9d582e60dff97a5248009d5a5fa2a23</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usPeerPortNumber</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>a1472b1532d03ab2057f67081e116457a</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usMSS</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>abd2c39637cacf9b3b4bb934d1c43be64</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>usMSSInit</name>
      <anchorfile>struct_t_c_p_window__t.html</anchorfile>
      <anchor>ab46f5a3d7e7e9452372e8cd5ff625c78</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>TCPWinSize_t</name>
    <filename>struct_t_c_p_win_size__t.html</filename>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulRxWindowLength</name>
      <anchorfile>struct_t_c_p_win_size__t.html</anchorfile>
      <anchor>a31a006b4cdadeb02ba0631ffdad7e9f7</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulTxWindowLength</name>
      <anchorfile>struct_t_c_p_win_size__t.html</anchorfile>
      <anchor>a6bfa12d5c5a63af08bcaca8b81bdc4e2</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="union">
    <name>UDPPacketHeader_t</name>
    <filename>union_u_d_p_packet_header__t.html</filename>
    <member kind="variable">
      <type>uint8_t</type>
      <name>ucBytes</name>
      <anchorfile>union_u_d_p_packet_header__t.html</anchorfile>
      <anchor>a3be686b900eda092711056d7b6de68ef</anchor>
      <arglist>[24]</arglist>
    </member>
    <member kind="variable">
      <type>uint32_t</type>
      <name>ulWords</name>
      <anchorfile>union_u_d_p_packet_header__t.html</anchorfile>
      <anchor>ac218ebdd30f53cc5dea89918865e8077</anchor>
      <arglist>[6]</arglist>
    </member>
  </compound>
  <compound kind="struct">
    <name>WinProperties_t</name>
    <filename>struct_win_properties__t.html</filename>
    <member kind="variable">
      <type>int32_t</type>
      <name>lTxBufSize</name>
      <anchorfile>struct_win_properties__t.html</anchorfile>
      <anchor>a999e0b398e52ffa79d5c8bfcff7a9323</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>lTxWinSize</name>
      <anchorfile>struct_win_properties__t.html</anchorfile>
      <anchor>a50c170f82dc44a406463dfeb72277b67</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>lRxBufSize</name>
      <anchorfile>struct_win_properties__t.html</anchorfile>
      <anchor>aafb5181e10dcf313d3d5d5d94a1f530d</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>int32_t</type>
      <name>lRxWinSize</name>
      <anchorfile>struct_win_properties__t.html</anchorfile>
      <anchor>a7a5729f01fbbf3e06ab911572cd2cecd</anchor>
      <arglist></arglist>
    </member>
  </compound>
  <compound kind="union">
    <name>xUnion32</name>
    <filename>unionx_union32.html</filename>
    <member kind="variable">
      <type>uint32_t</type>
      <name>u32</name>
      <anchorfile>unionx_union32.html</anchorfile>
      <anchor>a0b4c94abdafb022ad16715a8bde5ee58</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t</type>
      <name>u16</name>
      <anchorfile>unionx_union32.html</anchorfile>
      <anchor>a362fc666e3b98db61fb823c8a079d991</anchor>
      <arglist>[2]</arglist>
    </member>
    <member kind="variable">
      <type>uint8_t</type>
      <name>u8</name>
      <anchorfile>unionx_union32.html</anchorfile>
      <anchor>a57bc88ea027b2f345d590d1ef1e10883</anchor>
      <arglist>[4]</arglist>
    </member>
  </compound>
  <compound kind="union">
    <name>xUnionPtr</name>
    <filename>unionx_union_ptr.html</filename>
    <member kind="variable">
      <type>uint32_t *</type>
      <name>u32ptr</name>
      <anchorfile>unionx_union_ptr.html</anchorfile>
      <anchor>a50b27c7a9a159a9f99504c9da1ad462b</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint16_t *</type>
      <name>u16ptr</name>
      <anchorfile>unionx_union_ptr.html</anchorfile>
      <anchor>a64cd6ee0fbab334c3ba5f2b8c9818a0a</anchor>
      <arglist></arglist>
    </member>
    <member kind="variable">
      <type>uint8_t *</type>
      <name>u8ptr</name>
      <anchorfile>unionx_union_ptr.html</anchorfile>
      <anchor>a07a49178e15b944dc96ed0b4e6d29e81</anchor>
      <arglist></arglist>
    </member>
  </compound>
</tagfile>
