/* AUTOGENERATED FILE. DO NOT EDIT. */
#ifndef _MOCK_FREERTOS_STREAM_BUFFER_H
#define _MOCK_FREERTOS_STREAM_BUFFER_H

#include "unity.h"
#include <stdbool.h>
#include <stdint.h>
#include <fcntl.h>
#include <unity.h>
#include "FreeRTOS.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Stream_Buffer.h"

/* Ignore the following warnings, since we are copying code */
#if defined(__GNUC__) && !defined(__ICC) && !defined(__TMS470__)
#if __GNUC__ > 4 || (__GNUC__ == 4 && (__GNUC_MINOR__ > 6 || (__GNUC_MINOR__ == 6 && __GNUC_PATCHLEVEL__ > 0)))
#pragma GCC diagnostic push
#endif
#if !defined(__clang__)
#pragma GCC diagnostic ignored "-Wpragmas"
#endif
#pragma GCC diagnostic ignored "-Wunknown-pragmas"
#pragma GCC diagnostic ignored "-Wduplicate-decl-specifier"
#endif

void mock_FreeRTOS_Stream_Buffer_Init(void);
void mock_FreeRTOS_Stream_Buffer_Destroy(void);
void mock_FreeRTOS_Stream_Buffer_Verify(void);




#define vStreamBufferClear_Ignore() vStreamBufferClear_CMockIgnore()
void vStreamBufferClear_CMockIgnore(void);
#define vStreamBufferClear_StopIgnore() vStreamBufferClear_CMockStopIgnore()
void vStreamBufferClear_CMockStopIgnore(void);
#define vStreamBufferClear_ExpectAnyArgs() vStreamBufferClear_CMockExpectAnyArgs(__LINE__)
void vStreamBufferClear_CMockExpectAnyArgs(UNITY_LINE_TYPE cmock_line);
#define vStreamBufferClear_Expect(pxBuffer) vStreamBufferClear_CMockExpect(__LINE__, pxBuffer)
void vStreamBufferClear_CMockExpect(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer);
typedef void (* CMOCK_vStreamBufferClear_CALLBACK)(StreamBuffer_t* pxBuffer, int cmock_num_calls);
void vStreamBufferClear_AddCallback(CMOCK_vStreamBufferClear_CALLBACK Callback);
void vStreamBufferClear_Stub(CMOCK_vStreamBufferClear_CALLBACK Callback);
#define vStreamBufferClear_StubWithCallback vStreamBufferClear_Stub
#define vStreamBufferClear_ExpectWithArray(pxBuffer, pxBuffer_Depth) vStreamBufferClear_CMockExpectWithArray(__LINE__, pxBuffer, pxBuffer_Depth)
void vStreamBufferClear_CMockExpectWithArray(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, int pxBuffer_Depth);
#define vStreamBufferClear_ReturnThruPtr_pxBuffer(pxBuffer) vStreamBufferClear_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, sizeof(StreamBuffer_t))
#define vStreamBufferClear_ReturnArrayThruPtr_pxBuffer(pxBuffer, cmock_len) vStreamBufferClear_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, (int)(cmock_len * (int)sizeof(*pxBuffer)))
#define vStreamBufferClear_ReturnMemThruPtr_pxBuffer(pxBuffer, cmock_size) vStreamBufferClear_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, cmock_size)
void vStreamBufferClear_CMockReturnMemThruPtr_pxBuffer(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, int cmock_size);
#define vStreamBufferClear_IgnoreArg_pxBuffer() vStreamBufferClear_CMockIgnoreArg_pxBuffer(__LINE__)
void vStreamBufferClear_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferSpace_IgnoreAndReturn(cmock_retval) uxStreamBufferSpace_CMockIgnoreAndReturn(__LINE__, cmock_retval)
void uxStreamBufferSpace_CMockIgnoreAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferSpace_StopIgnore() uxStreamBufferSpace_CMockStopIgnore()
void uxStreamBufferSpace_CMockStopIgnore(void);
#define uxStreamBufferSpace_ExpectAnyArgsAndReturn(cmock_retval) uxStreamBufferSpace_CMockExpectAnyArgsAndReturn(__LINE__, cmock_retval)
void uxStreamBufferSpace_CMockExpectAnyArgsAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferSpace_ExpectAndReturn(pxBuffer, uxLower, uxUpper, cmock_retval) uxStreamBufferSpace_CMockExpectAndReturn(__LINE__, pxBuffer, uxLower, uxUpper, cmock_retval)
void uxStreamBufferSpace_CMockExpectAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, const size_t uxLower, const size_t uxUpper, size_t cmock_to_return);
typedef size_t (* CMOCK_uxStreamBufferSpace_CALLBACK)(const StreamBuffer_t* pxBuffer, const size_t uxLower, const size_t uxUpper, int cmock_num_calls);
void uxStreamBufferSpace_AddCallback(CMOCK_uxStreamBufferSpace_CALLBACK Callback);
void uxStreamBufferSpace_Stub(CMOCK_uxStreamBufferSpace_CALLBACK Callback);
#define uxStreamBufferSpace_StubWithCallback uxStreamBufferSpace_Stub
#define uxStreamBufferSpace_ExpectWithArrayAndReturn(pxBuffer, pxBuffer_Depth, uxLower, uxUpper, cmock_retval) uxStreamBufferSpace_CMockExpectWithArrayAndReturn(__LINE__, pxBuffer, pxBuffer_Depth, uxLower, uxUpper, cmock_retval)
void uxStreamBufferSpace_CMockExpectWithArrayAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, int pxBuffer_Depth, const size_t uxLower, const size_t uxUpper, size_t cmock_to_return);
#define uxStreamBufferSpace_IgnoreArg_pxBuffer() uxStreamBufferSpace_CMockIgnoreArg_pxBuffer(__LINE__)
void uxStreamBufferSpace_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferSpace_IgnoreArg_uxLower() uxStreamBufferSpace_CMockIgnoreArg_uxLower(__LINE__)
void uxStreamBufferSpace_CMockIgnoreArg_uxLower(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferSpace_IgnoreArg_uxUpper() uxStreamBufferSpace_CMockIgnoreArg_uxUpper(__LINE__)
void uxStreamBufferSpace_CMockIgnoreArg_uxUpper(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferDistance_IgnoreAndReturn(cmock_retval) uxStreamBufferDistance_CMockIgnoreAndReturn(__LINE__, cmock_retval)
void uxStreamBufferDistance_CMockIgnoreAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferDistance_StopIgnore() uxStreamBufferDistance_CMockStopIgnore()
void uxStreamBufferDistance_CMockStopIgnore(void);
#define uxStreamBufferDistance_ExpectAnyArgsAndReturn(cmock_retval) uxStreamBufferDistance_CMockExpectAnyArgsAndReturn(__LINE__, cmock_retval)
void uxStreamBufferDistance_CMockExpectAnyArgsAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferDistance_ExpectAndReturn(pxBuffer, uxLower, uxUpper, cmock_retval) uxStreamBufferDistance_CMockExpectAndReturn(__LINE__, pxBuffer, uxLower, uxUpper, cmock_retval)
void uxStreamBufferDistance_CMockExpectAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, const size_t uxLower, const size_t uxUpper, size_t cmock_to_return);
typedef size_t (* CMOCK_uxStreamBufferDistance_CALLBACK)(const StreamBuffer_t* pxBuffer, const size_t uxLower, const size_t uxUpper, int cmock_num_calls);
void uxStreamBufferDistance_AddCallback(CMOCK_uxStreamBufferDistance_CALLBACK Callback);
void uxStreamBufferDistance_Stub(CMOCK_uxStreamBufferDistance_CALLBACK Callback);
#define uxStreamBufferDistance_StubWithCallback uxStreamBufferDistance_Stub
#define uxStreamBufferDistance_ExpectWithArrayAndReturn(pxBuffer, pxBuffer_Depth, uxLower, uxUpper, cmock_retval) uxStreamBufferDistance_CMockExpectWithArrayAndReturn(__LINE__, pxBuffer, pxBuffer_Depth, uxLower, uxUpper, cmock_retval)
void uxStreamBufferDistance_CMockExpectWithArrayAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, int pxBuffer_Depth, const size_t uxLower, const size_t uxUpper, size_t cmock_to_return);
#define uxStreamBufferDistance_IgnoreArg_pxBuffer() uxStreamBufferDistance_CMockIgnoreArg_pxBuffer(__LINE__)
void uxStreamBufferDistance_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferDistance_IgnoreArg_uxLower() uxStreamBufferDistance_CMockIgnoreArg_uxLower(__LINE__)
void uxStreamBufferDistance_CMockIgnoreArg_uxLower(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferDistance_IgnoreArg_uxUpper() uxStreamBufferDistance_CMockIgnoreArg_uxUpper(__LINE__)
void uxStreamBufferDistance_CMockIgnoreArg_uxUpper(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferGetSpace_IgnoreAndReturn(cmock_retval) uxStreamBufferGetSpace_CMockIgnoreAndReturn(__LINE__, cmock_retval)
void uxStreamBufferGetSpace_CMockIgnoreAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferGetSpace_StopIgnore() uxStreamBufferGetSpace_CMockStopIgnore()
void uxStreamBufferGetSpace_CMockStopIgnore(void);
#define uxStreamBufferGetSpace_ExpectAnyArgsAndReturn(cmock_retval) uxStreamBufferGetSpace_CMockExpectAnyArgsAndReturn(__LINE__, cmock_retval)
void uxStreamBufferGetSpace_CMockExpectAnyArgsAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferGetSpace_ExpectAndReturn(pxBuffer, cmock_retval) uxStreamBufferGetSpace_CMockExpectAndReturn(__LINE__, pxBuffer, cmock_retval)
void uxStreamBufferGetSpace_CMockExpectAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, size_t cmock_to_return);
typedef size_t (* CMOCK_uxStreamBufferGetSpace_CALLBACK)(const StreamBuffer_t* pxBuffer, int cmock_num_calls);
void uxStreamBufferGetSpace_AddCallback(CMOCK_uxStreamBufferGetSpace_CALLBACK Callback);
void uxStreamBufferGetSpace_Stub(CMOCK_uxStreamBufferGetSpace_CALLBACK Callback);
#define uxStreamBufferGetSpace_StubWithCallback uxStreamBufferGetSpace_Stub
#define uxStreamBufferGetSpace_ExpectWithArrayAndReturn(pxBuffer, pxBuffer_Depth, cmock_retval) uxStreamBufferGetSpace_CMockExpectWithArrayAndReturn(__LINE__, pxBuffer, pxBuffer_Depth, cmock_retval)
void uxStreamBufferGetSpace_CMockExpectWithArrayAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, int pxBuffer_Depth, size_t cmock_to_return);
#define uxStreamBufferGetSpace_IgnoreArg_pxBuffer() uxStreamBufferGetSpace_CMockIgnoreArg_pxBuffer(__LINE__)
void uxStreamBufferGetSpace_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferFrontSpace_IgnoreAndReturn(cmock_retval) uxStreamBufferFrontSpace_CMockIgnoreAndReturn(__LINE__, cmock_retval)
void uxStreamBufferFrontSpace_CMockIgnoreAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferFrontSpace_StopIgnore() uxStreamBufferFrontSpace_CMockStopIgnore()
void uxStreamBufferFrontSpace_CMockStopIgnore(void);
#define uxStreamBufferFrontSpace_ExpectAnyArgsAndReturn(cmock_retval) uxStreamBufferFrontSpace_CMockExpectAnyArgsAndReturn(__LINE__, cmock_retval)
void uxStreamBufferFrontSpace_CMockExpectAnyArgsAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferFrontSpace_ExpectAndReturn(pxBuffer, cmock_retval) uxStreamBufferFrontSpace_CMockExpectAndReturn(__LINE__, pxBuffer, cmock_retval)
void uxStreamBufferFrontSpace_CMockExpectAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, size_t cmock_to_return);
typedef size_t (* CMOCK_uxStreamBufferFrontSpace_CALLBACK)(const StreamBuffer_t* pxBuffer, int cmock_num_calls);
void uxStreamBufferFrontSpace_AddCallback(CMOCK_uxStreamBufferFrontSpace_CALLBACK Callback);
void uxStreamBufferFrontSpace_Stub(CMOCK_uxStreamBufferFrontSpace_CALLBACK Callback);
#define uxStreamBufferFrontSpace_StubWithCallback uxStreamBufferFrontSpace_Stub
#define uxStreamBufferFrontSpace_ExpectWithArrayAndReturn(pxBuffer, pxBuffer_Depth, cmock_retval) uxStreamBufferFrontSpace_CMockExpectWithArrayAndReturn(__LINE__, pxBuffer, pxBuffer_Depth, cmock_retval)
void uxStreamBufferFrontSpace_CMockExpectWithArrayAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, int pxBuffer_Depth, size_t cmock_to_return);
#define uxStreamBufferFrontSpace_IgnoreArg_pxBuffer() uxStreamBufferFrontSpace_CMockIgnoreArg_pxBuffer(__LINE__)
void uxStreamBufferFrontSpace_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferGetSize_IgnoreAndReturn(cmock_retval) uxStreamBufferGetSize_CMockIgnoreAndReturn(__LINE__, cmock_retval)
void uxStreamBufferGetSize_CMockIgnoreAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferGetSize_StopIgnore() uxStreamBufferGetSize_CMockStopIgnore()
void uxStreamBufferGetSize_CMockStopIgnore(void);
#define uxStreamBufferGetSize_ExpectAnyArgsAndReturn(cmock_retval) uxStreamBufferGetSize_CMockExpectAnyArgsAndReturn(__LINE__, cmock_retval)
void uxStreamBufferGetSize_CMockExpectAnyArgsAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferGetSize_ExpectAndReturn(pxBuffer, cmock_retval) uxStreamBufferGetSize_CMockExpectAndReturn(__LINE__, pxBuffer, cmock_retval)
void uxStreamBufferGetSize_CMockExpectAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, size_t cmock_to_return);
typedef size_t (* CMOCK_uxStreamBufferGetSize_CALLBACK)(const StreamBuffer_t* pxBuffer, int cmock_num_calls);
void uxStreamBufferGetSize_AddCallback(CMOCK_uxStreamBufferGetSize_CALLBACK Callback);
void uxStreamBufferGetSize_Stub(CMOCK_uxStreamBufferGetSize_CALLBACK Callback);
#define uxStreamBufferGetSize_StubWithCallback uxStreamBufferGetSize_Stub
#define uxStreamBufferGetSize_ExpectWithArrayAndReturn(pxBuffer, pxBuffer_Depth, cmock_retval) uxStreamBufferGetSize_CMockExpectWithArrayAndReturn(__LINE__, pxBuffer, pxBuffer_Depth, cmock_retval)
void uxStreamBufferGetSize_CMockExpectWithArrayAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, int pxBuffer_Depth, size_t cmock_to_return);
#define uxStreamBufferGetSize_IgnoreArg_pxBuffer() uxStreamBufferGetSize_CMockIgnoreArg_pxBuffer(__LINE__)
void uxStreamBufferGetSize_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferMidSpace_IgnoreAndReturn(cmock_retval) uxStreamBufferMidSpace_CMockIgnoreAndReturn(__LINE__, cmock_retval)
void uxStreamBufferMidSpace_CMockIgnoreAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferMidSpace_StopIgnore() uxStreamBufferMidSpace_CMockStopIgnore()
void uxStreamBufferMidSpace_CMockStopIgnore(void);
#define uxStreamBufferMidSpace_ExpectAnyArgsAndReturn(cmock_retval) uxStreamBufferMidSpace_CMockExpectAnyArgsAndReturn(__LINE__, cmock_retval)
void uxStreamBufferMidSpace_CMockExpectAnyArgsAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferMidSpace_ExpectAndReturn(pxBuffer, cmock_retval) uxStreamBufferMidSpace_CMockExpectAndReturn(__LINE__, pxBuffer, cmock_retval)
void uxStreamBufferMidSpace_CMockExpectAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, size_t cmock_to_return);
typedef size_t (* CMOCK_uxStreamBufferMidSpace_CALLBACK)(const StreamBuffer_t* pxBuffer, int cmock_num_calls);
void uxStreamBufferMidSpace_AddCallback(CMOCK_uxStreamBufferMidSpace_CALLBACK Callback);
void uxStreamBufferMidSpace_Stub(CMOCK_uxStreamBufferMidSpace_CALLBACK Callback);
#define uxStreamBufferMidSpace_StubWithCallback uxStreamBufferMidSpace_Stub
#define uxStreamBufferMidSpace_ExpectWithArrayAndReturn(pxBuffer, pxBuffer_Depth, cmock_retval) uxStreamBufferMidSpace_CMockExpectWithArrayAndReturn(__LINE__, pxBuffer, pxBuffer_Depth, cmock_retval)
void uxStreamBufferMidSpace_CMockExpectWithArrayAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, int pxBuffer_Depth, size_t cmock_to_return);
#define uxStreamBufferMidSpace_IgnoreArg_pxBuffer() uxStreamBufferMidSpace_CMockIgnoreArg_pxBuffer(__LINE__)
void uxStreamBufferMidSpace_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define vStreamBufferMoveMid_Ignore() vStreamBufferMoveMid_CMockIgnore()
void vStreamBufferMoveMid_CMockIgnore(void);
#define vStreamBufferMoveMid_StopIgnore() vStreamBufferMoveMid_CMockStopIgnore()
void vStreamBufferMoveMid_CMockStopIgnore(void);
#define vStreamBufferMoveMid_ExpectAnyArgs() vStreamBufferMoveMid_CMockExpectAnyArgs(__LINE__)
void vStreamBufferMoveMid_CMockExpectAnyArgs(UNITY_LINE_TYPE cmock_line);
#define vStreamBufferMoveMid_Expect(pxBuffer, uxCount) vStreamBufferMoveMid_CMockExpect(__LINE__, pxBuffer, uxCount)
void vStreamBufferMoveMid_CMockExpect(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, size_t uxCount);
typedef void (* CMOCK_vStreamBufferMoveMid_CALLBACK)(StreamBuffer_t* pxBuffer, size_t uxCount, int cmock_num_calls);
void vStreamBufferMoveMid_AddCallback(CMOCK_vStreamBufferMoveMid_CALLBACK Callback);
void vStreamBufferMoveMid_Stub(CMOCK_vStreamBufferMoveMid_CALLBACK Callback);
#define vStreamBufferMoveMid_StubWithCallback vStreamBufferMoveMid_Stub
#define vStreamBufferMoveMid_ExpectWithArray(pxBuffer, pxBuffer_Depth, uxCount) vStreamBufferMoveMid_CMockExpectWithArray(__LINE__, pxBuffer, pxBuffer_Depth, uxCount)
void vStreamBufferMoveMid_CMockExpectWithArray(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, int pxBuffer_Depth, size_t uxCount);
#define vStreamBufferMoveMid_ReturnThruPtr_pxBuffer(pxBuffer) vStreamBufferMoveMid_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, sizeof(StreamBuffer_t))
#define vStreamBufferMoveMid_ReturnArrayThruPtr_pxBuffer(pxBuffer, cmock_len) vStreamBufferMoveMid_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, (int)(cmock_len * (int)sizeof(*pxBuffer)))
#define vStreamBufferMoveMid_ReturnMemThruPtr_pxBuffer(pxBuffer, cmock_size) vStreamBufferMoveMid_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, cmock_size)
void vStreamBufferMoveMid_CMockReturnMemThruPtr_pxBuffer(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, int cmock_size);
#define vStreamBufferMoveMid_IgnoreArg_pxBuffer() vStreamBufferMoveMid_CMockIgnoreArg_pxBuffer(__LINE__)
void vStreamBufferMoveMid_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define vStreamBufferMoveMid_IgnoreArg_uxCount() vStreamBufferMoveMid_CMockIgnoreArg_uxCount(__LINE__)
void vStreamBufferMoveMid_CMockIgnoreArg_uxCount(UNITY_LINE_TYPE cmock_line);
#define xStreamBufferLessThenEqual_IgnoreAndReturn(cmock_retval) xStreamBufferLessThenEqual_CMockIgnoreAndReturn(__LINE__, cmock_retval)
void xStreamBufferLessThenEqual_CMockIgnoreAndReturn(UNITY_LINE_TYPE cmock_line, BaseType_t cmock_to_return);
#define xStreamBufferLessThenEqual_StopIgnore() xStreamBufferLessThenEqual_CMockStopIgnore()
void xStreamBufferLessThenEqual_CMockStopIgnore(void);
#define xStreamBufferLessThenEqual_ExpectAnyArgsAndReturn(cmock_retval) xStreamBufferLessThenEqual_CMockExpectAnyArgsAndReturn(__LINE__, cmock_retval)
void xStreamBufferLessThenEqual_CMockExpectAnyArgsAndReturn(UNITY_LINE_TYPE cmock_line, BaseType_t cmock_to_return);
#define xStreamBufferLessThenEqual_ExpectAndReturn(pxBuffer, uxLeft, uxRight, cmock_retval) xStreamBufferLessThenEqual_CMockExpectAndReturn(__LINE__, pxBuffer, uxLeft, uxRight, cmock_retval)
void xStreamBufferLessThenEqual_CMockExpectAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, const size_t uxLeft, const size_t uxRight, BaseType_t cmock_to_return);
typedef BaseType_t (* CMOCK_xStreamBufferLessThenEqual_CALLBACK)(const StreamBuffer_t* pxBuffer, const size_t uxLeft, const size_t uxRight, int cmock_num_calls);
void xStreamBufferLessThenEqual_AddCallback(CMOCK_xStreamBufferLessThenEqual_CALLBACK Callback);
void xStreamBufferLessThenEqual_Stub(CMOCK_xStreamBufferLessThenEqual_CALLBACK Callback);
#define xStreamBufferLessThenEqual_StubWithCallback xStreamBufferLessThenEqual_Stub
#define xStreamBufferLessThenEqual_ExpectWithArrayAndReturn(pxBuffer, pxBuffer_Depth, uxLeft, uxRight, cmock_retval) xStreamBufferLessThenEqual_CMockExpectWithArrayAndReturn(__LINE__, pxBuffer, pxBuffer_Depth, uxLeft, uxRight, cmock_retval)
void xStreamBufferLessThenEqual_CMockExpectWithArrayAndReturn(UNITY_LINE_TYPE cmock_line, const StreamBuffer_t* pxBuffer, int pxBuffer_Depth, const size_t uxLeft, const size_t uxRight, BaseType_t cmock_to_return);
#define xStreamBufferLessThenEqual_IgnoreArg_pxBuffer() xStreamBufferLessThenEqual_CMockIgnoreArg_pxBuffer(__LINE__)
void xStreamBufferLessThenEqual_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define xStreamBufferLessThenEqual_IgnoreArg_uxLeft() xStreamBufferLessThenEqual_CMockIgnoreArg_uxLeft(__LINE__)
void xStreamBufferLessThenEqual_CMockIgnoreArg_uxLeft(UNITY_LINE_TYPE cmock_line);
#define xStreamBufferLessThenEqual_IgnoreArg_uxRight() xStreamBufferLessThenEqual_CMockIgnoreArg_uxRight(__LINE__)
void xStreamBufferLessThenEqual_CMockIgnoreArg_uxRight(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferGetPtr_IgnoreAndReturn(cmock_retval) uxStreamBufferGetPtr_CMockIgnoreAndReturn(__LINE__, cmock_retval)
void uxStreamBufferGetPtr_CMockIgnoreAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferGetPtr_StopIgnore() uxStreamBufferGetPtr_CMockStopIgnore()
void uxStreamBufferGetPtr_CMockStopIgnore(void);
#define uxStreamBufferGetPtr_ExpectAnyArgsAndReturn(cmock_retval) uxStreamBufferGetPtr_CMockExpectAnyArgsAndReturn(__LINE__, cmock_retval)
void uxStreamBufferGetPtr_CMockExpectAnyArgsAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferGetPtr_ExpectAndReturn(pxBuffer, ppucData, cmock_retval) uxStreamBufferGetPtr_CMockExpectAndReturn(__LINE__, pxBuffer, ppucData, cmock_retval)
void uxStreamBufferGetPtr_CMockExpectAndReturn(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, uint8_t** ppucData, size_t cmock_to_return);
typedef size_t (* CMOCK_uxStreamBufferGetPtr_CALLBACK)(StreamBuffer_t* pxBuffer, uint8_t** ppucData, int cmock_num_calls);
void uxStreamBufferGetPtr_AddCallback(CMOCK_uxStreamBufferGetPtr_CALLBACK Callback);
void uxStreamBufferGetPtr_Stub(CMOCK_uxStreamBufferGetPtr_CALLBACK Callback);
#define uxStreamBufferGetPtr_StubWithCallback uxStreamBufferGetPtr_Stub
#define uxStreamBufferGetPtr_ExpectWithArrayAndReturn(pxBuffer, pxBuffer_Depth, ppucData, ppucData_Depth, cmock_retval) uxStreamBufferGetPtr_CMockExpectWithArrayAndReturn(__LINE__, pxBuffer, pxBuffer_Depth, ppucData, ppucData_Depth, cmock_retval)
void uxStreamBufferGetPtr_CMockExpectWithArrayAndReturn(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, int pxBuffer_Depth, uint8_t** ppucData, int ppucData_Depth, size_t cmock_to_return);
#define uxStreamBufferGetPtr_ReturnThruPtr_pxBuffer(pxBuffer) uxStreamBufferGetPtr_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, sizeof(StreamBuffer_t))
#define uxStreamBufferGetPtr_ReturnArrayThruPtr_pxBuffer(pxBuffer, cmock_len) uxStreamBufferGetPtr_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, (int)(cmock_len * (int)sizeof(*pxBuffer)))
#define uxStreamBufferGetPtr_ReturnMemThruPtr_pxBuffer(pxBuffer, cmock_size) uxStreamBufferGetPtr_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, cmock_size)
void uxStreamBufferGetPtr_CMockReturnMemThruPtr_pxBuffer(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, int cmock_size);
#define uxStreamBufferGetPtr_ReturnThruPtr_ppucData(ppucData) uxStreamBufferGetPtr_CMockReturnMemThruPtr_ppucData(__LINE__, ppucData, sizeof(uint8_t*))
#define uxStreamBufferGetPtr_ReturnArrayThruPtr_ppucData(ppucData, cmock_len) uxStreamBufferGetPtr_CMockReturnMemThruPtr_ppucData(__LINE__, ppucData, (int)(cmock_len * (int)sizeof(*ppucData)))
#define uxStreamBufferGetPtr_ReturnMemThruPtr_ppucData(ppucData, cmock_size) uxStreamBufferGetPtr_CMockReturnMemThruPtr_ppucData(__LINE__, ppucData, cmock_size)
void uxStreamBufferGetPtr_CMockReturnMemThruPtr_ppucData(UNITY_LINE_TYPE cmock_line, uint8_t** ppucData, int cmock_size);
#define uxStreamBufferGetPtr_IgnoreArg_pxBuffer() uxStreamBufferGetPtr_CMockIgnoreArg_pxBuffer(__LINE__)
void uxStreamBufferGetPtr_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferGetPtr_IgnoreArg_ppucData() uxStreamBufferGetPtr_CMockIgnoreArg_ppucData(__LINE__)
void uxStreamBufferGetPtr_CMockIgnoreArg_ppucData(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferAdd_IgnoreAndReturn(cmock_retval) uxStreamBufferAdd_CMockIgnoreAndReturn(__LINE__, cmock_retval)
void uxStreamBufferAdd_CMockIgnoreAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferAdd_StopIgnore() uxStreamBufferAdd_CMockStopIgnore()
void uxStreamBufferAdd_CMockStopIgnore(void);
#define uxStreamBufferAdd_ExpectAnyArgsAndReturn(cmock_retval) uxStreamBufferAdd_CMockExpectAnyArgsAndReturn(__LINE__, cmock_retval)
void uxStreamBufferAdd_CMockExpectAnyArgsAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferAdd_ExpectAndReturn(pxBuffer, uxOffset, pucData, uxByteCount, cmock_retval) uxStreamBufferAdd_CMockExpectAndReturn(__LINE__, pxBuffer, uxOffset, pucData, uxByteCount, cmock_retval)
void uxStreamBufferAdd_CMockExpectAndReturn(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, size_t uxOffset, const uint8_t* pucData, size_t uxByteCount, size_t cmock_to_return);
typedef size_t (* CMOCK_uxStreamBufferAdd_CALLBACK)(StreamBuffer_t* pxBuffer, size_t uxOffset, const uint8_t* pucData, size_t uxByteCount, int cmock_num_calls);
void uxStreamBufferAdd_AddCallback(CMOCK_uxStreamBufferAdd_CALLBACK Callback);
void uxStreamBufferAdd_Stub(CMOCK_uxStreamBufferAdd_CALLBACK Callback);
#define uxStreamBufferAdd_StubWithCallback uxStreamBufferAdd_Stub
#define uxStreamBufferAdd_ExpectWithArrayAndReturn(pxBuffer, pxBuffer_Depth, uxOffset, pucData, pucData_Depth, uxByteCount, cmock_retval) uxStreamBufferAdd_CMockExpectWithArrayAndReturn(__LINE__, pxBuffer, pxBuffer_Depth, uxOffset, pucData, pucData_Depth, uxByteCount, cmock_retval)
void uxStreamBufferAdd_CMockExpectWithArrayAndReturn(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, int pxBuffer_Depth, size_t uxOffset, const uint8_t* pucData, int pucData_Depth, size_t uxByteCount, size_t cmock_to_return);
#define uxStreamBufferAdd_ReturnThruPtr_pxBuffer(pxBuffer) uxStreamBufferAdd_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, sizeof(StreamBuffer_t))
#define uxStreamBufferAdd_ReturnArrayThruPtr_pxBuffer(pxBuffer, cmock_len) uxStreamBufferAdd_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, (int)(cmock_len * (int)sizeof(*pxBuffer)))
#define uxStreamBufferAdd_ReturnMemThruPtr_pxBuffer(pxBuffer, cmock_size) uxStreamBufferAdd_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, cmock_size)
void uxStreamBufferAdd_CMockReturnMemThruPtr_pxBuffer(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, int cmock_size);
#define uxStreamBufferAdd_IgnoreArg_pxBuffer() uxStreamBufferAdd_CMockIgnoreArg_pxBuffer(__LINE__)
void uxStreamBufferAdd_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferAdd_IgnoreArg_uxOffset() uxStreamBufferAdd_CMockIgnoreArg_uxOffset(__LINE__)
void uxStreamBufferAdd_CMockIgnoreArg_uxOffset(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferAdd_IgnoreArg_pucData() uxStreamBufferAdd_CMockIgnoreArg_pucData(__LINE__)
void uxStreamBufferAdd_CMockIgnoreArg_pucData(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferAdd_IgnoreArg_uxByteCount() uxStreamBufferAdd_CMockIgnoreArg_uxByteCount(__LINE__)
void uxStreamBufferAdd_CMockIgnoreArg_uxByteCount(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferGet_IgnoreAndReturn(cmock_retval) uxStreamBufferGet_CMockIgnoreAndReturn(__LINE__, cmock_retval)
void uxStreamBufferGet_CMockIgnoreAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferGet_StopIgnore() uxStreamBufferGet_CMockStopIgnore()
void uxStreamBufferGet_CMockStopIgnore(void);
#define uxStreamBufferGet_ExpectAnyArgsAndReturn(cmock_retval) uxStreamBufferGet_CMockExpectAnyArgsAndReturn(__LINE__, cmock_retval)
void uxStreamBufferGet_CMockExpectAnyArgsAndReturn(UNITY_LINE_TYPE cmock_line, size_t cmock_to_return);
#define uxStreamBufferGet_ExpectAndReturn(pxBuffer, uxOffset, pucData, uxMaxCount, xPeek, cmock_retval) uxStreamBufferGet_CMockExpectAndReturn(__LINE__, pxBuffer, uxOffset, pucData, uxMaxCount, xPeek, cmock_retval)
void uxStreamBufferGet_CMockExpectAndReturn(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, size_t uxOffset, uint8_t* pucData, size_t uxMaxCount, BaseType_t xPeek, size_t cmock_to_return);
typedef size_t (* CMOCK_uxStreamBufferGet_CALLBACK)(StreamBuffer_t* pxBuffer, size_t uxOffset, uint8_t* pucData, size_t uxMaxCount, BaseType_t xPeek, int cmock_num_calls);
void uxStreamBufferGet_AddCallback(CMOCK_uxStreamBufferGet_CALLBACK Callback);
void uxStreamBufferGet_Stub(CMOCK_uxStreamBufferGet_CALLBACK Callback);
#define uxStreamBufferGet_StubWithCallback uxStreamBufferGet_Stub
#define uxStreamBufferGet_ExpectWithArrayAndReturn(pxBuffer, pxBuffer_Depth, uxOffset, pucData, pucData_Depth, uxMaxCount, xPeek, cmock_retval) uxStreamBufferGet_CMockExpectWithArrayAndReturn(__LINE__, pxBuffer, pxBuffer_Depth, uxOffset, pucData, pucData_Depth, uxMaxCount, xPeek, cmock_retval)
void uxStreamBufferGet_CMockExpectWithArrayAndReturn(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, int pxBuffer_Depth, size_t uxOffset, uint8_t* pucData, int pucData_Depth, size_t uxMaxCount, BaseType_t xPeek, size_t cmock_to_return);
#define uxStreamBufferGet_ReturnThruPtr_pxBuffer(pxBuffer) uxStreamBufferGet_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, sizeof(StreamBuffer_t))
#define uxStreamBufferGet_ReturnArrayThruPtr_pxBuffer(pxBuffer, cmock_len) uxStreamBufferGet_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, (int)(cmock_len * (int)sizeof(*pxBuffer)))
#define uxStreamBufferGet_ReturnMemThruPtr_pxBuffer(pxBuffer, cmock_size) uxStreamBufferGet_CMockReturnMemThruPtr_pxBuffer(__LINE__, pxBuffer, cmock_size)
void uxStreamBufferGet_CMockReturnMemThruPtr_pxBuffer(UNITY_LINE_TYPE cmock_line, StreamBuffer_t* pxBuffer, int cmock_size);
#define uxStreamBufferGet_ReturnThruPtr_pucData(pucData) uxStreamBufferGet_CMockReturnMemThruPtr_pucData(__LINE__, pucData, sizeof(uint8_t))
#define uxStreamBufferGet_ReturnArrayThruPtr_pucData(pucData, cmock_len) uxStreamBufferGet_CMockReturnMemThruPtr_pucData(__LINE__, pucData, (int)(cmock_len * (int)sizeof(*pucData)))
#define uxStreamBufferGet_ReturnMemThruPtr_pucData(pucData, cmock_size) uxStreamBufferGet_CMockReturnMemThruPtr_pucData(__LINE__, pucData, cmock_size)
void uxStreamBufferGet_CMockReturnMemThruPtr_pucData(UNITY_LINE_TYPE cmock_line, uint8_t* pucData, int cmock_size);
#define uxStreamBufferGet_IgnoreArg_pxBuffer() uxStreamBufferGet_CMockIgnoreArg_pxBuffer(__LINE__)
void uxStreamBufferGet_CMockIgnoreArg_pxBuffer(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferGet_IgnoreArg_uxOffset() uxStreamBufferGet_CMockIgnoreArg_uxOffset(__LINE__)
void uxStreamBufferGet_CMockIgnoreArg_uxOffset(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferGet_IgnoreArg_pucData() uxStreamBufferGet_CMockIgnoreArg_pucData(__LINE__)
void uxStreamBufferGet_CMockIgnoreArg_pucData(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferGet_IgnoreArg_uxMaxCount() uxStreamBufferGet_CMockIgnoreArg_uxMaxCount(__LINE__)
void uxStreamBufferGet_CMockIgnoreArg_uxMaxCount(UNITY_LINE_TYPE cmock_line);
#define uxStreamBufferGet_IgnoreArg_xPeek() uxStreamBufferGet_CMockIgnoreArg_xPeek(__LINE__)
void uxStreamBufferGet_CMockIgnoreArg_xPeek(UNITY_LINE_TYPE cmock_line);

#if defined(__GNUC__) && !defined(__ICC) && !defined(__TMS470__)
#if __GNUC__ > 4 || (__GNUC__ == 4 && (__GNUC_MINOR__ > 6 || (__GNUC_MINOR__ == 6 && __GNUC_PATCHLEVEL__ > 0)))
#pragma GCC diagnostic pop
#endif
#endif

#endif
