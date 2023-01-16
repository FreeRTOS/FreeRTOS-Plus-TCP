#include <string.h>
#include <stdlib.h>
#include <setjmp.h>
#include "cmock.h"
#include "mock_FreeRTOS_ND.h"


static struct mock_FreeRTOS_NDInstance
{
  unsigned char placeHolder;
} Mock;

extern jmp_buf AbortFrame;
extern int GlobalExpectCount;
extern int GlobalVerifyOrder;

void mock_FreeRTOS_ND_Verify(void)
{
}

void mock_FreeRTOS_ND_Init(void)
{
  mock_FreeRTOS_ND_Destroy();
}

void mock_FreeRTOS_ND_Destroy(void)
{
  CMock_Guts_MemFreeAll();
  memset(&Mock, 0, sizeof(Mock));
  GlobalExpectCount = 0;
  GlobalVerifyOrder = 0;
}

