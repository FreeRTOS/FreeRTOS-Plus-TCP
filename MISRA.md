# MISRA Compliance

The FreeRTOS-Plus-TCP library files conform to the [MISRA C:2012](https://www.misra.org.uk/MISRAHome/MISRAC2012/tabid/196/Default.aspx)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis.
Since the FreeRTOS-Plus-TCP library is a low level library and might need to interact with the network hardware directly, some MISRA violations as listed below are not "fixed".
Deviations from the MISRA standard are listed below:

### Suppressed with Coverity Comments
To find the violation references in the source files run grep on the source code
with ( Assuming reference 3 ):
```
grep 'MISRA Ref 3' . -rI
```
#### Rule 2.2

Ref 32, Ref 33, Ref 34
MISRA C-2012 Rule 2.2 Unions are used for checksum computation to speed up the
        process by utilizing the full length of registers (32-bits). After this,
        the 16-bit union members are used to then compute the final checksum.
        Doing this is considered as 'overwriting the variable' by Coverity.
        Thus, it marks some statements as dead code. This is a false positive.

#### Rule 8.9
Ref 26, Ref 57
MISRA C-2012 Rule 8.9 For unit-tests to be repeatable and independent of the
       order of execution, some variables have file scope definitions rather
       than function scope. The variables are still defined as static.

#### Rule 11.3
Ref 1, Ref 2, Ref 3, Ref 4, Ref 6, Ref 7, Ref 8, Ref 9, Ref 10, Ref 11, Ref 12,
Ref 13, Ref 14, Ref 17, Ref 18, Ref 19, Ref 20, Ref 21, Ref 23, Ref 24, Ref 25,
Ref 30, Ref 44, Ref 48, Ref 51, Ref 52, Ref 53, Ref 55, Ref 56, Ref 58, Ref 59,
Ref 60, Ref 61, Ref 62, Ref 63, Ref 64, Ref 65, Ref 66, Ref 67, Ref 68, Ref 69,
Ref 70, Ref 72, Ref 73, Ref 74, Ref 75, Ref 76, Ref 77, Ref 78, Ref 79, Ref 80,
Ref 81, Ref 82, Ref 83, Ref 84, Ref 85, Ref 86, Ref 87, Ref 90
MISRA C-2012 Rule 11.3 The data received/sent by the IP stack is represent as a
       byte stream. This byte stream needs to be casted to various data
       structures to access certain feilds of the packet. However, when casting
       a byte stream to a structure, MISRA warns us that it can lead to
       unaligned access. But, in case of FreeRTOS+TCP, `packed` structures are
       used to prevent that. Packed structures force the compiler to access any
       unaligned data byte by byte and hence mitigates the potential unaligned
       memory access violation.

#### Rule 11.4
Ref 5, Ref 39, Ref 40, Ref 41, Ref 42, Ref 43, Ref 46, Ref 49, Ref 50, Ref 71,
Ref 38, Ref 54
MISRA c-2012 Rule 11.4 Warns about conversion between a pointer and an integer.
       Whenever a socket is created using the `FreeRTOS_Socket` API, either a
       valid socket (a valid non-NULL pointer) is returned; or
       `FREERTOS_INVALID_SOCKET` is returned (which is essentially ~0U) to
       depic an error in the socket creation process. This coversion from ~0U
       to a pointer is used to convey the error to various functions. If the
       pointer is equal to `FREERTOS_INVALID_SOCKET`, then it is not
       dereferenced. Thus, this violation can be safely suppressed.
Ref 29
MISRA Rule 11.4 The following statement may trigger a:
        warning: cast increases required alignment of target type [-Wcast-align].
        It has been programatically checked that the pointer is well aligned
        before this point.
Ref 31
MISRA Rule 11.4 warns about casting pointer to an integer and vice versa.
        Here, the poiner to the starting byte of the packet is cast to an
        integer which is then used to see whether the pointer is well
        aligned or not. It is not used to access any pointer values. Thus, this
        violation can be safely suppressed.

#### Rule 11.6
Ref 16, Ref 27
When sending and receiving a DHCP event to the IP-stack, the events are
        converted to a void pointer and sent to the IP-task. The function used
        to send the events handles various events for the IP-task and thus only
        accepts void pointers. The IP-task converts the void pointer back to
        the event. Thus, this rule can be safely suppressed.
Ref 28
MISRA Rule 11.6 `uintptr_t` is guaranteed by the implementation to fit a
        pointer size of the platform. The conversion is required to move the
        pointer backward by a constant offset to get to a 'hidden' pointer
        which is not available for the user to use.

#### Rule 11.8
Ref 47
MISRA c-2012 Rule 11.8 warns about removing the `const` qualifier when
        assigning one value to another. In this case however, a function
        pointer is being copied. It doesn't make sense in case of function
        pointers for the pointee to be const or mutable. Thus, this rule is
        safe to suppress.

#### Rule 14.3
Ref 22
MISRA C-2012 Rule 14.3 False positive as the value might be changed
        depending on the conditionally compiled code
Ref 89
MISRA C-2012 Rule 14.3 Possibly a false positive as SIZE_MAX is shifted
        to the right (halved) which makes it a variant

#### Rule 21.6
Ref 35, Ref 36
MISRA C-2012 Rule 21.6 warns about the use of standard library input/output
        functions as they might have implementation defined or undefined
        behaviour. The function `snprintf` is used to insert information in a
        logging string. The function is bound by the number of bytes available
        in the buffer. When used as intended, the function will not overflow
        the provided buffer. Hence, this violation can be suppressed.

#### Rule 17.2
Ref 45
MISRA C-2012 Rule 17.2 warns about using recursion in software as that can have
        severe implications on the stack usage and can lead to a serious issue.
        In this case however, the number of recursions are limited by design.
        Any socket spawned (child) by a socket in listening state (parent)
        cannot be in listening state. Thus it is not possible for the child to
        have a secondary child socket thereby limiting the number of recursive
        calls to one.

#### Rule 20.10
Ref 88
MISRA C-2012 Rule 20.10 warns against the use of ## concatination operator.
        However, in this case, it must be used to support compile time
        assertions in case the preprocessor does not suppport sizeof. This
        operation (assert) has no runtime execution.
