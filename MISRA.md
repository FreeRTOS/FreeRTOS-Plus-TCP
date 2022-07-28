# MISRA Compliance

The FreeRTOS-Plus-TCP library files conform to the [MISRA C:2012](https://www.misra.org.uk/MISRAHome/MISRAC2012/tabid/196/Default.aspx)
guidelines, with the deviations listed below. Compliance is checked with Coverity static analysis.
Since the FreeRTOS-Plus-TCP library is designed for small-embedded devices, it needs to have a very small memory footprint and has to
be efficient. To achieve that and to increase the performace of the IP-stack, it deviates from some MISRA rules.
The specific deviations, suppressed inline, are listed below.

Additionally, [MISRA configuration file](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/tools/coverity_misra.config) contains the project wide deviations.

### Suppressed with Coverity Comments
To find the violation references in the source files run grep on the source code
with ( Assuming rule 11.4 violation; with justification in point 2 ):
```
grep 'MISRA Ref 11.4.2' . -rI
```
#### Rule 2.2

_Ref 2.2.1_

- MISRA C-2012 Rule 2.2 Unions are used for checksum computation to speed up the
        process by utilizing the full length of registers (32-bits). After this,
        the 16-bit union members are used to then compute the final checksum.
        Doing this is considered as 'overwriting the variable' by Coverity.
        Thus, it marks some statements as dead code. This is a false positive.

#### Rule 8.9
_Ref 8.9.1_

- MISRA C-2012 Rule 8.9 For unit-tests to be repeatable and independent of the
       order of execution, some variables have file scope definitions rather
       than function scope.

#### Rule 11.1
_Ref 11.1.1_

- MISRA C-2012 Rule 11.1 Converting from a void pointer to a function pointer,
    it is part of the API and the user is responsible of providing that pointer
    and their responsibility for that pointer to be valid.

#### Rule 11.3
_Ref 11.3.1_

- MISRA C-2012 Rule 11.3 The data received/sent by the IP stack is represent as a
       byte stream. This byte stream needs to be casted to various data
       structures to access certain fields of the packet. However, when casting
       a byte stream to a structure, MISRA warns us that it can lead to
       unaligned access. But, in case of FreeRTOS+TCP, the buffer in which the
       packets are stored are always aligned to a 4 byte word boundary with an
       offset of 2 bytes. The reason for this 2 byte offset is that the
       ethernet header is of 14 (12 + 2) bytes. Thus, everything except the
       ethernet header is properly aligned. There is one alignment exception,
       which is the sender protocol address in the ARP Header. To combat that,
       the sender protocol address field is declared as an array of 4 bytes
       instead of a `uint32_t`.
       More details can be found [here](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/pull/512#pullrequestreview-1035211706).

#### Rule 11.4
_Ref 11.4.1_

- MISRA c-2012 Rule 11.4 Warns about conversion between a pointer and an integer.
       Whenever a socket is created using the `FreeRTOS_Socket` API, either a
       valid socket (a valid non-NULL pointer) is returned; or
       `FREERTOS_INVALID_SOCKET` is returned (which is essentially ~0U) to
       depict an error in the socket creation process. This conversion from ~0U
       to a pointer is used to convey the error to various functions. If the
       pointer is equal to `FREERTOS_INVALID_SOCKET`, then it is not
       dereferenced. Thus, this violation can be safely suppressed.

_Ref 11.4.2_

- MISRA Rule 11.4 The following statement may trigger a:
        warning: cast increases required alignment of target type [-Wcast-align].
        It has been programatically checked that the pointer is well aligned
        before this point.

_Ref 11.4.3_

- MISRA Rule 11.4 warns about casting pointer to an integer and vice versa.
        Here, the poiner to the starting byte of the packet is cast to an
        integer which is then used to see whether the pointer is well
        aligned or not. It is not used to access any pointer values. Thus, this
        violation can be safely suppressed.

#### Rule 11.6
_Ref 11.6.1_

- When sending and receiving a DHCP event to the IP-stack, the events are
        converted to a void pointer and sent to the IP-task. The function used
        to send the events handles various events for the IP-task and thus only
        accepts void pointers. The IP-task converts the void pointer back to
        the original event. Thus, this rule can be safely suppressed.

_Ref 11.6.2_

- MISRA Rule 11.6 `uintptr_t` is guaranteed by the implementation to fit a
        pointer size of the platform. The pointer has to be moved backward by a
        constant offset to get to a 'hidden' pointer which is not available for
        the user to use. This conversion is done to achieve that while avoiding
        pointer arithmetic.

#### Rule 11.8
_Ref 11.8.1_

- MISRA c-2012 Rule 11.8 warns about removing the `const` qualifier when
        assigning one value to another. In this case however, a function
        pointer is being copied. It doesn't make sense in case of function
        pointers for the pointee to be const or mutable. Thus, this rule is
        safe to suppress.
1
#### Rule 14.3
_Ref 14.3.1_

- MISRA C-2012 Rule 14.3 False positive as the value might be changed
        depending on the conditionally compiled code

#### Rule 21.6
_Ref 21.6.1_

- MISRA C-2012 Rule 21.6 warns about the use of standard library input/output
        functions as they might have implementation defined or undefined
        behaviour. The function `snprintf` is used to insert information in a
        logging string. This is only used in a utility function which aids in
        debugging and is not part of the 'core' code governing the
        functionality of the TCP/IP stack.

#### Rule 17.2
_Ref 17.2.1_

- MISRA C-2012 Rule 17.2 warns about using recursion in software as that can have
        severe implications on the stack usage and can lead to a serious issue.
        In this case however, the number of recursions are limited by design.
        Any socket spawned (child) by a socket in listening state (parent)
        cannot be in listening state. Thus it is not possible for the child to
        have a secondary child socket thereby limiting the number of recursive
        calls to one.

#### Rule 20.10
_Ref 20.10.1_

- MISRA C-2012 Rule 20.10 warns against the use of ## concatination operator.
        However, in this case, it must be used to support compile time
        assertions in case the preprocessor does not suppport sizeof. This
        operation (assert) has no runtime execution.
