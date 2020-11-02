# MISRA Compliance

The FreeRTOS-Plus-TCP library files conform to the [MISRA C:2012](https://www.misra.org.uk/MISRAHome/MISRAC2012/tabid/196/Default.aspx)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis.
Since the FreeRTOS-Plus-TCP library is a low level library and might need to interact with the network hardware directly, some MISRA violations as listed below are not "fixed".
Deviations from the MISRA standard are listed below:

### Flagged by Coverity
| Deviation | Category | Justification |
| :-: | :-: | :-: |
| Rule 1.2 | Advisory | Language extenstions are being used in a portable manner for each specific compiler. |
| Rule 8.7 | Advisory | Functions without an external linkage are being used in other projects. Thus, function declarations are kept. |
| Rule 19.2 | Advisory | Unions are used to reduce the memory footprint of the stack. |
| Directive 4.6 | Advisory | Non-typedef-ed variables are used in compiler and platform specific manner (portable). |
| Rule 20.1 | Advisory | #includes are used to include compiler specific attributes to make "[packed structures](https://en.wikipedia.org/wiki/Data_structure_alignment)". |
| Rule 11.4 | Advisory | Integer to pointer conversion is done at places which are best served in that manner. |
| Rule 11.3 | Required | Pointer conversions are done to access various data members of a given data packet. |
| Rule 15.4 | Advisory | `break` statements are used in conjucture with `do-while(0)` to reduce `if-else` nesting. |
| Rule 8.13 | Advisory |  |
| Rule 10.5 | Advisory | Numerical casting is done only between certain variables and `enums`. It has been verified that the enums used can accomodate variables. |
| Rule 11.8 | Required | `const` identifier is removed in some cases since certain `struct`s are made to be used with modifiable types. |
| Rule 14.4 | Required | Condition `0` not having an essentially boolean type is used in portable layer of the Kernel for `taskENTER_CRITICAL` and `taskEXIT_CRITICAL`. |
| Rule 8.6 | Required | Some functions are declared but not defined since they are to be defined by the user application to provide 'hooks' for certain events. |
| Rule 2.3 | Advisory |  |
| Rule 20.10 | Advisory | `#` or `##` is used to create some utility functions for casting variables.  |
| Rule 10.4 | Required | Signed and unsigned variables are used together due to the variables acquired from the portable code. |
| Rule 13.5 | Required | Persistent side effects are required in some function calls (such as to maintain the state of a state-machine etc). |
| Rule 15.5 | Advisory | `return` statement is restrictively used to optimise the response time of the stack. |
| Rule 18.3 | Required | Relational operators are used with members of unions. |
| Rule 21.6 | Required | `snprintf` is used restrictively to format strings before placing them into buffers. |
| Rule 10.8 | Required | Unsigned expression is casted in one location to compare with a signed variable.  |
| Rule 11.1 | Required | `void *` is used to pass variables of various types to a function as parameter. |
| Rule 14.3 | Required | Controlling expression is not invariant in some cases due to dependence on a `#if`. |
| Rule 2.2 | Required | There is no dead code, just use of unions which confuses Coverity compiler. |
| Rule 5.9 | Advisory | Utility functions are defined in various files to not break various other projects. |
| Rule 8.9 | Advisory | For ease, configuration parameters are defined at a global scope even when used only once. |


### Suppressed with Coverity Comments
*None.*
