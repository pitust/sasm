%macro call
    mov grf, $ + 0x10
    mov mrp, %
%endmacro

.call fun

fun: