# sasm - The SIMDISCA Assembler

## Installation
You need to have installed LLVM to emit ELF objects:
 - on everything except macOS, LLVM has to be in PATH
 - on macOS, it has to be installed via homebrew. It only works on M1 macs at the moment though.

You also need to have _nightly_ rust installed unless there are pre-built binaries for your platform available.
```sh
git clone git@github.com:pitust/sasm
cd sasm
cargo +nightly install --path .
```

Sample assembly file:
```asm
; This code should be used as a reference for a basic firmware
; program. This code is written in official SIMDISCA assembly
; syntax, and uses official mnemonics. The official, recommended
; assembler for SIMDISCA is sasm:
;   https://github.com/pitust/sasm

-off 0xFFFC0000
-entry start

start:
    mv mri, interrupt_table
    mv orl, mrf
    mv orr, 2
    mv mrf, bro
    mv mre, 0x80000000
    mv mrp, mrp

interrupt_table:
    x31 dd 0
    dd interface_interrupt_handler

interface_interrupt_handler:
    mv prs, prb
    mv orl, prs
    mv orr, 4
    mv mrp, d ars    
```
`sasm` is able to understand code in a multitude of styles:
```asm
-off 0xFFFC0000
start:
    mov mrp, mrp
    mov mrp, (start >> 2) | 1
```