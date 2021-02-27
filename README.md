# sasm - The SIMDISCA Assembler

## Installation
You need to have installed LLVM to emit ELF objects:
 - on everything except macOS, LLVM has to be in PATH
 - on macOS, it has to be installed via homebrew. It only works on M1 macs at the moment though.

You also need to have rust installed unless there are pre-built binaries for your platform available.
```sh
git clone git@github.com:pitust/sasm
cd sasm
cargo install --path .
```
