# Simple Dioptase Emulator

This emulator is for the user-mode subset of the [Dioptase ISA](https://github.com/b-Rocks2718/Dioptase/blob/main/docs/ISA.md)  

It accepts a pseudo-ELF file output by my assembler and runs the program. Will allocate sections specified by the ELF file
and fail if memory outside them is accessed. 

## Usage

Run the emulator with `cargo run -- <file>.hex`  
The value in r1 when the program terminates is printed.

Use `--debug` to start an interactive debugger (label breakpoints require `.debug` files built with assembler `--debug`)

### Debug Commands

- `r` reset and run until break/watchpoint/halt
- `c` continue execution
- `n` step one instruction
- `break <label|addr>` set breakpoint
- `breaks` list breakpoints
- `delete <label|addr>` remove breakpoint
- `watch [r|w|rw] <addr>` stop on memory access
- `watchs` list watchpoints
- `unwatch <addr>` remove watchpoint
- `info regs` print all registers/flags
- `info <reg>` print a single register
- `info <addr>` print word at address
- `x <addr> <len>` dump memory range
- `set reg <reg> <value>` write a register
- `q` quit

## Testing

Run all tests with `cargo test`

Test assume the file structure is the same as how things are orginized in the [Dioptase repo](https://github.com/b-Rocks2718/Dioptase/tree/main). This allows the tests to access the assembler.
