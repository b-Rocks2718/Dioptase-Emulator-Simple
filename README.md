# Simple Dioptase Emulator

This emulator is for the user-mode subset of the [Dioptase ISA](https://github.com/b-Rocks2718/Dioptase/blob/main/docs/ISA.md)  

It assumes all addresses have been mapped by the TLB (a segfault will never happen)

## Usage

Run the emulator with `cargo run -- <file>.hex`

## Testing

Run all tests with `cargo test`
