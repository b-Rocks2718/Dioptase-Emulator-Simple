.text
.global _start
_start:
  # ALU-immediate op 18 (sxtb) has no immediate encoding in docs/ISA.md and
  # must stop the emulator (it used to execute sxtb).
  .fill 0x08812000
  mov  r2, r1
  movi r1, 0
  trap
