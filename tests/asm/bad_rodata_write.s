.text
.global _start
_start:
  movi r1 0x1234
  sw   r1, [RODATA]
  mov  r2, r1
  movi r1, 0
  trap

.rodata
RODATA:
  .fill 0x0
