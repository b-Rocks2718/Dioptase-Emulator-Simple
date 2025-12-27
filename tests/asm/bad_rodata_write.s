.text
.global _start
_start:
  movi r1 0x1234
  sw   r1, [RODATA]
  sys  EXIT

.rodata
RODATA:
  .fill 0x0
