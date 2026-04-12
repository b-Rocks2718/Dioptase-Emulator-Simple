.text
.global _start
_start:
  movi r3 0x5555
  movi r1, 2
  lsr  r3 r3 r1
  lsr  r3 r3 1
  mov  r1, r3
  mov  r2, r1
  movi r1, 0
  trap # should return 0xAAA