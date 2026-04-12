.text
.global _start
_start:
  movi r2 0xFFFF7FFF
  movi r3 0x00008000
  sxtd r4 r2
  sxtd r5 r3
  sub  r1 r4 r5
  mov  r2, r1
  movi r1, 0
  trap # should return 0x0000FFFF
