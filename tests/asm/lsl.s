.text
.global _start
_start:
  movi r3 0xAAAA
  movi r1, 2
  lsl  r3 r3 r1
  lsl  r3 r3 1
  mov  r1, r3
  mov  r2, r1
  movi r1, 0
  trap # should return 0x55550