.text
.global _start
_start:
  movi r2 0x123456
  movi r7 0x111111
  push r2
  push r7
  pop  r0
  pop  r1
  mov  r2, r1
  movi r1, 0
  trap
