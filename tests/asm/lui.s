.text
.global _start
_start:
  lui  r6 0xAA000000
  mov  r6 r6
  mov  r3 r6
  mov  r1, r3
  mov  r2, r1
  movi r1, 0
  trap # should return 0xAA000000
  