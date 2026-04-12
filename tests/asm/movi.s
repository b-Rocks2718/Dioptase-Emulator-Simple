.text
.global _start
_start:
  movi r3 0xABABABAB
  mov  r1, r3
  mov  r2, r1
  movi r1, 0
  trap # should return 0xABABABAB