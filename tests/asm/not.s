.text
.global _start
_start:
  movi r3 0xFFFFFFFD
  not  r3 r3
  not  r4, 0
  add  r3, r3, r4
  mov  r1, r3
  mov  r2, r1
  movi r1, 0
  trap # should return 1