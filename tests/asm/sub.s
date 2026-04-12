.text
.global _start
_start:
  add  r5 r0 12
  add  r7 r0 19
  sub  r3 r5 r7
  sub  r3 r3 1
  mov  r1, r3
  mov  r2, r1
  movi r1, 0
  trap # should return 8