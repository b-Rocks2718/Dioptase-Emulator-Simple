.text
.global _start
_start:
  add  r5 r0 10
  add  r7 r0 11
  add  r3 r5 r7
  add  r3 r3 r3
  add  r3 r3 -4
  mov  r1, r3
  mov  r2, r1
  movi r1, 0
  trap     # should return 38
