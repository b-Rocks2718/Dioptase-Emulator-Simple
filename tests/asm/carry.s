  .text
  .global _start
_start:
  movi r1 1
  movi r2 0
  cmp  r1 r2
  bae  ok   # must be taken
  add  r1 r0 1  # should not be executed
  mov  r2, r1
  movi r1, 0
  trap
ok:
  add  r1 r0 42
  mov  r2, r1
  movi r1, 0
  trap   # should return 42
