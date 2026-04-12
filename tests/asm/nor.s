.text
.global _start
_start:
  add  r4 r0 10
  add  r1 r0 12
  nor  r3 r1 r4 
  nor  r3 r3 8 # should be 6
  mov  r1, r3
  mov  r2, r1
  movi r1, 0
  trap