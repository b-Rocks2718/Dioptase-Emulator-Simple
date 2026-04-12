.text
.global _start
_start:
  add  r1 r0 10
  add  r2 r0 11
  add  r3 r0 10
  cmp  r1 r2
  bnz  label # this should be taken
  movi r1 0xE
  mov  r2, r1
  movi r1, 0
  trap
label:
  cmp  r1 r3
  bnz  label2 # this branch should not be taken
  movi r1 0
  mov  r2, r1
  movi r1, 0
  trap
label2:
  movi r1 0xF
  mov  r2, r1
  movi r1, 0
  trap