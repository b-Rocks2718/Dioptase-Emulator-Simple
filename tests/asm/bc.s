.text
.global _start
_start:
  movi r1 0x80000000
  add  r0 r1 r1
  bc   label # this should be taken
  movi r1 0xE
  mov  r2, r1
  movi r1, 0
  trap
label:
  add  r0 r0 r0
  bc   label2 # this branch should not be taken
  movi r1 1
  mov  r2, r1
  movi r1, 0
  trap
label2:
  movi r1 0xF
  mov  r2, r1
  movi r1, 0
  trap