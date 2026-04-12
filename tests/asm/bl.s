.text
.global _start
_start:
  movi r1 0x8FFF0000
  movi r2 3
  cmp  r1 r2
  bl   label # this should be taken
  movi r1 0xE
  mov  r2, r1
  movi r1, 0
  trap
label:
  cmp  r2 r1
  bl   label2 # this branch should not be taken
  cmp  r0 r0
  bl   label3 # this branch should not be taken
  movi r1 2
  mov  r2, r1
  movi r1, 0
  trap
label2:
  movi r1 0xF
  mov  r2, r1
  movi r1, 0
  trap
label3:
  movi r1 0xD
  mov  r2, r1
  movi r1, 0
  trap