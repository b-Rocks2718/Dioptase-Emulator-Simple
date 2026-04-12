.text
.global _start
_start:
  movi r1 0x8FFF
  movi r2 3
  cmp  r2 r1
  bbe  label # this should be taken
  movi r1 0xA
  mov  r2, r1
  movi r1, 0
  trap
label:
  cmp  r1 r2
  bbe  label2 # this branch should not be taken
  cmp  r0 r0
  bbe  label3 # this branch should be taken
  movi r1 0xD
  mov  r2, r1
  movi r1, 0
  trap
label2:
  movi r1 0xF
  mov  r2, r1
  movi r1, 0
  trap
label3:
  movi r1 1
  mov  r2, r1
  movi r1, 0
  trap