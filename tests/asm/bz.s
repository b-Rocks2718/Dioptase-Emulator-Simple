_start:
  add  r1 r0 10
  add  r2 r0 11
  add  r3 r0 10
  cmp  r1 r3
  bz   label # this should be taken
  movi r3 0xE
  sys  EXIT
label:
  cmp  r1 r2
  bz   label2 # this branch should not be taken
  movi r3 1
  sys  EXIT
label2:
  movi r3 0xF
  sys  EXIT