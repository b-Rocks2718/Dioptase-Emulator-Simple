_start:
  movi r1 0x100
  movi r2 0x12345678
  swa  r2 [r1, 0]   # store a word
  lwa  r0 [r1, 0]   # attempt to load into r0; should be ignored
  add  r1 r0 r0     # r1 should still be zero
  sys  EXIT
