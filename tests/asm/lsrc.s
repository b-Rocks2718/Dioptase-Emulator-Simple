_start:
  movi r4 0x5557
  movi r3 0x00A0
  movi r9, 1
  lsr  r4 r4 r9
  lsrc r3 r3 r9
  lsr  r4 r4 1
  lsrc r3 r3 1
  sys  EXIT # should return 0xC0000028