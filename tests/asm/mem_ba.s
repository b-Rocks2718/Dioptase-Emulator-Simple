_start:
  add  r4 r0 10
  movi r5 0x42424242
  sba  r5 [r4, 90] # store at address 100
  lba  r3 [r0, 100]
  sys  EXIT     # should return 0x42
