_start:
  movi r3 0xAAAA
  lsl  r3 r3 3
  sys  EXIT # should return 0x55550