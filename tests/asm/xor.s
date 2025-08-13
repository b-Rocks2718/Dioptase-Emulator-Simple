_start:
  add  r1 r0 15
  add  r2 r0 18
  xor  r3 r2 r1
  # should return 11101 = 29
  sys  EXIT