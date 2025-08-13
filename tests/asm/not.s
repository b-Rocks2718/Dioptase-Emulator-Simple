_start:
  movi r3 0xFFFFFFFD
  not  r3 r3
  sys  EXIT # should return 2