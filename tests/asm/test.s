DATA:
  .fill 21

_start:
  movi r7, 7
  lw  r6, [DATA]
  sub r7, r6, r7
  sw  r7, [DATA]
  lw  r3, [DATA]
  sys EXIT
