DATA:
  .fill 21

_start:
  movi r7, 14
  sw  r7, [r0, DATA]
  lw  r3, [r0, DATA]
  sys EXIT