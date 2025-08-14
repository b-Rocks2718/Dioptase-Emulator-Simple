DATA_1: .fill 0xFFFFFFFF

_start:
  lw   r13, [DATA_1]
  sw   r13, [DATA_2]
  lw   r3,  [DATA_2]
  sys  EXIT     # should return -1

.space 277
DATA_2: .fill 38