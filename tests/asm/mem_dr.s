DATA_1: .fill 0xFFFFFFFF

_start:
  ld   r13, [DATA_1]
  sd   r13, [DATA_2]
  ld   r3,  [DATA_2]
  sys  EXIT     # should return 0xFFFF

.space 277
DATA_2: .fill 38