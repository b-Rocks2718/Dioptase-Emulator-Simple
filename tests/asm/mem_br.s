DATA_1: .fill 0xFFFFFFFF

_start:
  lb   r13, [DATA_1]
  sb   r13, [DATA_2]
  lb   r3,  [DATA_2]
  sys  EXIT     # should return 0xFF

.space 277
DATA_2: .fill 38