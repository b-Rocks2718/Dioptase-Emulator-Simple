DATA_1: .fill 0xFFFFFFFF

_start:
  lw   r13, [DATA_1]
  nop
  nop
  nop
  lw   r10, [DATA_2]
  nop
  nop
  nop
  add  r13, r10, r13
  nop
  nop
  nop
  nop
  sw   r13, [DATA_2]
  nop
  nop
  nop
  lw   r3,  [DATA_2]
  nop
  nop
  nop
  nop
  sys  EXIT     # should return 0x25 = 37

.space 277
DATA_2: .fill 38