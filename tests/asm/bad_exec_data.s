.text
.global _start
_start:
  br   DATA
  sys  EXIT

.data
DATA:
  .fill 0x0
