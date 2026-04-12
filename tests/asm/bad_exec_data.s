.text
.global _start
_start:
  br   DATA
  mov  r2, r1
  movi r1, 0
  trap

.data
DATA:
  .fill 0x0
