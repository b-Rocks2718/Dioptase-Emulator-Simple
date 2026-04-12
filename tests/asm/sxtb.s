.text
.global _start
_start:
  movi r2 0xFFFFFF7F
  movi r3 0x00000080
  sxtb r4 r2
  sxtb r5 r3
  sub  r1 r4 r5
  mov  r2, r1
  movi r1, 0
  trap # should return 0x000000FF
