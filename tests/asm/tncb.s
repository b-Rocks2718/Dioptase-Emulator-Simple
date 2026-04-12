.text
.global _start
_start:
  movi r2 0x12345680
  tncb r3 r2
  add  r1 r3 1
  mov  r2, r1
  movi r1, 0
  trap # should return 0x00000081
