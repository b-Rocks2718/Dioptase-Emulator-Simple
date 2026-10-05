.text
.global _start
_start:
  # asr by 0 must leave a negative value unchanged (it used to return -1).
  movi r3 0x80000010
  asr  r1 r3 0
  mov  r2, r1
  movi r1, 0
  trap # should return 0x80000010
