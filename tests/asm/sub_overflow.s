.text
.global _start
_start:
  movi r1 0x80000000
  movi r2 1
  sub  r4 r1 r2       # 0x80000000 - 1 = 0x7FFFFFFF with overflow set
  bo   overflow       # should be taken
  movi r1 0xBAD       # failure path if overflow was not set
  mov  r2, r1
  movi r1, 0
  trap
overflow:
  movi r1 1
  mov  r2, r1
  movi r1, 0
  trap
