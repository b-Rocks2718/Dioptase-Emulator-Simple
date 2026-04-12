.text
.global _start
_start:
  call far_label
  mov  r2, r1
  movi r1, 0
  trap # should return 42

  mov  r2, r1

  movi r1, 0

  trap
  mov  r2, r1
  movi r1, 0
  trap
  mov  r2, r1
  movi r1, 0
  trap

far_label:
  add  r3 r0 21
  add  r3 r3 21
  mov  r1, r3
  ret  

  mov  r2, r1

  movi r1, 0

  trap
  mov  r2, r1
  movi r1, 0
  trap
  mov  r2, r1
  movi r1, 0
  trap