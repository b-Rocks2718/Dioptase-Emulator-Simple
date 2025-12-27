.text
.global _start
_start:
  mov  r1 sp
  movi r2 0x12345678
  swa  r2 [r1, -0x10]   # store a word in the stack region
  lwa  r0 [r1, -0x10]   # attempt to load into r0; should be ignored
  add  r1 r0 r0     # r1 should still be zero
  sys  EXIT
