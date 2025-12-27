.text
.global _start
_start:
  mov  r4 sp
  movi r5 0x42424242
  sda  r5 [r4, -0x10] # store at address 0x7FFFFFF0
  lda  r3 [r4, -0x10]
  mov  r1, r3
  sys  EXIT     # should return 04242
