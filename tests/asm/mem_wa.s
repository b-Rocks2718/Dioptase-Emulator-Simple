.text
.global _start
_start:
  mov  r4 sp
  movi r5 0x42424242
  swa  r5 [r4, -0x10] # store at address 0x7FFFFFF0
  lwa  r3 [r4, -0x10]
  mov  r1, r3
  mov  r2, r1
  movi r1, 0
  trap     # should return 0x42424242
