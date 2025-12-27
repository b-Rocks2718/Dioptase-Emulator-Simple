.text
.global _start
_start:
  # Setup: store 0x10 at an absolute addr within the stack region (sp - 0x10).
  mov  r4 sp
  add  r2 r0 0x10
  swa  r2 [r4, -0x10]

  # Absolute swap: r5 <- old (0x10), mem <- 0x22.
  add  r6 r0 0x22
  swpa r5, r6, [r4, -0x10]

  # PC-relative swap: r8 <- old (0x33), mem <- 0x44.
  add  r7 r0 0x44
  swp  r8, r7, [SWAP_REL]

  # PC-relative swap immediate: r10 <- old (0x55), mem <- 0x66.
  add  r9 r0 0x66
  swp  r10, r9, [SWAP_IMM]

  # Read back updated memory to validate side effects.
  lwa  r11 [r4, -0x10] # expect 0x22
  lw   r12, [SWAP_REL] # expect 0x44
  lw   r13, [SWAP_IMM] # expect 0x66

  # Sum of all observed values:
  # r5(0x10) + r11(0x22) + r8(0x33) + r12(0x44) + r10(0x55) + r13(0x66) = 0x164
  add  r14 r5 r11
  add  r14 r14 r8
  add  r14 r14 r12
  add  r14 r14 r10
  add  r14 r14 r13
  mov  r1, r14
  sys  EXIT     # should return 0x164

.data
SWAP_REL: .fill 0x33
SWAP_IMM: .fill 0x55
