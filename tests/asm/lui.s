.text
.global _start
_start:
  lui  r6 0xAA000000
  mov  r6 r6
  mov  r3 r6
  mov  r1, r3
  sys  EXIT # should return 0xAA000000
  