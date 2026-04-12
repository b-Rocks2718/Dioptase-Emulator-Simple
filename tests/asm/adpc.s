  .text
  .global _start
_start:
  # adpc should resolve the absolute address of target.
  adpc r1, target
  lw   r2, [target_addr]
  sub  r1, r1, r2
  mov  r2, r1
  movi r1, 0
  trap

target:
  nop

  .data
target_addr:
  .fill target
