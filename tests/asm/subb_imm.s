.text
.global _start
_start:
  # Immediate subb computes i - rB - borrow, like immediate sub (i - rB).
  add  r4 r0 8
  add  r6 r0 1
  sub  r2 r6 r0  # 1 - 0: carry set (no borrow); must directly precede subb
  subb r1 r4 50
  mov  r2, r1
  movi r1, 0
  trap # should return 50 - 8 = 42
