import times_succ
import times_zero

theorem times_one ( n : ℕ ) : n*1 = n := by
  rewrite [times_succ, times_zero, plus_zero]
  rfl
