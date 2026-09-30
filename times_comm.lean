import times_succ
import times_zero

theorem times.comm ( m n : ℕ ) : m*n = n*m := by
  induction m
  case zero =>
    rewrite [zero_times]
    rewrite [times_zero]
    rfl
  case succ m ih =>
    rewrite [succ_times]
    rewrite [times_succ]
    rewrite [ih]
    rfl
