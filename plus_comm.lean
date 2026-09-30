import plus_zero
import plus_succ

theorem plus.comm (m:ℕ) (n:ℕ) : m+n = n+m := by
  induction m
  case zero =>
    change 0 + n = n + 0
    rewrite [zero_plus]
    rewrite [plus_zero]
    rfl
  case succ m ih =>
    rewrite [succ_plus]
    rewrite [plus_succ]
    rewrite [ih]
    rfl
