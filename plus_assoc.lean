import zero_plus
import succ_plus

theorem plus.assoc (m n p:ℕ) : (m + n) + p = m + (n + p) := by
  induction m
  case zero =>
    change (0+n)+p = 0 + (n+p)
    rewrite [zero_plus]
    rewrite [zero_plus]
    rfl
  case succ m ih =>
    rewrite [succ_plus]
    rewrite [succ_plus]
    rewrite [succ_plus]
    rewrite [ih]
    rfl
