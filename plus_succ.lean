import defs
import zero_plus
import succ_plus

theorem plus_succ (m n:ℕ) : m + n.succ = (m + n).succ := by
  induction m
  case zero =>
    change 0 + n.succ = (0 + n).succ
    rewrite [zero_plus]
    rewrite [zero_plus]
    rfl
  case succ m ih =>
    rewrite [succ_plus]
    rewrite [ih]
    rewrite [succ_plus]
    rfl
