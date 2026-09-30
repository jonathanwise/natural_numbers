import plus_succ
import plus_zero

theorem plus_one (n : ℕ) : n + 1 = n.succ := by
  rewrite [plus_succ, plus_zero]
  rfl
