import defs
import zero_plus
import succ_plus

theorem plus_zero (n : ℕ) : n + 0 = n := by
  induction n
  case zero =>
    rewrite [zero_plus]
    rfl
  case succ n ih =>
    change n.succ + 0 = n.succ
    rewrite [succ_plus]
    rewrite [ih]
    rfl
