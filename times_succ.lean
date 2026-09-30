import zero_times
import succ_times
import plus_assoc
import plus_comm

theorem times_succ ( m n : ℕ ) : m * n.succ = m + m*n := by
  induction m
  case zero =>
    change 0 * n.succ = 0 + 0*n
    rewrite [zero_times, zero_times, zero_plus]
    rfl
  case succ m ih =>
    change n.succ + m*n.succ = m.succ + m.succ*n
    rewrite [ih]
    rewrite [succ_times]
    change (1+n) + (m + m*n) = (1+m) + (n + m*n)
    simp [← plus.assoc, plus.comm]
