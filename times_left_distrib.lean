import zero_times
import succ_times
import plus_assoc
import plus_comm

theorem times.left_distrib ( m n p : ℕ ) : m * (n + p) = m*n + m*p := by
  induction m
  case zero =>
    rewrite [zero_times, zero_times, zero_times, zero_plus]
    rfl
  case succ m ih =>
    rewrite [succ_times, succ_times, succ_times]
    rewrite [ih]
    simp only [← plus.assoc, plus.comm]
