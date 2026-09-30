import times_right_distrib

theorem times.assoc (m n p : ℕ) : (m * n) * p = m * (n * p) := by
  induction m
  case zero =>
    rewrite [zero_times, zero_times, zero_times]
    rfl
  case succ m ih =>
    rewrite [succ_times, succ_times, right_distrib, ih]
    rfl
