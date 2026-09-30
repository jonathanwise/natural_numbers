import times_comm
import times_left_distrib

theorem times.right_distrib ( m n p : ℕ ) : ( m + n ) * p = m*p + n*p := by
  simp [times.comm, times.left_distrib]
