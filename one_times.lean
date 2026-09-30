import succ_times
import zero_times
import plus_zero

theorem one_times ( n : ℕ ) : 1*n = n := by
  simp only [succ_times, zero_times, plus_zero]
