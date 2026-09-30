import zero_plus

theorem times_zero ( n : ℕ ) : n*0 = 0 := by
  induction n
  case zero =>
    rfl
  case succ m ih =>
    change 0 + m*0 = 0
    rewrite [zero_plus]
    rewrite [ih]
    rfl
