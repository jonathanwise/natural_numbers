import plus_assoc

example { a b c d : ℕ } :  a + (b + ( c + d ) ) =  a + b + c + d := by
  simp [plus.assoc]
