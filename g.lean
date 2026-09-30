import zero_times

def g ( n : ℕ ) : ℕ := match n with
  | .zero => 0
  | .succ n => 2 + ( g n )

theorem g_doubles : ∀ n : ℕ, g n = n * 2 := by
  intro n
  induction n
  case zero =>
    unfold g
    rewrite [zero_times]
    rfl
  case succ n ih =>
    unfold g
    unfold times
    rewrite [ih]
    rfl
