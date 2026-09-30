theorem propositional_example_1 ( hpq : P ∨ Q ) ( hqr : Q ∨ R ) : P ∨ Q ∨ R := by
  apply Or.elim hpq
  intro hp
  apply Or.intro_left
  exact hp
  intro hq
  apply Or.intro_right
  apply Or.intro_left
  exact hq
