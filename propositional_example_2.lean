theorem propositional_example_2 { P Q R : Prop } ( h : P∧Q → R ) : P → Q → R := by
  intro hp
  intro hq
  have hpq : P ∧ Q := ⟨ hp, hq ⟩
  apply h
  exact hpq
