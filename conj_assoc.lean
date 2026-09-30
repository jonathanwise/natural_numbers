theorem conj.assoc : P∧Q∧R ↔ (P∧Q)∧R := by
  apply Iff.intro
  · intro hpqr
    have ⟨ hp, hq, hr ⟩ := hpqr
    apply And.intro
    apply And.intro
    exact hp
    exact hq
    exact hr
  · intro hpqr
    have ⟨ hpq, hr ⟩ := hpqr
    have ⟨ hp, hq ⟩ := hpq
    apply And.intro
    exact hp
    apply And.intro
    exact hq
    exact hr
