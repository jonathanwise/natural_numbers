theorem conj.comm ( h : P ∧ Q ) : Q ∧ P := by
  have ⟨ hp, hq ⟩ := h
  apply And.intro
  · exact hq
  · exact hp
