#print And.intro
#print And.elim

theorem conj.comm ( h : P ∧ Q ) 
: Q ∧ P :=
  And.elim (fun p q => And.intro q p) h

example ( h : P ∧ Q )
: Q ∧ P := by
  apply And.elim
  case h => exact h
  case f => 
    intro p q
    apply And.intro
    exact q
    exact p

example ( h : P ∧ Q )
: Q ∧ P := by
  apply And.elim _ h
  intro p q
  exact And.intro q p

example ( h : P ∧ Q )
: Q ∧ P := by
  apply And.elim _ h
  intro p q
  exact ⟨ q, p ⟩


example ( h : P ∧ Q ) 
: Q ∧ P := by
  have ⟨ hp, hq ⟩ := h
  apply And.intro
  · exact hq
  · exact hp

example ( h : P ∧ Q )
: Q ∧ P := by
  let hp := h.1
  let hq := h.2
  exact ⟨ hq, hp ⟩

example ( h : P ∧ Q )
: Q ∧ P := by
  have ⟨ p, q ⟩ := h
  exact ⟨ q, p ⟩

theorem ex ( h : P ∧ Q )
: Q ∧ P := ⟨ h.2, h.1 ⟩

#print ex
#print conj.comm

set_option pp.all true in
#print ex

set_option pp.all true in
#print conj.comm
