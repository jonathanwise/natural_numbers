def sum.comm { P Q : Type } ( h : P ⊕ Q ) 
: Q ⊕ P := by
  sorry





example { P Q : Type } ( h : P ⊕ Q ) 
: Q ⊕ P := by
  apply Sum.elim _ _ h
  · intro hp
    apply Sum.inr
    exact hp
  · intro hq
    apply Sum.inl
    exact hq
