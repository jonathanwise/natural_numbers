theorem disj.comm ( h : P ∨ Q ) : Q ∨ P := by
  apply Or.elim h
  · intro hp
    apply Or.intro_right
    exact hp
  · intro hq
    apply Or.intro_left
    exact hq
