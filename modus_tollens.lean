theorem modus_tollens {P Q:Prop} ( h : ¬ P ∨ Q ) : P → Q := by
  intro hp
  apply Or.elim h
  intro hnp
  contradiction
  intro hq
  exact hq
