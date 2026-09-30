theorem modus_ponens { P Q R : Prop }
  ( hpq : P → Q ) ( hqr : Q → R )
  : P → R := by
    intro hp
    apply hqr
    apply hpq
    exact hp
