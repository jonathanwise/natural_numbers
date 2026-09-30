import defs

def f ( n : ℕ ) : ℕ := match n with
  | .zero => 0
  | .succ n => 1 + n + ( f n )
