

-- notation "ℕ" => Nat

inductive ℕ where
  | zero : ℕ
  | succ : ℕ → ℕ 

namespace ℕ
protected def ofNat : Nat → ℕ
  | 0          => .zero
  | Nat.succ n => .succ (ℕ.ofNat n)

@[default_instance 200]
instance (n : Nat) : OfNat ℕ n where
  ofNat := ℕ.ofNat n
end ℕ


def plus (m n : ℕ) : ℕ := match m with
  | .zero => n
  | .succ m => (plus m n).succ
  
infixl:65 (priority := high) " + " => plus

def times (m n : ℕ) : ℕ := match m with
  | .zero => 0
  | .succ m => n + times m n

infixl:70 (priority := high) " * " => times

def power (m n : ℕ) : ℕ := match n with
  | .zero => 1
  | .succ n => m * power m n

local infixl:75 (priority := high) " ^ " => power


