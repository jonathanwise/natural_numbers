import plus_one
import plus_assoc_example
import times_one
import one_times
import times_assoc
import f
import g
import disj_comm
import sum_comm
import propositional_example_1
import conj_comm
import conj_assoc
import modus_ponens
import propositional_example_2
import modus_tollens


theorem disj_assoc : P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := by
  apply Iff.intro
  · intro h
    cases h
    case mp.inl hp =>
      apply Or.inl
      apply Or.inl
      exact hp
    case mp.inr hqr =>
      cases hqr
      case inl hq =>
        apply Or.inl
        apply Or.inr
        exact hq
      case inr hr =>
        apply Or.inr
        exact hr
  · intro h
    induction h using Or.rec
    case mpr.inl hpq =>
      induction hpq using Or.rec
      case inl hp =>
        apply Or.inl
        exact hp
      case inr hq =>
        apply Or.inr
        apply Or.inl
        exact hq
    case mpr.inr hr =>
      apply Or.inr
      apply Or.inr
      exact hr





theorem partial_contraposition ( h : P → Q ) ( hnq : ¬ Q ) : ¬ P := by
  change P → False
  intro hp
  change Q → False at hnq
  apply hnq
  apply h
  exact hp

open Classical
theorem contraposition : ( P → Q ) ↔ (¬ Q → ¬ P) := by
  apply Iff.intro
  · intro hpq
    intro hnq
    intro hp
    apply hnq
    apply hpq
    exact hp
  · intro h
    intro hp
    apply byContradiction
    intro hnq
    have := h hnq
    contradiction

theorem implication_composition  {P Q R : Prop} ( hpr : P → R ) ( hqr : Q → R ) : P ∨ Q → R := by
  intro hpq
  apply Or.elim hpq
  · intro hp
    apply hpr
    exact hp
  · intro hq
    apply hqr
    exact hq

  




theorem ex_falso {P : Prop} : False → P := by
  intro h
  cases h


open Classical
theorem iff_neg_neg {P:Prop} : P ↔ ¬ ¬ P := by
  apply Iff.intro
  · intro hp
    intro hnp
    contradiction
  · intro hnnp
    apply byContradiction
    intro hnp
    contradiction


theorem universal_conjunction_example 
  { T : Type } { P Q R : T → Prop }
  (h₁ : ∀ x:T, P x → Q x) 
  (h₂ : ∀ x:T, P x → R x) 
  : ∀ x:T, P x → Q x ∧ R x := by
  intro t 
  intro hpt 
  apply And.intro 
  have := h₁ t
  apply this 
  exact hpt 
  have := h₂ t 
  apply this 
  exact hpt 


theorem not_forall_from_exists_not (h : ∃ x:T, ¬ P x) : ¬ ∀ x:T, P x := by
  /- Our goal is to show ¬ ∀ x:T, P x. -/
  intro h₁ /- We prove a negation by assuming the thing we want to negate and deriving a contradiction. -/
  obtain ⟨t, hnpt⟩ := h /- h says that there is some x in T where ¬ P x, so we can introduce a t:T and hnpt:¬P t to our knowledge. -/
  have := h₁ t /- h₁ says that P x is true for every x in T, so we can apply it to t, since t is in T. This gives us P t. -/
  contradiction /- But now we have both P t and ¬ P t, which is a contradiction. -/



theorem not_exists_from_forall_not (h : ∀ x:T, ¬ P x) : ¬ ∃ x:T, P x := by
    intro h₁ /- We have to prove ¬ ∃ x:T, P x, so we assume ∃ x:T, P x and derive a contradiction. -/
    obtain ⟨t,hpt⟩ := h₁ /- h₁ says there is an x in T where P x is true, so we can introduce a t in T and P t. -/
    have h₂ := h t /- h applies to every x in T so it applied to t.  This gives ¬ P t. -/
    contradiction /- And ¬ P t contradicts P t. -/


theorem forall_not_from_not_exists (h : ¬ ∃ x:T, P x) : ∀ x:T, ¬ P x := by
    /- Our goal is ∀ x:T, ¬ P x. -/
    intro t /- The goal is universally quantified, so we introduce t in T and we need to show ¬ P t. -/
    intro hpt /- We prove ¬ P t by assuming P t and deriving a contradiction. -/
    /- Now we need a plan.  Where will the contradiction come from?  The goal will be to contradict ¬ ∃ x, P x. -/
    have h₁ : ∃ x, P x := by
        apply Exists.intro t
        exact hpt
    contradiction


open Classical
theorem exists_not_from_not_forall (h : ¬ ∀ x:T, P x) : ∃ x:T, ¬ P x := by
  /- Our goal is ∃ x:T, ¬ P x. -/
  apply byContradiction /- We will argue by contradiction.  This changes our goal to (original goal) → False. -/
  intro a /- Our goal is ¬ ∃x, ¬ P x so we assume ∃ x, ¬ P x and derive a contradiction. -/
  apply h /- h says that ∀ x:T, P x is false, so we can obtain a contradiction by proving ∀ x:T, P x.  Now our goal becomes ∀ x:T, P x. -/
  intro t /- We prove the universally quantified statement ∀ x:T, P t by introducing t an arbitrary t in T and showing that P t is true -/
  apply byContradiction /- We'll do this one by contradiction again.  This changes our goal to showing that the opposite of our goal is false. -/
  intro hnpt /- We show ¬ P t → False by assuming ¬ P t and deriving a contradiction. -/
  apply a /- Since ¬ ∃ x, ¬ P x, we can get a contradiction by proving ∃ x, ¬ P x. -/
  apply Exists.intro t /- To prove an existentially quantified statement, we just need to find some x in T such that ¬ P x.  We'll use t. Our goal changes to showing ¬ P t. -/
  exact hnpt /- And we already know ¬ P t. -/


theorem not_forall_iff_exists_not  : (¬ ∀ x:T, P x) ↔ (∃ x:T, ¬ P x) := by
  apply Iff.intro
  · intro h
    apply exists_not_from_not_forall
    exact h
  · intro h
    apply not_forall_from_exists_not
    exact h


theorem not_exists_iff_forall_not : (¬ ∃ x:T, P x) ↔ (∀ x:T, ¬ P x) := by
  apply Iff.intro
  · intro h
    apply forall_not_from_not_exists
    exact h
  · intro h
    apply not_exists_from_forall_not
    exact h
