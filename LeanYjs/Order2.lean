import Mathlib.Tactic.Basic
import Mathlib.Tactic.WLOG
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.ApplyAt

variable { α : Type }
variable (r : α → α → Prop)

inductive OrderRankLowerBound : α → Nat → Prop where
  | zero a : OrderRankLowerBound a 0
  | succ (a n)
      (witness : α)
      (hr : r witness a)
      (hw : OrderRankLowerBound witness n) :
      OrderRankLowerBound a (n + 1)

@[simp]
def OrderRankRel (r : α → α → Prop) (a : α) (n : Nat) : Prop :=
  OrderRankLowerBound r a n ∧ (∀ m, OrderRankLowerBound r a m -> m <= n)

section HaveRank

variable (hHaveRank : ∀ x, ∃ n, OrderRankRel r x n)

lemma OrderRankRelUnique ( a : α ) :
  forall ( n m : Nat ), OrderRankRel r a n -> OrderRankRel r a m -> n = m := by
  intro n m h1 h2
  obtain ⟨ h1, h1' ⟩ := h1
  obtain ⟨ h2, h2' ⟩ := h2
  have hor : n ≤ m := by
    apply h2' <;> assumption
  have hor : m ≤ n := by
    apply h1' <;> assumption
  omega

lemma OrderRankRelLt (a b : α) (n m : Nat) :
  OrderRankRel r a n -> OrderRankRel r b m -> r a b -> n < m := by
  intro hna hmb rab
  obtain ⟨ hn, hna ⟩ := hna
  obtain ⟨ hm, hmb ⟩ := hmb
  have h1 : OrderRankLowerBound r b (n + 1) := by
    apply OrderRankLowerBound.succ <;> assumption
  have h2 : n + 1 <= m := by
    apply hmb <;> assumption
  omega

lemma OrderRankRelEq (a b : α) (n : Nat) :
  OrderRankRel r a n -> OrderRankRel r b n -> ¬ r a b := by
  intro hna hmb rab
  have h : n < n := by
    apply OrderRankRelLt r a b n n <;> assumption
  omega

end HaveRank

lemma OrderRankRelUpperBound (a : α) (n : Nat) :
  (∀ m, OrderRankLowerBound r a m -> m <= n) → ∃ m, OrderRankRel r a m ∧ m <= n := by
  intro h
  induction n generalizing a with
  | zero =>
    exists 0
    constructor
    . constructor
      . constructor
      . tauto
    . omega
  | succ n ih =>
    by_cases hle : OrderRankLowerBound r a (n + 1)
    . exists n + 1
      constructor <;> tauto
    . have h1 : ∀ m, OrderRankLowerBound r a m -> m <= n := by
        intro m h
        have  h2 : m <= n + 1 := by tauto
        wlog h3 : m = n + 1
        . omega
        subst h3
        tauto
      apply ih at h1
      obtain ⟨ m, hm, hle ⟩ := h1
      exists m
      tauto
