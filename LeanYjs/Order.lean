import Mathlib.Tactic.Basic
import Mathlib.Tactic.WLOG
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.ApplyAt

inductive OrderRankRel { α : Type } (r : α → α → Prop) : α → Nat → Prop where
  | zero (a) : (∀ x, ¬ r x a) -> OrderRankRel r a 0
  | succ (a n)
      (witness : α)
      (hr : r witness a)
      (hw : OrderRankRel r witness n)
      (h_all : ∀ x, r x a → OrderRankRel r x n) :
      OrderRankRel r a (n + 1)

lemma OrderRankRelUnique { α : Type } { r : α → α → Prop } ( a : α ) :
  forall ( n m : Nat ), OrderRankRel r a n -> OrderRankRel r a m -> n = m := by
  intro n m h1 h2
  wlog hmn : m < n with H
  case inr =>
    have hor : n = m ∨ n < m := by omega
    cases hor with
    | inl eq =>
      apply eq
    | inr hlt =>
      symm
      apply (H (n := m) (m := n)) <;> try assumption

  revert a h1 m h2
  induction n with
  | zero =>
    omega
  | succ n ih =>
    intro a m hreln hrelm hineq
    cases m with
    | zero =>
      cases hrelm with
      | zero _ h =>
        cases hreln with
        | succ a n witness hr hw h_all =>
          apply h at hr
          tauto
    | succ m =>
      cases hrelm with
      | succ a m witness hr hw h_all =>
        cases hreln with
        | succ a n witness' hr' hw' h_all' =>
          rewrite [ih (a := witness') (m := m)] <;> try tauto
          omega
