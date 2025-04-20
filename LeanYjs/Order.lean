import Mathlib.Tactic.Basic
import Mathlib.Tactic.WLOG
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.ApplyAt

def immediateLt {α : Type} (r : α → α → Prop) (a b : α) : Prop :=
  r a b ∧ ¬ ∃ c, r a c ∧ r c b

inductive OrderRankRel {α : Type} (r : α → α → Prop) : α → Nat → Prop where
  | zero (a) : (∀ x, ¬ r x a) → OrderRankRel r a 0
  | succ (a n)
      (witness : α)
      (hr : immediateLt r witness a)
      (hw : OrderRankRel r witness n)
      (h_all : ∀ x, r x a → (¬ ∃ b, r x b ∧ immediateLt r b a) -> OrderRankRel r x n) :
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
      obtain ⟨ _, h ⟩ := hrelm
      obtain ⟨⟩ | ⟨ a, n, witness, hr, hw, h_all ⟩ := hreln
      obtain ⟨ h1, h2 ⟩ := hr
      exfalso
      apply h at h1 <;> assumption
    | succ m =>
      obtain ⟨⟩ | ⟨ a, m, witness, hr, hw, h_all ⟩ := hrelm
      obtain ⟨⟩ | ⟨ a, n, witness', hr', hw', h_all' ⟩ := hreln
      rewrite [ih (a := witness') (m := m)] <;> try tauto
      apply h_all <;> try assumption
      unfold immediateLt at hr' <;> tauto
      unfold immediateLt at *
      obtain ⟨ h1, h2 ⟩ := hr'
      intros hneg
      obtain ⟨ b, h1 ⟩ := hneg
      apply h2
      exists b
      tauto
      omega

lemma OrderRankRelLt {α : Type} (r : α -> α -> Prop) (a b : α) (n m : Nat) :
  OrderRankRel r a n -> OrderRankRel r b m -> r a b -> n < m := by
  intro hna hmb rab
  induction m generalizing n a b with
  | zero =>
    obtain ⟨ b, hnb ⟩ := hmb
    -- b has rank 0, so no x with r x b, but r a b, contradiction
    exfalso
    exact hnb a rab
  | succ m him =>
    obtain ⟨  ⟩ | ⟨ _, _, witness, hw1, hw2, h_all ⟩  := hmb
    wlog himm : ∃ b_1, r a b_1 ∧ immediateLt r b_1 b
    . have hna' : OrderRankRel r a m := by
        apply h_all <;> try assumption

      have heq : n = m := by
        apply OrderRankRelUnique (a := a) <;> assumption
      omega

    obtain ⟨ a', ha', ha'' ⟩ := himm

    have ha'm : OrderRankRel r a' m := by
      apply h_all (x := a')  <;> try assumption
      . unfold immediateLt at ha'' <;> tauto
      . intros hneg
        obtain ⟨ b_1, h1, h2, h3 ⟩ := hneg
        obtain ⟨ h4, h5 ⟩ := ha''
        apply h5
        exists b_1

    have hlt : n < m := by
      apply him (b := a') <;> try assumption
    omega
