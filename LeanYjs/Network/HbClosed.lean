import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.Use
import Mathlib.Tactic.CongrExclamation
import Mathlib.Data.List.Induction

import LeanYjs.ListLemmas

open List

abbrev CausalOrder A := PartialOrder A

section hb_concurrent

variable {A : Type} (hb : CausalOrder A)

def hb_concurrent (a b : A) : Prop :=
  ¬ (hb.le a b) ∧ ¬ (hb.le b a)

theorem hb_concurrent_symm {a b : A} :
  hb_concurrent hb a b ↔ hb_concurrent hb b a := by
  simp [hb_concurrent, and_comm]

def hbClosed (ops : List A) : Prop :=
  ∀a b l₁ l₂, ops = l₁ ++ a :: l₂ → b < a → b ∈ l₁

inductive hbClosedI : List A → Prop where
  | nil : hbClosedI []
  | append_singleton : ∀ (a : A) (ops : List A),
      hbClosedI ops →
      (∀b < a, b ∈ ops) →
      hbClosedI (ops ++ [a])

theorem hbClosed_hbClosedI {ops : List A} :
  hbClosed hb ops → hbClosedI (hb := hb) ops := by
  induction ops using List.reverseRecOn with
  | nil =>
    grind [hbClosedI]
  | append_singleton ops x ih =>
    intros hclosed
    constructor
    . apply ih
      grind [hbClosed]
    . intros b hlt
      grind [hbClosed]

theorem hbClosedI_hbClosed {ops : List A} :
  hbClosedI (hb := hb) ops → hbClosed hb ops := by
  intros h
  induction h with
  | nil =>
    simp [hbClosed]
  | append_singleton x ops hclosed h_all_lt ih =>
    intros a b l₁ l₂ heq hlt
    cases List.eq_nil_or_concat' l₂ with
    | inl hnil =>
      subst l₂
      grind [List.append_inj']
    | inr hconcat =>
      obtain ⟨ l₂, y, heq_l₂ ⟩ := hconcat
      subst heq_l₂
      rw [←List.cons_append, ←List.append_assoc] at heq
      have ⟨ heq, hxy ⟩ := List.append_inj' heq (by simp)
      grind [hbClosed]

theorem hbClosed_iff_hbClosedI {ops : List A} :
  hbClosed hb ops ↔ hbClosedI (hb := hb) ops := by
  constructor
  · exact hbClosed_hbClosedI (hb := hb)
  · exact hbClosedI_hbClosed (hb := hb)

theorem hbClosedI_snoc {l : List A} :
  hbClosedI (hb := hb) l →
  l = [] ∨ ∃ ops a, l = ops ++ [a] ∧ hbClosedI (hb := hb) ops ∧ (∀ b < a, b ∈ ops) := by
  intro h
  cases h with
  | nil =>
    left; rfl
  | append_singleton a ops h_ops h_all =>
    right
    refine ⟨ ops, a, rfl, h_ops, h_all ⟩

theorem hbClosed_append_singleton_of_all_lt {ops : List A} {a : A} :
  hbClosed hb ops →
  (∀ x < a, x ∈ ops) →
  hbClosed hb (ops ++ [a]) := by
  intro h_closed h_all
  have h_closedI : hbClosedI (hb := hb) ops :=
    hbClosed_hbClosedI (hb := hb) h_closed
  have h_closedI' : hbClosedI (hb := hb) (ops ++ [a]) :=
    hbClosedI.append_singleton a ops h_closedI h_all
  exact hbClosedI_hbClosed (hb := hb) h_closedI'

-- Swapping adjacent concurrent elements preserves hbClosedI.
theorem hbClosedI_swap (ops₀ ops₁ : List A) (a b : A) :
  hbClosedI (hb := hb) (ops₀ ++ a :: b :: ops₁) →
  hb_concurrent hb b a →
  hbClosedI (hb := hb) (ops₀ ++ b :: a :: ops₁) := by
  intro h_closed h_concurrent
  -- induct on the suffix ops₁ (last element)
  induction ops₁ using List.reverseRecOn generalizing ops₀ with
  | nil =>
    -- ops₀ ++ a :: b :: [] = (ops₀ ++ [a]) ++ [b]
    have h_closed' : hbClosedI (hb := hb) ((ops₀ ++ [a]) ++ [b]) := by
      simpa [List.append_assoc] using h_closed
    have h_snoc := hbClosedI_snoc (hb := hb) h_closed'
    have h_ne : ((ops₀ ++ [a]) ++ [b]) ≠ [] := by simp
    cases h_snoc with
    | inl hnil =>
      cases (h_ne hnil)
    | inr hsnoc =>
      obtain ⟨ ops, x, h_eq, h_ops, h_all ⟩ := hsnoc
      -- ops ++ [x] = (ops₀ ++ [a]) ++ [b]
      have h_parts := List.append_inj' h_eq (by simp)
      have h_ops_eq : ops = ops₀ ++ [a] := h_parts.1.symm
      have h_x_eq : x = b := by
        have : [x] = [b] := h_parts.2.symm
        simpa using this
      subst h_x_eq
      have h_ops' : hbClosedI (hb := hb) (ops₀ ++ [a]) := by
        simpa [h_ops_eq] using h_ops
      -- extract hbClosedI ops₀
      have h_snoc2 := hbClosedI_snoc (hb := hb) h_ops'
      have h_ne2 : ops₀ ++ [a] ≠ [] := by simp
      cases h_snoc2 with
      | inl hnil =>
        cases (h_ne2 hnil)
      | inr hsnoc2 =>
        obtain ⟨ ops', a', h_eq2, h_ops0, h_all_a ⟩ := hsnoc2
        have h_parts2 := List.append_inj' h_eq2 (by simp)
        have h_ops0_eq : ops' = ops₀ := h_parts2.1.symm
        have h_a_eq : a' = a := by
          have : [a'] = [a] := h_parts2.2.symm
          simpa using this
        subst h_a_eq
        have h_ops0' : hbClosedI (hb := hb) ops₀ := by
          simpa [h_ops0_eq] using h_ops0
        -- build ops₀ ++ [b]
        have h_ops0b : hbClosedI (hb := hb) (ops₀ ++ [x]) := by
          apply hbClosedI.append_singleton
          · exact h_ops0'
          · intro t ht
            -- from h_all : ∀ t < x, t ∈ ops₀ ++ [a']
            have ht' : t ∈ ops₀ ++ [a'] := by
              have := h_all t ht
              simpa [h_ops_eq] using this
            -- t ≠ a' since a' < x would contradict concurrency
            have h_not_a_lt_b : ¬ a' < x := by
              intro hlt
              exact h_concurrent.2 (le_of_lt hlt)
            -- thus t ∈ ops₀
            simp [List.mem_append] at ht'
            cases ht' with
            | inl hmem =>
              simpa [List.mem_append, hmem] using (Or.inl hmem)
            | inr h_eq =>
              subst h_eq
              cases (h_not_a_lt_b ht)
        -- now append a to get ops₀ ++ [b] ++ [a]
        have h_ops0ba : hbClosedI (hb := hb) ((ops₀ ++ [x]) ++ [a']) := by
          apply hbClosedI.append_singleton
          · exact h_ops0b
          · intro t ht
            have ht' : t ∈ ops₀ := by
              have := h_all_a t ht
              simpa [h_ops0_eq] using this
            simpa [List.mem_append, ht'] using (Or.inl ht')
        simpa [List.append_assoc] using h_ops0ba
  | append_singleton ops₁ x ih =>
    -- ops₁ = ops₁ ++ [x]
    have h_closed' : hbClosedI (hb := hb) ((ops₀ ++ a :: b :: ops₁) ++ [x]) := by
      simpa [List.append_assoc] using h_closed
    have h_snoc := hbClosedI_snoc (hb := hb) h_closed'
    have h_ne : (ops₀ ++ a :: b :: ops₁) ++ [x] ≠ [] := by simp
    cases h_snoc with
    | inl hnil =>
      cases (h_ne hnil)
    | inr hsnoc =>
      obtain ⟨ ops, y, h_eq, h_ops, h_all ⟩ := hsnoc
      -- ops = ops₀ ++ a :: b :: ops₁, y = x
      have h_parts := List.append_inj' h_eq (by simp)
      have h_ops_eq : ops = ops₀ ++ a :: b :: ops₁ := h_parts.1.symm
      have h_y_eq : y = x := by
        have : [y] = [x] := h_parts.2.symm
        simpa using this
      subst h_y_eq
      have h_ops' : hbClosedI (hb := hb) (ops₀ ++ a :: b :: ops₁) := by
        simpa [h_ops_eq] using h_ops
      have h_swapped : hbClosedI (hb := hb) (ops₀ ++ b :: a :: ops₁) :=
        ih ops₀ h_ops'
      -- append x back; need ∀ t < x, t ∈ ops₀ ++ b :: a :: ops₁
      have h_swapped' : hbClosedI (hb := hb) ((ops₀ ++ b :: a :: ops₁) ++ [y]) := by
        apply hbClosedI.append_singleton
        · exact h_swapped
        · intro t ht
          have ht' : t ∈ ops₀ ++ a :: b :: ops₁ := by
            have := h_all t ht
            simpa [h_ops_eq] using this
          -- membership preserved under swapping a and b
          simp [List.mem_append] at ht'
          rcases ht' with ht' | ht'
          · simpa [List.mem_append, ht'] using (Or.inl ht')
          · rcases ht' with ht' | ht'
            · -- t = a
              subst ht'
              simp [List.mem_append]
            · rcases ht' with ht' | ht'
              · -- t = b
                subst ht'
                simp [List.mem_append]
              · simp [List.mem_append, ht']
      simpa [List.append_assoc] using h_swapped'

-- Swapping adjacent concurrent elements preserves hbClosed.
theorem hbClosed_swap (ops₀ ops₁ : List A) (a b : A) :
  hbClosed hb (ops₀ ++ a :: b :: ops₁) →
  hb_concurrent hb b a →
  hbClosed hb (ops₀ ++ b :: a :: ops₁) := by
  intro h_closed h_concurrent
  rw [hbClosed_iff_hbClosedI (hb := hb)] at h_closed ⊢
  exact hbClosedI_swap (hb := hb) ops₀ ops₁ a b h_closed h_concurrent

-- Remove a concurrent element b (and a trailing a) while preserving hbClosed.
theorem hbClosed_remove_concurrent (ops₀ ops₁ : List A) (a b : A) :
  hbClosed hb (ops₀ ++ b :: ops₁ ++ [a]) →
  (∀ x ∈ ops₁, hb_concurrent hb x b) →
  hbClosed hb (ops₀ ++ ops₁) := by
  intro h_closed h_concurrent
  have h_closedI : hbClosedI (hb := hb) (ops₀ ++ b :: ops₁ ++ [a]) :=
    (hbClosed_hbClosedI (hb := hb)) h_closed
  -- move b right across ops₁
  have h_moved : hbClosedI (hb := hb) (ops₀ ++ ops₁ ++ b :: [a]) := by
    have aux :
      ∀ (ops₀ ops₁ : List A),
        hbClosedI (hb := hb) (ops₀ ++ b :: ops₁ ++ [a]) →
        (∀ x ∈ ops₁, hb_concurrent hb x b) →
        hbClosedI (hb := hb) (ops₀ ++ ops₁ ++ b :: [a]) := by
      intro ops₀ ops₁ h_closedI h_concurrent
      induction ops₁ generalizing ops₀ with
      | nil =>
        simpa [List.append_assoc] using h_closedI
      | cons x xs ih =>
        have hx : hb_concurrent hb x b := by
          have := h_concurrent x (by simp)
          simpa using this
        have h_swapped : hbClosedI (hb := hb) (ops₀ ++ x :: b :: xs ++ [a]) := by
          have h0 : hbClosedI (hb := hb) (ops₀ ++ b :: x :: (xs ++ [a])) := by
            simpa [List.append_assoc] using h_closedI
          have h1 := hbClosedI_swap (hb := hb) ops₀ (xs ++ [a]) b x h0 hx
          simpa [List.append_assoc] using h1
        have h_swapped' : hbClosedI (hb := hb) ((ops₀ ++ [x]) ++ b :: xs ++ [a]) := by
          simpa [List.append_assoc] using h_swapped
        have h_concurrent' : ∀ y ∈ xs, hb_concurrent hb y b := by
          intro y hy
          exact h_concurrent y (by simp [hy])
        have h_ih := ih (ops₀ := ops₀ ++ [x]) h_swapped' h_concurrent'
        simpa [List.append_assoc] using h_ih
    exact aux ops₀ ops₁ h_closedI h_concurrent
  -- drop trailing a, then b
  have h_moved' : hbClosedI (hb := hb) ((ops₀ ++ ops₁ ++ [b]) ++ [a]) := by
    simpa [List.append_assoc] using h_moved
  have h_snoc1 := hbClosedI_snoc (hb := hb) h_moved'
  have h_ne1 : (ops₀ ++ ops₁ ++ [b]) ++ [a] ≠ [] := by simp
  cases h_snoc1 with
  | inl hnil =>
    cases (h_ne1 hnil)
  | inr hsnoc =>
    obtain ⟨ ops, a', h_eq, h_ops, h_all ⟩ := hsnoc
    have h_parts := List.append_inj' h_eq (by simp)
    have h_ops_eq : ops = ops₀ ++ ops₁ ++ [b] := h_parts.1.symm
    have h_a_eq : a' = a := by
      have : [a'] = [a] := h_parts.2.symm
      simpa using this
    subst h_a_eq
    have h_ops' : hbClosedI (hb := hb) (ops₀ ++ ops₁ ++ [b]) := by
      simpa [h_ops_eq] using h_ops
    have h_snoc2 := hbClosedI_snoc (hb := hb) h_ops'
    have h_ne2 : ops₀ ++ ops₁ ++ [b] ≠ [] := by simp
    cases h_snoc2 with
    | inl hnil =>
      cases (h_ne2 hnil)
    | inr hsnoc2 =>
      obtain ⟨ ops2, b', h_eq2, h_ops2, h_all2 ⟩ := hsnoc2
      have h_parts2 := List.append_inj' h_eq2 (by simp)
      have h_ops2_eq : ops2 = ops₀ ++ ops₁ := h_parts2.1.symm
      have h_b_eq : b' = b := by
        have : [b'] = [b] := h_parts2.2.symm
        simpa using this
      subst h_b_eq
      have h_ops2' : hbClosedI (hb := hb) (ops₀ ++ ops₁) := by
        simpa [h_ops2_eq] using h_ops2
      exact hbClosedI_hbClosed (hb := hb) h_ops2'

end hb_concurrent
