import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.Use
import Mathlib.Tactic.CongrExclamation

-- import LeanYjs.Network.Basic

abbrev CausalOrder A := PartialOrder A

section CausalOrder

class Operation (A : Type) where
  State : Type
  Error : Type
  effect : A → State → Except Error State

variable {A : Type} [DecidableEq A] (hb : CausalOrder A)

def hb_concurrent (a b : A) : Prop :=
  ¬ (hb.le a b) ∧ ¬ (hb.le b a)

inductive hb_consistent : List A → Prop where
  | nil : hb_consistent []
  | cons : ∀ (a : A) (ops : List A),
      hb_consistent ops →
      (∀ b, b ∈ ops → ¬ b ≤ a) →
      hb_consistent (a :: ops)

theorem option_not_lt_same {x : Option ℕ} :
  ¬ x < x := by
  intro h
  cases x with
  | none =>
    simp at h
  | some n =>
    simp at h

theorem List.memf_idxOf?_eq_some {a : A} {l : List A} :
  a ∈ l → ∃ idx, l.idxOf? a = some idx := by
  induction l with
  | nil =>
    simp
  | cons b l ih =>
    intro h_mem
    simp at h_mem
    cases Decidable.eq_or_ne a b with
    | inl h_eq =>
      rw [h_eq]
      use 0
      simp [List.idxOf?_cons]
    | inr h_neq =>
      have h_mem_tail : a ∈ l := by
        cases h_mem with
        | inl => contradiction
        | inr => assumption
      specialize ih h_mem_tail
      obtain ⟨ idx, h_idx ⟩ := ih
      use idx + 1
      simp [List.idxOf?_cons, h_idx]
      intros h_eq
      subst a
      contradiction

omit [DecidableEq A] in lemma hb_consistent_tail (a : A) (ops : List A) :
  (h_consistent : hb_consistent hb (a :: ops)) →
  hb_consistent hb ops := by
  intro h_consistent
  cases h_consistent
  assumption

omit [DecidableEq A] theorem no_dup_cons_eq (a : A) {ops₀ ops₁ : List A} :
  (∀ x, x ∈ a :: ops₀ ↔ x ∈ a :: ops₁) →
  (a :: ops₀).Nodup → (a :: ops₁).Nodup →
  (∀ x, x ∈ ops₀ ↔ x ∈ ops₁) := by
  intros h_mem_iff no_dup₀ no_dup₁ x
  specialize h_mem_iff x
  simp at h_mem_iff no_dup₀ no_dup₁
  obtain ⟨ a_not_mem_ops₀, no_dup₀ ⟩ := no_dup₀
  obtain ⟨ b_not_mem_ops₁, no_dup₁ ⟩ := no_dup₁
  constructor
  . intro h_mem_ops₀
    have h : x = a ∨ x ∈ ops₀ := by
      right; assumption
    rw [h_mem_iff] at h
    cases h with
    | inl h_eq =>
      subst h_eq
      contradiction
    | inr h_mem_ops₁ =>
      assumption
  . intro h_mem_ops₁
    have h : x = a ∨ x ∈ ops₁ := by
      right; assumption
    rw [← h_mem_iff] at h
    cases h with
    | inl h_eq =>
      subst h_eq
      contradiction
    | inr h_mem_ops₀ =>
      assumption

variable [Operation A]

abbrev Effect := Operation.State A → Except (Operation.Error A) (Operation.State A)

def effect (op : A) : Effect (A := A) :=
  Operation.effect op

def effect_comp (op1 op2 : Effect (A := A)) : Effect (A := A) := fun s => op1 s >>= op2

local infix:99 " ▷ " => effect_comp

theorem effect_comp_assoc (op1 op2 op3 : Effect (A := A)) :
  effect_comp (effect_comp op1 op2) op3 = effect_comp op1 (effect_comp op2 op3) := by
  funext s
  simp [effect_comp]
  unfold effect_comp
  simp

def concurrent_commutative (list : List A) : Prop :=
  ∀ a b, a ∈ list → b ∈ list → hb_concurrent hb a b →
    effect_comp (effect a) (effect b) = effect_comp (effect b) (effect a)

omit [Operation A] in theorem hb_consistent_concurrent (a : A) (ops₀ ops₁ : List A) :
  hb_consistent hb (ops₀ ++ a :: ops₁) →
  ∀ x, x ∈ ops₀ → ¬a ≤ x := by
  intro h_consistent x h_mem
  induction ops₀ with
  | nil =>
    simp at h_mem
  | cons y ys ih =>
    simp at h_mem
    cases h_consistent with
    | cons b ops h_consistent_tail h_no_lt =>
      simp at h_no_lt
      cases h_mem with
      | inl h_eq =>
        subst x
        apply h_no_lt
        simp
      | inr h_mem_tail =>
        apply ih h_consistent_tail h_mem_tail

theorem hb_concurrent_foldr {ops₀ ops₁ : List A} :
  concurrent_commutative hb (ops₀ ++ a :: ops₁) →
  (∀ x ∈ ops₀, hb_concurrent hb x a) →
  List.foldr (effect_comp (A := A)) (effect a ▷ init) (List.map (fun a => effect a) ops₀) =
  effect a ▷ List.foldr (effect_comp (A := A)) init (List.map (fun a => effect a) ops₀) := by
  induction ops₀ with
  | nil =>
    simp
  | cons b bs ih =>
    intro h_comm h_concurrent
    simp
    rw [ih]
    . rw [←effect_comp_assoc]
      have h_effect_b_effect_a_comm : effect b ▷ effect a = effect a ▷ effect b := by
        apply h_comm
        . simp
        . simp
        . apply h_concurrent; simp
      rw [h_effect_b_effect_a_comm]
      rw [effect_comp_assoc]
    . intros x y h_x_mem h_y_mem
      apply h_comm
      . simp at *
        right; assumption
      . simp at *
        right; assumption
    . intros; apply h_concurrent; simp; right; assumption

theorem hb_consistent_effect_convergent (ops₀ ops₁ : List A) (init : Effect)
  (h_consistent₀ : hb_consistent hb ops₀)
  (h_consistent₁ : hb_consistent hb ops₁)
  (h_commutative : concurrent_commutative hb ops₀)
  (no_dup₀ : ops₀.Nodup) (no_dup₁ : ops₁.Nodup) :
  (∀ a, a ∈ ops₀ ↔ a ∈ ops₁) →
  (ops₀.map (fun a => effect a) |> List.foldr effect_comp init) =
  (ops₁.map (fun a => effect a) |> List.foldr effect_comp init) :=
by
  induction ops₀ generalizing ops₁ init with
  | nil =>
    intros h_mem
    have ops₁_eq_nil : ops₁ = [] := by
      cases ops₁ with
      | nil => rfl
      | cons a ops₁ =>
        specialize h_mem a
        simp at h_mem
    rw [ops₁_eq_nil]
  | cons a ops₀ ih =>
    intros h_mem
    cases ops₁ with
    | nil =>
      specialize h_mem a
      simp at h_mem
    | cons b ops₁ =>
      by_cases h_eq : a = b
      . -- Case a = b
        simp
        rw [h_eq]
        ext s
        congr 1
        apply ih
        . apply hb_consistent_tail hb a ops₀ h_consistent₀
        . apply hb_consistent_tail hb b ops₁ h_consistent₁
        . intros a b h_a_mem h_b_mem h_concurrent
          apply h_commutative
          . simp; right; assumption
          . simp; right; assumption
          . assumption
        . simp at no_dup₀
          obtain ⟨ h_no_dup₀ ⟩ := no_dup₀
          assumption
        . simp at no_dup₁
          obtain ⟨ h_no_dup₁ ⟩ := no_dup₁
          assumption
        . subst h_eq
          apply no_dup_cons_eq _ h_mem no_dup₀ no_dup₁
      . -- Case a ≠ b
        have ⟨ ops₁_first, ops₁_last, h_ops₁_eq ⟩ : ∃ ops₁_first ops₁_last, ops₁ = ops₁_first ++ a :: ops₁_last := by
          have h_a_mem_ops₁ : a ∈ ops₁ := by
            specialize h_mem a
            simp at h_mem
            cases h_mem with
            | inl h_eq' =>
              subst h_eq'
              contradiction
            | inr h_mem' =>
              assumption
          rw [List.mem_iff_append] at h_a_mem_ops₁
          assumption
        rw [h_ops₁_eq]
        simp
        have h_a_concurrent_op₁_first : ∀ x, x ∈ ops₁_first → hb_concurrent hb x a := by
          intros x h_mem_ops₁_first
          constructor
          . cases h_consistent₀ with
            | cons _ _ h_consistent_tail h_no_lt =>
              apply h_no_lt
              have h_x_in_ops1 : x ∈ b :: ops₁ := by
                rw [h_ops₁_eq]
                simp
                right; left; assumption
              have x_neq_a : x ≠ a := by
                intro h_eq'
                rw [h_ops₁_eq] at no_dup₁
                rw [List.nodup_cons] at no_dup₁
                simp at no_dup₁
                obtain ⟨ _, h_no_dup₁ ⟩ := no_dup₁
                rw [List.nodup_append] at h_no_dup₁
                obtain ⟨ _, _, h_no_dup_last ⟩ := h_no_dup₁
                simp at h_no_dup_last
                apply h_no_dup_last at h_mem_ops₁_first
                obtain ⟨ h_eq'', _ ⟩ := h_mem_ops₁_first
                contradiction
              rw [← h_mem] at h_x_in_ops1
              simp at h_x_in_ops1
              cases h_x_in_ops1 with
              | inl h_eq' =>
                contradiction
              | inr h_mem' =>
                assumption
          . apply hb_consistent_concurrent hb a (b :: ops₁_first) ops₁_last
            . rw [h_ops₁_eq] at h_consistent₁
              assumption
            . simp; right; assumption
        . subst h_ops₁_eq
          have h_concurrent : concurrent_commutative hb (ops₁_first ++ a :: ops₁_last) := by
            sorry
          have h_a_b_concurrent : hb_concurrent hb a b := by
            sorry
          rw [hb_concurrent_foldr hb h_concurrent h_a_concurrent_op₁_first]
          rw [<-effect_comp_assoc]
          rw [h_commutative b a]
          rw [effect_comp_assoc]
          congr!
          rw [ih (b :: ops₁_first ++ ops₁_last) init]
          simp
          . cases h_consistent₀
            assumption
          . sorry
          . intros x y h_x_mem h_ey_mem h_concurrent
            apply h_commutative
            simp; right; assumption
            simp; right; assumption
            assumption
          . simp at no_dup₀
            obtain ⟨ ⟩ := no_dup₀
            assumption
          . sorry
          . intros x
            constructor
            . intro h_mem₀
              have h_mem₀_cons : x ∈ a :: ops₀ := by
                simp; right; assumption
              rw [h_mem] at h_mem₀_cons
              simp at *
              rcases h_mem₀_cons with h_eq' | ⟨ h | ⟨ h | h ⟩ ⟩
              . left; assumption
              . right; left; assumption
              . subst h; obtain ⟨ h_eq'', _ ⟩ := no_dup₀
                contradiction
              . right; right; assumption
            . sorry
          . rw [h_mem]
            simp
          . simp
          . sorry

end CausalOrder
