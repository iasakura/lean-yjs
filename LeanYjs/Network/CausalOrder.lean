import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.Use
import Mathlib.Tactic.CongrExclamation

import LeanYjs.ListLemmas

open List

-- import LeanYjs.Network.Basic

abbrev CausalOrder A := PartialOrder A

section CausalOrder

class Operation (A : Type) where
  State : Type
  Error : Type
  init : State
  effect : A → State → Except Error State

variable {A : Type} [DecidableEq A] (hb : CausalOrder A)

def hb_concurrent (a b : A) : Prop :=
  ¬ (hb.le a b) ∧ ¬ (hb.le b a)

omit [DecidableEq A] in theorem hb_concurrent_symm {a b : A} :
  hb_concurrent hb a b ↔ hb_concurrent hb b a := by
  simp [hb_concurrent, and_comm]

inductive hb_consistent : List A → Prop where
  | nil : hb_consistent []
  | cons : ∀ (a : A) (ops : List A),
      hb_consistent ops →
      (∀ b, b ∈ ops → ¬ b ≤ a) →
      hb_consistent (a :: ops)

inductive hb_strong_consistent : List A → List A → Prop where
  | nil : hb_strong_consistent ops []
  | cons : ∀ (a : A) (ops₀ ops₁ : List A),
      hb_strong_consistent (a :: ops₀) ops₁ →
      (∀b, b < a → b ∈ ops₀) →
      hb_strong_consistent ops₀ (a :: ops₁)

theorem List.sublist_mem {A : Type} {l₁ l₂ : List A} (h_sublist : l₁ <+ l₂) {a : A} :
  a ∈ l₁ → a ∈ l₂ := by
  intros h_mem
  induction h_sublist with
  | slnil =>
    assumption
  | @cons l₁ l₂ x h_sublist ih =>
    simp
    right; simp [ih, h_mem]
  | @cons₂ l₁ l₂ x h_sublist ih =>
    simp at h_mem |-
    cases h_mem with
    | inl h_eq =>
      left; assumption
    | inr h_mem =>
      right; simp [ih, h_mem]

omit [DecidableEq A] in theorem hb_consistent_sublist {ops₀ ops₁ : List A} :
  hb_consistent hb ops₀ →
  ops₁ <+ ops₀ →
  hb_consistent hb ops₁ := by
  intros h_consistent h_sublist
  induction h_sublist with
  | slnil =>
    assumption
  | @cons l₁ l₂ x h_sublist ih =>
    cases h_consistent
    apply ih; assumption
  | @cons₂ l₁ l₂ x h_sublist ih =>
    cases h_consistent with
    | cons a ops h_consistent_tail h_consistent_h_no_lt =>
      apply hb_consistent.cons
      . apply ih; assumption
      . intros b h_b_mem h_b_leq_x
        have h_b_mem_l₂ : b ∈ l₂ := by
          apply List.sublist_mem h_sublist; assumption
        apply h_consistent_h_no_lt b h_b_mem_l₂ h_b_leq_x

theorem option_not_lt_same {x : Option ℕ} :
  ¬ x < x := by
  intro h
  cases x with
  | none =>
    simp at h
  | some n =>
    simp at h

omit [DecidableEq A] in lemma hb_consistent_tail (a : A) (ops : List A) :
  (h_consistent : hb_consistent hb (a :: ops)) →
  hb_consistent hb ops := by
  intro h_consistent
  cases h_consistent
  assumption

variable [Operation A]

abbrev Effect := Operation.State A → Except (Operation.Error A) (Operation.State A)

def effect (op : A) : Effect (A := A) :=
  Operation.effect op

def effect_comp (op1 op2 : Effect (A := A)) : Effect (A := A) := fun s => op1 s >>= op2

local infix:99 " ▷ " => effect_comp

omit [DecidableEq A] in theorem effect_comp_assoc (op1 op2 op3 : Effect (A := A)) :
  effect_comp (effect_comp op1 op2) op3 = effect_comp op1 (effect_comp op2 op3) := by
  funext s
  simp [effect_comp]
  unfold effect_comp
  simp

def compatibleOp [DecidableEq A] (s : Operation.State A) (op : A) : Prop :=
  ∃ops, hb_consistent hb ops ∧
    (∀ a, a < op → a ∈ ops) ∧
    (∀ a ∈ ops, ¬op ≤ a) ∧
    (ops.map (fun a => effect a) |> List.foldr effect_comp Except.pure) Operation.init = Except.ok s

def concurrent_commutative (list : List A) : Prop :=
  ∀ a b, a ∈ list → b ∈ list → hb_concurrent hb a b →
    ∀ s : Operation.State A, compatibleOp hb s a → compatibleOp hb s b →
      effect_comp (effect a) (effect b) s = effect_comp (effect b) (effect a) s

omit [DecidableEq A] [Operation A] in theorem hb_consistent_concurrent (a : A) (ops₀ ops₁ : List A) :
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

inductive compatibleOps [DecidableEq A] (hb : CausalOrder A) : Operation.State A → List A → Prop where
  | nil : compatibleOps hb s []
  | cons :
      compatibleOp hb s a →
      effect a s = Except.ok s' →
      compatibleOps hb s' ops' →
      compatibleOps hb s (a :: ops')

theorem hb_concurrent_foldr {ops₀ ops₁ : List A} {s : Operation.State A} :
  concurrent_commutative hb (ops₀ ++ a :: ops₁) →
  (∀ x ∈ ops₀, hb_concurrent hb x a) →
  compatibleOps hb s (ops₀ ++ a :: ops₁) →
  List.foldr (effect_comp (A := A)) (effect a ▷ init) (List.map (fun a => effect a) ops₀) s =
  (effect a ▷ List.foldr (effect_comp (A := A)) init (List.map (fun a => effect a) ops₀)) s := by
  induction ops₀ with
  | nil =>
    simp
  | cons b bs ih =>
    intro h_comm h_concurrent hcompatible
    simp
    symm
    calc
      _ = ((effect a ▷ effect b) ▷ (foldr effect_comp init (map (fun a => effect a) bs))) s := by rw [effect_comp_assoc]
      _ = ((effect a ▷ effect b) s >>= (foldr effect_comp init (map (fun a => effect a) bs))) := by rfl
      _ = ((effect b ▷ effect a) s >>= (foldr effect_comp init (map (fun a => effect a) bs))) := by
        rw [h_comm a b] <;> try grind [hb_concurrent]
        simp [hb_concurrent] at *
        grind
        



    rw [ih]
    . rw [←effect_comp_assoc]
      have h_effect_b_effect_a_comm : effect b ▷ effect a = effect a ▷ effect b := by
        ext s
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

theorem effect_comp_apply {op1 op2 : Effect (A := A)} {s : Operation.State A} :
  effect_comp op1 op2 s = op1 s >>= op2 := by
  rfl

theorem hb_consistent_effect_convergent (ops₀ ops₁ : List A) (init : Effect) s
  (h_consistent₀ : hb_consistent hb ops₀)
  (h_consistent₁ : hb_consistent hb ops₁)
  (hcompatible₀ : compatibleOps hb s ops₀)
  (hcompatible₁ : compatibleOps hb s ops₁)
  (h_commutative : concurrent_commutative hb ops₀)
  (no_dup₀ : ops₀.Nodup) (no_dup₁ : ops₁.Nodup) :
  (∀ a, a ∈ ops₀ ↔ a ∈ ops₁) →
  (ops₀.map (fun a => effect a) |> List.foldr effect_comp init) s =
  (ops₁.map (fun a => effect a) |> List.foldr effect_comp init) s :=
by
  induction ops₀ generalizing ops₁ s with
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
        simp [effect_comp]
        rw [h_eq]
        have (eq := hx) x := effect b s; rw [<-hx]
        cases x with
        | error e => rfl
        | ok x =>
          simp [bind, Except.bind.eq_2]
          apply ih
          . apply hb_consistent_tail hb a ops₀ h_consistent₀
          . apply hb_consistent_tail hb b ops₁ h_consistent₁
          . cases hcompatible₀; grind
          . cases hcompatible₁; grind
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
            apply List.no_dup_cons_eq _ h_mem no_dup₀ no_dup₁
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
        have h_a_concurrent_op₁_first : ∀ x, x ∈ b :: ops₁_first → hb_concurrent hb x a := by
          intros x h_mem_ops₁_first
          constructor
          . cases h_consistent₀ with
            | cons _ _ h_consistent_tail h_no_lt =>
              apply h_no_lt
              have h_x_in_ops1 : x ∈ b :: ops₁ := by
                rw [h_ops₁_eq]
                rw [<-List.cons_append]
                apply List.mem_append_left
                assumption
              have x_neq_a : x ≠ a := by
                rw [h_ops₁_eq] at no_dup₁
                have h_eq' : (b :: (ops₁_first ++ a :: ops₁_last)) = ((b :: ops₁_first) ++ a :: ops₁_last) := by
                  simp
                rw [h_eq'] at no_dup₁
                rw [List.nodup_append] at no_dup₁
                obtain ⟨ _, _, h_not_a_mem ⟩ := no_dup₁
                apply h_not_a_mem
                . assumption
                . simp
              rw [←h_mem] at h_x_in_ops1
              simp at h_x_in_ops1
              cases h_x_in_ops1 with
              | inl h_eq' =>
                contradiction
              | inr h_mem' =>
                assumption
          . apply hb_consistent_concurrent hb a (b :: ops₁_first) ops₁_last
            . rw [h_ops₁_eq] at h_consistent₁
              assumption
            . assumption
        subst h_ops₁_eq
        -- Here, we have ops₁ = ops₁_first ++ a :: ops₁_last and a || ops₁_first
        have h_concurrent : concurrent_commutative hb (ops₁_first ++ a :: ops₁_last) := by
          intros c d h_c_mem h_d_mem h_concurrent
          simp at h_c_mem h_d_mem
          apply h_commutative c d _ _ h_concurrent
          . rw [h_mem]; simp
            right; assumption
          . rw [h_mem]; simp
            right; assumption
        have h_a_b_concurrent : hb_concurrent hb a b := by
          rw [hb_concurrent_symm]
          apply h_a_concurrent_op₁_first
          simp
        have h_a_concurrent_op₁_first : ∀ x, x ∈ ops₁_first → hb_concurrent hb x a := by
          intros; apply h_a_concurrent_op₁_first; simp; right; assumption
        rw [hb_concurrent_foldr hb h_concurrent h_a_concurrent_op₁_first]
        rw [<-effect_comp_assoc]
        have heq :
          ((effect b ▷ effect a) ▷ foldr effect_comp (foldr effect_comp init (map (fun a => effect a) ops₁_last))
            (map (fun a => effect a) ops₁_first)) s =
          ((effect b ▷ effect a) s) >>= foldr effect_comp (foldr effect_comp init (map (fun a => effect a) ops₁_last))
            (map (fun a => effect a) ops₁_first) := by
          simp [effect_comp]
        rw [heq, h_commutative b a]
        . have heq :
            (effect a ▷ effect b) s >>=
              foldr effect_comp (foldr effect_comp init (map (fun a => effect a) ops₁_last)) (map (fun a => effect a) ops₁_first) =
            ((effect a ▷ effect b) ▷ foldr effect_comp (foldr effect_comp init (map (fun a => effect a) ops₁_last))
              (map (fun a => effect a) ops₁_first)) s := by
            simp [effect_comp]
          rw [heq]
          rw [effect_comp_assoc]
          rw [effect_comp_apply]
          rw [effect_comp_apply]
          cases heq : effect a s with
          | error e => rfl
          | ok s' =>
            simp [bind, Except.bind.eq_2]
            rw [ih (b :: ops₁_first ++ ops₁_last)]
            . simp
            . cases h_consistent₀
              assumption
            . apply hb_consistent_sublist _ h_consistent₁
              simp
            . cases hcompatible₀; grind
            . cases hcompatible₁

            . intros x y h_x_mem h_ey_mem h_concurrent
              apply h_commutative
              simp; right; assumption
              simp; right; assumption
              assumption
            . simp at no_dup₀
              obtain ⟨ ⟩ := no_dup₀
              assumption
            . apply Nodup.sublist _ no_dup₁
              simp
            -- . intros op h_op_mem
            --   obtain ⟨ ops', hops' ⟩ := h_compatible op (by simp [h_op_mem])
            --   use ops' ++ [a]
            --   sorry
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
              . grind
        . rw [h_mem]
          simp
        . simp
        . simp [hb_concurrent] at *
          obtain ⟨ h_not_le_ab, h_not_le_ba ⟩ := h_a_b_concurrent
          constructor <;> assumption
        . cases hcompatible₁; grind
        . cases hcompatible₀; grind

end CausalOrder
